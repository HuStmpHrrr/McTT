(** * The Constructors of a View in the Gluing Model

    A view's constructor is its container's at the view's instance of the
    container's uniform parameters ([wf_exp_eq_con_view]): the view's
    parameters and arguments, glued along the view's telescopes, are glued
    along the container's at the instance, since the two telescopes are
    equal there, syntactically ([decl_typed_view_nparams], [decl_typed_view_args]) and in
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
From Mctt.Core.Syntactic Require Import Records.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Completeness.Records Require Model.
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

(** A term glued at a type along a substitution [σ'] that is [τ] then [σ]
    is glued along [σ] at the instance by [τ]: its values along [τ] and at
    the value of [τ] are related, by its validity. *)
Lemma glu_with_sub_along : forall Γ0 Δ0 τ M A RΓ0 (i : nat) Δ σ σ' ρ ρτ,
    Γ0 ⊨ˢ τ ≈ τ : Δ0 -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> RΓ0 ρ ρ -> ⟦ τ ⟧s ρ ↘ ρτ ->
    Δ0 ⊨ M : A -> sb_eq (τ ⨟ σ) σ' ->
    glu_rel_exp_with_sub i Δ M A σ' ρτ ->
    exists j : nat, glu_rel_exp_with_sub j Δ M[τ] A[τ] σ ρ.
Proof.
  intros * Hτ HRΓ0 Hρ Eτ HM Heq [a m P El Ea Em Hg HMg].
  destruct HM as [R0 HΔ0 l HMgen].
  destruct (HMgen _ _ HRΓ0 _ _ Hτ _ _ _ _ Hρ Eτ Eτ)
    as (E & [aτ a1 a2 aτ' Eaτ Ea1 Ea2 Eaτ' Hac] & [mτ m1 m2 mτ' Emτ Em1 Em2 Emτ' Hmc]).
  assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (m1 = m) as -> by (eapply functional_eval_exp; eassumption).
  destruct Hac as (Hac1 & _); destruct Hmc as (Hmc1 & _).
  set (J := Nat.max i l).
  destruct (glu_univ_elem_cumu_ge (i := i) (j := J) (Nat.le_max_l _ _) Hg) as (P1 & El1 & Hg1).
  pose proof (glu_univ_elem_exp_cumu_ge (Nat.le_max_l i l) Hg Hg1 HMg) as HMg1.
  pose proof (per_univ_elem_cumu_ge l J _ _ _ (Nat.le_max_r _ _) Hac1) as HacJ.
  destruct (per_univ_elem_sym _ _ _ _ HacJ) as [HacJ' HEsym].
  pose proof (proj1 (per_univ_elem_trans _ _ _ _ HacJ) _ _ HacJ') as Hττ.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ E HacJ') Hg1) as Hgτ.
  exists J.
  refine (mk_glu_rel_exp_with_sub _ _ _ _ _ _ aτ mτ P1 El1 Eaτ Emτ Hgτ _).
  rewrite !exp_sub_sub, !(exp_sub_sb_eq _ _ _ Heq).
  eapply glu_univ_elem_trm_resp_per_elem; [ exact Hgτ | exact Hττ | exact HMg1 | exact (HEsym _ _ Hmc1) ].
Qed.

(** Terms glued along [σ] at the instances of a closed telescope are glued
    arguments of it, at their values. *)
Lemma params_glu_args_at : forall C Γ RΓ Δ σ ρ Ms vs, tele_ass C -> ctx_scoped 0 C -> ⊨ C -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T ->
       exists i : nat, glu_rel_exp_with_sub i Δ N T σ ρ) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> glu_args Δ C Id nil (List.map (fun M => M[σ]) Ms) vs.
Proof.
  intros * Hass Hs HC HΓ HRΓ Hρ Hl HMs HMg Hv.
  pose proof (closed_args_gargs _ _ _ _ _ _ Hass HC HΓ HRΓ Hρ Hl HMs Hv) as Hpg.
  assert (Lv : List.length vs = List.length C) by (rewrite <- Hl; exact (Completeness.Inductives.Model.eval_exps_length _ _ _ Hv)).
  constructor; [ rewrite List.length_map; exact Hl | exact Lv |].
  intros k M T v A HM HT Hv' HA.
  apply nth_error_map_inv in HM as (N & HN & ->).
  rewrite <- (tele_insts_sub C 0 Id Id σ Ms Hass Hs ltac:(intros; lia)) in HT.
  apply nth_error_map_inv in HT as (T0 & HT0 & ->).
  destruct (HMg k N T0 HN HT0) as [i [a m P El Ea Em Hgl HNg]].
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

(** Terms glued at the instances of a closed telescope are glued
    arguments of it, at their values. *)
Lemma params_glu_args : forall C Γ RΓ Sb Δ σ ρ Ms vs, tele_ass C -> ctx_scoped 0 C -> ⊨ C -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊩ N : T) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> glu_args Δ C Id nil (List.map (fun M => M[σ]) Ms) vs.
Proof.
  intros * Hass Hs HC HΓ HRΓ HSb Hσ Hl HMs HMg Hv.
  eapply params_glu_args_at; [ exact Hass | exact Hs | exact HC | exact HΓ | exact HRΓ
                             | exact (glu_ctx_env_per_env HSb HRΓ Hσ) | exact Hl | exact HMs | | exact Hv ].
  intros k N T HN HT.
  destruct (glu_rel_exp_clean_inversion1 HSb (HMg k N T HN HT)) as [i Hi].
  exists i; exact (Hi _ _ _ Hσ).
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

(** A substitution of a list of terms past a telescope [C] is glued when
    each term is glued at its instance's type, at any gluing of the
    type's value at which the instance is glued: the substitution of the
    terms before it is glued, so the type is. *)
Lemma glu_sub_of_list_by : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    tele_ass C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 -> List.length Ms = List.length C -> List.length vs = List.length C ->
    (forall k M T v A a (i : nat) P El, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C σ0 Ms) k = Some T ->
       List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass A) ->
       ⟦ A ⟧ env_args ρ0 (List.firstn k vs) ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ T ® P ->
       Δ ⊢ M : T ® v ∈ El) ->
    Δ ⊢ˢ sb_of_list σ0 Ms ® env_args ρ0 vs ∈ Sb.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass HC H0 Hσ L1 L2 Hby.
  - destruct Ms; [| discriminate ]; destruct vs; [| discriminate ]; cbn.
    apply (functional_glu_ctx_env H0 HC); exact Hσ.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M0 Ms]; [ cbn in L1; lia |]; destruct vs as [| v0 vs]; [ cbn in L2; lia |].
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (glu_ctx_env_suffix _ _ _ Hass HC) as [Sb1 HC1].
    destruct (glu_ctx_env_cons_clean_inversion H0 HC1) as (i' & HA & HT & HSb1).
    destruct (HT _ _ _ Hσ) as [a' P' El' Ha' Hglu' HP'].
    assert (HM0 : Δ ⊢ M0 : A[σ0] ® v0 ∈ El').
    { apply (Hby 0 M0 A[σ0] v0 A a' i' P' El'); try reflexivity; try assumption.
      - rewrite tele_insts_snoc; reflexivity.
      - rewrite List.rev_app_distr; reflexivity. }
    assert (Hσ1 : Δ ⊢ˢ σ0,,M0 ® ρ0 ↦ v0 ∈ Sb1)
      by (apply HSb1; eapply cons_glu_sub_pred_helper; eassumption).
    cbn [sb_of_list env_args List.fold_left].
    cbn [List.length] in L1, L2.
    refine (IH _ _ _ _ _ _ Ms vs Hass HC HC1 Hσ1 ltac:(lia) ltac:(lia) _).
    intros k M T v A0 a i P El HM HT0 Hv HA0 Ea Hg HTP.
    apply (Hby (S k) M T v A0 a i P El); try assumption.
    + rewrite tele_insts_snoc; exact HT0.
    + rewrite List.rev_app_distr; exact HA0.
Qed.

(** The same, the terms glued along the telescope: each at its type's
    value, its type glued there. *)
Lemma glu_args_by : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    tele_ass C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 -> List.length Ms = List.length C -> List.length vs = List.length C ->
    (forall k M T v A a (i : nat) P El, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C σ0 Ms) k = Some T ->
       List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass A) ->
       ⟦ A ⟧ env_args ρ0 (List.firstn k vs) ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ T ® P ->
       Δ ⊢ M : T ® v ∈ El) ->
    glu_args Δ C σ0 ρ0 Ms vs.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass HC H0 Hσ L1 L2 Hby.
  - destruct Ms; [| discriminate ]; destruct vs; [| discriminate ]; apply glu_args_nil.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M0 Ms]; [ cbn in L1; lia |]; destruct vs as [| v0 vs]; [ cbn in L2; lia |].
    pose proof HC as HC0; rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (glu_ctx_env_suffix _ _ _ Hass HC) as [Sb1 HC1].
    destruct (glu_ctx_env_cons_clean_inversion H0 HC1) as (i' & HA & HT & HSb1).
    destruct (HT _ _ _ Hσ) as [a' P' El' Ha' Hglu' HP'].
    assert (HM0 : Δ ⊢ M0 : A[σ0] ® v0 ∈ El').
    { apply (Hby 0 M0 A[σ0] v0 A a' i' P' El'); try reflexivity; try assumption.
      - rewrite tele_insts_snoc; reflexivity.
      - rewrite List.rev_app_distr; reflexivity. }
    assert (Hσ1 : Δ ⊢ˢ σ0,,M0 ® ρ0 ↦ v0 ∈ Sb1)
      by (apply HSb1; eapply cons_glu_sub_pred_helper; eassumption).
    cbn [List.length] in L1, L2.
    apply (proj2 (glu_args_snoc _ _ _ _ _ _ _ _ _)); split; [ exact (mk_glu_arg _ _ _ _ _ _ _ a' P' El' Ha' Hglu' HP' HM0) |].
    refine (IH _ _ _ _ _ _ Ms vs Hass HC HC1 Hσ1 ltac:(lia) ltac:(lia) _).
    intros k M T v A0 a i P El HM HT0 Hv HA0 Ea Hg HTP.
    apply (Hby (S k) M T v A0 a i P El); try assumption.
    + rewrite tele_insts_snoc; exact HT0.
    + rewrite List.rev_app_distr; exact HA0.
Qed.

(** ** The Group's Members at Glued Uniform Parameters

    A declared member's type former applied to glued uniform parameters is
    glued at the member's type over them ([self_ty]): the gluing of the
    former ([glu_rel_exp_ind0]) at the parameters given. *)

Section SelfArgs.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.

  Lemma self_entry_glu : forall j Mj Δ Us ups, ind_member D j = Some Mj -> j < ind_ndecl D -> ⊢ Δ ->
      glu_args Δ (ind_uparams D) Id nil Us ups ->
      glu_arg Δ (env_args nil ups) (self_ty D Mj) (self_ty D Mj)[sb_of_list Id Us] (apps (a_ind p j) Us) (d_ind p j ups).
  Proof.
    intros * HMj Hj HΔ HUs.
    destruct (member_lt_decl _ _ _ _ _ Hdt HMj Hj) as [pm Hh].
    pose proof (decl_closed_params_ass D j Mj Hc HMj) as HassP.
    pose proof (grp_tele_ass_nparams _ Hass _ _ HMj) as HassN.
    pose proof (decl_closed_ass _ Hc) as HassU.
    destruct (glu_ind_decl_params _ HG _ _ HMj) as [SbP HSbP]; unfold im_params in HSbP.
    destruct (glu_ctx_env_suffix _ _ _ HassN HSbP) as [SbU HSbU].
    assert (Hσ : Δ ⊢ˢ sb_of_list Id Us ® env_args nil ups ∈ SbU).
    { eapply glu_sub_of_list with (C := ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact HassU | rewrite List.app_nil_r; exact HSbU | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ | exact HUs ]. }
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LUs Lups].
    destruct (ind_ty_typed0 _ _ _ _ _ Hdt HMj) as [j0 Hj0].
    destruct (glu_ctx_env_entries_valid _ _ _ HassN HSbP j0) as (i & Hji & HAents).
    assert (Hi : ⋅ ⊢ ind_ty D Mj : Typeω@i) by (eapply lift_exp_ge; [ exact Hji | exact Hj0 ]).
    pose proof Hi as Hi'; unfold ind_ty in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ HassP Hi') as [HCs _].
    assert (HST : ind_uparams D ⊢ self_ty D Mj : Typeω@i)
      by (pose proof (HCs (im_nparams Mj) (ind_uparams D) eq_refl) as H; rewrite List.app_nil_r in H; exact H).
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HassU HUs) as Hgu.
    assert (Lu : List.length ups = ind_nu D) by (unfold ind_nu; congruence).
    pose proof (completeness_fundamental_exp _ _ _ HST) as HSTv.
    destruct (rel_exp_of_typ_inversion_simple HSTv) as [RU [HRU Hty]].
    pose proof (Completeness.Inductives.Model.uparams_rel_env D HD ups ups Hgu Lu RU HRU) as HρU.
    destruct (Hty _ _ HρU) as (a & a' & Ea & _ & Haa).
    assert (Haa' : per_univ i a a) by (etransitivity; [ exact Haa | symmetry; exact Haa ]).
    destruct (per_univ_glu_univ_elem _ _ Haa') as (P & El & HgA).
    assert (HM : Δ ⊢ apps (a_ind p j) Us : (self_ty D Mj)[sb_of_list Id Us] ® d_ind p j ups ∈ El).
    { pose proof Ea as Ea0; unfold self_ty in Ea0 |- *.
      eapply (ctx_pi_glu_elem_by (fun xs w => w = d_ind p j xs) (a_ind p j) (im_params D Mj ++ ⋅))
        with (Δt := im_nparams Mj) (Γb := ind_uparams D) (Sb_b := SbU) (Sb := SbP) (xs := ups);
        [ reflexivity | | exact HassN | exact HSbU | exact HSbP | exists nil; unfold im_params; rewrite List.app_nil_r; reflexivity
        | intros; eapply HAents; eassumption
        | | exact Hσ | congruence | reflexivity | | | | exact Ea0 | exact HgA ].
      all: clear HAents.
      - (** One more argument: the former at it. *)
        intros Δ1 Γ' Sb' Δ' σ' xs x w HT _ _ HlΓ ->.
        exists (d_ind p j (xs ++ x :: nil)); split; [| reflexivity ].
        eapply eval_app_indty; [ exact Hl | exact HMj |].
        assert (List.length Γ' <= List.length (im_params D Mj ++ ⋅)) by (rewrite HT, List.length_app; lia).
        rewrite List.app_nil_r, length_im_params in *; lia.
      - intros Δ1 Δ2 Heq.
        pose proof (HCs Δ1 (Δ2 ++ ind_uparams D) ltac:(unfold im_params; rewrite Heq, List.app_assoc; reflexivity)) as H.
        rewrite List.app_nil_r in H; exact H.
      - fold (self_ty D Mj).
        eapply wf_apps_closed_pi; [ exact HassU | exact (decl_closed_uparams _ Hc) | exact (self_ty_scoped _ _ _ Hc HMj) | exact HST | exact HΔ
                                  | | exact LUs | intros; eapply glu_args_typed; [ exact HassU | exact HUs | eassumption | eassumption ] ].
        unfold self_ty; rewrite <- ctx_pi_app; change (ctx_pi (im_nparams Mj ++ ind_uparams D) (ind_sort D)[wk_shiftn (im_nn Mj)]ʷ)
          with (ind_ty D Mj).
        eapply wf_ind; eassumption.
      - (** The value is in the relation of the type: the former at the
            variables is valid. *)
        intros R a0 Ea1 HR.
        pose proof (Completeness.Inductives.Model.valid_self_apps D HD Hc (valid_group_sort _ _ Hg) p Hl Hass (decl_typed_order _ _ _ Hdt)
                      (decl_typed_mvc _ _ _ Hdt) j Mj HMj Hj) as HV.
        destruct (rel_exp_under_ctx_simple HV) as (RU2 & HRU2 & l & Hsim).
        pose proof (Completeness.Inductives.Model.uparams_rel_env D HD ups ups Hgu Lu RU2 HRU2) as HρU2.
        destruct (Hsim _ _ HρU2) as (b & b' & R0 & Eb & Eb' & HR0 & m & m' & Em & Em' & Hmm).
        assert (Ed : ⟦ apps (a_ind p j) (vars_from 0 (ind_nu D)) ⟧ env_args nil ups ↘ d_ind p j ups).
        { apply Modules.eval_apps_exp; exists (d_ind p j nil), ups; split; [ constructor | split ].
          - pose proof (Decl.eval_vars_from_args ups nil nil) as H; rewrite List.app_nil_r in H; cbn in H.
            rewrite <- Lu; exact H.
          - exact (eval_apps_indty p D j Mj ups nil Hl HMj ltac:(cbn; unfold im_np; lia)). }
        assert (m = d_ind p j ups) as -> by (eapply functional_eval_exp; eassumption).
        assert (m' = d_ind p j ups) as -> by (eapply functional_eval_exp; eassumption).
        unfold self_ty in Eb, Eb'.
        assert (b = a0) as -> by (eapply functional_eval_exp; eassumption).
        assert (b' = a0) as -> by (eapply functional_eval_exp; eassumption).
        apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR0 HR); exact Hmm.
      - (** All the parameters: the former's sort. *)
        intros Δ' φ Ms vs w' Hφ HgN -> b P0 El0 Hb Hgb HPb.
        assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
        pose proof (glu_args_wk _ _ _ _ _ _ _ HassU (decl_closed_uparams _ Hc) Hφ HUs) as HUs'.
        apply (glu_args_closed_base _ _ _ (sb_wk Id φ) _ _ _ HassU (decl_closed_uparams _ Hc)) in HUs'.
        apply (glu_args_sb_eq _ _ _ _ _ _ _ (sb_wk_sb_of_list Us Id φ)) in HgN.
        destruct (glu_args_length _ _ _ _ _ _ HgN) as [LMs Lvs].
        assert (Hall : glu_args Δ' (im_params D Mj) Id nil (List.map (fun N => N[φ]ʷ) Us ++ Ms) (ups ++ vs)).
        { apply (glu_args_closed_base _ _ (sb_wk Id φ) _ _ _ _ HassP (decl_closed_params _ _ _ Hc HMj)).
          unfold im_params; apply glu_args_app; [ exact HassU | rewrite List.length_map; exact LUs | exact Lups |].
          split; [ exact HUs' | exact HgN ]. }
        pose proof (ind_former_base p D Hl HG Hc Hdt (valid_group_sort _ _ Hg) Hass j Mj pm Δ' _ _ i b P0 El0 HMj Hh HΔ' Hall Hb Hgb HPb)
          as H.
        rewrite (exp_sub_sb_eq _ _ _ (sb_of_list_cong Ms _ _ (sb_wk_sb_of_list Us Id φ))), <- sb_of_list_app.
        rewrite (sb_of_list_scoped_base _ _ _ Id); [ exact H |].
        replace (List.length (List.map (fun X => X[φ]ʷ) Us ++ Ms)) with (im_np D Mj)
          by (rewrite List.length_app, List.length_map, LUs, LMs, length_im_nparams; unfold im_np, ind_nu; lia).
        exact (sort_shift_scoped D Hc Mj). }
    exact (mk_glu_arg _ _ _ _ _ _ i a P El Ea HgA (glu_univ_elem_trm_typ _ _ _ _ HgA _ _ _ _ HM) HM).
  Qed.

  (** *** The Members as Variables, at the Members' Values *)

  Lemma grp_selfs_from_app : forall j l1 l2,
      grp_selfs_from D j (l1 ++ l2) = grp_selfs_from D (j + List.length l1) l2 ++ grp_selfs_from D j l1.
  Proof.
    intros j l1; revert j; induction l1 as [| M l1 IH]; intros j l2; cbn [List.app grp_selfs_from List.length].
    - rewrite Nat.add_0_r, List.app_nil_r; reflexivity.
    - rewrite IH, <- List.app_assoc; replace (j + S (List.length l1)) with (S j + List.length l1) by lia; reflexivity.
  Qed.

  Let Hsu := valid_group_sort _ _ Hg.
  Let Hord := decl_typed_order _ _ _ Hdt.
  Let Hmv := decl_typed_mvc _ _ _ Hdt.

  (** The values of the members' type formers at the uniform parameters. *)
  Lemma eval_self_apps : forall ups l, List.length ups = ind_nu D -> (forall j, List.In j l -> j < ind_ndecl D) ->
      ⟦ List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) l ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups
        ↘ List.map (fun j => d_ind p j ups) l.
  Proof.
    intros ups l Lu; induction l as [| j l IH]; intros Hin; cbn [List.map]; [ constructor |].
    constructor; [| apply IH; intros; apply Hin; right; assumption ].
    assert (Hj : j < ind_ndecl D) by (apply Hin; left; reflexivity).
    destruct (List.nth_error (ind_members D) j) as [Mj |] eqn:HMj;
      [| apply List.nth_error_None in HMj; pose proof (ind_ndecl_le D); lia ].
    apply Modules.eval_apps_exp; exists (d_ind p j nil), ups; split; [ constructor | split ].
    - pose proof (Decl.eval_vars_from_args ups nil nil) as H; rewrite List.app_nil_r in H; cbn in H.
      rewrite <- Lu; exact H.
    - exact (eval_apps_indty p D j Mj ups nil Hl HMj ltac:(cbn; unfold im_np; lia)).
  Qed.

  (** The first [k] members as variables are the innermost entries of
      [grp_selfs]. *)
  Lemma selfs_split : forall k, k <= ind_ndecl D ->
      exists Rest, grp_selfs D = Rest ++ grp_selfs_from D 0 (List.firstn k (ind_members D)).
  Proof.
    intros k Hk; unfold grp_selfs.
    rewrite <- (List.firstn_skipn k (List.firstn (ind_ndecl D) (ind_members D))), grp_selfs_from_app, List.firstn_firstn,
      Nat.min_l by exact Hk.
    eexists; reflexivity.
  Qed.

  Lemma self_prefix_sem : forall k, k <= ind_ndecl D -> ⊨ grp_selfs_from D 0 (List.firstn k (ind_members D)) ++ ind_uparams D.
  Proof.
    intros k Hk; destruct (selfs_split k Hk) as [Rest HR].
    pose proof (Completeness.Inductives.Model.grp_sctx_sem D HD Hc) as HS; unfold grp_sctx in HS.
    rewrite HR, <- List.app_assoc in HS; exact (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HS).
  Qed.

  Lemma grp_selfs_ass : tele_ass (grp_selfs D).
  Proof.
    unfold grp_selfs; generalize 0; induction (List.firstn (ind_ndecl D) (ind_members D)) as [| M ms IH]; intros j;
      cbn [grp_selfs_from]; [ constructor |].
    apply List.Forall_app; split; [ apply IH | constructor; [ eexists; reflexivity | constructor ] ].
  Qed.

  Lemma length_grp_selfs : List.length (grp_selfs D) = ind_ndecl D.
  Proof. unfold grp_selfs; rewrite length_grp_selfs_from, List.length_firstn; pose proof (ind_ndecl_le D); lia. Qed.

  (** The uniform parameters and the first [k] members' values at them are
      related at the first [k] members as variables: [grp_sb] is valid
      ([grp_sb_gsub]). *)
  Lemma self_env_rel : forall ups, per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      forall k R, k <= ind_ndecl D ->
      EF grp_selfs_from D 0 (List.firstn k (ind_members D)) ++ ind_uparams D
        ≈ grp_selfs_from D 0 (List.firstn k (ind_members D)) ++ ind_uparams D ∈ per_ctx_env ↘ R ->
      R (env_args (env_args nil ups) (List.firstn k (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D)))))
        (env_args (env_args nil ups) (List.firstn k (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D))))).
  Proof.
    intros ups Hgu Lu k R Hk HR.
    set (ss := List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D))).
    assert (Lss : List.length ss = ind_ndecl D) by (unfold ss; rewrite List.length_map, List.length_seq; reflexivity).
    pose proof (Completeness.Inductives.Model.grp_sb_gsub D HD Hc Hsu p Hl Hass Hord Hmv) as Hgs.
    destruct (Completeness.LogicalRelation.Instance.gsub_props Hgs) as [_ Hlink].
    destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
    pose proof (Completeness.Inductives.Model.uparams_rel_env D HD ups ups Hgu Lu RU HRU) as HρU.
    pose proof (Completeness.Inductives.Model.grp_sctx_sem D HD Hc) as HSs.
    destruct (rel_ctx_wf_per_ctx_env HSs) as [RS HRS].
    destruct (Hlink _ _ HRU Id Id (rel_sub_id (ex_intro _ _ HRU)) RS HRS _ _ HρU (eval_sub_id _)) as (e1 & Ee1 & He).
    assert (Ess : ⟦ grp_sb p D ⟧s gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ env_args (env_args nil ups) ss).
    { unfold grp_sb; apply (Completeness.Inductives.Decl.eval_sb_of_list _ Id _ _ _ (eval_sub_id _)).
      apply (eval_self_apps ups _ Lu); intros j Hj; apply List.in_seq in Hj; lia. }
    pose proof (He _ Ess) as HRSe.
    assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
    assert (HRSs : RS (env_args (env_args nil ups) ss) (env_args (env_args nil ups) ss))
      by (etransitivity; [ symmetry |]; exact HRSe).
    clear e1 Ee1 He HRSe.
    assert (HassS : tele_ass (List.rev (grp_selfs D))) by exact (List.Forall_rev grp_selfs_ass).
    destruct (Completeness.Inductives.Decl.rel_gargs (List.rev (grp_selfs D)) (ind_uparams D) RU RS HRU
                ltac:(rewrite List.rev_involutive; exact HSs) HassS ltac:(rewrite List.rev_involutive; exact HRS)
                _ _ ss ss ltac:(rewrite List.length_rev, length_grp_selfs; exact Lss)
                ltac:(rewrite List.length_rev, length_grp_selfs; exact Lss) HRSs) as [_ Hpg].
    destruct (selfs_split k Hk) as [Rest HRest].
    rewrite HRest, List.rev_app_distr in Hpg.
    assert (Lk : List.length (List.firstn k ss) = List.length (List.rev (grp_selfs_from D 0 (List.firstn k (ind_members D)))))
      by (rewrite List.length_rev, length_grp_selfs_from, !List.length_firstn, Lss; pose proof (ind_ndecl_le D); lia).
    rewrite <- (List.firstn_skipn k ss) in Hpg.
    destruct (Completeness.Inductives.Decl.per_gargs_app _ _ _ _ _ _ _ _ Lk Hpg Lk) as [Hpre _].
    assert (Lu' : List.length ups = List.length (List.rev (ind_uparams D))) by (rewrite List.length_rev; exact Lu).
    pose proof (Completeness.Inductives.Decl.per_gargs_app_intro _ _ _ _ _ _ _ _ Lu' Hgu Hpre) as Hall.
    rewrite <- List.rev_app_distr in Hall.
    assert (Lall : List.length (ups ++ List.firstn k ss)
                   = List.length (grp_selfs_from D 0 (List.firstn k (ind_members D)) ++ ind_uparams D))
      by (rewrite !List.length_app; rewrite List.length_rev in Lk, Lu'; lia).
    pose proof (Completeness.Inductives.Model.gargs_env_rel _ R _ _ nil nil HR (self_prefix_sem k Hk) Lall Hall) as H.
    rewrite env_args_app in H; exact H.
  Qed.

  (** A member's type as the type of its variable, after the variables of
      the members before it, at their values: related to the member's type
      at the uniform parameters. *)
  Lemma self_wk_rel : forall ups, per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      forall k Mk a a0, k < ind_ndecl D -> ind_member D k = Some Mk ->
      ⟦ (self_ty D Mk)[wk_shiftn k]ʷ ⟧ env_args (env_args nil ups)
          (List.firstn k (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D)))) ↘ a ->
      ⟦ self_ty D Mk ⟧ env_args nil ups ↘ a0 ->
      exists l : nat, Dom a ≈ a0 ∈ per_univ l.
  Proof.
    intros ups Hgu Lu k Mk a a0 Hk HMk Ea Ea0.
    destruct (Completeness.Inductives.Model.self_ty_sem D HD Hc k Mk HMk) as [i HS].
    pose proof (self_prefix_sem k ltac:(lia)) as HC.
    assert (HPl : List.length (grp_selfs_from D 0 (List.firstn k (ind_members D))) = k)
      by (rewrite length_grp_selfs_from, List.length_firstn; pose proof (ind_ndecl_le D); lia).
    destruct (rel_exp_under_ctx_wk_simple (Completeness.UnitCases.rel_wk_under_ctx_shiftn _ (ind_uparams D) HC) HS)
      as (RW & HRW & l & Hwk).
    pose proof (self_env_rel ups Hgu Lu k RW ltac:(lia) HRW) as HE.
    destruct (Hwk _ _ HE) as (x & x' & Rx & Ex & Ex' & HRx & m & m' & Em & Em' & Hmm).
    rewrite HPl in Em.
    assert (Lf : List.length (List.firstn k (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D)))) = k)
      by (rewrite List.length_firstn, List.length_map, List.length_seq; lia).
    replace (List.length (grp_selfs_from D 0 (List.firstn k (ind_members D))))
      with (List.length (List.firstn k (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D))))) in Em' by congruence.
    rewrite Completeness.UnitCases.eval_wk_shiftn_args in Em'.
    assert (m = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (m' = a0) as -> by (eapply functional_eval_exp; eassumption).
    cbn in Ex; inversion Ex; subst.
    basic_invert_per_univ_elem HRx.
    match goal with Hm : ?r a a0, H : ?r <~> _ |- _ => apply H in Hm; destruct Hm as [Rm HRm] end.
    eexists; exists Rm; exact HRm.
  Qed.

  (** [grp_sb] after glued uniform parameters [Us] is glued at the members
      as variables, at the uniform parameters' values and the members'
      values at them. *)
  Lemma grp_sb_glu : forall Δ Us ups SbS, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      EG grp_sctx D ∈ glu_ctx_env ↘ SbS ->
      Δ ⊢ˢ sb_of_list (sb_of_list Id Us) (List.map (fun j => apps (a_ind p j) Us) (List.seq 0 (ind_ndecl D)))
        ® env_args (env_args nil ups) (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D))) ∈ SbS.
  Proof.
    intros * HΔ HUs HSbS.
    pose proof (decl_closed_ass _ Hc) as HassU.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HassU HUs) as Hgu.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LUs Lups].
    assert (Lu : List.length ups = ind_nu D) by (unfold ind_nu; congruence).
    unfold grp_sctx in HSbS.
    destruct (glu_ctx_env_suffix _ _ _ grp_selfs_ass HSbS) as [SbU HSbU].
    assert (Hσ : Δ ⊢ˢ sb_of_list Id Us ® env_args nil ups ∈ SbU).
    { eapply glu_sub_of_list with (C := ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact HassU | rewrite List.app_nil_r; exact HSbU | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ | exact HUs ]. }
    eapply glu_sub_of_list_by with (C := grp_selfs D) (Γ0 := ind_uparams D) (Sb0 := SbU);
      [ exact grp_selfs_ass | exact HSbS | exact HSbU | exact Hσ
      | rewrite List.length_map, List.length_seq, length_grp_selfs; reflexivity
      | rewrite List.length_map, List.length_seq, length_grp_selfs; reflexivity |].
    intros k M T v A a i P El HM HT Hv HA Ea Hga HPT.
    assert (Hk : k < ind_ndecl D)
      by (rewrite <- (List.length_seq (ind_ndecl D) 0), <- (List.length_map (fun j => d_ind p j ups));
          apply List.nth_error_Some; congruence).
    rewrite List.nth_error_map, (List.nth_error_nth' _ 0) in HM, Hv by (rewrite List.length_seq; exact Hk).
    rewrite List.seq_nth in HM, Hv by exact Hk; cbn in HM, Hv; injection HM as <-; injection Hv as <-.
    destruct (Completeness.Inductives.Model.nth_rev_grp_selfs D (ind_ndecl D) k (le_n _) Hk) as (Mk & HMk & HAk).
    unfold grp_selfs in HA; rewrite HAk in HA; injection HA as <-.
    apply tele_insts_nth in HT as (A' & HA' & ->).
    unfold grp_selfs in HA'; rewrite HAk in HA'; injection HA' as <-.
    (** The instance is the member's type at the uniform parameters. *)
    assert (HTe : (self_ty D Mk)[wk_shiftn k]ʷ[sb_of_list (sb_of_list Id Us)
                    (List.firstn k (List.map (fun j => apps (a_ind p j) Us) (List.seq 0 (ind_ndecl D))))]
                  = (self_ty D Mk)[sb_of_list Id Us]).
    { rewrite exp_sub_wk; apply exp_sub_sb_eq.
      intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      set (L := List.firstn k (List.map (fun j => apps (a_ind p j) Us) (List.seq 0 (ind_ndecl D)))).
      assert (HL : List.length L = k) by (unfold L; rewrite List.length_firstn, List.length_map, List.length_seq; lia).
      replace (x + k) with (List.length L + x) by lia.
      apply sb_of_list_ge. }
    rewrite HTe in HPT |- *.
    (** The member's former, glued at the type's value at the uniform
        parameters, and moved to the value given. *)
    destruct (self_entry_glu k Mk Δ Us ups HMk Hk HΔ HUs) as [i0 a0 P0 El0 Ea0 Hg0 HP0 HM0].
    destruct (self_wk_rel ups Hgu Lu k Mk a a0 Hk HMk Ea Ea0) as [l Hl'].
    eapply glu_univ_elem_exp_conv_uidx; [ symmetry; exact Hl' | exact Hg0 | exact Hga | exact HM0 | exact HPT ].
  Qed.
End SelfArgs.

(** ** A View's Parameters and Arguments, at its Container's Telescopes *)

Section ViewConArgs.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Let HgQ := Hcv _ _ _ _ _ _ _ HMk Hh Hq.
  Let HcQ := valid_group_closed _ _ HgQ.

  Lemma view_is_length : List.length Is = ind_nu Dq.
  Proof.
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-; exact HIl.
  Qed.

  (** The view's instance, filed, glued along glued uniform parameters of
      the group: the instance with the members as variables is glued
      ([glu_ind_decl_view_self]), along [grp_sb] after the parameters
      ([grp_sb_glu]), and so the filed instance is ([glu_with_sub_along]). *)
  Lemma filed_view_is_glu : forall Δ Us ups, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall j I T, List.nth_error Is j = Some I -> List.nth_error (tele_insts (ind_uparams Dq) Id Is) j = Some T ->
      exists i : nat, glu_rel_exp_with_sub i Δ I T (sb_of_list Id Us) (env_args nil ups).
  Proof.
    intros * HΔ HUs j I T HI HT.
    pose proof (decl_closed_ass _ Hc) as HassU.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HassU HUs) as Hgu.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LUs Lups].
    assert (Lu : List.length ups = ind_nu D) by (unfold ind_nu; congruence).
    destruct (glu_ind_decl_view_self _ HG) as [IsS HV].
    rewrite (glu_views_self_link _ _ HV _ (valid_group_mpath _ _ Hg) _ _ _ _ _ _ HMk Hh) in HI, HT.
    rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (grp_sb p D) (IsS k) (decl_closed_ass _ HcQ) (decl_closed_uparams _ HcQ)
                  ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HI as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    pose proof (glu_views_self_is _ _ HV _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HI0 HT0) as HgI.
    pose proof HgI as [SbS HSbS _ _].
    destruct (glu_rel_exp_clean_inversion1 HSbS HgI) as [iS HiS].
    pose proof (grp_sb_glu VP p D HVP HPD HG Δ Us ups SbS HΔ HUs HSbS) as HσS.
    pose proof (HiS _ _ _ HσS) as Hw.
    pose proof (Completeness.Inductives.Model.grp_sb_gsub D HD Hc (valid_group_sort _ _ Hg) p Hl Hass (decl_typed_order _ _ _ Hdt)
                  (decl_typed_mvc _ _ _ Hdt)) as Hgs.
    destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
    pose proof (Completeness.Inductives.Model.uparams_rel_env D HD ups ups Hgu Lu RU HRU) as HρU.
    assert (Eτ : ⟦ grp_sb p D ⟧s gc_deps ⍮ gc_stack ⍮ env_args nil ups
                   ↘ env_args (env_args nil ups) (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D)))).
    { unfold grp_sb; apply (Completeness.Inductives.Decl.eval_sb_of_list _ Id _ _ _ (eval_sub_id _)).
      apply (eval_self_apps VP p D HVP HPD ups _ Lu); intros j' Hj'; apply List.in_seq in Hj'; lia. }
    assert (HI0v : grp_sctx D ⊨ I0 : T0)
      by (eapply completeness_fundamental_exp; eapply glu_rel_exp_to_wf_exp; exact HgI).
    assert (Heq : sb_eq (grp_sb p D ⨟ sb_of_list Id Us)
                    (sb_of_list (sb_of_list Id Us) (List.map (fun j => apps (a_ind p j) Us) (List.seq 0 (ind_ndecl D))))).
    { unfold grp_sb; rewrite sb_of_list_compose_gen, List.map_map.
      etransitivity; [ apply sb_of_list_cong, sb_compose_id_left |].
      rewrite (List.map_ext _ (fun j => apps (a_ind p j) Us)); [ reflexivity |].
      intros j'; rewrite apps_exp_sub; cbn [exp_sub].
      replace (ind_nu D) with (List.length Us) by (unfold ind_nu; congruence).
      rewrite vars_from_sb_of_list; reflexivity. }
    destruct (glu_with_sub_along _ _ _ _ _ _ _ _ _ _ _ _ (Completeness.LogicalRelation.Instance.gsub_valid Hgs) HRU HρU Eτ
                HI0v Heq Hw) as [i Hi].
    exists i; exact Hi.
  Qed.

  (** The view's instance of the container's uniform parameters, at glued
      uniform parameters of the group. *)
  Lemma view_uparams_glu : forall Δ Us ups cs, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cs ->
      glu_args Δ (ind_uparams Dq) Id nil (List.map (fun I => I[sb_of_list Id Us]) Is) cs.
  Proof.
    intros * HΔ HUs Ecs.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ (decl_closed_ass _ Hc) HUs) as Hgu.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [_ Lups].
    destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
    pose proof (Completeness.Inductives.Model.uparams_rel_env D HD ups ups Hgu ltac:(unfold ind_nu; exact Lups) RU HRU) as HρU.
    eapply params_glu_args_at with (Γ := ind_uparams D) (RΓ := RU) (ρ := env_args nil ups);
      [ exact (decl_closed_ass _ HcQ) | exact (decl_closed_uparams _ HcQ) | exact (valid_ind_decl_uparams _ (valid_group_valid _ _ HgQ)) | exact (valid_ind_decl_uparams _ HD)
      | exact HRU | exact HρU | exact view_is_length | | | exact Ecs ].
    - intros j I T HI HT; exact (vg_view_is p D Hg Hcv _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HI HT).
    - intros j I T HI HT; exact (filed_view_is_glu Δ Us ups HΔ HUs j I T HI HT).
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
    pose proof (valid_group_valid _ _ HgQ) as HDQ.
    set (tc := List.rev (im_nparams Mi')) in *; set (tg := List.rev (im_nparams Mv)) in *.
    assert (Hlr : j <= List.length tc) by (assert (j < List.length tc) by (apply List.nth_error_Some; congruence); lia).
    (** The container's telescope, from no base to the instance's. *)
    pose proof (valid_ind_decl_uparams _ HDQ) as HUQ.
    destruct (rel_ctx_wf_per_ctx_env HUQ) as [RQ HRQ].
    assert (Hlc' : List.length cups = List.length (ind_uparams Dq)) by (rewrite Hlc; reflexivity).
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups)) by exact (gargs_env_rel _ _ _ _ _ _ HRQ HUQ Hlc' Hcr).
    assert (HQ1 : RQ (env_args nil cups) (env_args (env_args nil ups) cups))
      by exact (closed_env_base _ _ _ _ _ _ _ _ (decl_closed_ass _ HcQ) HUQ HRQ Hlc' Hlc' HQ0).
    assert (Hac : tele_ass tc) by exact (List.Forall_rev (member_nparams_ass Dq HcQ _ _ HMi')).
    assert (Hag : tele_ass tg) by exact (List.Forall_rev (member_nparams_ass D Hc _ _ HMv)).
    assert (HWc0 : ⊨ List.rev tc ++ ind_uparams Dq) by (unfold tc; rewrite List.rev_involutive; exact (valid_ind_decl_params _ HDQ _ _ HMi')).
    assert (HTc0 : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                     exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (valid_ind_decl_npar _ HDQ _ _ _ _ HMi' HA))).
    destruct (tele_base_change tc (ind_uparams Dq) RQ (env_args nil cups) (env_args (env_args nil ups) cups)
                Hac HWc0 HTc0 HRQ HQ1 j vs Hlv Hlr Hgc) as [Hg1 _].
    (** The two telescopes, equal under the view's instance. *)
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    assert (HaC0 : tele_ass (List.rev tc ++ ind_uparams Dq)) by (apply List.Forall_app; split; [ apply List.Forall_rev; exact Hac | exact (decl_closed_ass _ HcQ) ]).
    assert (HWc : ⊨ List.rev tc ++ ind_uparams Dq ++ ind_uparams D)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HaC0 HWc0 HUD))).
    assert (HTc : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ++ ind_uparams D ⊨ A : Typeω@i).
    { intros j0 A HA; destruct (HTc0 _ _ HA) as [i HAv].
      assert (Ha0 : tele_ass (List.rev (List.firstn j0 tc) ++ ind_uparams Dq))
        by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (decl_closed_ass _ HcQ) ]).
      exists i; rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ Ha0 (rel_ctx_wf_firstn _ _ j0 HWc0) HUD HAv). }
    assert (HWg : ⊨ List.rev tg ++ ind_uparams D) by (unfold tg; rewrite List.rev_involutive; exact (valid_ind_decl_params _ HD _ _ HMv)).
    assert (HTg : forall j0 A, List.nth_error tg j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tg) ++ ind_uparams D ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (valid_ind_decl_npar _ HD _ _ _ _ HMv HA))).
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
      by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (decl_closed_ass _ HcQ) ]).
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
    pose proof (glu_args_per_gargs _ _ _ _ _ _ (decl_closed_ass _ Hc) HUs) as Hgu.
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
      pose proof (decl_typed_view_nparams _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv) as Hext.
      assert (HσU : Δ ⊢ˢ sb_of_list Id Us : ind_uparams D).
      { apply (wf_uparams_sub _ _ _ _ _ Hdt HΔ HUl).
        intros; eapply glu_args_typed; [ exact (decl_closed_ass _ Hc) | exact HUs | eassumption | eassumption ]. }
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

  (** Conversely, from the container's telescope at the view's instance to
      the group's member's at the view's uniform parameters. *)
  Lemma view_nparams_glu_rev : forall Δ Us Ns ups ns cs i' Mi' v Mv, ⊢ Δ -> List.length ups = ind_nu D ->
      glu_args Δ (ind_uparams D) Id nil Us ups ->
      ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      glu_args Δ (im_nparams Mi') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)) (env_args nil cs) Ns ns ->
      ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cs ->
      glu_args Δ (im_nparams Mv) (sb_of_list Id Us) (env_args nil ups) Ns ns.
  Proof.
    intros * HΔ Hu HUs HMi' Hv HMv HNs Ecs.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ (decl_closed_ass _ Hc) HUs) as Hgu.
    pose proof (view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (decl_closed_nparams_ass D Hc _ _ HMv) as HaV.
    pose proof (decl_closed_nparams_ass Dq HcQ _ _ HMi') as HaC.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HaC HNs) as Hgn.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
    destruct (glu_args_length _ _ _ _ _ _ HNs) as [HNl Hnl].
    apply (glu_args_transfer Δ (im_nparams Mi') (im_nparams Mv) _ (sb_of_list Id Us) (env_args nil cs) (env_args nil ups) Ns ns HaC HaV
             ltac:(rewrite !length_im_nparams; lia) HNs).
    - intros kk A' A a HA' HA Hk Ea Hpg.
      assert (Hpc : per_gargs (List.firstn kk (List.rev (im_nparams Mi'))) (env_args nil cs) (env_args nil cs)
                      (List.firstn kk ns) (List.firstn kk ns)).
      { rewrite <- (List.firstn_skipn kk (List.rev (im_nparams Mi'))), <- (List.firstn_skipn kk ns) in Hgn.
        assert (Hl1 : List.length (List.firstn kk ns) = List.length (List.firstn kk (List.rev (im_nparams Mi'))))
          by (rewrite !List.length_firstn, List.length_rev; lia).
        exact (proj1 (Decl.per_gargs_app _ _ _ _ _ _ _ _ Hl1 Hgn Hl1)). }
      destruct (view_nparam_types ups cs i' Mi' v Mv Hgu Hu Ecs HMi' Hv HMv kk (List.firstn kk ns) A A'
                  ltac:(rewrite List.length_firstn; lia) HA HA' Hpg Hpc) as (b & a0 & i & Eb & Ea0 & Hba).
      assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
      exists b, i; split; [ exact Eb | exact (per_univ_sym' _ _ _ Hba) ].
    - intros kk T' T HT' HT.
      pose proof (decl_typed_view_nparams _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv) as Hext.
      assert (HσU : Δ ⊢ˢ sb_of_list Id Us : ind_uparams D).
      { apply (wf_uparams_sub _ _ _ _ _ Hdt HΔ HUl).
        intros; eapply glu_args_typed; [ exact (decl_closed_ass _ Hc) | exact HUs | eassumption | eassumption ]. }
      pose proof (sub_preserves_ext _ _ _ _ _ _ _ Hext HσU) as He.
      apply Views.ext_eq_sym_ass in He; [| apply tele_ass_sub; exact HaV ].
      assert (EV : forall X, tele_insts (tele_sub X (sb_of_list Id Us)) Id Ns = tele_insts X (sb_of_list Id Us) Ns)
        by (intros; rewrite tele_insts_tele_sub; apply tele_insts_sb_eq, sb_compose_id_right).
      assert (EC : tele_insts (tele_sub (tele_sub (im_nparams Mi') (sb_of_list Id Is)) (sb_of_list Id Us)) Id Ns
                   = tele_insts (im_nparams Mi') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)) Ns).
      { rewrite EV, tele_insts_tele_sub.
        apply (tele_insts_agree _ (ind_nu Dq)); [ exact HaC | exact (decl_closed_nparams_scoped Dq HcQ _ _ HMi') |].
        intros x Hx; rewrite <- view_is_length in Hx.
        exact (sb_of_list_map_nth Is (sb_of_list Id Us) x Hx). }
      rewrite <- EV in HT; rewrite <- EC in HT'.
      eapply (tele_insts_ext_eq Δ _ _ Ns He (tele_ass_sub _ _ (tele_ass_sub _ _ HaC)) (tele_ass_sub _ _ HaV)
                ltac:(rewrite !length_tele_sub, length_im_nparams; rewrite length_im_nparams in HNl; lia)); [| exact HT' | exact HT ].
      intros j N T0 HN HT0; rewrite EC in HT0.
      eapply glu_args_typed; [ exact HaC | exact HNs | eassumption | eassumption ].
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
      pose proof (decl_typed_view_args _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv Hcon' Hcon) as Hext.
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
        apply sb_qn_list_agree; rewrite view_is_length; unfold im_np in Hx; rewrite HlNs; pose proof (view_member_nn_eq := view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv); lia. }
      rewrite <- EV in HT; rewrite <- EC in HT'.
      eapply (tele_insts_ext_eq Δ _ _ As He (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _))
                (tele_ass_sub _ _ (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _)))
                ltac:(rewrite length_tele_sub, length_cargs_ctx; exact LA)); [| exact HT | exact HT' ].
      intros j N T0 HN HT0; rewrite EV in HT0.
      eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ].
  Qed.
End ViewConArgs.

(** ** The Constructor of a Record View is a Tuple *)

(** The fields of a tuple of a record view, as the view's constructor's
    arguments: the second components of the fields, by name. *)
Lemma map_snd_combine_eq : forall {X Y : Type} (xs : list X) (ys : list Y),
    List.length xs = List.length ys -> List.map snd (List.combine xs ys) = ys.
Proof. intros X Y; induction xs as [| x xs IH]; intros [| y ys] Hl; cbn in *; try lia; f_equal; auto. Qed.

(** The tuple of a record view's fields, typed along the view's
    constructor's telescope at [σ0], is of the record type at the view's
    instance at [σ0]: the record view equation ([decl_typed_rview_fields])
    turns that telescope into the record's fields at the instance. *)
Lemma rview_tuple_typed : forall Ψ p D j Mj qr Is fl c gs σ0 As,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil -> ⊢ Ψ ->
    Ψ ⊢ˢ σ0 : im_params D Mj ->
    Ψ ⊢ˢ sb_of_list σ0 As : cargs_ctx p D Mj gs ++ im_params D Mj ->
    List.length As = List.length gs ->
    Ψ ⊢ a_tuple (apps_exp (a_record qr) (List.map (fun I => I[σ0]) Is)) (List.combine fl As)
      : apps_exp (a_record qr) (List.map (fun I => I[σ0]) Is).
Proof.
  intros * Hl Hj Hh Hcs HΨ Hσ0 HA HAl.
  pose proof (ctx_wf_gctx _ _ _ HΨ) as Hg.
  pose proof (decls_of_ctx _ _ _ HΨ) as HDs.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (decl_typed_rstruct _ _ _ HD) as Hrs.
  destruct (rview_struct_record _ _ _ Hrs _ _ _ _ _ Hj Hh) as [R HR].
  pose proof (rview_record_lookup _ _ _ _ _ _ HR) as HlR.
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR) as HRt.
  pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) HlR) as HRc.
  destruct (rview_params _ _ _ _ _ _ _ _ HD Hj Hh) as [HEG _].
  destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ Hj Hh) as (gs0 & Hcs0 & Hlen).
  rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
  pose proof (rview_record_names _ _ _ _ _ _ HR) as Hfl.
  set (Ns := List.map (fun I => I[σ0]) Is) in *.
  assert (HNl : List.length Ns = List.length (record_params R))
    by (unfold Ns; rewrite List.length_map; exact (rview_record_count _ _ _ _ _ _ HR)).
  assert (HNs : forall k N T, nth_error Ns k = Some N -> nth_error (tele_insts (record_params R) Id Ns) k = Some T ->
             Ψ ⊢ N : T).
  { intros k N T HN HT; unfold Ns in HN, HT.
    rewrite <- record_params_insts_sub in HT by exact HRc.
    apply nth_error_map_inv in HN as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    pose proof (decl_typed_rview_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ Hj Hh HlR HI0 HT0) as H.
    rewrite <- HEG in H; exact (sub_preserves_exp _ _ _ _ _ _ _ H Hσ0). }
  pose proof (decl_typed_rview_fields _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ Hj Hh HlR Hcs) as HE.
  rewrite <- HEG in HE.
  assert (HassF : tele_ass (tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id Is))).
  { apply tele_ass_sub; unfold record_fctx, tele_ass; apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; eauto. }
  pose proof (wf_sub_compose _ _ _ _ _ _ _ (ctxsub_ext _ _ _ _ _ HE HassF) HA) as HA'.
  rewrite sb_compose_id_left in HA'.
  assert (HlF : List.length As = List.length (tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id Is)))
    by (rewrite length_tele_sub, length_record_fctx by lia; rewrite HAl, Hlen, Hfl, List.length_map; reflexivity).
  pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ HassF HlF HA') as HAs.
  (** The record type at the instance is a type. *)
  pose proof (record_typed_former _ _ _ _ _ HRt HlR (wf_sub_dom _ _ _ _ _ Hσ0)) as Hrt.
  pose proof (wf_exp_eq_record_apps _ _ _ _ _ Ns Ns Hrt HlR HNl HNl
                ltac:(intros j0 X Y T HX HY HT; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; eapply HNs; eassumption))
    as HTT.
  destruct (wf_record_inversion Hrt) as [R0 Hl0 _ _ _ _ _ HS _ _].
  rewrite HlR in Hl0; injection Hl0 as <-.
  assert (HPw : ⊢ gc_deps ⍮ gc_stack ⍮ record_params R) by (eapply presup_is_univ_ctx; eassumption).
  assert (HSs : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ᵤ (record_sort R)[sb_of_list Id Ns]).
  { eapply (proj1 (proj2 (proj2 (proj2 sub_preserves_wf)))); [ exact HS |].
    rewrite <- (List.app_nil_r (record_params R)).
    eapply wf_sub_of_list; [ exact (typed_params_ass _ _ _ HRt) | rewrite List.app_nil_r; exact HPw
                           | exact (wf_sub_to_nil _ _ _ HΨ) | exact HNl | exact HNs ]. }
  destruct (wf_exp_eq_is_univ_large HSs HTT) as [i HTi].
  assert (HTt : Ψ ⊢ apps_exp (a_record qr) Ns : Typeω@i) by (gen_presups; eassumption).
  assert (HlfA : List.length fl = List.length As) by lia.
  eapply wf_tuple; [ exact HTt | exact HTi | exact Hrt | exact HlR | exact HNl | exact HNs
                   | rewrite map_fst_combine_len by exact HlfA; exact Hfl |].
  intros k f M U HM HU.
  rewrite map_snd_combine_eq by exact HlfA.
  assert (HMk : nth_error As k = Some M).
  { pose proof (f_equal (option_map snd) HM) as HM'; rewrite <- List.nth_error_map, map_snd_combine_eq in HM' by exact HlfA.
    exact HM'. }
  assert (HkA : k < List.length As) by (apply List.nth_error_Some; congruence).
  assert (Hk : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some (tele_insts (tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id Is)) σ0 As) k)
    as [T HT]; [ rewrite length_tele_insts by exact HassF; rewrite <- HlF; lia |].
  pose proof (HAs _ _ _ HMk HT) as HMT.
  rewrite tele_insts_tele_sub in HT.
  destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA0 & ->).
  rewrite Completeness.Records.Model.rev_record_fctx, List.nth_error_firstn in HA0.
  destruct (Nat.ltb_spec k (List.length (record_fields R))); [| lia ].
  unfold Completeness.Records.Model.field_tele in HA0; rewrite List.nth_error_map, HU in HA0; cbn in HA0; injection HA0 as <-.
  enough (EU : U[sb_of_list (sb_of_list Id Is ⨟ σ0) (List.firstn k As)] = U[sb_of_list Id (Ns ++ List.firstn k As)])
    by (rewrite <- EU; exact HMT).
  rewrite (exp_sub_sb_eq _ _ (sb_of_list (sb_of_list σ0 Ns) (List.firstn k As))).
  - rewrite <- sb_of_list_app; eapply exp_scoped_sub_agree; [ exact (closed_fields _ HRc _ _ _ HU) |].
    intros z Hz; apply sb_of_list_lt_base; rewrite List.length_app, HNl, List.length_firstn; lia.
  - apply sb_of_list_cong.
    etransitivity; [ apply sb_of_list_compose_gen |]; apply sb_of_list_cong; intros z; reflexivity.
Qed.

(** The constructor of a record view at the group's uniform parameters
    [Us] and fields [As] typed along its telescope is the tuple of the
    fields at the record type at the view's instance there
    ([wf_exp_eq_con_rview]). *)
Lemma rview_con_tuple : forall Ψ p D j Mj qr Is fl c gs Us As,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil -> ⊢ Ψ -> List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Ψ ⊢ U : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mj gs) (sb_of_list Id Us) As) k = Some T -> Ψ ⊢ N : T) ->
    Ψ ⊢ apps (a_con p j c) (Us ++ As) ≈ a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl As)
      : im_ty_at p j Mj Us nil.
Proof.
  intros * Hl Hj Hh Hcs HΨ HUl HUs HAl HAs.
  pose proof (ctx_wf_gctx _ _ _ HΨ) as Hg.
  pose proof (decls_of_ctx _ _ _ HΨ) as HDs.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (decl_typed_rstruct _ _ _ HD) as Hrs.
  destruct (rview_params _ _ _ _ _ _ _ _ HD Hj Hh) as [HEG Hnn].
  destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ Hj Hh) as (gs0 & Hcs0 & Hlen).
  rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
  pose proof (ind_con_single _ _ _ Hcs) as Hcon.
  assert (HPw : ⊢ gc_deps ⍮ gc_stack ⍮ im_params D Mj ++ nil)
    by (rewrite List.app_nil_r; exact (member_params_wf _ _ _ _ _ HD Hj)).
  assert (HUs' : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (im_params D Mj) Id Us) k = Some T ->
             Ψ ⊢ U : T) by (rewrite HEG; exact HUs).
  assert (Hσ0 : Ψ ⊢ˢ sb_of_list Id Us : im_params D Mj).
  { rewrite <- (List.app_nil_r (im_params D Mj)).
    eapply wf_sub_of_list; [ exact (decl_closed_params_ass D j Mj (proj2 (decl_of_lookup _ _ _ _ _ HΨ Hl)) Hj) | exact HPw
                           | exact (wf_sub_to_nil _ _ _ HΨ) | rewrite length_im_params; unfold im_np; lia | exact HUs' ]. }
  assert (Hin : List.In (c, gs) (im_cons Mj)) by (rewrite Hcs; left; reflexivity).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hj Hin gs nil (eq_sym (List.app_nil_r gs))) as (Hall & _ & _).
  assert (HA : Ψ ⊢ˢ sb_of_list (sb_of_list Id Us) As : cargs_ctx p D Mj gs ++ im_params D Mj)
    by (eapply wf_sub_of_list; [ apply cargs_ctx_aux_ass | exact Hall | exact Hσ0 | rewrite length_cargs_ctx; exact HAl | exact HAs ]).
  pose proof (rview_tuple_typed Ψ p D j Mj qr Is fl c gs (sb_of_list Id Us) As Hl Hj Hh Hcs HΨ Hσ0 HA HAl) as Ht.
  assert (HUPs : forall k P P' T, List.nth_error Us k = Some P -> List.nth_error Us k = Some P' ->
             List.nth_error (tele_insts (im_params D Mj) Id Us) k = Some T -> Ψ ⊢ P ≈ P' : T)
    by (intros k0 P0 P0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HUs'; eassumption).
  pose proof (wf_exp_eq_con_apps_member Ψ p D j Mj c gs Us Us As As Hl Hj Hcon HΨ
                ltac:(unfold im_np; lia) ltac:(unfold im_np; lia) HUPs HAl HAl
                ltac:(intros j0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl;
                      eapply HAs; eassumption)) as HC.
  rewrite List.firstn_all2, List.skipn_all2 in HC by lia.
  unfold ind_mty in HC; rewrite Hj in HC.
  assert (HCt : Ψ ⊢ apps (a_con p j c) (Us ++ As) : im_ty_at p j Mj Us nil) by (gen_presups; eassumption).
  assert (HTy : im_ty_at p j Mj Us nil = apps_exp (a_record qr) (List.map (fun I => I[sb_of_list Id Us]) Is))
    by (unfold im_ty_at, im_pre; rewrite Hh, List.app_nil_r; reflexivity).
  assert (Hpre : im_pre Mj Us = List.map (fun I => I[sb_of_list Id Us]) Is) by (unfold im_pre; rewrite Hh; reflexivity).
  eapply wf_exp_eq_con_rview; [ exact Hl | exact Hj | exact Hh | exact HUl | lia | exact HCt | rewrite Hpre, HTy; exact Ht ].
Qed.

(** A telescope of assumptions holds no module slot. *)
Lemma tele_ass_no_mod : forall C x U, tele_ass C -> C ∋ #x ≔ₘ U -> False.
Proof.
  intros * Hass H; induction H; inversion Hass as [| ? ? [? Heq] ?]; subst; try discriminate; eauto.
Qed.

(** Substitutions into a telescope of assumptions with the same terms at
    its variables are equal. *)
Lemma wf_sub_eq_of_agree : forall Ψ C σ σ', tele_ass C -> Ψ ⊢ˢ σ : C -> Ψ ⊢ˢ σ' : C ->
    (forall x, x < List.length C -> sentry_exp (σ x) = sentry_exp (σ' x)) -> Ψ ⊢ˢ σ ≈ σ' : C.
Proof.
  intros * Hass Hσ Hσ' Hag.
  constructor; [ exact Hσ | exact Hσ' | | intros * Hx; exfalso; exact (tele_ass_no_mod _ _ _ Hass Hx) ].
  intros x A Hx.
  pose proof (wf_sub_apply _ _ _ _ _ Hσ _ _ Hx) as H.
  cbn [exp_sub] in H |- *.
  rewrite <- (Hag x) by (eapply ctx_lookup_length; exact Hx).
  apply wf_exp_eq_refl; exact H.
Qed.

(** Equal substitutions of lists, restricted to a prefix of the lists. *)
Lemma wf_sub_eq_of_list_prefix : forall Ψ σ σ' Ms Ns Ms' Ns' Δ Γ0,
    ⊢ Δ ++ Γ0 -> List.length Ns = List.length Δ -> List.length Ns' = List.length Δ ->
    Ψ ⊢ˢ sb_of_list σ (Ms ++ Ns) ≈ sb_of_list σ' (Ms' ++ Ns') : Δ ++ Γ0 -> Ψ ⊢ˢ sb_of_list σ Ms ≈ sb_of_list σ' Ms' : Γ0.
Proof.
  intros * HΔ Hl Hl' Hσ.
  pose proof (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ (wf_wk_shiftn_app' _ _ _ _ HΔ)) Hσ) as H.
  eapply wf_sub_eq_sb_eq; [| | exact H ]; [ rewrite <- Hl | rewrite <- Hl' ]; apply sb_shift_of_list_app.
Qed.

(** Substitutions of a list over equal bases, the list typed over the
    first, are equal. *)
Lemma sb_of_list_base_eq : forall Ψ Δ Γ0 β β' L, tele_ass Δ -> ⊢ Δ ++ Γ0 -> Ψ ⊢ˢ β ≈ β' : Γ0 ->
    Ψ ⊢ˢ sb_of_list β L : Δ ++ Γ0 -> List.length L = List.length Δ -> Ψ ⊢ˢ sb_of_list β L ≈ sb_of_list β' L : Δ ++ Γ0.
Proof.
  intros * Hass HΔ Hβ HL Hl.
  pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ Hass Hl HL) as HMs.
  apply wf_sub_eq_of_list_left; [ exact Hass | exact HΔ | exact Hβ | exact Hl | exact Hl | exact HMs | exact HMs |].
  intros k N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HMs _ _ _ HN HT).
Qed.

(** Projections of equal elements at equal substitutions are equal
    substitutions: the projections of the generic element, over its
    type [T], typed into [C], instantiated at both. *)
Lemma projs_sub_eq : forall Ψ Γ0 T (i : nat) C τ σ σ' X X' ns,
    Γ0 ⊢ T : Typeω@i -> Ψ ⊢ˢ σ ≈ σ' : Γ0 -> Ψ ⊢ X ≈ X' : T[σ] ->
    Γ0 ▹ T ⊢ˢ sb_of_list (τ ⨟ ι ↑) (projections_of ns #0) : C ->
    Ψ ⊢ˢ sb_of_list (τ ⨟ σ) (projections_of ns X) ≈ sb_of_list (τ ⨟ σ') (projections_of ns X') : C.
Proof.
  intros * HT Hσ HX Hθ.
  assert (Hext : Ψ ⊢ˢ σ,,X ≈ σ',,X' : Γ0 ▹ T).
  { destruct (presup_exp_eq HX) as (_ & HX0 & HX1 & _).
    eapply wf_sub_eq_extend; [ exact Hσ | exact HT | exact HX0 | | exact HX ].
    eapply wf_conv'; [ exact HX1 | exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HT Hσ) ]. }
  pose proof (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ Hθ Hext) as H.
  assert (E : forall s M, sb_eq (sb_of_list (τ ⨟ ι ↑) (projections_of ns #0) ⨟ (s,,M)) (sb_of_list (τ ⨟ s) (projections_of ns M))).
  { intros s M; etransitivity; [ apply sb_of_list_compose_gen |].
    rewrite projections_of_sub; apply sb_of_list_cong.
    intros x; unfold sb_compose; rewrite sentry_sub_sub; reflexivity. }
  exact (wf_sub_eq_sb_eq _ _ _ _ _ _ (E σ X) (E σ' X') H).
Qed.

(** An element [X] of a record view equal to the view's constructor at
    the uniform parameters [Us] and fields [As] typed along its telescope:
    its projections are the fields, as substitutions into the telescope.
    The constructor is the tuple of the fields ([rview_con_tuple]), whose
    projections are its fields ([tuple_pre_eq]) along the record's
    fields, which the record view equation ([decl_typed_rview_fields])
    turns into the constructor's telescope. *)
Lemma rview_con_projs_eq : forall Ψ p D j Mj qr Is fl c gs Us As X,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil -> ⊢ Ψ -> List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Ψ ⊢ U : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mj gs) (sb_of_list Id Us) As) k = Some T -> Ψ ⊢ N : T) ->
    Ψ ⊢ X ≈ apps (a_con p j c) (Us ++ As) : im_ty_at p j Mj Us nil ->
    Ψ ⊢ˢ sb_of_list (sb_of_list Id Us) (projections_of fl X) ≈ sb_of_list (sb_of_list Id Us) As
      : cargs_ctx p D Mj gs ++ im_params D Mj.
Proof.
  intros * Hl Hj Hh Hcs HΨ HUl HUs HAl HAs HX.
  pose proof (rview_con_tuple Ψ p D j Mj qr Is fl c gs Us As Hl Hj Hh Hcs HΨ HUl HUs HAl HAs) as HCt.
  pose proof (ctx_wf_gctx _ _ _ HΨ) as Hg.
  pose proof (decls_of_ctx _ _ _ HΨ) as HDs.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (decl_typed_rstruct _ _ _ HD) as Hrs.
  destruct (rview_struct_record _ _ _ Hrs _ _ _ _ _ Hj Hh) as [R HR].
  pose proof (rview_record_lookup _ _ _ _ _ _ HR) as HlR.
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR) as HRt.
  pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) HlR) as HRc.
  destruct (rview_params _ _ _ _ _ _ _ _ HD Hj Hh) as [HEG Hnn].
  destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ Hj Hh) as (gs0 & Hcs0 & Hlen).
  rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
  pose proof (rview_record_names _ _ _ _ _ _ HR) as Hfl.
  set (σ0 := sb_of_list Id Us).
  assert (HPw : ⊢ gc_deps ⍮ gc_stack ⍮ im_params D Mj ++ nil)
    by (rewrite List.app_nil_r; exact (member_params_wf _ _ _ _ _ HD Hj)).
  assert (HUs' : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (im_params D Mj) Id Us) k = Some T ->
             Ψ ⊢ U : T) by (rewrite HEG; exact HUs).
  assert (Hσ0 : Ψ ⊢ˢ σ0 : im_params D Mj).
  { rewrite <- (List.app_nil_r (im_params D Mj)).
    eapply wf_sub_of_list; [ exact (decl_closed_params_ass D j Mj (proj2 (decl_of_lookup _ _ _ _ _ HΨ Hl)) Hj) | exact HPw
                           | exact (wf_sub_to_nil _ _ _ HΨ) | rewrite length_im_params; unfold im_np; lia | exact HUs' ]. }
  assert (Hin : List.In (c, gs) (im_cons Mj)) by (rewrite Hcs; left; reflexivity).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hj Hin gs nil (eq_sym (List.app_nil_r gs))) as (Hall & _ & _).
  assert (HA : Ψ ⊢ˢ sb_of_list σ0 As : cargs_ctx p D Mj gs ++ im_params D Mj)
    by (eapply wf_sub_of_list; [ apply cargs_ctx_aux_ass | exact Hall | exact Hσ0 | rewrite length_cargs_ctx; exact HAl | exact HAs ]).
  pose proof (rview_tuple_typed Ψ p D j Mj qr Is fl c gs σ0 As Hl Hj Hh Hcs HΨ Hσ0 HA HAl) as Ht.
  set (Ns := List.map (fun I => I[σ0]) Is) in *.
  assert (HNl : List.length Ns = List.length (record_params R))
    by (unfold Ns; rewrite List.length_map; exact (rview_record_count _ _ _ _ _ _ HR)).
  assert (HNs : forall k N T, nth_error Ns k = Some N -> nth_error (tele_insts (record_params R) Id Ns) k = Some T ->
             Ψ ⊢ N : T).
  { intros k N T HN HT; unfold Ns in HN, HT.
    rewrite <- record_params_insts_sub in HT by exact HRc.
    apply nth_error_map_inv in HN as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    pose proof (decl_typed_rview_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ Hj Hh HlR HI0 HT0) as H.
    rewrite <- HEG in H; exact (sub_preserves_exp _ _ _ _ _ _ _ H Hσ0). }
  pose proof (decl_typed_rview_fields _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ Hj Hh HlR Hcs) as HE.
  rewrite <- HEG in HE.
  set (n := List.length (record_fields R)) in *.
  set (RS := tele_sub (record_fctx R n) (sb_of_list Id Is)) in *.
  assert (HassF : tele_ass RS).
  { apply tele_ass_sub; unfold record_fctx, tele_ass; apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; eauto. }
  assert (HlF : List.length As = List.length RS)
    by (unfold RS, n; rewrite length_tele_sub, length_record_fctx by lia; rewrite HAl, Hlen, Hfl, List.length_map; reflexivity).
  (** The entries of the record's fields' telescope at [σ0]: the fields'
      types at the parameters and the entries before. *)
  assert (HRSi : forall L k T, List.length L = n -> List.nth_error (tele_insts RS σ0 L) k = Some T ->
             exists f U, List.nth_error (record_fields R) k = Some (f, U) /\ T = U[sb_of_list Id (Ns ++ List.firstn k L)]).
  { intros L k T HL HT.
    unfold RS in HT; rewrite tele_insts_tele_sub in HT.
    destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA0 & ->).
    rewrite Completeness.Records.Model.rev_record_fctx, List.nth_error_firstn in HA0.
    destruct (Nat.ltb_spec k n); [| discriminate ].
    unfold Completeness.Records.Model.field_tele in HA0; rewrite List.nth_error_map in HA0.
    destruct (List.nth_error (record_fields R) k) as [[f U] |] eqn:HU; cbn in HA0; [| discriminate ]; injection HA0 as <-.
    exists f, U; split; [ reflexivity |].
    rewrite (exp_sub_sb_eq _ _ (sb_of_list (sb_of_list σ0 Ns) (List.firstn k L))).
    - rewrite <- sb_of_list_app; eapply exp_scoped_sub_agree; [ exact (closed_fields _ HRc _ _ _ HU) |].
      intros z Hz; apply sb_of_list_lt_base; rewrite List.length_app, HNl, List.length_firstn; lia.
    - apply sb_of_list_cong.
      etransitivity; [ apply sb_of_list_compose_gen |]; apply sb_of_list_cong; intros z; reflexivity. }
  (** The same, along the record's own telescope at its parameters. *)
  assert (HRPi : forall L k T, List.nth_error (tele_insts (record_fctx R n) (sb_of_list Id Ns) L) k = Some T ->
             exists f U, List.nth_error (record_fields R) k = Some (f, U) /\ T = U[sb_of_list Id (Ns ++ List.firstn k L)]).
  { intros L k T HT.
    destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA0 & ->).
    rewrite Completeness.Records.Model.rev_record_fctx, List.nth_error_firstn in HA0.
    destruct (Nat.ltb_spec k n); [| discriminate ].
    unfold Completeness.Records.Model.field_tele in HA0; rewrite List.nth_error_map in HA0.
    destruct (List.nth_error (record_fields R) k) as [[f U] |] eqn:HU; cbn in HA0; [| discriminate ]; injection HA0 as <-.
    exists f, U; split; [ reflexivity |]; rewrite sb_of_list_app; reflexivity. }
  (** The fields, typed along the record's fields. *)
  pose proof (wf_sub_compose _ _ _ _ _ _ _ (ctxsub_ext _ _ _ _ _ HE HassF) HA) as HA'.
  rewrite sb_compose_id_left in HA'.
  pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ HassF HlF HA') as HAsR.
  assert (HAn : List.length As = n) by (rewrite HlF; unfold RS; rewrite length_tele_sub, length_record_fctx by lia; reflexivity).
  assert (HlfA : List.length fl = List.length As) by lia.
  set (fs := List.combine fl As) in *.
  assert (Hfs : List.map fst fs = List.map fst (record_fields R)) by (unfold fs; rewrite map_fst_combine_len by exact HlfA; exact Hfl).
  assert (Hsfs : List.map snd fs = As) by (unfold fs; apply map_snd_combine_eq; exact HlfA).
  assert (HMs : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
             Ψ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]).
  { intros k f M U HM HU; rewrite Hsfs.
    assert (HMk : nth_error As k = Some M).
    { pose proof (f_equal (option_map snd) HM) as HM'; rewrite <- List.nth_error_map, Hsfs in HM'; exact HM'. }
    assert (Hk : k < n) by (apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts RS σ0 As) k) as [T HT]; [ rewrite length_tele_insts by exact HassF; lia |].
    destruct (HRSi As k T HAn HT) as (f' & U' & HU' & ->).
    rewrite HU in HU'; injection HU' as <- <-.
    exact (HAsR _ _ _ HMk HT). }
  (** The tuple's projections are its fields. *)
  pose proof (record_typed_former _ _ _ _ _ HRt HlR (wf_sub_dom _ _ _ _ _ Hσ0)) as Hrt.
  destruct (presup_exp Ht) as [_ [it Hit]].
  pose proof (tuple_pre_eq _ _ _ _ _ _ _ _ it Ht (wf_exp_eq_refl Hit) Hrt HlR HNl HNs Hfs HMs n (le_n _)) as Hpre.
  set (tup := a_tuple (apps_exp (a_record qr) Ns) fs) in *.
  set (Lt := record_pre R n tup) in *.
  assert (HLt : List.length Lt = n) by (unfold Lt; apply length_record_pre; lia).
  assert (HassP : tele_ass (record_params R)) by exact (typed_params_ass _ _ _ HRt).
  assert (HE1 : forall k N N' T, List.nth_error Lt k = Some N -> List.nth_error As k = Some N' ->
             List.nth_error (tele_insts RS σ0 Lt) k = Some T -> Ψ ⊢ N ≈ N' : T).
  { intros k N N' T HN HN' HT.
    destruct (HRSi Lt k T HLt HT) as (f & U & HU & ->).
    assert (Hk : k < n) by (apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts (record_fctx R n) (sb_of_list Id Ns) Lt) k) as [T' HT'].
    { rewrite length_tele_insts by apply record_fctx_ass; rewrite length_record_fctx by lia; lia. }
    destruct (HRPi Lt k T' HT') as (f' & U' & HU' & ->).
    rewrite HU in HU'; injection HU' as <- <-.
    apply (Hpre (List.length Ns + k)).
    - rewrite List.nth_error_app2, Nat.add_comm, Nat.add_sub by lia; exact HN.
    - rewrite List.nth_error_app2, Nat.add_comm, Nat.add_sub by lia.
      rewrite List.firstn_all2, Hsfs by (rewrite List.length_map, <- Hsfs, List.length_map in *; lia); exact HN'.
    - rewrite tele_insts_app by (first [ exact HassP | lia ]).
      rewrite List.nth_error_app2 by (rewrite length_tele_insts by exact HassP; lia).
      rewrite length_tele_insts by exact HassP.
      replace (List.length Ns + k - Nat.min (List.length (record_params R)) (List.length Ns)) with k by lia; exact HT'. }
  assert (HE1' : forall k N, List.nth_error Lt k = Some N -> exists N' T, List.nth_error As k = Some N' /\
             List.nth_error (tele_insts RS σ0 Lt) k = Some T).
  { intros k N HN.
    assert (Hk : k < n) by (rewrite <- HLt; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some As k ltac:(lia)) as [N' HN'].
    destruct (nth_error_lt_some (tele_insts RS σ0 Lt) k) as [T HT];
      [ rewrite length_tele_insts by exact HassF; unfold RS; rewrite length_tele_sub, length_record_fctx by lia; lia |].
    eauto. }
  assert (ER : Ψ ⊢ˢ sb_of_list σ0 Lt ≈ sb_of_list σ0 As : RS ++ im_params D Mj).
  { apply wf_sub_eq_of_list_left; [ exact HassF | exact (ext_eq_ctx_left _ _ _ _ _ HE) | exact (wf_sub_eq_refl _ _ _ _ _ Hσ0)
                                  | unfold RS; rewrite length_tele_sub, length_record_fctx by lia; exact HLt
                                  | unfold RS; rewrite length_tele_sub, length_record_fctx by lia; exact HAn | | | exact HE1 ].
    - intros k N T HN HT; destruct (HE1' k N HN) as (N' & T' & HN' & HT'); rewrite HT in HT'; injection HT' as <-.
      destruct (presup_exp_eq (HE1 _ _ _ _ HN HN' HT)) as (_ & H0 & _); exact H0.
    - intros k N' T HN' HT.
      destruct (nth_error_lt_some Lt k) as [N HN]; [ rewrite HLt, <- HAn; apply List.nth_error_Some; congruence |].
      destruct (presup_exp_eq (HE1 _ _ _ _ HN HN' HT)) as (_ & _ & H0 & _); exact H0. }
  pose proof (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ (ctxsub_ext_rev _ _ _ _ _ HE HassF) ER) as EC.
  pose proof (wf_sub_eq_sb_eq _ _ _ _ _ _ (sb_compose_id_left _) (sb_compose_id_left _) EC) as EC'.
  assert (ELt : Lt = projections_of fl tup)
    by (unfold Lt, n, record_pre, projections_of; rewrite List.firstn_all, Hfl, List.map_map; reflexivity).
  rewrite ELt in EC'.
  (** [X]'s projections are the tuple's. *)
  assert (HTy : im_ty_at p j Mj Us nil = apps_exp (a_record qr) Ns)
    by (unfold im_ty_at, im_pre; rewrite Hh, List.app_nil_r; reflexivity).
  assert (Hpre0 : im_pre Mj Us = Ns) by (unfold im_pre; rewrite Hh; reflexivity).
  rewrite HTy, Hpre0 in HCt; rewrite HTy in HX; fold tup in HCt.
  pose proof (wf_exp_eq_trans _ _ _ _ _ _ _ HX HCt) as HXt.
  assert (HΨT : ⊢ Ψ ▹ apps_exp (a_record qr) Ns) by mauto 3.
  assert (Hσ1 : Ψ ▹ apps_exp (a_record qr) Ns ⊢ˢ σ0 ⨟ ι ↑ : im_params D Mj)
    by (eapply wf_sub_compose; [ exact Hσ0 | apply wf_sub_of_wk, wf_wk_shift; exact HΨT ]).
  assert (Hx0 : Ψ ▹ apps_exp (a_record qr) Ns ⊢ #0 : apps_exp (a_record qr) (List.map (fun I => I[σ0 ⨟ ι ↑]) Is)).
  { replace (apps_exp (a_record qr) (List.map (fun I => I[σ0 ⨟ ι ↑]) Is)) with (apps_exp (a_record qr) Ns)[ι ↑];
      [ rewrite exp_sub_of_wk; mauto 3
      | unfold Ns; rewrite apps_exp_sub, List.map_map; f_equal; apply List.map_ext; intros; rewrite exp_sub_sub; reflexivity ]. }
  pose proof (rview_fields_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hj Hh Hcs Hσ1 Hx0) as Hθ.
  assert (Hid : Ψ ⊢ˢ Id ≈ Id : Ψ) by (apply wf_sub_eq_refl; mauto 3).
  assert (HXt' : Ψ ⊢ X ≈ tup : (apps_exp (a_record qr) Ns)[Id]) by (rewrite exp_sub_id; exact HXt).
  pose proof (projs_sub_eq _ _ _ _ _ _ _ _ _ _ _ Hit Hid HXt' Hθ) as EX.
  assert (Eb : sb_eq (σ0 ⨟ Id) σ0) by apply sb_compose_id_right.
  pose proof (wf_sub_eq_sb_eq _ _ _ _ _ _ (sb_of_list_cong _ _ _ Eb) (sb_of_list_cong _ _ _ Eb) EX) as EX'.
  eapply wf_sub_eq_trans; [ exact EX' | exact EC' ].
Qed.

(** At a recursive field [f] of shape [tf] of a record view, after the
    fields [fs1], of an element [X] equal to the view's constructor at
    [Us] and [As]: the components of the field's shape at [As] are those
    at [X]'s projections, and the field [Nf] is [X]'s projection. *)
Lemma rview_field_eqs : forall Ψ p D j Mj qr Is fl c gs Us As X fs1 f tf fs2 Nf,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil -> ⊢ Ψ -> List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Ψ ⊢ U : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mj gs) (sb_of_list Id Us) As) k = Some T -> Ψ ⊢ N : T) ->
    Ψ ⊢ X ≈ apps (a_con p j c) (Us ++ As) : im_ty_at p j Mj Us nil ->
    List.combine fl gs = fs1 ++ (f, ca_rec tf) :: fs2 -> List.nth_error As (List.length fs1) = Some Nf ->
    Ψ ⊢ˢ cargs_sub (sb_of_list Id Us) (List.map snd fs1) As ≈ sb_of_list (sb_of_list Id Us) (projections_of (fields_args fs1) X)
      : cargs_strat (List.map snd fs1) ++ im_params D Mj /\
    Ψ ⊢ Nf ≈ a_proj f X : ptyp_ty_at p D Us (cargs_sub (sb_of_list Id Us) (List.map snd fs1) As) tf.
Proof.
  intros * Hl Hj Hh Hcs HΨ HUl HUs HAl HAs HX Ec HNf.
  pose proof (rview_con_projs_eq Ψ p D j Mj qr Is fl c gs Us As X Hl Hj Hh Hcs HΨ HUl HUs HAl HAs HX) as H2.
  pose proof (ctx_wf_gctx _ _ _ HΨ) as Hg.
  pose proof (decls_of_ctx _ _ _ HΨ) as HDs.
  pose proof (HDs _ _ Hl) as HD.
  pose proof (decl_of_lookup _ _ _ _ _ HΨ Hl) as [_ Hc].
  destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ HD) _ _ _ _ _ Hj Hh) as (gs' & Hcs' & Hlen).
  rewrite Hcs in Hcs'; injection Hcs' as _ <-.
  destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
  set (gs1 := List.map snd fs1) in *; set (gs2 := List.map snd fs2) in *.
  assert (Hl1 : List.length gs1 = List.length fs1) by (unfold gs1; apply List.length_map).
  set (σ0 := sb_of_list Id Us) in *.
  pose proof (wf_sub_eq_sym _ _ _ _ _ _ H2) as H2s.
  (** The field: [X]'s projection, at its type at [As]. *)
  assert (Hpf : List.nth_error (projections_of fl X) (List.length fs1) = Some (a_proj f X)).
  { rewrite Efl; unfold projections_of; rewrite List.map_app, List.nth_error_app2 by (rewrite !List.length_map; lia).
    rewrite !List.length_map, Nat.sub_diag; reflexivity. }
  assert (HlP : List.length (projections_of fl X) = List.length gs) by (unfold projections_of; rewrite List.length_map; lia).
  destruct (nth_error_lt_some (tele_insts (cargs_ctx p D Mj gs) σ0 As) (List.length gs1)) as [TA HTA].
  { rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx, HAl, Egs, List.length_app; cbn; lia. }
  assert (Lc : List.length (cargs_ctx p D Mj gs) = List.length gs) by apply length_cargs_ctx.
  pose proof (wf_sub_eq_of_list_inv Ψ (cargs_ctx p D Mj gs) (im_params D Mj) σ0 σ0 As (projections_of fl X)
                (cargs_ctx_aux_ass _ _ _ _ _) ltac:(lia) ltac:(lia) H2s (List.length gs1) Nf (a_proj f X) TA
                ltac:(rewrite Hl1; exact HNf) ltac:(rewrite Hl1; exact Hpf) HTA) as H3.
  destruct (rview_params _ _ _ _ _ _ _ _ HD Hj Hh) as [HEG Hnn].
  assert (HUnp : List.length Us = im_np D Mj) by (unfold im_np; rewrite Hnn; lia).
  pose proof (cargs_rec_type_at p D Mj gs gs1 tf gs2 Us As TA Egs Hc HUnp HTA) as ETA.
  rewrite List.firstn_all2 in ETA by lia.
  assert (Eσ : sb_eq (ι (wk_pat (cargs_pat gs1)) ⨟ sb_of_list Id (Us ++ List.firstn (List.length gs1) As)) (cargs_sub σ0 gs1 As)).
  { rewrite sb_of_list_app; fold σ0; rewrite <- (cargs_sub_firstn gs1 σ0 As).
    apply cargs_sub_pat; rewrite List.length_firstn; rewrite HAl, Egs, List.length_app; cbn; lia. }
  rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ _ Eσ) in ETA.
  subst TA.
  split; [| exact H3 ].
  clear H3 Eσ HTA.
  (** The components: the prefix before the field, past the pattern. *)
  destruct (List.nth_error_split As (List.length fs1) HNf) as (As1 & As2 & EAs & HlA1).
  set (Δ2 := cargs_ctx_aux p D (im_nn Mj) (cargs_pat (gs1 ++ ca_rec tf :: nil)) gs2
             ++ cargs_ctx_aux p D (im_nn Mj) (cargs_pat gs1) (ca_rec tf :: nil)).
  assert (ECtx : cargs_ctx p D Mj gs ++ im_params D Mj = Δ2 ++ (cargs_ctx p D Mj gs1 ++ im_params D Mj)).
  { rewrite Egs.
    replace (gs1 ++ ca_rec tf :: gs2) with ((gs1 ++ ca_rec tf :: nil) ++ gs2) by (rewrite <- List.app_assoc; reflexivity).
    unfold Δ2; rewrite cargs_ctx_app, cargs_ctx_snoc, <- !List.app_assoc; reflexivity. }
  assert (EPj : projections_of fl X = projections_of (List.map fst fs1) X ++ (a_proj f X :: projections_of (List.map fst fs2) X))
    by (rewrite Efl; unfold projections_of; rewrite List.map_app; reflexivity).
  assert (LΔ2 : List.length Δ2 = S (List.length gs2))
    by (unfold Δ2; rewrite List.length_app, !length_cargs_ctx_aux; cbn; lia).
  assert (Hall : ⊢ cargs_ctx p D Mj gs ++ im_params D Mj) by exact (wf_sub_cod _ _ _ _ _ (wf_sub_eq_left _ _ _ _ _ _ H2s)).
  rewrite ECtx in Hall, H2s; rewrite EAs, EPj in H2s.
  assert (LA2 : List.length gs = List.length As1 + S (List.length As2)) by (rewrite <- HAl, EAs, List.length_app; reflexivity).
  assert (LA3 : List.length As2 = List.length gs2) by (rewrite Egs, List.length_app in LA2; cbn [List.length] in LA2; lia).
  assert (LP2 : List.length (projections_of (List.map fst fs2) X) = List.length gs2)
    by (unfold projections_of, gs2; rewrite !List.length_map; reflexivity).
  pose proof (wf_sub_eq_of_list_prefix Ψ σ0 σ0 As1 (Nf :: As2) (projections_of (List.map fst fs1) X)
                (a_proj f X :: projections_of (List.map fst fs2) X) Δ2 (cargs_ctx p D Mj gs1 ++ im_params D Mj) Hall
                ltac:(cbn [List.length]; lia) ltac:(cbn [List.length]; lia) H2s) as Ep.
  assert (Hin : List.In (c, gs) (im_cons Mj)) by (rewrite Hcs; left; reflexivity).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hj Hin gs1 _ Egs) as (_ & _ & Hφ).
  pose proof (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hφ) Ep) as EC.
  refine (wf_sub_eq_sb_eq _ _ _ _ _ _ _ _ EC).
  - rewrite <- (cargs_sub_firstn gs1 σ0 As), EAs.
    replace (List.firstn (List.length gs1) (As1 ++ Nf :: As2)) with As1
      by (rewrite List.firstn_app, List.firstn_all2, (proj2 (Nat.sub_0_le _ _)) by lia; cbn [List.firstn];
          rewrite List.app_nil_r; reflexivity).
    apply cargs_sub_pat; lia.
  - pose proof (wk_pat_projections fs1 nil σ0 X) as E; rewrite List.app_nil_r in E.
    etransitivity; [ exact E |]; apply sb_of_list_cong; intros z; reflexivity.
Qed.

(** ** The Instance of a Record View, Glued

    As a view's instance ([view_uparams_glu]): the record view's instance
    of the record's parameters, at glued uniform parameters of the
    group. *)
Section RviewIs.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (qr : qname) (Is : list exp) (fl : list String.string) (R : record_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_record qr Is fl) (HR : valid_rview_record qr R).
  Let HlR := valid_rview_record_lookup _ _ HR.
  Let HcR := valid_rview_record_closed _ _ HR.

  (** The record view's instance, filed, glued along glued uniform
      parameters of the group, as [filed_view_is_glu]. *)
  Lemma filed_rview_is_glu : forall Δ Us ups, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall j I T, List.nth_error Is j = Some I -> List.nth_error (tele_insts (record_params R) Id Is) j = Some T ->
      exists i : nat, glu_rel_exp_with_sub i Δ I T (sb_of_list Id Us) (env_args nil ups).
  Proof.
    intros * HΔ HUs j I T HI HT.
    pose proof (decl_closed_ass _ Hc) as HassU.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HassU HUs) as Hgu.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LUs Lups].
    assert (Lu : List.length ups = ind_nu D) by (unfold ind_nu; congruence).
    destruct (glu_ind_decl_view_self _ HG) as [IsS HV].
    rewrite (glu_views_self_rlink _ _ HV _ (valid_group_mpath _ _ Hg) _ _ _ _ _ HMk Hh) in HI, HT.
    rewrite <- (record_params_insts_sub R (IsS k) (grp_sb p D) HcR) in HT.
    apply nth_error_map_inv in HI as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    pose proof (glu_views_self_ris _ _ HV _ _ _ _ _ _ _ _ _ HMk Hh HlR HI0 HT0) as HgI.
    pose proof HgI as [SbS HSbS _ _].
    destruct (glu_rel_exp_clean_inversion1 HSbS HgI) as [iS HiS].
    pose proof (grp_sb_glu VP p D HVP HPD HG Δ Us ups SbS HΔ HUs HSbS) as HσS.
    pose proof (HiS _ _ _ HσS) as Hw.
    pose proof (Completeness.Inductives.Model.grp_sb_gsub D HD Hc (valid_group_sort _ _ Hg) p Hl Hass (decl_typed_order _ _ _ Hdt)
                  (decl_typed_mvc _ _ _ Hdt)) as Hgs.
    destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
    pose proof (Completeness.Inductives.Model.uparams_rel_env D HD ups ups Hgu Lu RU HRU) as HρU.
    assert (Eτ : ⟦ grp_sb p D ⟧s gc_deps ⍮ gc_stack ⍮ env_args nil ups
                   ↘ env_args (env_args nil ups) (List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D)))).
    { unfold grp_sb; apply (Completeness.Inductives.Decl.eval_sb_of_list _ Id _ _ _ (eval_sub_id _)).
      apply (eval_self_apps VP p D HVP HPD ups _ Lu); intros j' Hj'; apply List.in_seq in Hj'; lia. }
    assert (HI0v : grp_sctx D ⊨ I0 : T0)
      by (eapply completeness_fundamental_exp; eapply glu_rel_exp_to_wf_exp; exact HgI).
    assert (Heq : sb_eq (grp_sb p D ⨟ sb_of_list Id Us)
                    (sb_of_list (sb_of_list Id Us) (List.map (fun j => apps (a_ind p j) Us) (List.seq 0 (ind_ndecl D))))).
    { unfold grp_sb; rewrite sb_of_list_compose_gen, List.map_map.
      etransitivity; [ apply sb_of_list_cong, sb_compose_id_left |].
      rewrite (List.map_ext _ (fun j => apps (a_ind p j) Us)); [ reflexivity |].
      intros j'; rewrite apps_exp_sub; cbn [exp_sub].
      replace (ind_nu D) with (List.length Us) by (unfold ind_nu; congruence).
      rewrite vars_from_sb_of_list; reflexivity. }
    destruct (glu_with_sub_along _ _ _ _ _ _ _ _ _ _ _ _ (Completeness.LogicalRelation.Instance.gsub_valid Hgs) HRU HρU Eτ
                HI0v Heq Hw) as [i Hi].
    exists i; exact Hi.
  Qed.

  (** The record view's instance of the record's parameters, at glued
      uniform parameters of the group. *)
  Lemma rview_uparams_glu : forall Δ Us ups cs, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cs ->
      glu_args Δ (record_params R) Id nil (List.map (fun I => I[sb_of_list Id Us]) Is) cs.
  Proof.
    intros * HΔ HUs Ecs.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ (decl_closed_ass _ Hc) HUs) as Hgu.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [_ Lups].
    destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
    pose proof (Completeness.Inductives.Model.uparams_rel_env D HD ups ups Hgu ltac:(unfold ind_nu; exact Lups) RU HRU) as HρU.
    pose proof (ctx_wf_gctx _ _ _ HΔ) as Hgc.
    destruct (rview_struct_record _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMk Hh) as [R' HR'].
    pose proof (valid_rview_record_lookup _ _ HR) as HlR0.
    rewrite (rview_record_lookup _ _ _ _ _ _ HR') in HlR0; injection HlR0 as ->.
    eapply params_glu_args_at with (Γ := ind_uparams D) (RΓ := RU) (ρ := env_args nil ups);
      [ exact (typed_params_ass _ _ _ (valid_rview_record_typed _ _ HR)) | exact (closed_params _ HcR)
      | exact (params_valid _ (valid_rview_record_valid _ _ HR)) | exact (valid_ind_decl_uparams _ HD)
      | exact HRU | exact HρU | exact (rview_record_count _ _ _ _ _ _ HR') | | | exact Ecs ].
    - intros j I T HI HT.
      exact (completeness_fundamental_exp _ _ _
               (decl_typed_rview_is _ _ _ _ Hgc Hdt Hl _ _ _ _ _ _ _ _ _ HMk Hh (rview_record_lookup _ _ _ _ _ _ HR') HI HT)).
    - intros j I T HI HT; exact (filed_rview_is_glu Δ Us ups HΔ HUs j I T HI HT).
  Qed.
End RviewIs.

(** ** The Constructor of a View *)

(** A constructor's value does not depend on the environment. *)
Lemma eval_con_env : forall p k c ρ ρ' m, ⟦ a_con p k c ⟧ ρ ↘ m -> ⟦ a_con p k c ⟧ ρ' ↘ m.
Proof.
  intros * H; inversion H; subst;
    [ eapply eval_exp_con | eapply eval_exp_con_view | eapply eval_exp_con_rview | eapply eval_exp_con_rview_empty ]; eassumption.
Qed.

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
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
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
    pose proof (valid_group_closed _ _ HgQ) as HcQ.
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
    apply glu_args_app in HgP' as [HUs HNs]; [| exact (decl_closed_ass _ Hc) | exact HUl | exact Hu ].
    (** The container's value, at the view's instance. *)
    inversion Hw as [pm' xs Hh0 | qc' kc' Is' vm' xs Hh0 Hlt | qc' kc' Is' vm' xs cs Hh0 Hle Ecs | qr' Is' fl' xs Hh0 _
                    | qr' Is' fl' xs Hh0 _]; subst; rewrite Hh in Hh0;
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
        [ exact (decl_closed_ass _ HcQ) | rewrite List.length_map; exact HIl | rewrite (eval_exps_length _ _ _ Ecs); exact HIl |].
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
        apply (eval_apps_indty qc Dq kc Mkc (cs ++ ns) nil (valid_group_lookup _ _ HgQ) HMkc).
        cbn; rewrite List.length_app, (eval_exps_length _ _ _ Ecs); unfold im_np; lia. }
    assert (Hbb : exists R, DF b ≈ b' ∈ per_univ_elem i ↘ R).
    { destruct (eval_mty_inv p D k Mk _ _ _ _ HMk ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Hb)
        as (cs0 & bs0 & Ecs0 & Ebs0 & ->).
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
                  (glu_args_per_gargs _ _ _ _ _ _ (decl_closed_ass _ Hc) HUs) HZ HRZ HlZ ltac:(rewrite List.length_app; lia) HE Ecs0)
        as (cups & Ecups & Hgc).
      pose proof (functional_eval_exps' _ _ _ _ Ecups Ecs) as ->.
      destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
      assert (Hl0 : List.length cs0 = ind_nu Dq)
        by (destruct (Decl.per_gargs_length _ _ _ _ _ Hgc) as [L1 L2]; pose proof (eval_exps_length _ _ _ Ecs);
            rewrite ?List.length_rev in *; unfold ind_nu in *; lia).
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HRb (valid_group_lookup _ _ HgQ) Hl0 Hl0) as [_ _ _ _ _ _ Hns _].
      unfold member_nparams in Hns; rewrite HMkc in Hns.
      pose proof (valid_group_valid _ _ HgQ) as HDQ.
      pose proof (uparams_sym Dq HDQ HcQ _ _ Hgc ltac:(rewrite (eval_exps_length _ _ _ Ecs); exact HIl)) as Hgc'.
      destruct (sort_value Dq HDQ cs0 (uparams_refl_l Dq HDQ HcQ _ _ Hgc') Hl0) as [aq Eaq].
      pose proof (ind_relate Dq HDQ HcQ (valid_group_sort _ _ HgQ) qc (valid_group_lookup _ _ HgQ) (valid_group_ass _ _ HgQ) kc Mkc pmc cs0 cs ns ns aq
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
    { pose proof (glu_args_params_top _ _ _ _ _ HassP (decl_closed_params D k Mk Hc HMk) HgP) as [_ HPty _].
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
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mkc & Hq & HMkc & Hkd & _ & _ & Hvm & _).
    pose proof (valid_groups_containers VP HVP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq) as HPq.
    pose proof (valid_groups_valid VP HVP qc Dq HPq) as HgQ.
    assert (Hhd : exists pmc, im_head Mkc = mh_decl pmc).
    { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMkc) Hkd) as Hd0.
      unfold im_is_decl in Hd0; destruct (im_head Mkc); [ eauto | discriminate | discriminate ]. }
    destruct Hhd as [pmc Hhc].
    destruct (Completeness.Inductives.Con.view_con_container p D Hass Hdt k Mk qc kc Is vm Dq Mkc c gs HMk Hh Hq HMkc Hcon)
      as (gs' & Hcon' & Hcorr).
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (HassC : tele_ass (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk Hin (eq_sym (List.app_nil_r gs))) as HsC.
    destruct (sort_bound_of Dq (valid_group_sort _ _ HgQ)) as [n0 Hn0].
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
      destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
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
