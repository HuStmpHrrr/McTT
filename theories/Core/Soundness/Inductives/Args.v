(** * Glued Arguments along a Telescope

    The machinery the gluing of the inductive types is built from: lists of
    terms glued positionwise to lists of values along a telescope
    ([glu_args]) make glued substitutions ([glu_sub_of_list]); a closed
    constant whose applications to glued arguments are glued, with values
    given by a relation along the arguments, is glued at a [Π] over the
    telescope ([ctx_pi_glu_elem_by]).  The rest are facts about the
    instances of the telescopes of a group's members. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
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
  { (** The universe index *)
    glu_arg_lvl : universe_index
    (** The type's value *)
  ; glu_arg_val : domain
    (** Its type predicate *)
  ; glu_arg_typ : glu_typ_pred
    (** Its element predicate *)
  ; glu_arg_exp : glu_exp_pred
    (** [A] evaluates in [ρ] to it *)
  ; glu_arg_eval : ⟦ A ⟧ ρ ↘ glu_arg_val
    (** It is glued at the universe *)
  ; glu_arg_elem : DG glu_arg_val ∈ glu_univ_elem glu_arg_lvl ↘ glu_arg_typ ↘ glu_arg_exp
    (** [T] is glued to it *)
  ; glu_arg_glu_typ : Δ ⊢ T ® glu_arg_typ
    (** [M] at [T] is glued to [v] *)
  ; glu_arg_glu : Δ ⊢ M : T ® v ∈ glu_arg_exp }.

(** The terms [Ms] glued to the values [vs] along [C], positionwise: each
    type evaluated in [ρ] extended by the values before it, at their
    telescope ([env_tele]). *)
Record glu_args (Δ : ctx) (C : ctx) (τ : sub) (ρ : env) (Ms : list exp) (vs : list domain) : Prop := mk_glu_args
  { (** One term per entry *)
    glu_args_len : List.length Ms = List.length C
    (** One value per entry *)
  ; glu_args_vals_len : List.length vs = List.length C
    (** Each term glued to its value at its type, after those before *)
  ; glu_args_glu : forall k M T v κ A, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C τ Ms) k = Some T ->
      List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass κ A) ->
      glu_arg Δ (env_tele ρ (List.rev C) (List.firstn k vs)) A T M v }.

Lemma glu_args_nil : forall Δ τ ρ, glu_args Δ nil τ ρ nil nil.
Proof. intros; constructor; [ reflexivity | reflexivity |]; intros [] *; discriminate. Qed.

Lemma glu_args_snoc : forall Δ C κ A τ ρ M Ms v vs,
    glu_args Δ (C ++ ⋅ ▹{κ} A) τ ρ (M :: Ms) (v :: vs) <->
    glu_arg Δ ρ A A[τ] M v /\ glu_args Δ C (τ,,M) (ρ ↦ v ⦂ entry_type_closure A ρ) Ms vs.
Proof.
  intros; split.
  - intros [L1 L2 H]; rewrite tele_insts_snoc, List.rev_app_distr, !List.length_app in *;
      cbn [List.rev List.app List.length] in *.
    split; [ exact (H 0 _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl) |].
    constructor; [ lia | lia |].
    intros k M' T v' κ' A' HM HT Hv HA; exact (H (S k) _ _ _ _ _ HM HT Hv HA).
  - intros [H0 [L1 L2 H]]; constructor;
      rewrite ?tele_insts_snoc, ?List.rev_app_distr, ?List.length_app; cbn [List.rev List.app List.length];
      [ lia | lia |].
    intros [| k] M' T v' κ' A' HM HT Hv HA; cbn in HM, HT, Hv, HA.
    + injection HM as <-; injection HT as <-; injection Hv as <-; injection HA as <- <-; exact H0.
    + exact (H k _ _ _ _ _ HM HT Hv HA).
Qed.

(** The entry at a position of a telescope of assumptions. *)
Lemma glu_args_ass_nth : forall C k, all_assumptions C -> k < List.length C ->
    exists κ A, List.nth_error (List.rev C) k = Some (ce_ass κ A).
Proof.
  intros * Hass Hk.
  destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; exact Hk)) as [e He].
  assert (He' := He); apply List.nth_error_In in He'; apply List.in_rev in He'.
  destruct (proj1 (List.Forall_forall _ _) Hass _ He') as (κ & A & ->); eauto.
Qed.

Lemma glu_args_typed : forall Δ C τ ρ Ms vs, all_assumptions C -> glu_args Δ C τ ρ Ms vs ->
    forall k M T, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C τ Ms) k = Some T -> Δ ⊢ M : T.
Proof.
  intros * Hass [L1 L2 H] k M T HM HT.
  assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
  destruct (glu_args_ass_nth _ _ Hass Hk) as (κ & A & HA).
  destruct (H _ _ _ _ _ _ HM HT Hv HA) as [i a P El _ Hglu _ HMg].
  eapply glu_univ_elem_trm_escape; eassumption.
Qed.

Lemma glu_args_sb_eq : forall Δ C τ τ' ρ Ms vs, sb_eq τ τ' -> glu_args Δ C τ ρ Ms vs -> glu_args Δ C τ' ρ Ms vs.
Proof. intros * Hτ [L1 L2 H]; constructor; [ exact L1 | exact L2 |]; rewrite <- (tele_insts_sb_eq _ _ _ _ Hτ); exact H. Qed.

Lemma glu_args_length : forall Δ C τ ρ Ms vs, glu_args Δ C τ ρ Ms vs ->
    List.length Ms = List.length C /\ List.length vs = List.length C.
Proof. intros * [L1 L2 _]; split; assumption. Qed.

(** Each argument's type is a type and the argument an element of it, so
    glued arguments are related to themselves along the telescope. *)
Lemma glu_args_per_tele_args : forall C Δ τ ρ Ms vs, all_assumptions C -> glu_args Δ C τ ρ Ms vs ->
    per_tele_args (List.rev C) ρ ρ vs vs.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass Hg.
  - destruct (glu_args_length _ _ _ _ _ _ Hg) as [_ Hl]; destruct vs; [ constructor | discriminate ].
  - unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He].
    apply List.Forall_cons_iff in He as [(κ & A & ->) _].
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2]; rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M Ms]; [ cbn in L1; lia |]; destruct vs as [| v vs]; [ cbn in L2; lia |].
    apply glu_args_snoc in Hg as [[i a P El Ha Hglu _ HM] Hg].
    rewrite List.rev_app_distr; cbn [List.rev List.app].
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ HM HR) as Hv.
    apply (per_tele_args_cons (i := large_level i) R);
      [ exact (mk_rel_mod_eval a a Ha Ha (per_univ_elem_cumu_universe_index _ _ _ _ HR _ (universe_index_le_large_level i)))
      | exact Hv | exact (IH _ _ _ _ _ Hass Hg) ].
Qed.

(** ** Glued Substitutions from Glued Arguments *)

Lemma glu_ctx_env_suffix : forall C Γ Sb, all_assumptions C -> EG C ++ Γ ∈ glu_ctx_env ↘ Sb ->
    exists Sb', EG Γ ∈ glu_ctx_env ↘ Sb'.
Proof.
  induction C as [| e C IH]; intros * Hass H; [ eauto |].
  apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass].
  cbn [List.app] in H; inversion H; subst; eauto.
Qed.

(** [σ,,M] into an assumption entry, its head stored at the type as a
    closure in the tail's environment, as the arguments of a telescope
    are ([env_tele]). *)
Lemma cons_glu_sub_pred_helper_closure : forall {Γ Sb Δ σ ρ κ A a} {i : nat} {P El M c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M : A[σ] ® c ∈ El ->
    Δ ⊢ˢ σ,,M ® ρ ↦ c ⦂ entry_type_closure A ρ ∈ cons_glu_sub_pred i Γ κ A Sb.
Proof.
  intros * HSb Hσg HA Ha Hglu Hc.
  (** As at the type's value ([cons_glu_sub_pred_helper]): only the head's
      readability reads the stored type. *)
  pose proof (cons_glu_sub_pred_helper HSb Hσg HA Ha Hglu Hc) as Hx.
  inversion Hx as [? ? ? ? P' El' Hσt Ha' Hg' Hh _ _ Htl]; subst.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
  pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ Hc HR) as Hcc.
  econstructor; [ exact Hσt | exact Ha' | exact Hg' | exact Hh | | | exact Htl ].
  - (** The stored type is the type's closure, of the type's value *)
    exists (entry_type_closure A ρ); split; [ reflexivity |].
    refine (mk_glu_stored_type _ _ _ _ (entry_type_closure A ρ) i a P El ltac:(apply eval_entry_type_closure; exact Ha) Hglu _).
    rewrite exp_sub_shift_extend; exact Hc.
  - split; [ exact (proj1 (entry_readable_of_elem_closure Ha Ha HR Hcc)) | cbn; lia ].
Qed.

Lemma glu_sub_of_list : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    all_assumptions C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 -> glu_args Δ C σ0 ρ0 Ms vs ->
    Δ ⊢ˢ sb_of_list σ0 Ms ® env_tele ρ0 (List.rev C) vs ∈ Sb.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass HC H0 Hσ Hg.
  - destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2].
    destruct Ms; [| discriminate ]; destruct vs; [| discriminate ]; cbn.
    apply (functional_glu_ctx_env H0 HC); exact Hσ.
  - unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He];
      apply List.Forall_cons_iff in He as [(κ & A & ->) _].
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2]; rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M0 Ms]; [ cbn in L1; lia |]; destruct vs as [| v0 vs]; [ cbn in L2; lia |].
    apply glu_args_snoc in Hg as [[i a P El Ha Hglu HP HM] Hg].
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (glu_ctx_env_suffix _ _ _ Hass HC) as [Sb1 HC1].
    destruct (glu_ctx_env_cons_clean_inversion H0 HC1) as (i' & HA & HT & HSb1).
    destruct (HT _ _ _ Hσ) as [a' P' El' Ha' Hglu' HP'].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    pose proof (glu_univ_elem_exp_conv_universe_index (ex_intro _ R HR) Hglu Hglu' HM HP') as HM'.
    assert (Hσ1 : Δ ⊢ˢ σ0,,M0 ® ρ0 ↦ v0 ⦂ entry_type_closure A ρ0 ∈ Sb1)
      by (apply HSb1; eapply cons_glu_sub_pred_helper_closure; eassumption).
    rewrite List.rev_app_distr; cbn [sb_of_list List.rev List.app].
    exact (IH _ _ _ _ _ _ _ _ Hass HC HC1 Hσ1 Hg).
Qed.

(** The heads of an environment of a telescope of assumptions [C], glued
    at their stored types against the components of [σ]
    ([glu_stored_type]), each in its tail. *)
Fixpoint glu_tele_stored (Δ : ctx) (C : ctx) (σ : sub) (ρ : env) : Prop :=
  match C with
  | nil => True
  | ce_ass _ A :: C' =>
      (exists t, env_entry ρ 0 = de_term (ρ 0) t /\ glu_stored_type Δ σ A ρ t) /\
      glu_tele_stored Δ C' (Wk ⨟ σ) ρ↯
  | _ :: _ => True
  end.

(** A substitution glued into a telescope of assumptions [C] over [Γ0],
    at [ρ0] extended by typed values [vts], is glued at [ρ0] extended by
    the same values at other types [vts'], when the context's PER relates
    the two environments and the new heads are glued at their stored
    types: the heads' types evaluate to related types in the related
    tails, and the PER says the new heads read back. *)
Lemma glu_sub_retype : forall C Γ0 Sb RC, all_assumptions C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb ->
    EF C ++ Γ0 ≈ C ++ Γ0 ∈ per_ctx_env ↘ RC ->
    forall Δ σ ρ0 vts vts', List.map fst vts = List.map fst vts' -> List.length vts = List.length C ->
    RC (env_extend_typed ρ0 vts) (env_extend_typed ρ0 vts') ->
    glu_tele_stored Δ C σ (env_extend_typed ρ0 vts') ->
    Δ ⊢ˢ σ ® env_extend_typed ρ0 vts ∈ Sb -> Δ ⊢ˢ σ ® env_extend_typed ρ0 vts' ∈ Sb.
Proof.
  induction C as [| e C IH]; intros * Hass HC HRC * Hv Lv HE Hst Hσ.
  - destruct vts; [| discriminate ]; destruct vts'; [| discriminate ]; exact Hσ.
  - apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass].
    assert (Lv' : List.length vts' = S (List.length C))
      by (rewrite <- (List.length_map fst vts'), <- Hv, List.length_map; exact Lv).
    destruct (List.exists_last (l := vts) ltac:(intros ->; discriminate)) as (vts1 & vt & ->).
    destruct (List.exists_last (l := vts') ltac:(intros ->; discriminate)) as (vts1' & vt' & ->).
    rewrite !List.map_app in Hv; cbn [List.map] in Hv.
    apply List.app_inj_tail in Hv as [Hv1 Hv0].
    rewrite List.length_app in Lv; cbn [List.length] in Lv.
    rewrite !env_extend_typed_app in HE, Hσ, Hst |- *; cbn [env_extend_typed List.fold_left] in HE, Hσ, Hst |- *.
    cbn [glu_tele_stored] in Hst; destruct Hst as [Hst0 Hst1].
    rewrite env_extend_typed_app in HE; cbn [env_extend_typed List.fold_left] in HE.
    cbn [List.app] in HC, HRC.
    destruct (glu_ctx_env_suffix (ce_ass κ A :: nil) (C ++ Γ0) _ ltac:(repeat constructor; eauto) HC) as [TSb HTSb].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HC) as (i & HA & HT & HSb).
    destruct (glu_ctx_env_per_ctx_env HTSb) as [RT HRT].
    destruct (per_ctx_env_cons_clean_inversion HRT HRC) as (i' & hr & Hhr & _ & HRCe).
    apply HRCe in HE as [HEt _ _ HEr _ HErr].
    apply HSb in Hσ; inversion Hσ as [? ? ? ? P El Hσt Ha Hg Hh _ _ Htl]; subst.
    cbn [tl extend_env drop_env] in HEt, Htl, Ha.
    pose proof (IH _ _ _ Hass HTSb HRT _ _ _ _ _ Hv1 ltac:(lia) HEt Hst1 Htl) as Htl'.
    destruct (HT _ _ _ Htl') as [a' P' El' Ha' Hg' HP'].
    destruct (Hhr _ _ HEt) as [a1 a1' Ea1 Ea1' HR1].
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a1' = a') as -> by (eapply functional_eval_exp; eassumption).
    apply HSb; econstructor; [ exact Hσt | exact Ha' | exact Hg' | | exact Hst0 | exact HErr | exact Htl' ].
    assert (Haa : Dom a ≈ a' ∈ per_univ i') by (eexists; exact HR1).
    replace ((env_extend_typed ρ0 vts1' ↦ fst vt' ⦂ snd vt') 0) with ((env_extend_typed ρ0 vts1 ↦ fst vt ⦂ snd vt) 0)
      by (cbn; rewrite Hv0; reflexivity).
    refine (glu_univ_elem_exp_conv Haa Hg Hg' Hh _).
    rewrite <- exp_sub_of_wk, exp_sub_sub; exact HP'.
Qed.

(** ** Constants of [Π]-Types over Telescopes *)

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

(** A constant [X] of a [Π] over the telescope [Δt], whose values along its
    arguments are given by the relation [Fr], is glued at the [Π] when its
    applications to glued arguments are glued at the codomain.  The
    arguments so far are the values [xs] of the context [Γb] already
    consumed, a suffix of the full telescope [T]; [Fr] extends along an
    argument whose values so far are those of a glued substitution of a
    suffix of [T] ([Happ]): the value of a view's constructor at its last
    uniform parameter needs the uniform parameters related. *)
Lemma exp_wk_q_sub_extend : forall C σ φ N, C[q σ][wk_q φ]ʷ[Id,,N] = C[(sb_wk σ φ),,N].
Proof.
  intros; rewrite exp_wk_sub, exp_sub_sub; apply exp_sub_sb_eq.
  intros [| x]; cbn; [ reflexivity |].
  change ((q σ) (S x)) with (sentry_wk (σ x) wk_shift).
  rewrite sentry_wk_wk, sentry_sub_wk, <- sentry_sub_of_wk; apply sentry_sub_sb_eq; intros y; reflexivity.
Qed.

(** An application of a term of a [Π] into a universe, over a substitution,
    after a Kripke weakening. *)
Lemma wf_app_wk_q : forall Δ Δ' σ φ κ A C M N (i : nat),
    Δ ⊢ A[σ] : abs_kind_sort κ Typeω@i ->
    Δ ▹{κ} A[σ] ⊢ C[q σ] : Typeω@i ->
    Δ ⊢ M : a_pi κ ak_relevant A[σ] C[q σ] -> Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ N : A[σ][φ]ʷ ->
    Δ' ⊢ M[φ]ʷ $ N : C[(sb_wk σ φ),,N].
Proof.
  intros * HA HC HM Hφ HN.
  pose proof (kripke_preserves_exp _ _ _ _ _ HM Hφ) as Hw; cbn [exp_wk] in Hw.
  pose proof (kripke_preserves_exp _ _ _ _ _ HA Hφ) as HAφ; rewrite abs_kind_sort_wk in HAφ; cbn [exp_wk] in HAφ.
  pose proof (kripke_preserves_kind_sort_q _ _ _ ak_relevant _ _ _ _ _ HC HA Hφ) as HCφ.
  assert (H : Δ' ⊢ M[φ]ʷ $ N : C[q σ][wk_q φ]ʷ[Id,,N])
    by (eapply wf_app; [ exact HAφ | apply sort_kind_abs_kind_sort | exact HCφ | apply pi_kinds_relevant | exact Hw | exact HN ]).
  rewrite exp_wk_q_sub_extend in H.
  exact H.
Qed.

(** An element of a type's relation is one of a type related to it. *)
Lemma per_elem_transfer : forall {i j k R1 R2 R3 a b x y},
    DF a ≈ a ∈ per_univ_elem i ↘ R1 -> DF a ≈ b ∈ per_univ_elem j ↘ R2 -> DF b ≈ b ∈ per_univ_elem k ↘ R3 ->
    Dom x ≈ y ∈ R1 -> Dom x ≈ y ∈ R3.
Proof.
  intros * H1 H2 H3 Hxy.
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ H1 H2) in Hxy.
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ H2)) H3); exact Hxy.
Qed.

(** An entry of a telescope, valid at an index: a type of the sort of its
    kind next to the large universe there, glued as a type at every
    glued substitution. *)
Definition glu_entry_valid_at (i : nat) (Γ : ctx) (κ : abs_kind) (A : typ) : Prop :=
  Γ ⊢ A : abs_kind_sort κ Typeω@i /\
    forall Sb, EG Γ ∈ glu_ctx_env ↘ Sb -> forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_typ_with_sub i Δ A σ ρ.

(** A type glued as a term of a large universe is a valid entry at the
    universe's index. *)
Lemma glu_entry_valid_of_rel : forall {Γ A} {i : nat}, Γ ⊩ A : Typeω@i -> glu_entry_valid_at i Γ ak_relevant A.
Proof.
  intros * HA.
  split; [ exact (glu_rel_exp_to_wf_exp HA) |].
  intros Sb HSb Δ σ ρ Hσ.
  destruct HA as [Sb' HSb' L HAg].
  assert (E : Sb <∙> Sb') by (eapply functional_glu_ctx_env; eassumption).
  destruct (HAg _ _ _ (proj1 (E _ _ _) Hσ)) as [s m Ps Els Es Hm Hgs HAs].
  simplify_evals; cbn [domain_kind glu_term_value] in Hm.
  basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
  destruct HAs as [_ _ [Pm Elm Hgm Hpm]].
  econstructor; [ exact Hm | exact Hgm | exact Hpm ].
Qed.

(** The values of a type of a sort at two environments a context PER
    relates are related ([completeness_fundamental_exp]). *)
Lemma typ_values_rel : forall {Γ T κ R} {i : nat},
    Γ ⊢ T : abs_kind_sort κ Typeω@i -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R ->
      exists t t', ⟦ T ⟧ ρ ↘ t /\ ⟦ T ⟧ ρ' ↘ t' /\ Dom t ≈ t' ∈ per_univ i.
Proof.
  intros * HT HR.
  exact (rel_type_inversion_simple_at HR (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HT))).
Qed.

(** Arguments of a glued telescope, each glued at its type's own value,
    where its type is glued by the telescope at the arguments before
    (the hypothesis is given the type's gluing at the value). *)
Lemma glu_args_of_typed : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    all_assumptions C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 ->
    List.length Ms = List.length C -> List.length vs = List.length C ->
    (forall k M T v κ A b (j : nat) P El, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C σ0 Ms) k = Some T ->
       List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass κ A) ->
       ⟦ A ⟧ env_tele ρ0 (List.rev C) (List.firstn k vs) ↘ b -> DG b ∈ glu_univ_elem j ↘ P ↘ El -> Δ ⊢ T ® P ->
       Δ ⊢ M : T ® v ∈ El) ->
    glu_args Δ C σ0 ρ0 Ms vs.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass HC H0 Hσ L1 L2 Hrel.
  - destruct Ms; [| discriminate ]; destruct vs; [| discriminate ]; apply glu_args_nil.
  - unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He];
      apply List.Forall_cons_iff in He as [(κ & A & ->) _].
    rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M Ms]; [ cbn in L1; lia |]; destruct vs as [| v vs]; [ cbn in L2; lia |].
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (glu_ctx_env_suffix _ _ _ Hass HC) as [Sb1 HC1].
    destruct (glu_ctx_env_cons_clean_inversion H0 HC1) as (i' & HAi' & HT & HSb1).
    (** The head, glued at its type's value at [ρ0], where its type is glued *)
    destruct (HT _ _ _ Hσ) as [b Pb Elb Eb Hgb HPb].
    pose proof (Hrel 0 M A[σ0] v κ A b i' Pb Elb eq_refl ltac:(rewrite tele_insts_snoc; reflexivity) eq_refl
                  ltac:(rewrite List.rev_app_distr; reflexivity) Eb Hgb HPb) as HMb.
    apply glu_args_snoc; split; [ exact (mk_glu_arg _ _ _ _ _ _ i' b Pb Elb Eb Hgb HPb HMb) |].
    (** The rest, after the head *)
    assert (Hσ1 : Δ ⊢ˢ σ0,,M ® ρ0 ↦ v ⦂ entry_type_closure A ρ0 ∈ Sb1)
      by (apply HSb1; eapply cons_glu_sub_pred_helper_closure; eassumption).
    eapply IH; [ exact Hass | exact HC | exact HC1 | exact Hσ1 | cbn in L1; lia | cbn in L2; lia |].
    intros k M' T v' κ' A' b0 j P El HM0 HT0 Hv0 HA0 Hb0 Hg HTP.
    apply (Hrel (S k) M' T v' κ' A' b0 j P El); [ exact HM0 | rewrite tele_insts_snoc; exact HT0 | exact Hv0
                                         | rewrite List.rev_app_distr; exact HA0 | rewrite List.rev_app_distr; exact Hb0
                                         | exact Hg | exact HTP ].
Qed.

(** Terms glued to their values, each at some type value related to the
    value of its type at the telescope's own environment, are glued
    arguments: each type is glued at its own value at the substitution the
    arguments before it make ([glu_args_of_typed]), which is the witness
    the element moves to ([glu_univ_elem_exp_conv]). *)
Lemma glu_args_of_related : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    all_assumptions C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 ->
    List.length Ms = List.length C -> List.length vs = List.length C ->
    (forall k M T v κ A b, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C σ0 Ms) k = Some T ->
       List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass κ A) ->
       ⟦ A ⟧ env_tele ρ0 (List.rev C) (List.firstn k vs) ↘ b ->
       exists (j j' : nat) a P El, DG a ∈ glu_univ_elem j ↘ P ↘ El /\ Dom a ≈ b ∈ per_univ j' /\ Δ ⊢ M : T ® v ∈ El) ->
    glu_args Δ C σ0 ρ0 Ms vs.
Proof.
  intros * Hass HC H0 Hσ L1 L2 Hrel.
  eapply glu_args_of_typed; [ exact Hass | exact HC | exact H0 | exact Hσ | exact L1 | exact L2 |].
  intros k M T v κ A b j P El HM HT Hv HA Eb Hgb HPb.
  destruct (Hrel k M T v κ A b HM HT Hv HA Eb) as (j0 & j' & a & Pa & Ela & Hga & Hab & HMa).
  exact (glu_univ_elem_exp_conv Hab Hga Hgb HMa HPb).
Qed.

(** The main induction of [ctx_pi_glu_elem_by], at an environment [ρa]
    related to the canonical one of the arguments consumed so far,
    [env_tele nil (List.rev Γb) xs]: a [Π] stores its codomain's arguments
    at their types' values ([eval_app_fn]), the telescope at their types
    as closures; the two are related in [Γb]'s context PER and glued by
    the same substitution.  The domains are glued at [ρa] itself, and the
    codomain [B], a type glued at every glued substitution, is the witness
    the constant moves to from the canonical environment
    ([glu_univ_elem_exp_conv]). *)
Lemma ctx_pi_glu_elem_by_at : forall (Fr : list domain -> domain -> Prop) X T,
    (forall φ, X[φ]ʷ = X) ->
    (forall Δ1 Γ' Sb' Δ' σ' xs x w, T = Δ1 ++ Γ' -> EG Γ' ∈ glu_ctx_env ↘ Sb' ->
       Δ' ⊢ˢ σ' ® env_tele nil (List.rev Γ') (xs ++ x :: nil) ∈ Sb' -> List.length Γ' = S (List.length xs) -> Fr xs w ->
       exists u, $| w & x | gc_deps ⍮ gc_stack ↘ u /\ Fr (xs ++ x :: nil) u) ->
    forall Δt Γb Sb_b Sb B (i : nat), all_assumptions Δt -> EG Γb ∈ glu_ctx_env ↘ Sb_b -> EG Δt ++ Γb ∈ glu_ctx_env ↘ Sb ->
    (exists Δ0, T = Δ0 ++ Δt ++ Γb) ->
    (forall Δ1 κ A Δ2, Δt = Δ1 ++ ce_ass κ A :: Δ2 -> glu_entry_valid_at i (Δ2 ++ Γb) κ A) ->
    (forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ Γb ⊢ ctx_pi Δ1 B : Typeω@i) ->
    glu_entry_valid_at i (Δt ++ Γb) ak_relevant B ->
    forall Δ σ xs Xs w RΓ ρa, EF Γb ≈ Γb ∈ per_ctx_env ↘ RΓ -> Dom ρa ≈ env_tele nil (List.rev Γb) xs ∈ RΓ ->
      Δ ⊢ˢ σ ® ρa ∈ Sb_b ->
      Δ ⊢ˢ σ ® env_tele nil (List.rev Γb) xs ∈ Sb_b -> List.length Γb = List.length xs -> Fr xs w ->
      Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ->
      (forall R a, ⟦ ctx_pi Δt B ⟧ env_tele nil (List.rev Γb) xs ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> R w w) ->
      (forall Δ' φ Ms vs w', Δ' ⊢ᵏ φ : Δ -> glu_args Δ' Δt (sb_wk σ φ) (env_tele nil (List.rev Γb) xs) Ms vs -> Fr (xs ++ vs) w' ->
         forall b P El, ⟦ B ⟧ env_tele nil (List.rev (Δt ++ Γb)) (xs ++ vs) ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
           (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w' w') ->
           Δ' ⊢ apps X (List.map (fun N => N[φ]ʷ) Xs ++ Ms) : B[sb_of_list (sb_wk σ φ) Ms] ® w' ∈ El) ->
      forall a P El, ⟦ ctx_pi Δt B ⟧ ρa ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ® w ∈ El.
Proof.
  intros Fr X T HXw Happ Δt.
  induction Δt as [| e Δt IH] using List.rev_ind;
    intros * Hass HCb HC [Δ0 HT] HA HCs HBg * HRΓ Hρa Hσa Hσ Hlen Hw HXt HPER Hbase * Ha Hglu.
  - cbn [ctx_pi_at List.app] in *.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HCb _ _ _ Hσ)).
    (** The codomain at the canonical environment, then moved to its value
        at [ρa], where it is glued as a type, the witness *)
    pose proof (HCs nil nil eq_refl) as HBt; cbn [ctx_pi_at List.app] in HBt.
    destruct (typ_values_rel (κ := ak_relevant) HBt HRΓ _ _ Hρa) as (b1 & b & Eb1 & Eb & Hbb).
    assert (b1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hb0 : Dom b ≈ b ∈ per_univ i) by (etransitivity; [ symmetry; exact Hbb | exact Hbb ]).
    destruct (per_univ_glu_univ_elem _ _ Hb0) as (Pb & Elb & Hglub).
    pose proof (Hbase Δ wk_id nil nil w (kripke_id _ HΔ) (glu_args_nil _ _ _) ltac:(rewrite List.app_nil_r; exact Hw)
                  _ _ _ ltac:(rewrite !List.app_nil_r; exact Eb) Hglub) as H.
    cbn [sb_of_list] in H; rewrite <- exp_wk_sub, exp_wk_id, map_wk_id, !List.app_nil_r in H.
    pose proof (H ltac:(intros R HR; exact (HPER _ _ Eb HR))) as HXb.
    destruct HBg as [_ HBg].
    destruct (HBg _ HCb _ _ _ Hσa) as [a' Pa Ela Ea' Hga HPa].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga Hglu) as [EP _].
    assert (Hba : Dom b ≈ a ∈ per_univ i) by (symmetry; exact Hbb).
    exact (glu_univ_elem_exp_conv Hba Hglub Hglu HXb (proj1 (EP _ _) HPa)).
  - assert (Hass' := Hass); unfold all_assumptions in Hass'; apply List.Forall_app in Hass' as [HassΔ He].
    apply List.Forall_cons_iff in He as [(κ & A & ->) _].
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HCb _ _ _ Hσ)).
    assert (Hσt : Δ ⊢ˢ σ : Γb) by exact (glu_ctx_env_sub_escape HCb _ _ _ Hσ).
    pose proof (HCs (Δt ++ ⋅ ▹{κ} A) nil (eq_sym (List.app_nil_r _))) as HCp; cbn [List.app] in HCp.
    destruct (HA Δt κ A nil eq_refl) as [HAw HAg]; cbn [List.app] in HAw, HAg.
    pose proof (HCs Δt (⋅ ▹{κ} A) eq_refl) as HCqw; cbn [List.app] in HCqw.
    (** The canonical environment and its values *)
    set (ρc := env_tele nil (List.rev Γb) xs) in *.
    destruct (typ_values_rel (κ := ak_relevant) HCp HRΓ _ _ Hρa) as (a1 & ac & Ea1 & Eac & Haac).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (typ_values_rel HAw HRΓ _ _ Hρa) as (d & dc & Ed & Edc & Hddc).
    rewrite ctx_pi_snoc in Ha, Eac, HXt, HPER, HCp.
    inversion Ha; subst.
    functional_eval_rewrite_clear.
    inversion Eac; subst; functional_eval_rewrite_clear.
    destruct Haac as [RΠ HRΠ].
    assert (HRcc : DF Πᵈ{κ} dc ρc (ctx_pi Δt B) ≈ Πᵈ{κ} dc ρc (ctx_pi Δt B) ∈ per_univ_elem i ↘ RΠ)
      by (etransitivity; [ symmetry; exact HRΠ | exact HRΠ ]).
    pose proof (HPER _ _ Eac HRcc) as Hwc.
    pose proof Hddc as [Rd HRd].
    invert_glu_univ_elem Hglu.
    match goal with Hg : glu_univ_elem _ ?IP ?IEl d |- _ => rename Hg into Hgd end.
    match goal with Hp : per_univ_elem _ ?ir d d |- _ => rename Hp into Hin end.
    match goal with Hp : per_univ_elem _ ?er (d_pi _ _ d _ _) (d_pi _ _ d _ _) |- _ => rename Hp into Hel end.
    match goal with H1 : forall c (equiv_c : _ c c) b, _ -> glu_univ_elem _ _ _ b |- _ => rename H1 into HOd end.
    pose proof (per_elem_transfer HRcc (proj1 (per_univ_elem_sym _ _ _ _ HRΠ)) Hel Hwc) as Hfx.
    (** Typing at [σ] *)
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCp Hσt) as HPit; cbn [exp_sub] in HPit.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HAw Hσt) as HAt; rewrite abs_kind_sort_sub in HAt; cbn [exp_sub] in HAt.
    pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hσt HAw (sort_kind_abs_kind_sort _ _) HAt) as Hq.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCqw Hq) as HCqt; cbn [exp_sub] in HCqt.
    (** The domain, glued at the canonical environment and at [ρa] *)
    destruct (HAg _ HCb _ _ _ Hσ) as [dc' Px Elx Edc' Hgx HPx].
    assert (dc' = dc) as -> by (eapply functional_eval_exp; eassumption).
    destruct (HAg _ HCb _ _ _ Hσa) as [d' Pd Eld Ed' Hgd' HPd].
    assert (d' = d) as -> by (eapply functional_eval_exp; eassumption).
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hgd' Hgd) as [EP _].
    pose proof (proj1 (EP _ _) HPd) as HAσP.
    rewrite ctx_pi_snoc.
    match goal with HE : ?el <∙> pi_glu_exp_pred _ _ _ _ _ _ _ _ |- ?el _ _ _ _ => apply HE end.
    cbn [exp_sub] in HXt |- *.
    eapply mk_pi_glu_exp_pred with (IT := A[σ]) (OT := (ctx_pi Δt B)[q σ]);
      [ exact HXt | exact Hfx | apply wf_exp_eq_refl; exact HPit | exact HAt | exact HCqt | |].
    + intros Δ' φ Hφ; exact (glu_univ_elem_typ_monotone _ _ _ _ Hgd _ _ _ _ HAσP Hφ).
    + intros Δ' φ N n Hφ HN equiv_n.
      (** The function applied, at the actual [Π] *)
      pose proof Hel as Hel'.
      invert_per_univ_elem Hel'.
      match goal with HE : elem_rel <~> pi_elements _ _ _ ?xr, HC0 : forall c c' (e : _ c c'), rel_mod_eval _ _ _ _ _ (?xr c c' e) |- _ =>
        rename HE into H0; rename HC0 into HCod end.
      destruct (pi_elements_app _ _ _ _ _ _ (proj1 (H0 _ _) Hfx) _ _ equiv_n) as [r r' Er Er' Hrr].
      destruct (HCod _ _ equiv_n) as [ba ba' Eba Eba' Hbb].
      functional_eval_rewrite_clear.
      rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
      destruct (glu_ctx_env_suffix _ _ _ HassΔ HC) as [Sb1 HC1].
      destruct (glu_ctx_env_cons_clean_inversion HCb HC1) as (i' & HAi' & HTi' & HSb1).
      pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (HTi' _ _ _ Hσφ) as [a1 P1 El1 Ha1 Hg1 HP1].
      assert (a1 = dc) as -> by (eapply functional_eval_exp; eassumption).
      assert (HN1 : Δ' ⊢ N : A[sb_wk σ φ] ® n ∈ El1).
      { rewrite <- exp_wk_sub.
        refine (glu_univ_elem_exp_conv Hddc Hgd Hg1 HN _); rewrite exp_wk_sub; exact HP1. }
      assert (Hσ1 : Δ' ⊢ˢ (sb_wk σ φ),,N ® ρc ↦ n ⦂ entry_type_closure A ρc ∈ Sb1)
        by (apply HSb1; eapply cons_glu_sub_pred_helper_closure; eassumption).
      (** The same at [ρa] extended by the argument at its type's value *)
      pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσa Hφ) as Hσaφ.
      destruct (HTi' _ _ _ Hσaφ) as [a2 P2 El2 Ha2 Hg2 HP2].
      assert (a2 = d) as -> by (eapply functional_eval_exp; eassumption).
      assert (HN2 : Δ' ⊢ N : A[sb_wk σ φ] ® n ∈ El2).
      { rewrite <- exp_wk_sub.
        assert (Hdd : Dom d ≈ d ∈ per_univ i) by (eexists; exact Hin).
        refine (glu_univ_elem_exp_conv Hdd Hgd Hg2 HN _); rewrite exp_wk_sub; exact HP2. }
      assert (Hσa1 : Δ' ⊢ˢ (sb_wk σ φ),,N ® ρa ↦ n ⦂ entry_type_value d ∈ Sb1)
        by (apply HSb1; eapply cons_glu_sub_pred_helper; [ exact HCb | exact Hσaφ | exact HAi' | exact Ed | exact Hg2 | exact HN2 ]).
      assert (Hρc' : env_tele nil (List.rev (Γb ▹{κ} A)) (xs ++ n :: nil) = ρc ↦ n ⦂ entry_type_closure A ρc)
        by (cbn [List.rev]; apply env_tele_snoc; rewrite List.length_rev; lia).
      rewrite <- Hρc' in Hσ1.
      destruct (Happ (Δ0 ++ Δt) (Γb ▹{κ} A) Sb1 Δ' _ xs n w ltac:(rewrite <- !List.app_assoc; reflexivity) HC1 Hσ1
                  ltac:(cbn; lia) Hw) as (u & Eu & Hu).
      assert (r = u) as -> by (eapply functional_eval_app; eassumption).
      exists u; split; [ exact Eu |].
      rewrite exp_sub_q_extend_wk.
      pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgd _ _ _ _ HN) as HNt.
      pose proof (wf_app_wk_q _ _ _ _ _ _ _ _ _ _ HAt HCqt HXt Hφ HNt) as HXt'.
      replace ((apps X Xs)[φ]ʷ $ N) with (apps X (List.map (fun M => M[φ]ʷ) Xs ++ N :: nil)) in HXt' |- *
        by (rewrite apps_exp_snoc, apps_wk, HXw; reflexivity).
      assert (HA' : forall Δ1 κ0 A0 Δ2, Δt = Δ1 ++ ce_ass κ0 A0 :: Δ2 -> glu_entry_valid_at i (Δ2 ++ Γb ▹{κ} A) κ0 A0).
      { intros Δ1 κ0 A0 Δ2 Heq.
        pose proof (HA Δ1 κ0 A0 (Δ2 ++ ⋅ ▹{κ} A) ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as H'.
        rewrite <- List.app_assoc in H'; exact H'. }
      assert (HCs' : forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ Γb ▹{κ} A ⊢ ctx_pi Δ1 B : Typeω@i).
      { intros Δ1 Δ2 Heq.
        pose proof (HCs Δ1 (Δ2 ++ ⋅ ▹{κ} A) ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as H'.
        rewrite <- List.app_assoc in H'; exact H'. }
      (** The extended environments, actual and canonical, are related *)
      pose proof (per_ctx_env_of_typ (κ := κ) HRΓ (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HAw))) as HRΓA.
      pose proof (proj1 (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hin HRd n n) equiv_n) as Hnd.
      assert (HRdc : DF dc ≈ dc ∈ per_univ_elem i ↘ Rd) by (etransitivity; [ symmetry; exact HRd | exact HRd ]).
      assert (Hρa' : per_env_extend A A RΓ (ρa ↦ n ⦂ entry_type_value d) (env_tele nil (List.rev (Γb ▹{κ} A)) (xs ++ n :: nil))).
      { rewrite Hρc'.
        apply per_env_extend_intro'; [ exact Hρa | exact (per_head_of Ed Edc HRd Hnd) | exact (proj1 (entry_readable_of_elem Hin equiv_n)) |].
        exact (proj1 (entry_readable_of_elem_closure Edc Edc HRdc Hnd)). }
      destruct (typ_values_rel (κ := ak_relevant) HCqw HRΓA _ _ Hρa') as (ba1 & bc & Eba1 & Ebc & [Rx HRx]).
      assert (ba1 = ba) as -> by (eapply functional_eval_exp; eassumption).
      assert (HPER' : forall R a', ⟦ ctx_pi Δt B ⟧ env_tele nil (List.rev (Γb ▹{κ} A)) (xs ++ n :: nil) ↘ a' ->
                        DF a' ≈ a' ∈ per_univ_elem i ↘ R -> R u u).
      { intros R a' Ea' HR.
        assert (a' = bc) as -> by (eapply functional_eval_exp; eassumption).
        exact (per_elem_transfer Hbb HRx HR Hrr). }
      assert (HBv' : glu_entry_valid_at i (Δt ++ Γb ▹{κ} A) ak_relevant B)
        by (rewrite <- List.app_assoc in HBg; exact HBg).
      refine (IH (Γb ▹{κ} A) Sb1 Sb B i HassΔ HC1 HC ltac:(exists Δ0; rewrite <- !List.app_assoc; reflexivity) HA' HCs' HBv'
                Δ' _ (xs ++ n :: nil) _ u _ (ρa ↦ n ⦂ entry_type_value d) HRΓA Hρa' Hσa1 Hσ1
                ltac:(cbn; rewrite List.length_app; cbn; lia) Hu HXt' HPER' _ ba _ _ Eba (HOd _ equiv_n _ Eba)).
      intros Δ'' φ' Ms vs w' Hφ' Hg Hw' b0 P0 El0 Hb0 Hg0 HPb0.
      pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hφφ.
      assert (Hsb : sb_eq (sb_wk ((sb_wk σ φ),,N) φ') ((sb_wk σ (φ ⊙ φ')),,N[φ']ʷ))
        by (intros [| y]; cbn; [ reflexivity | apply sentry_wk_wk ]).
      assert (Hg' : glu_args Δ'' (Δt ++ ⋅ ▹{κ} A) (sb_wk σ (φ ⊙ φ')) ρc (N[φ']ʷ :: Ms) (n :: vs)).
      { apply glu_args_snoc; split; [| rewrite <- Hρc'; eapply glu_args_sb_eq; [ exact Hsb | exact Hg ] ].
        apply (mk_glu_arg _ _ _ _ _ _ i dc Px Elx Edc Hgx).
        - rewrite <- exp_wk_sub; exact (glu_univ_elem_typ_monotone _ _ _ _ Hgx _ _ _ _ HPx Hφφ).
        - rewrite <- exp_wk_sub, <- exp_wk_wk.
          assert (HNφ : Δ'' ⊢ N[φ']ʷ : A[σ][φ]ʷ[φ']ʷ ® n ∈ IEl) by (eapply glu_univ_elem_exp_monotone; eassumption).
          refine (glu_univ_elem_exp_conv Hddc Hgd Hgx HNφ _).
          rewrite exp_wk_wk; exact (glu_univ_elem_typ_monotone _ _ _ _ Hgx _ _ _ _ HPx Hφφ). }
      assert (Hb0' : ⟦ B ⟧ env_tele nil (List.rev ((Δt ++ ⋅ ▹{κ} A) ++ Γb)) (xs ++ n :: vs) ↘ b0)
        by (rewrite <- !List.app_assoc in *; exact Hb0).
      rewrite <- List.app_assoc in Hw'; cbn [List.app] in Hw'.
      pose proof (Hbase Δ'' (φ ⊙ φ') (N[φ']ʷ :: Ms) (n :: vs) w' Hφφ Hg' Hw' b0 P0 El0 Hb0' Hg0 HPb0) as Hr.
      cbn [sb_of_list] in Hr.
      rewrite <- (exp_sub_sb_eq _ _ _ (sb_of_list_cong Ms _ _ Hsb)) in Hr.
      rewrite List.map_app, map_wk_wk, <- List.app_assoc; cbn [List.map List.app].
      exact Hr.
Qed.

(** A constant [X] of a [Π] over the telescope [Δt], whose values along its
    arguments are given by the relation [Fr], is glued at the [Π] when its
    applications to glued arguments are glued at the codomain, all at the
    canonical environment of the arguments consumed so far. *)
Lemma ctx_pi_glu_elem_by : forall (Fr : list domain -> domain -> Prop) X T,
    (forall φ, X[φ]ʷ = X) ->
    (forall Δ1 Γ' Sb' Δ' σ' xs x w, T = Δ1 ++ Γ' -> EG Γ' ∈ glu_ctx_env ↘ Sb' ->
       Δ' ⊢ˢ σ' ® env_tele nil (List.rev Γ') (xs ++ x :: nil) ∈ Sb' -> List.length Γ' = S (List.length xs) -> Fr xs w ->
       exists u, $| w & x | gc_deps ⍮ gc_stack ↘ u /\ Fr (xs ++ x :: nil) u) ->
    forall Δt Γb Sb_b Sb B (i : nat), all_assumptions Δt -> EG Γb ∈ glu_ctx_env ↘ Sb_b -> EG Δt ++ Γb ∈ glu_ctx_env ↘ Sb ->
    (exists Δ0, T = Δ0 ++ Δt ++ Γb) ->
    (forall Δ1 κ A Δ2, Δt = Δ1 ++ ce_ass κ A :: Δ2 -> glu_entry_valid_at i (Δ2 ++ Γb) κ A) ->
    (forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ Γb ⊢ ctx_pi Δ1 B : Typeω@i) ->
    glu_entry_valid_at i (Δt ++ Γb) ak_relevant B ->
    forall Δ σ xs Xs w, Δ ⊢ˢ σ ® env_tele nil (List.rev Γb) xs ∈ Sb_b -> List.length Γb = List.length xs -> Fr xs w ->
      Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ->
      (forall R a, ⟦ ctx_pi Δt B ⟧ env_tele nil (List.rev Γb) xs ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> R w w) ->
      (forall Δ' φ Ms vs w', Δ' ⊢ᵏ φ : Δ -> glu_args Δ' Δt (sb_wk σ φ) (env_tele nil (List.rev Γb) xs) Ms vs -> Fr (xs ++ vs) w' ->
         forall b P El, ⟦ B ⟧ env_tele nil (List.rev (Δt ++ Γb)) (xs ++ vs) ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
           (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w' w') ->
           Δ' ⊢ apps X (List.map (fun N => N[φ]ʷ) Xs ++ Ms) : B[sb_of_list (sb_wk σ φ) Ms] ® w' ∈ El) ->
      forall a P El, ⟦ ctx_pi Δt B ⟧ env_tele nil (List.rev Γb) xs ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ® w ∈ El.
Proof.
  intros * HXw Happ * Hass HCb HC HT HA HCs HBv * Hσ Hlen Hw HXt HPER Hbase * Ha Hglu.
  destruct (glu_ctx_env_per_ctx_env HCb) as [RΓ HRΓ].
  pose proof (glu_ctx_env_per_env HCb HRΓ Hσ) as Hρ.
  exact (ctx_pi_glu_elem_by_at Fr X T HXw Happ Δt Γb Sb_b Sb B i Hass HCb HC HT HA HCs HBv Δ σ xs Xs w RΓ _ HRΓ Hρ
           Hσ Hσ Hlen Hw HXt HPER Hbase a P El Ha Hglu).
Qed.

(** The same over a closed telescope, at the value of the [Π] at any
    environment: the empty context relates every two environments. *)
Lemma ctx_pi_glu_elem_by_closed : forall (Fr : list domain -> domain -> Prop) X T,
    (forall φ, X[φ]ʷ = X) ->
    (forall Δ1 Γ' Sb' Δ' σ' xs x w, T = Δ1 ++ Γ' -> EG Γ' ∈ glu_ctx_env ↘ Sb' ->
       Δ' ⊢ˢ σ' ® env_tele nil (List.rev Γ') (xs ++ x :: nil) ∈ Sb' -> List.length Γ' = S (List.length xs) -> Fr xs w ->
       exists u, $| w & x | gc_deps ⍮ gc_stack ↘ u /\ Fr (xs ++ x :: nil) u) ->
    forall Δt Sb B (i : nat), all_assumptions Δt -> ⊢ᵍ gc_deps ⍮ gc_stack -> EG Δt ++ ⋅ ∈ glu_ctx_env ↘ Sb ->
    (exists Δ0, T = Δ0 ++ Δt ++ ⋅) ->
    (forall Δ1 κ A Δ2, Δt = Δ1 ++ ce_ass κ A :: Δ2 -> glu_entry_valid_at i (Δ2 ++ ⋅) κ A) ->
    (forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ ⋅ ⊢ ctx_pi Δ1 B : Typeω@i) ->
    glu_entry_valid_at i (Δt ++ ⋅) ak_relevant B ->
    forall Δ σ Xs w, Δ ⊢ˢ σ : ⋅ -> Fr nil w ->
      Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ->
      (forall R a, ⟦ ctx_pi Δt B ⟧ env_tele nil (List.rev ⋅) nil ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> R w w) ->
      (forall Δ' φ Ms vs w', Δ' ⊢ᵏ φ : Δ -> glu_args Δ' Δt (sb_wk σ φ) (env_tele nil (List.rev ⋅) nil) Ms vs -> Fr (nil ++ vs) w' ->
         forall b P El, ⟦ B ⟧ env_tele nil (List.rev (Δt ++ ⋅)) (nil ++ vs) ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
           (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w' w') ->
           Δ' ⊢ apps X (List.map (fun N => N[φ]ʷ) Xs ++ Ms) : B[sb_of_list (sb_wk σ φ) Ms] ® w' ∈ El) ->
      forall ρ a P El, ⟦ ctx_pi Δt B ⟧ ρ ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ® w ∈ El.
Proof.
  intros * HXw Happ * Hass Hg HC HT HA HCs HBv * Hσ Hw HXt HPER Hbase * Ha Hglu.
  assert (HCb : EG ⋅ ∈ glu_ctx_env ↘ nil_glu_sub_pred) by (eapply glu_ctx_env_nil; [ reflexivity | exact Hg ]).
  destruct (glu_ctx_env_per_ctx_env HCb) as [RΓ HRΓ].
  assert (Hρ : Dom ρ ≈ env_tele nil (List.rev ⋅) nil ∈ RΓ)
    by (inversion HRΓ; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
  exact (ctx_pi_glu_elem_by_at Fr X T HXw Happ Δt ⋅ nil_glu_sub_pred Sb B i Hass HCb HC HT HA HCs HBv Δ σ nil Xs w RΓ ρ HRΓ Hρ
           Hσ Hσ eq_refl Hw HXt HPER Hbase a P El Ha Hglu).
Qed.

(** ** Closed Constants *)

Lemma typ_nil_rel' : forall T (i : nat) ρ ρ',
    ⋅ ⊢ T : Typeω@i ->
    exists a a', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HT%completeness_fundamental_exp.
  destruct (rel_exp_of_typ_inversion_simple HT) as [env_rel [Hnil H]].
  apply H.
  inversion Hnil as [? Heq | | | |]; subst.
  apply Heq; exact I.
Qed.

(** A closed constant glued at the value of its closed type at every
    environment is glued at the empty context.  The value of a closed type
    may depend on the environment, through the environments its kept
    proofs capture. *)
Lemma glu_closed_const : forall X T (i : nat) m0,
    (forall σ, X[σ] = X) -> (forall σ, T[σ] = T) -> ⋅ ⊢ T : Typeω@i ->
    (forall ρ, ⟦ X ⟧ ρ ↘ m0) ->
    (forall Δ σ, Δ ⊢ˢ σ : ⋅ -> forall ρ a P El, ⟦ T ⟧ ρ ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
       Δ ⊢ X : T ® m0 ∈ El) ->
    ⋅ ⊩ X : T.
Proof.
  intros * HXs HTs HT HXe H.
  assert (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; eapply presup_exp_ctx; exact HT).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ econstructor; [ reflexivity | exact Hg ] |].
  intros Δ σ ρ Hσ; cbn in Hσ.
  destruct (typ_nil_rel' _ _ ρ ρ HT) as (a & a0 & Ha & Ha0 & Haa).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_glu_univ_elem _ _ Haa) as (P & El & Hglu').
  pose proof (H _ _ Hσ _ _ _ _ Ha Hglu') as HXg.
  assert (HTt : Δ ⊢ T : abs_kind_sort ak_relevant Typeω@i)
    by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ HT Hσ) as HTσ; rewrite HTs in HTσ; exact HTσ).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu' (glu_univ_elem_trm_typ _ _ _ _ Hglu' _ _ _ _ HXg) HTt) as [Hk _].
  econstructor; [ exact Ha | rewrite Hk; apply HXe | exact Hglu' |].
  rewrite HXs, HTs; exact HXg.
Qed.

(** A closed constant whose value depends on the environment only through
    a relation: glued at the empty context when every value it takes is
    glued at the value of its type at every environment. *)
Lemma glu_closed_const_by : forall X T (i : nat) (V : domain -> Prop),
    (forall σ, X[σ] = X) -> (forall σ, T[σ] = T) -> ⋅ ⊢ T : Typeω@i ->
    (forall ρ, exists m0, ⟦ X ⟧ ρ ↘ m0 /\ V m0) ->
    (forall Δ σ m0, Δ ⊢ˢ σ : ⋅ -> V m0 -> forall ρ a P El, ⟦ T ⟧ ρ ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
       Δ ⊢ X : T ® m0 ∈ El) ->
    ⋅ ⊩ X : T.
Proof.
  intros * HXs HTs HT HXe H.
  assert (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; eapply presup_exp_ctx; exact HT).
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ econstructor; [ reflexivity | exact Hg ] |].
  intros Δ σ ρ Hσ; cbn in Hσ.
  destruct (typ_nil_rel' _ _ ρ ρ HT) as (a & a0 & Ha & Ha0 & Haa).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_glu_univ_elem _ _ Haa) as (P & El & Hglu').
  destruct (HXe ρ) as (m0 & Hm0 & HV).
  pose proof (H _ _ _ Hσ HV _ _ _ _ Ha Hglu') as HXg.
  assert (HTt : Δ ⊢ T : abs_kind_sort ak_relevant Typeω@i)
    by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ HT Hσ) as HTσ; rewrite HTs in HTσ; exact HTσ).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hglu' (glu_univ_elem_trm_typ _ _ _ _ Hglu' _ _ _ _ HXg) HTt) as [Hk _].
  econstructor; [ exact Ha | rewrite Hk; exact Hm0 | exact Hglu' |].
  rewrite HXs, HTs; exact HXg.
Qed.

(** ** The Entries of a Glued Telescope *)

(** A type glued at an index is glued at every larger one. *)
Lemma glu_rel_typ_with_sub_cumu : forall {i j : nat} {Δ A σ ρ}, i <= j ->
    glu_rel_typ_with_sub i Δ A σ ρ -> glu_rel_typ_with_sub j Δ A σ ρ.
Proof.
  intros * Hle [a P El Ha Hg HP].
  destruct (glu_univ_elem_cumu_ge Hle Hg) as (P' & El' & Hg').
  econstructor; [ exact Ha | exact Hg' | eapply glu_univ_elem_typ_cumu_ge; [ exact Hle | exact Hg | exact Hg' | exact HP ] ].
Qed.

Lemma lift_kind_sort_ge : forall {Γ A κ} {i j : nat}, i <= j ->
    Γ ⊢ A : abs_kind_sort κ Typeω@i -> Γ ⊢ A : abs_kind_sort κ Typeω@j.
Proof. intros * Hle HA; destruct κ; cbn in *; [ eapply lift_exp_ge; eassumption | exact HA | exact HA ]. Qed.

Lemma glu_entry_valid_at_cumu : forall {i j : nat} {Γ κ A}, i <= j -> glu_entry_valid_at i Γ κ A -> glu_entry_valid_at j Γ κ A.
Proof.
  intros * Hle [HA HAg]; split; [ exact (lift_kind_sort_ge Hle HA) |].
  intros Sb HSb Δ σ ρ Hσ; exact (glu_rel_typ_with_sub_cumu Hle (HAg _ HSb _ _ _ Hσ)).
Qed.

(** The head of a glued context of an assumption is valid. *)
Lemma glu_ctx_env_head_valid : forall Γ κ A Sb, EG Γ ▹{κ} A ∈ glu_ctx_env ↘ Sb -> exists i, glu_entry_valid_at i Γ κ A.
Proof.
  intros * H; inversion H as [| ? ? ? i TSb ? HΓ HA HT HSb | | |]; subst.
  exists i; split; [ exact HA |].
  intros Sb' HSb' Δ σ ρ Hσ.
  apply HT; apply (functional_glu_ctx_env HSb' HΓ); exact Hσ.
Qed.

Lemma glu_ctx_env_entries_valid : forall C Γb Sb, all_assumptions C -> EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall (i0 : nat), exists (i : nat), i0 <= i /\
      forall Δ1 κ A Δ2, C = Δ1 ++ ce_ass κ A :: Δ2 -> glu_entry_valid_at i (Δ2 ++ Γb) κ A.
Proof.
  induction C as [| e C IH]; intros * Hass H i0.
  - exists i0; split; [ lia |]; intros [] *; discriminate.
  - apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass].
    cbn [List.app] in H.
    assert (HCx : exists SbC, EG C ++ Γb ∈ glu_ctx_env ↘ SbC) by (inversion H; subst; eexists; eassumption).
    destruct HCx as [SbC HC].
    destruct (glu_ctx_env_head_valid _ _ _ _ H) as [k Hk].
    destruct (IH _ _ Hass HC (Nat.max i0 k)) as (i1 & Hle & Hi).
    exists i1; split; [ lia |].
    intros [| e' Δ1] κ' A' Δ2 Heq; cbn [List.app] in Heq; injection Heq; intros; subst;
      [ eapply glu_entry_valid_at_cumu; [| exact Hk ]; lia | eauto ].
Qed.

(** ** Glued Arguments of Closed Telescopes *)

Lemma universe_index_le_max : forall u j, universe_index_le u (ul (Nat.max (large_level u) j)).
Proof. intros [] j; cbn; [ exact I | lia ]. Qed.

Lemma wf_sub_nil' : forall Δ σ, ⊢ Δ -> Δ ⊢ˢ σ : ⋅.
Proof.
  intros * HΔ; constructor; [ exact HΔ | apply wf_ctx_empty; eapply ctx_wf_gctx; exact HΔ | | |];
    intros * Hx; inversion Hx.
Qed.

Lemma tele_insts_closed_base : forall C σ σ' Ms, all_assumptions C -> ctx_scoped 0 C ->
    tele_insts C σ Ms = tele_insts C σ' Ms.
Proof.
  intros * Hass Hs.
  pose proof (tele_insts_sub C 0 σ σ' Id Ms Hass Hs ltac:(intros; lia)) as H.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in H.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in H.
  exact H.
Qed.

Lemma glu_args_closed_base : forall Δ C τ τ' ρ Ms vs, all_assumptions C -> ctx_scoped 0 C ->
    glu_args Δ C τ ρ Ms vs -> glu_args Δ C τ' ρ Ms vs.
Proof.
  intros * Hass Hs [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
  rewrite <- (tele_insts_closed_base _ τ τ'); assumption.
Qed.

Lemma glu_args_wk : forall Δ Δ' φ C ρ Ms vs, all_assumptions C -> ctx_scoped 0 C -> Δ' ⊢ᵏ φ : Δ ->
    glu_args Δ C Id ρ Ms vs -> glu_args Δ' C Id ρ (List.map (fun M => M[φ]ʷ) Ms) vs.
Proof.
  intros * Hass Hs Hφ [L1 L2 H]; constructor; [ rewrite List.length_map; exact L1 | exact L2 |].
  intros k M T v κ A HM HT Hv HA.
  rewrite List.nth_error_map in HM.
  destruct (List.nth_error Ms k) as [M0 |] eqn:HM0; [| discriminate ]; injection HM as <-.
  rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
  destruct (List.nth_error (tele_insts C Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
  destruct (H _ _ _ _ _ _ HM0 HT0 Hv HA) as [i a P El Ha Hglu HP HMg].
  apply (mk_glu_arg _ _ _ _ _ _ i a P El Ha Hglu).
  - eapply glu_univ_elem_typ_monotone; eassumption.
  - eapply glu_univ_elem_exp_monotone; eassumption.
Qed.

(** An equation of a glued type at a sort is one at its value's kind. *)
Lemma glu_typ_exp_eq_kind : forall {i a P El Γ T T' S},
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> Γ ⊢ T ® P -> Γ ⊢ T ≈ T' : S -> type_sort S ->
    exists j : nat, Γ ⊢ T ≈ T' : abs_kind_sort (domain_kind a) Typeω@j.
Proof.
  intros * Hg HP HTT HS.
  destruct (type_sort_abs_kind_sort_inv _ HS) as (κ & j & ->).
  destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ κ j Hg HP (presup_exp_eq_left HTT)) as [Hk _].
  exists j; rewrite Hk; exact HTT.
Qed.

Lemma lift_kind_sort_eq_ge : forall {Γ A A' κ} {i j : nat}, i <= j ->
    Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i -> Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@j.
Proof. intros * Hle HA; destruct κ; cbn in *; [ eapply lift_exp_eq_ge; eassumption | exact HA | exact HA ]. Qed.

Lemma glu_args_resp_eq : forall Δ C ρ Ms Ms' vs, all_assumptions C -> ⊢ C -> ⊢ Δ ->
    exps_eq_at Δ C Ms Ms' -> glu_args Δ C Id ρ Ms vs -> glu_args Δ C Id ρ Ms' vs.
Proof.
  intros * Hass HC HΔ [Hl HMM] [L1 L2 H].
  constructor; [ congruence | exact L2 |].
  intros k M' T' v κ A HM' HT' Hv HA.
  assert (Hk : k < List.length C) by (rewrite <- L1, Hl; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some Ms k ltac:(lia)) as [M HM].
  destruct (nth_error_lt_some (tele_insts C Id Ms) k) as [T HT]; [ rewrite length_tele_insts by exact Hass; lia |].
  destruct (H _ _ _ _ _ _ HM HT Hv HA) as [i a P El Ha Hglu HP HMg].
  assert (HCe : ⊢ C ++ ⋅) by (rewrite List.app_nil_r; exact HC).
  assert (HId : Δ ⊢ˢ Id ≈ Id : ⋅) by (apply wf_sub_eq_refl, wf_sub_nil'; exact HΔ).
  destruct (tele_insts_cong C Δ ⋅ Id Id Ms Ms' Hass HCe HId L1 ltac:(lia) HMM k T T' HT HT') as (S & HS & HTS).
  destruct (glu_typ_exp_eq_kind Hglu HP HTS HS) as [j HTT].
  pose proof (universe_index_le_max i j) as Hij.
  destruct (glu_univ_elem_cumu_ge_universe_index (i := i) (j := ul (Nat.max (large_level i) j)) Hij Hglu) as (P' & El' & Hglu').
  assert (HP' : Δ ⊢ T ® P') by (eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hij | exact Hglu | exact Hglu' | exact HP ]).
  assert (HTT' : Δ ⊢ T ≈ T' : abs_kind_sort (domain_kind a) Typeω@(Nat.max (large_level i) j))
    by (eapply lift_kind_sort_eq_ge; [| exact HTT ]; lia).
  apply (mk_glu_arg _ _ _ _ _ _ (ul (Nat.max (large_level i) j)) a P' El' Ha Hglu');
    [ eapply glu_univ_elem_typ_resp_exp_eq; eassumption |].
  eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hglu' | | exact HTT' ].
  eapply glu_univ_elem_trm_resp_exp_eq;
    [ exact Hglu' | eapply glu_univ_elem_exp_cumu_ge_universe_index; [ exact Hij | exact Hglu | exact Hglu' | exact HMg ] | exact (HMM _ _ _ _ HM HM' HT) ].
Qed.

Lemma firstn_app_ge : forall {X} (l1 l2 : list X) k, List.length l1 <= k ->
    List.firstn k (l1 ++ l2) = l1 ++ List.firstn (k - List.length l1) l2.
Proof. intros; rewrite List.firstn_app, List.firstn_all2 by lia; reflexivity. Qed.

Lemma firstn_app_le : forall {X} (l1 l2 : list X) k, k <= List.length l1 ->
    List.firstn k (l1 ++ l2) = List.firstn k l1.
Proof. intros; rewrite List.firstn_app; replace (k - List.length l1) with 0 by lia; cbn; apply List.app_nil_r. Qed.

(** A telescope's environment reads only as many of its types as there
    are values ([tele_entries_firstn]). *)
Lemma env_tele_prefix : forall ρ T1 T2 pre, List.length pre <= List.length T1 ->
    env_tele ρ (T1 ++ T2) pre = env_tele ρ T1 pre.
Proof.
  intros * Hl; unfold env_tele; rewrite (tele_entries_firstn pre (T1 ++ T2)), (tele_entries_firstn pre T1).
  rewrite List.firstn_app; replace (List.length pre - List.length T1) with 0 by lia; cbn; rewrite List.app_nil_r; reflexivity.
Qed.

Lemma glu_args_app : forall Δ C1 C2 τ ρ Ms1 Ms2 vs1 vs2, all_assumptions C1 ->
    List.length Ms1 = List.length C1 -> List.length vs1 = List.length C1 ->
    glu_args Δ (C2 ++ C1) τ ρ (Ms1 ++ Ms2) (vs1 ++ vs2) <->
    glu_args Δ C1 τ ρ Ms1 vs1 /\ glu_args Δ C2 (sb_of_list τ Ms1) (env_tele ρ (List.rev C1) vs1) Ms2 vs2.
Proof.
  intros * Hass HM1 Hv1.
  assert (Ht1 : List.length (tele_insts C1 τ Ms1) = List.length C1) by (rewrite length_tele_insts by exact Hass; lia).
  assert (Hr1 : List.length (List.rev C1) = List.length C1) by apply List.length_rev.
  split.
  - intros [L1 L2 H]; rewrite !List.length_app in L1, L2.
    rewrite tele_insts_app, List.rev_app_distr in H by assumption.
    split; constructor; [ lia | lia | | lia | lia |].
    + intros k M T v κ A HM HT Hv HA.
      assert (Hk : k < List.length C1) by (rewrite <- HM1; apply List.nth_error_Some; congruence).
      pose proof (H k M T v κ A) as H'.
      rewrite (firstn_app_le vs1), env_tele_prefix in H' by (rewrite ?List.length_firstn; lia).
      apply H'; rewrite List.nth_error_app1 by lia; assumption.
    + intros k M T v κ A HM HT Hv HA.
      pose proof (H (List.length C1 + k) M T v κ A) as H'.
      rewrite firstn_app_ge, env_tele_app in H' by lia.
      replace (List.length C1 + k - List.length vs1) with k in H' by lia.
      apply H'; rewrite List.nth_error_app2 by lia.
      * replace (List.length C1 + k - List.length Ms1) with k by lia; exact HM.
      * replace (List.length C1 + k - List.length (tele_insts C1 τ Ms1)) with k by lia; exact HT.
      * replace (List.length C1 + k - List.length vs1) with k by lia; exact Hv.
      * replace (List.length C1 + k - List.length (List.rev C1)) with k by lia; exact HA.
  - intros [[L1 L2 H1] [L3 L4 H2]]; constructor; [ rewrite !List.length_app; lia | rewrite !List.length_app; lia |].
    rewrite tele_insts_app, List.rev_app_distr by assumption.
    intros k M T v κ A HM HT Hv HA.
    destruct (Nat.lt_ge_cases k (List.length C1)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HM, HT, Hv, HA by lia.
      rewrite (firstn_app_le vs1), env_tele_prefix by (rewrite ?List.length_firstn; lia).
      exact (H1 _ _ _ _ _ _ HM HT Hv HA).
    + rewrite List.nth_error_app2 in HM, HT, Hv, HA by lia.
      rewrite firstn_app_ge, env_tele_app by lia.
      rewrite HM1, Ht1, Hv1, Hr1 in *.
      exact (H2 _ _ _ _ _ _ HM HT Hv HA).
Qed.

Lemma read_ps_nth : forall s ρ T vs Rs, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Rs ->
    List.length Rs = List.length vs /\
    forall k v κ A, List.nth_error vs k = Some v -> List.nth_error T k = Some (ce_ass κ A) ->
      exists a (V : nf), ⟦ A ⟧ env_tele ρ T (List.firstn k vs) ↘ a /\ Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ V /\
        List.nth_error Rs k = Some V.
Proof.
  induction 1; [ split; [ reflexivity | intros [] *; discriminate ] |].
  match goal with H : _ /\ _ |- _ => destruct H as [IHl IHn] end.
  split; [ cbn; congruence |].
  intros [| k] v0 κ0 A0 Hv HA; cbn in Hv, HA.
  - injection Hv as <-; injection HA as <- <-; do 2 eexists; split; [ eassumption | split; [ eassumption | reflexivity ] ].
  - destruct (IHn _ _ _ _ Hv HA) as (a0 & V0 & Ha0 & HV0 & HN0); exists a0, V0; repeat split; assumption.
Qed.

(** The readback equations of a list of terms at a telescope, from each
    position's. *)
Lemma glu_nfs_eq_at_of_nth : forall Γ T Ms Ws, List.length Ms = List.length Ws ->
    (forall k M W A, List.nth_error Ms k = Some M -> List.nth_error Ws k = Some W ->
       List.nth_error (tele_insts T Id Ms) k = Some A -> glu_nf_eq Γ M W A) ->
    (forall k M, List.nth_error Ms k = Some M -> exists A, List.nth_error (tele_insts T Id Ms) k = Some A) ->
    glu_nfs_eq_at Γ T Ms Ws.
Proof.
  intros * Hl HW _.
  unfold glu_nfs_eq_at; split; [ rewrite !List.length_map; exact Hl |].
  intros k X Y A HX HY HAk.
  rewrite !List.nth_error_map in HY.
  destruct (List.nth_error Ws k) as [W |] eqn:HWk; [| discriminate ]; injection HY as <-.
  exact (HW _ _ _ _ HX HWk HAk).
Qed.

(** Arguments glued along a member's telescope are glued to their values
    by their readback. *)
Lemma glu_args_params_top : forall Dh Mh Δ Ms vs, all_assumptions (im_params Dh Mh) -> ctx_scoped 0 (im_params Dh Mh) ->
    glu_args Δ (im_params Dh Mh) Id nil Ms vs -> glu_params_top Dh Mh Δ Ms vs.
Proof.
  intros * Hass Hs Hg; pose proof Hg as [L1 L2 H].
  constructor; [ rewrite L1; apply length_im_params | |].
  - intros k M T HM HT.
    assert (Hk : k < List.length (im_params Dh Mh)) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as (κ & A & He).
    destruct (H _ _ _ _ _ _ HM HT Hv He) as [i a P El _ Hglu _ HMg].
    eapply glu_univ_elem_trm_escape; eassumption.
  - intros Δ' φ Rs Hφ HRs.
    destruct (read_ps_nth _ _ _ _ _ HRs) as [HRl HRn].
    apply glu_nfs_eq_at_of_nth; [ rewrite List.length_map, HRl; congruence | |].
    + intros k X Y T HX HY HT.
      rewrite List.nth_error_map in HX.
      destruct (List.nth_error Ms k) as [M |] eqn:HM; [| discriminate ]; injection HX as <-.
      rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
      destruct (List.nth_error (tele_insts (im_params Dh Mh) Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
      assert (Hk : k < List.length (im_params Dh Mh)) by (rewrite <- L1; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
      destruct (glu_args_ass_nth _ _ Hass Hk) as (κ & A & He).
      destruct (HRn _ _ _ _ Hv He) as (a' & V & Ha' & HV & HY').
      rewrite HY' in HY; injection HY as <-.
      destruct (H _ _ _ _ _ _ HM HT0 Hv He) as [i a P El Ha Hglu HP HMg].
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (realize_glu_elem_top _ _ _ _ Hglu _ _ _ _ HMg) as [? ? _ _ _ _ Hrb].
      exact (Hrb _ _ _ Hφ HV).
    + intros k X HX.
      apply nth_error_lt_some.
      rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.length_map, length_tele_insts_params by first [ exact Hass | rewrite L1; apply length_im_params ].
      assert (HXk : k < List.length (List.map (fun P => P[φ]ʷ) Ms)) by (apply List.nth_error_Some; congruence).
      rewrite List.length_map in HXk; exact HXk.
Qed.

(** ** The Non-Recursive Arguments, Syntactically *)

(** The terms among [As] at the non-recursive positions of [gs]. *)
Fixpoint nonrec_exps (gs : list carg) (As : list exp) : list exp :=
  match gs, As with
  | ca_arg _ _ :: gs, A :: As => A :: nonrec_exps gs As
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

Lemma nonrec_exps_nth_arg : forall gs gs1 κ A gs2 As N, gs = gs1 ++ ca_arg κ A :: gs2 -> List.length As = List.length gs ->
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
    destruct g as [κ B | Ps]; cbn [wk_pat nonrec_exps sb_of_list].
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
Lemma cargs_arg_type : forall p D Mk gs gs1 κ A gs2 σ As T, gs = gs1 ++ ca_arg κ A :: gs2 ->
    List.nth_error (tele_insts (cargs_ctx p D Mk gs) σ As) (List.length gs1) = Some T ->
    T = A[wk_pat (cargs_pat gs1)]ʷ[sb_of_list σ (List.firstn (List.length gs1) As)].
Proof.
  intros * -> HT.
  destruct (tele_insts_nth _ _ _ _ _ HT) as (κ0 & A0 & HA & ->).
  unfold cargs_ctx in HA; rewrite cargs_ctx_aux_app in HA; cbn [cargs_ctx_aux] in HA.
  rewrite !List.rev_app_distr in HA; cbn [List.rev List.app] in HA.
  rewrite List.nth_error_app2 in HA by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag in HA; cbn in HA.
  injection HA as _ <-; rewrite List.app_nil_r; reflexivity.
Qed.

(** The type of a recursive argument: the shape's type at the uniform
    parameters of the parameters, under the parameters and the
    non-recursive arguments before it. *)
Lemma cargs_rec_type_shape : forall p D Mk gs gs1 t gs2 Ps As T, gs = gs1 ++ ca_rec t :: gs2 ->
    decl_closed D -> List.length Ps = im_np D Mk ->
    List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Ps) As) (List.length gs1) = Some T ->
    T = ptyp_ty_at p D (List.firstn (ind_nu D) Ps) (sb_of_list Id (Ps ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))) t.
Proof.
  intros * Heq Hc HPl HT.
  assert (HAl : List.length gs1 < List.length As).
  { destruct (Nat.lt_ge_cases (List.length gs1) (List.length As)) as [| Hge]; [ assumption |].
    rewrite (proj2 (List.nth_error_None _ _)) in HT; [ discriminate |].
    rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; subst gs; rewrite List.length_app; cbn; lia. }
  rewrite (cargs_rec_type_at _ _ _ _ _ _ _ _ _ _ Heq Hc HPl HT).
  apply ptyp_ty_at_sb_eq.
  rewrite !sb_of_list_app; apply wk_pat_sb_of_list; rewrite List.length_firstn; lia.
Qed.

(** The types of the non-uniform parameters of a recursive argument ending
    in the member [Mj], at an instance [Us ++ Ys] of the context it is
    declared in. *)
Lemma rec_tele_inst : forall D j Mj Pr L τ Us Ys m T, decl_closed D -> ind_member D j = Some Mj ->
    List.length Us = ind_nu D -> List.length Ys = L ->
    List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) Pr) m = Some T ->
    List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id Us) (List.map (fun P => P[sb_of_list τ (Us ++ Ys)]) Pr)) m
      = Some T[sb_of_list τ (Us ++ Ys)].
Proof.
  intros * Hc HMj HUl HYl HT.
  rewrite <- (tele_insts_sub _ (ind_nu D) (sb_of_wk (wk_shiftn L)));
    [ rewrite List.nth_error_map, HT; reflexivity
    | eapply decl_closed_nparams_ass; eassumption | eapply decl_closed_nparams_scoped; eassumption |].
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
Lemma ptyp_ty_at_shape_step : forall p D t τ Us Ys φ b, decl_closed D -> List.length Us = ind_nu D ->
    (ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us) (q (sb_of_list τ (Us ++ Ys))) t)[(ι φ),,b]
    = ptyp_ty_at p D (List.map (fun U => U[φ]ʷ) Us)
        (sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))) t.
Proof.
  intros * Hc HUl; rewrite ptyp_ty_at_sub by (try exact Hc; rewrite List.length_map; exact HUl).
  rewrite List.map_map.
  rewrite (List.map_ext _ (fun U => U[φ]ʷ) (fun U => exp_shift_extend_wk U φ b)).
  apply ptyp_ty_at_sb_eq.
  rewrite List.app_assoc, <- List.map_app; apply sb_q_shape_step.
Qed.

(** A glued instance of a context extended by a term glued at the new
    entry's type. *)
Lemma glu_sub_snoc : forall Γ κ B Sb Sb' Δ σ ρ b c',
    EG Γ ∈ glu_ctx_env ↘ Sb -> EG ce_ass κ B :: Γ ∈ glu_ctx_env ↘ Sb' -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
    glu_arg Δ ρ B B[σ] b c' ->
    Δ ⊢ˢ σ,,b ® ρ ↦ c' ⦂ entry_type_closure B ρ ∈ Sb'.
Proof.
  intros * HSb HSb' Hσ Hb.
  apply (glu_sub_of_list (⋅ ▹{κ} B) Γ Sb' Sb Δ σ ρ (b :: nil) (c' :: nil)); [ repeat constructor; eauto | exact HSb' | exact HSb | exact Hσ |].
  apply (glu_args_snoc Δ nil κ B σ ρ b nil c' nil); split; [ exact Hb | apply glu_args_nil ].
Qed.

(** An element glued at a type of a value is glued at another type of it,
    at another gluing of it. *)
Lemma glu_elem_retype : forall (i j : universe_index) a P El P' El' Γ A A' M m,
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El -> Γ ⊢ A' ® P' -> Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * Hi Hj HA HM HA'.
  set (n := Nat.max (large_level i) (large_level j)).
  assert (Hin : universe_index_le i (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
  assert (Hjn : universe_index_le j (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_universe_index Hin Hi) as (Pn & Eln & Hn).
  pose proof (glu_univ_elem_typ_cumu_ge_universe_index Hin Hi Hn HA) as HAn.
  pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hin Hi Hn HM) as HMn.
  pose proof (glu_univ_elem_typ_cumu_ge_universe_index Hjn Hj Hn HA') as HA'n.
  assert (HMn' : Γ ⊢ M : A' ® m ∈ Eln).
  { assert (Hd : a = LevelSortᵈ \/ not_level_sort a) by (destruct a; first [ left; reflexivity | right; discriminate ]).
    destruct Hd as [-> | Hnl].
    - (* at the sort of levels, both types are it *)
      clear Hi Hj; basic_invert_glu_univ_elem Hn; apply_predicate_equivalence.
      destruct HAn as [-> _], HA'n as [-> _]; exact HMn.
    - pose proof (glu_univ_elem_typ_unique_upto_exp_eq' Hn Hnl HAn HA'n) as HE.
      exact (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hn _ _ _ _ _ HMn HE). }
  exact (glu_univ_elem_exp_lower_universe_index Hjn Hj Hn HA' HMn').
Qed.

(** An element of the relation of a domain's type, read at a related value. *)
Lemma dr_to_rel : forall B ρ b a1 c (i : universe_index) R (jd : universe_index), ⟦ B ⟧ ρ ↘ b -> Dom a1 ≈ b ∈ per_univ jd ->
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

(** ** Closed Gluing at [⋅] Weakens to Every Glued Context

    Simpler than [closed_weaken_sem]: [nil_glu_sub_pred] does not constrain
    the environment, and the terms are the same, so no closedness is needed. *)

Lemma glu_rel_exp_nil_weaken : forall Γ N T, ⊩ Γ -> ⋅ ⊩ N : T -> Γ ⊩ N : T.
Proof.
  intros * [SbΓ HΓ] [Sb0 H0 i Hi].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HΓ |]; intros Δ σ ρ Hσ.
  apply Hi.
  inversion H0 as [Sb' Heq Hg | | | |]; subst.
  apply (Heq Δ σ ρ); cbn.
  apply wf_sub_nil', (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HΓ _ _ _ Hσ)).
Qed.

End Fixed_GCtx.
