(** * The Contexts of the Arguments of a Group's Constructors, Glued

    The gluing counterpart of [Completeness/Inductives/ArgTypes.v]: each
    prefix of the arguments of a constructor of a member of a filed group
    is a glued context over the member's parameters, weakened to its
    non-recursive arguments by [wk_pat] ([glu_group_cargs_all]).  A
    recursive argument's type is the [Π] over its shape's domains of the
    type of the member it ends in ([glu_group_shape_leaf]), and a member's
    type is a declared member's type former at the uniform parameters as
    variables, a view's container's at the view's instance, or a record
    view's record ([glu_group_mty]).  Where the PER model substitutes the
    uniform parameters as variables ([gsub]), the substitution is a
    weakening, so glued weakenings ([Γ ⊩ʷ φ : Δ]) suffice. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases UnitCases.
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
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Glued Weakenings

    The constructions of [Γ ⊩ʷ φ : Δ] the arguments' contexts need, as
    the PER model's of [Γ ⊨ʷ φ : Δ]: the identity, the shift past an entry,
    composition, the shift past a prefix and the lifting under an
    assumption. *)

(** A glued substitution may be presented in any pointwise equal form. *)
Lemma glu_sub_resp_sb_eq : forall Γ Sb Δ σ σ' ρ, EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢ˢ σ ® ρ ∈ Sb -> sb_eq σ σ' -> Δ ⊢ˢ σ' ® ρ ∈ Sb.
Proof.
  intros * HSb Hσ E.
  exact (glu_ctx_env_sub_resp_sub_eq HSb Hσ (wf_sub_eq_of_sb_eq _ _ _ _ _ _ (glu_ctx_env_sub_escape HSb _ _ _ Hσ) E)).
Qed.

Lemma glu_rel_wk_id : forall Γ, ⊩ Γ -> Γ ⊩ʷ wk_id : Γ.
Proof.
  intros Γ [Sb HSb].
  destruct (glu_ctx_env_per_ctx_env HSb) as [R HR].
  refine (mk_glu_rel_wk _ _ _ Sb HSb Sb HSb (wf_wk_id _ _ _ (glu_ctx_env_wf_ctx HSb)) _ _).
  - eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) | intros x Hx; exact Hx |].
    intros ρ ρ' _ x _; apply entry_propositional_id_wk.
  - intros Δ σ ρ Hσ; rewrite eval_wk_id.
    eapply glu_sub_resp_sb_eq; [ exact HSb | exact Hσ |].
    rewrite sb_of_wk_id; symmetry; apply sb_compose_id_left.
Qed.

Lemma glu_rel_wk_shift : forall Γ e, ⊩ e :: Γ -> e :: Γ ⊩ʷ ↑ : Γ.
Proof.
  intros Γ e [Sb HSb].
  assert (HT : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HSb; subst; eexists; eassumption).
  destruct HT as [TSb HTSb].
  refine (mk_glu_rel_wk _ _ _ Sb HSb TSb HTSb (wf_wk_shift _ _ _ _ (glu_ctx_env_wf_ctx HSb)) _ _).
  - exact (rel_wk_under_ctx_shift (completeness_fundamental_ctx _ (glu_ctx_env_wf_ctx HSb))).
  - intros Δ σ ρ Hσ; rewrite eval_wk_shift.
    eapply glu_sub_resp_sb_eq; [ exact HTSb | exact (glu_ctx_env_sub_tail HSb HTSb Hσ) |].
    rewrite sb_of_wk_shift; reflexivity.
Qed.

Lemma glu_rel_wk_compose : forall Γ Δ Θ' φ ψ, Γ ⊩ʷ ψ : Δ -> Δ ⊩ʷ φ : Θ' -> Γ ⊩ʷ (φ ⊙ ψ) : Θ'.
Proof.
  intros * [SbΓ HSbΓ SbΔ HSbΔ Hψt Hψs Hψg] [SbΔ' HSbΔ' SbΘ HSbΘ Hφt Hφs Hφg].
  assert (E : SbΔ <∙> SbΔ') by (eapply functional_glu_ctx_env; eassumption).
  refine (mk_glu_rel_wk _ _ _ SbΓ HSbΓ SbΘ HSbΘ (wf_wk_compose _ _ _ _ _ _ _ Hψt Hφt)
            (rel_wk_under_ctx_compose _ _ _ _ _ Hψs Hφs) _).
  intros Δ0 σ ρ Hσ.
  pose proof (Hψg _ _ _ Hσ) as H1; apply E in H1.
  pose proof (Hφg _ _ _ H1) as H2.
  assert (Hψm : WkMono ψ) by (destruct Hψs as [? ? ? ? Hw _ _]; exact (rel_wk_mono _ _ _ Hw)).
  assert (Hφm : WkMono φ) by (destruct Hφs as [? ? ? ? Hw _ _]; exact (rel_wk_mono _ _ _ Hw)).
  rewrite eval_wk_compose by assumption.
  eapply glu_sub_resp_sb_eq; [ exact HSbΘ | exact H2 |].
  rewrite sb_of_wk_compose, sb_compose_assoc; reflexivity.
Qed.

(** A glued substitution into [Ψ ++ Γ], past [Ψ]: glued into [Γ] at the
    environment's tail past [Ψ]. *)
Lemma glu_sub_shiftn : forall Ψ Γ Sb TSb, EG Ψ ++ Γ ∈ glu_ctx_env ↘ Sb -> EG Γ ∈ glu_ctx_env ↘ TSb ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> Δ ⊢ˢ ι (wk_shiftn (List.length Ψ)) ⨟ σ ® List.skipn (List.length Ψ) ρ ∈ TSb.
Proof.
  induction Ψ as [| e Ψ IH]; intros * HSb HT * Hσ; cbn [List.length List.app List.skipn] in *.
  - eapply glu_sub_resp_sb_eq; [ exact HT | apply (functional_glu_ctx_env HSb HT); exact Hσ |].
    intros x; cbn; f_equal; lia.
  - assert (HT' : exists TSb', EG Ψ ++ Γ ∈ glu_ctx_env ↘ TSb') by (inversion HSb; subst; eexists; eassumption).
    destruct HT' as [TSb' HTSb'].
    pose proof (IH _ _ _ HTSb' HT _ _ _ (glu_ctx_env_sub_tail HSb HTSb' Hσ)) as H.
    destruct ρ as [| d ρ]; cbn [drop_env List.tl] in H |- *; [ rewrite List.skipn_nil in H |].
    all: eapply glu_sub_resp_sb_eq; [ exact HT | exact H |].
    all: intros x; cbn; f_equal; lia.
Qed.

Lemma glu_rel_wk_shiftn : forall Ψ Γ, ⊩ Ψ ++ Γ -> ⊩ Γ -> Ψ ++ Γ ⊩ʷ (wk_shiftn (List.length Ψ)) : Γ.
Proof.
  intros Ψ Γ [Sb HSb] [TSb HT].
  refine (mk_glu_rel_wk _ _ _ Sb HSb TSb HT (wf_wk_shiftn_app' _ _ _ _ (glu_ctx_env_wf_ctx HSb))
            (rel_wk_under_ctx_shiftn _ _ (completeness_fundamental_ctx _ (glu_ctx_env_wf_ctx HSb))) _).
  intros Δ σ ρ Hσ; rewrite eval_wk_shiftn; exact (glu_sub_shiftn _ _ _ _ HSb HT _ _ _ Hσ).
Qed.

(** Lifted under an assumption: the head is the source's, glued at the
    type's value at the weakened tail, related to the weakened type's
    value at the tail ([rel_type_inversion_wk]). *)
Lemma glu_rel_wk_q : forall Γ ψ Δ κ A (i : nat), Γ ⊩ʷ ψ : Δ -> Δ ⊩ A : abs_kind_sort κ Typeω@i ->
    Γ ▹{κ} A[ψ]ʷ ⊩ʷ (wk_q ψ) : Δ ▹{κ} A.
Proof.
  intros * Hψ HA.
  pose proof Hψ as [SbΓ HSbΓ SbΔ HSbΔ Hψt Hψs Hψg].
  pose proof (glu_rel_exp_wk Hψ HA) as HAw; rewrite abs_kind_sort_wk in HAw; cbn [exp_wk] in HAw.
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt; pose proof (glu_rel_exp_to_wf_exp HAw) as HAwt.
  destruct (glu_rel_ctx_extend (ex_intro _ _ HSbΓ) HAw (sort_kind_abs_kind_sort κ i)) as [SbΓA HSbΓA].
  destruct (glu_rel_ctx_extend (ex_intro _ _ HSbΔ) HA (sort_kind_abs_kind_sort κ i)) as [SbΔA HSbΔA].
  pose proof (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HAt)) as HAv.
  pose proof (wf_wk_q _ _ _ _ _ _ _ _ Hψt HAt (sort_kind_abs_kind_sort κ i) HAwt) as Hqt.
  refine (mk_glu_rel_wk _ _ _ SbΓA HSbΓA SbΔA HSbΔA Hqt (rel_wk_under_ctx_q Hψs HAv) _).
  intros Δ' σ ρ Hσ.
  assert (Hψm : WkMono ψ) by (destruct Hψs as [? ? ? ? Hw _ _]; exact (rel_wk_mono _ _ _ Hw)).
  destruct (glu_ctx_env_cons_clean_inversion HSbΓ HSbΓA) as (i1 & _ & _ & E1).
  destruct (glu_ctx_env_cons_clean_inversion HSbΔ HSbΔA) as (i2 & _ & HT2 & E2).
  pose proof (glu_ctx_env_sub_escape HSbΓA _ _ _ Hσ) as Hσt.
  apply E1 in Hσ; inversion Hσ as [? ? ? a P El _ Ea Hg Hh Hpr Hrd Htl]; subst.
  apply E2.
  (** The tail: the source's, weakened *)
  assert (Htl2 : Δ' ⊢ˢ Wk ⨟ (ι (wk_q ψ) ⨟ σ) ® (⟪wk_q ψ⟫ ρ)↯ ∈ SbΔ).
  { rewrite eval_wk_q_tail by exact Hψm.
    eapply glu_sub_resp_sb_eq; [ exact HSbΔ | exact (Hψg _ _ _ Htl) | intros x; reflexivity ]. }
  destruct (HT2 _ _ _ Htl2) as [a2 P2 El2 Ea2 Hg2 HP2].
  (** The two values of the head's type, related *)
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [RΓ HRΓ].
  pose proof (glu_ctx_env_per_env HSbΓ HRΓ Htl) as Hρt.
  destruct (rel_type_inversion_wk Hψs HAv) as (R0 & HR0 & Hw).
  assert (E0 : RΓ <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hw _ _ (proj1 (E0 _ _) Hρt)) as (b1 & b2 & Eb1 & Eb2 & Hb).
  rewrite eval_wk_q_tail in Ea2 by exact Hψm.
  assert (b1 = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (b2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  (** The head's type, syntactically *)
  assert (ET : A[↑]ʷ[ι (wk_q ψ) ⨟ σ] = A[ψ]ʷ[↑]ʷ[σ]) by (rewrite !exp_sub_wk; apply exp_sub_sb_eq; intros x; reflexivity).
  assert (ET2 : A[Wk ⨟ (ι (wk_q ψ) ⨟ σ)] = A[↑]ʷ[ι (wk_q ψ) ⨟ σ])
    by (rewrite exp_sub_wk; apply exp_sub_sb_eq; rewrite sb_of_wk_shift; reflexivity).
  rewrite ET2, ET in HP2.
  rewrite <- (eval_wk_q_tail ψ ρ) in Ea2 by exact Hψm.
  econstructor; [ exact (wf_sub_compose _ _ _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hqt) Hσt) | exact Ea2 | exact Hg2 | | | | exact Htl2 ].
  - rewrite eval_wk_q_zero, ET.
    exact (glu_univ_elem_exp_conv Hb Hg Hg2 Hh HP2).
  - intros (c & Ec & Hc); rewrite eval_wk_q_zero_entry, eval_wk_q_zero; apply Hpr.
    assert (c = a2) as -> by (eapply functional_eval_exp; eassumption).
    destruct Hb as [Rb HRb]; exists a; split; [ exact Ea | rewrite (per_univ_elem_kind _ _ _ _ HRb); exact Hc ].
  - rewrite eval_wk_q_zero_entry; exact Hrd.
Qed.

(** ** Glued Substitutions

    The constructions of [Γ ⊩ˢ τ : Δ] the iterated application of a type
    former needs, as the PER model's [gsub]: the identity, the extension
    by a glued term, and the lifting under an assumption.  The targets are
    telescopes of assumptions, where a glued substitution moves along the
    context PER: an environment related to a glued one is glued. *)

Lemma glu_sub_resp_per : forall Γ Sb R, all_assumptions Γ -> EG Γ ∈ glu_ctx_env ↘ Sb -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    forall Δ σ ρ ρ', Dom ρ ≈ ρ' ∈ R -> Δ ⊢ˢ σ ® ρ ∈ Sb -> Δ ⊢ˢ σ ® ρ' ∈ Sb.
Proof.
  induction Γ as [| e Γ IH]; intros * Hass HC HR * Hρ Hσ.
  - inversion HC; subst.
    match goal with E : Sb <∙> nil_glu_sub_pred |- _ => apply E; apply E in Hσ; exact Hσ end.
  - apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass].
    assert (HT : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HC; subst; eexists; eassumption).
    destruct HT as [TSb HTSb].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HC) as (i & _ & HTT & HSb).
    destruct (glu_ctx_env_per_ctx_env HTSb) as [RT HRT].
    destruct (per_ctx_env_cons_clean_inversion HRT HR) as (i' & hr & Hhr & _ & HRCe).
    apply HRCe in Hρ as [HEt Hhd _ HEr _ HErr].
    apply HSb in Hσ; inversion Hσ as [? ? ? a P El Hσt Ha Hg Hh _ _ Htl]; subst.
    pose proof (IH _ _ Hass HTSb HRT _ _ _ _ HEt Htl) as Htl'.
    destruct (HTT _ _ _ Htl') as [a' P' El' Ha' Hg' HP'].
    destruct (Hhr _ _ HEt) as [a1 a1' Ea1 Ea1' HR1].
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a1' = a') as -> by (eapply functional_eval_exp; eassumption).
    apply HSb; econstructor; [ exact Hσt | exact Ha' | exact Hg' | | exact HEr | exact HErr | exact Htl' ].
    assert (Haa : Dom a ≈ a' ∈ per_univ i') by (eexists; exact HR1).
    pose proof (glu_univ_elem_exp_conv Haa Hg Hg' Hh ltac:(rewrite <- exp_sub_of_wk, exp_sub_sub; exact HP')) as Hh'.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hg') as [R2 HR2].
    pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR1 HR2) as ER.
    exact (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hg' _ HR2 _ _ _ _ _ Hh' (proj1 (ER _ _) Hhd)).
Qed.

Lemma glu_rel_sub_id : forall Γ, ⊩ Γ -> Γ ⊩ˢ Id : Γ.
Proof.
  intros Γ [Sb HSb].
  pose proof (glu_ctx_env_wf_ctx HSb) as HΓw.
  refine (mk_glu_rel_sub _ _ _ Sb HSb Sb HSb (wf_sub_id _ _ _ HΓw)
            (rel_sub_id (rel_ctx_wf_per_ctx_env (completeness_fundamental_ctx _ HΓw))) _).
  intros Δ σ ρ Hσ; exists ρ; split.
  - eapply glu_sub_resp_sb_eq; [ exact HSb | exact Hσ |]; symmetry; apply sb_compose_id_left.
  - intros R ρτ0 HR Hev.
    pose proof (glu_ctx_env_per_env HSb HR Hσ) as Hρ.
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    pose proof (rel_sub_under_ctx_at' (rel_sub_id (rel_ctx_wf_per_ctx_env (completeness_fundamental_ctx _ HΓw))) HR HR
                  _ _ _ _ Hρ Hev (eval_sub_id _ _)) as H1.
    etransitivity; [ exact H1 | exact (per_ctx_env_retag_left HR _ _ Hρ) ].
Qed.

(** The extension of a substitution by an entry, evaluated: the
    substitution's value is the tail, and the entry's value the head when
    it is no proposition ([eval_sub_extend_inv], at any entry). *)
#[local] Transparent eval_sub.
Lemma eval_sub_extend_gen_inv : forall e0 Δ σ e ρ ρτ,
    ⟦ sb_extend σ e : e0 :: Δ ⟧s ρ ↘ ρτ ->
    ⟦ σ : Δ ⟧s ρ ↘ ρτ↯ /\
      (~ entry_propositional gc_deps gc_stack (e0 :: Δ)%list ρτ 0 -> ⟦ sentry_exp e ⟧ ρ ↘ ρτ 0).
Proof.
  intros * H; split.
  - intros x Hx; rewrite env_entry_drop, (ctx_entry_tag_drop e0); change (ctx_entry_unit Δ x) with (ctx_entry_unit (e0 :: Δ) (S x)); split.
    + intros Hp; apply (H (S x) ltac:(cbn; lia)); exact (proj2 (entry_propositional_succ _ _ _ _) Hp).
    + intros Hn; apply (H (S x) ltac:(cbn; lia)); intros Hp; exact (Hn (proj1 (entry_propositional_succ _ _ _ _) Hp)).
  - intros Hn; pose proof (proj2 (H 0 ltac:(cbn; lia)) Hn) as Hx; cbn in Hx.
    assert (E0 : ρτ 0 = match hd absent_entry ρτ with de_mod _ _ => Propᵈ | de_term d _ | de_dm d _ _ _ => d end)
      by (destruct ρτ; reflexivity).
    rewrite E0; clear E0.
    destruct e as [y | M | Hm | N Hm]; cbn [sentry_exp eval_sentry] in Hx |- *.
    + rewrite Hx.
      replace (match retag_entry _ _ (env_entry ρ y) with de_mod _ _ => Propᵈ | de_term d _ | de_dm d _ _ _ => d end)
        with (env_var ρ y) by (unfold env_var; destruct (env_entry ρ y); reflexivity).
      econstructor.
    + destruct Hx as (m0 & -> & Hx0); exact Hx0.
    + destruct Hx as (h0 & -> & _); econstructor.
    + destruct Hx as (n0 & h0 & -> & Hx0 & _); exact Hx0.
Qed.
#[local] Opaque eval_sub.

(** Extended by an entry whose term is glued: glued at a value of the
    extension, its tail moved to it along the target's PER
    ([glu_sub_resp_per]), its head the term's value. *)
Lemma glu_rel_sub_extend_gen : forall Γ τ Δ κ A e (i : nat), all_assumptions Δ ->
    Γ ⊩ˢ τ : Δ -> Δ ⊩ A : abs_kind_sort κ Typeω@i -> Γ ⊩ sentry_exp e : A[τ] ->
    Γ ⊢ˢ sb_extend τ e : Δ ▹{κ} A -> Γ ⊨ˢ sb_extend τ e ≈ sb_extend τ e : Δ ▹{κ} A ->
    Γ ⊩ˢ sb_extend τ e : Δ ▹{κ} A.
Proof.
  intros * HassΔ Hτ HA HN Hst Hs.
  pose proof Hτ as [SbΓ HSbΓ SbΔ HSbΔ Hτt Hτs Hτg].
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  pose proof (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HAt)) as HAv.
  destruct (glu_rel_ctx_extend (ex_intro _ _ HSbΔ) HA (sort_kind_abs_kind_sort κ i)) as [SbΔA HSbΔA].
  refine (mk_glu_rel_sub _ _ _ SbΓ HSbΓ SbΔA HSbΔA Hst Hs _).
  intros Δ' σ ρ Hσ.
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [RΓ HRΓ].
  destruct (glu_ctx_env_per_ctx_env HSbΔ) as [RΔ HRΔ].
  destruct (glu_ctx_env_per_ctx_env HSbΔA) as [RΔA HRΔA].
  pose proof (glu_ctx_env_per_env HSbΓ HRΓ Hσ) as Hρ.
  destruct (rel_sub_under_ctx_simple Hs) as [RΓ1 [HRΓ1 [RΔA1 [HRΔA1 Hsim]]]].
  assert (E1 : RΓ <~> RΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hsim _ _ (proj1 (E1 _ _) Hρ)) as [ρτ' [_ [Hev _]]].
  exists ρτ'; split; [| intros R ρτ0 HR Hev0; exact (rel_sub_under_ctx_at' Hs HRΓ HR _ _ _ _ Hρ Hev0 Hev) ].
  destruct (eval_sub_extend_gen_inv _ _ _ _ _ _ Hev) as [Hevt Hhd].
  (** The tail, moved to the value's *)
  destruct (Hτg _ _ _ Hσ) as (ρτ & Hσ' & Hrel).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HRΔ).
  pose proof (glu_sub_resp_per _ _ _ HassΔ HSbΔ HRΔ _ _ _ _ (symmetry (Hrel _ _ HRΔ Hevt)) Hσ') as Htl.
  destruct (glu_ctx_env_cons_clean_inversion HSbΔ HSbΔA) as (i2 & _ & HT2 & E2).
  apply E2.
  assert (Htl2 : Δ' ⊢ˢ Wk ⨟ ((sb_extend τ e) ⨟ σ) ® ρτ'↯ ∈ SbΔ)
    by (eapply glu_sub_resp_sb_eq; [ exact HSbΔ | exact Htl | intros x; reflexivity ]).
  destruct (HT2 _ _ _ Htl2) as [a0 P0 El0 Ea0 Hg0 HP0].
  (** The head: the term's value, glued at its type moved to the value *)
  pose proof HN as [SbΓ' HSbΓ' iN HNb].
  assert (E' : SbΓ <∙> SbΓ') by (eapply functional_glu_ctx_env; eassumption).
  destruct (HNb _ _ _ (proj1 (E' _ _ _) Hσ)) as [aN n PN ElN EaN En HgN HEN].
  destruct (Completeness.LogicalRelation.Telescope.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HRΓ Hτs Hρ Hevt) as (b1 & b2 & Eb1 & Eb2 & Hb).
  assert (b1 = aN) as -> by (eapply functional_eval_exp; eassumption).
  assert (b2 = a0) as -> by (eapply functional_eval_exp; eassumption).
  assert (ET : A[↑]ʷ[(sb_extend τ e) ⨟ σ] = A[τ][σ]) by (rewrite exp_sub_wk, exp_sub_sub; apply exp_sub_sb_eq; intros x; reflexivity).
  assert (ET2 : A[Wk ⨟ ((sb_extend τ e) ⨟ σ)] = A[τ][σ]) by (rewrite exp_sub_sub; apply exp_sub_sb_eq; intros x; reflexivity).
  rewrite ET2 in HP0.
  pose proof (glu_univ_elem_exp_conv Hb HgN Hg0 HEN HP0) as HE0.
  pose proof (rel_sub_under_ctx_at' Hs HRΓ HRΔA _ _ _ _ Hρ Hev Hev) as Hρτ'.
  destruct (per_ctx_env_cons_clean_inversion HRΔ HRΔA) as (i3 & hr & Hhr & _ & HRe).
  apply HRe in Hρτ' as [Ht' Hh' Hl' _ Hrd' _].
  econstructor; [ exact (wf_sub_compose _ _ _ _ _ _ _ Hst (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ)) | exact Ea0 | exact Hg0 | | exact Hl' | exact Hrd' | exact Htl2 ].
  rewrite ET; replace (#0[(sb_extend τ e) ⨟ σ]) with ((sentry_exp e)[σ]) by (rewrite sentry_exp_sub; reflexivity).
  (** The value there is the term's: the same at an evaluated kind, both
      proofs at a proposition *)
  destruct (glu_univ_elem_per_univ _ _ _ _ Hg0) as [R0 HR0].
  apply (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hg0 _ HR0 _ _ _ _ _ HE0).
  destruct Hb as [Rb HRb]; pose proof (per_univ_elem_kind _ _ _ _ HRb) as Hk.
  destruct (Hhr _ _ Ht') as [c1 c2 Ec1 Ec2 HRc].
  assert (c1 = a0) as -> by (eapply functional_eval_exp; eassumption).
  assert (c2 = a0) as -> by (eapply functional_eval_exp; eassumption).
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRc HR0) as Ehr.
  assert (HPR0 : PER R0) by (eapply per_elem_PER; exact HR0).
  destruct (domain_kind a0) eqn:Hk0.
  2:{ (** At a proposition both are proofs *)
    pose proof (per_univ_elem_propositional _ _ _ _ HR0 Hk0) as Ep.
    destruct (glu_univ_elem_per_univ _ _ _ _ HgN) as [RN HRN].
    destruct (glu_univ_elem_prop_inv _ _ _ _ (per_univ_elem_per_prop_of_kind HRN Hk) HgN) as [_ HElN].
    apply HElN in HEN; destruct HEN as [_ _ Hpn].
    apply Ep; split; [ exact (proj1 Hpn) | exact (proj1 (proj1 (Ep _ _) (proj1 (Ehr _ _) Hh'))) ]. }
  (** At an evaluated kind the head is the term's value *)
  all: assert (Hnp : ~ entry_propositional gc_deps gc_stack (Δ ▹{κ} A) ρτ' 0)
         by (intros Hp; apply (proj1 (entry_propositional_zero_head _ _ _)) in Hp;
             apply (proj1 (head_propositional_of_rel_typ (e := ce_ass κ A) (A := A) hr _ _ HRΔ ltac:(reflexivity) Hhr Ht')) in Hp;
             destruct Hp as (c & Ec & Hc); assert (c = a0) as -> by (eapply functional_eval_exp; eassumption); congruence).
  all: rewrite Hk in En; cbn [glu_term_value] in En.
  all: pose proof (functional_eval_exp _ _ _ _ (Hhd Hnp) En) as Heqn; rewrite <- Heqn.
  all: apply Ehr; exact Hh'.
Qed.

(** Extended by a glued term *)
Lemma glu_rel_sub_ext : forall Γ τ Δ κ A N (i : nat), all_assumptions Δ ->
    Γ ⊩ˢ τ : Δ -> Δ ⊩ A : abs_kind_sort κ Typeω@i -> Γ ⊩ N : A[τ] -> Γ ⊩ˢ τ,,N : Δ ▹{κ} A.
Proof.
  intros * HassΔ Hτ HA HN.
  pose proof Hτ as [_ _ _ _ Hτt Hτs _].
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt; pose proof (glu_rel_exp_to_wf_exp HN) as HNt.
  pose proof (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HAt)) as HAv.
  assert (HNs : exp_scoped (List.length Γ) N) by exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HNt))).
  exact (glu_rel_sub_extend_gen _ _ _ _ _ (se_exp N) i HassΔ Hτ HA HN
           (wf_sub_extend _ _ _ _ _ _ _ _ _ Hτt HAt (sort_kind_abs_kind_sort κ i) HNt)
           (rel_sub_under_ctx_extend (κ := κ) Hτs HAv (completeness_fundamental_exp _ _ _ HNt) HNs HNs)).
Qed.

(** Postcomposed with a glued weakening: glued at the substitution's
    glued environment at the weakened one, related to the values of the
    composite by the semantic substitution's Kripke clause. *)
Lemma glu_rel_sub_wk : forall Γ' ψ Γ τ Δ, Γ' ⊩ʷ ψ : Γ -> Γ ⊩ˢ τ : Δ -> Γ' ⊩ˢ sb_wk τ ψ : Δ.
Proof.
  intros * [SbΓ' HSbΓ' SbΓ1 HSbΓ1 Hψt Hψs Hψg] [SbΓ HSbΓ SbΔ HSbΔ Hτt Hτs Hτg].
  assert (E : SbΓ1 <∙> SbΓ) by (eapply functional_glu_ctx_env; eassumption).
  pose proof (rel_sub_under_ctx_wk Hτs Hψs) as Hs.
  refine (mk_glu_rel_sub _ _ _ SbΓ' HSbΓ' SbΔ HSbΔ (wf_sub_wk _ _ _ _ _ _ _ Hτt Hψt) Hs _).
  intros Δ' σ ρ Hσ.
  pose proof (Hψg _ _ _ Hσ) as Hσ1; apply E in Hσ1.
  destruct (Hτg _ _ _ Hσ1) as (ρτ & Hστ & Hrel).
  exists ρτ; split.
  - eapply glu_sub_resp_sb_eq; [ exact HSbΔ | exact Hστ |].
    rewrite sb_wk_compose, sb_compose_assoc; reflexivity.
  - intros R X HR HX.
    pose proof Hψs as [R1 HR1 R2 HR2 Hψw Hψb _].
    pose proof Hτs as [RΓ0 HRΓ0 RΔ0 HRΔ0 Hb _].
    assert (E2 : R2 <~> RΓ0) by (eapply per_ctx_env_right_irrel; eassumption).
    assert (Hψw' : rel_wk ψ R1 RΓ0) by (destruct Hψw as [Hm Hw]; split; [ exact Hm | intros; apply E2, Hw; assumption ]).
    pose proof (glu_ctx_env_per_env HSbΓ' HR1 Hσ) as Hρ.
    destruct (Hb _ _ HR1 _ Hψw' Hψb _ _ Hρ) as [ρ1 ρ2 ρ3 ρ4 E1 E2' _ _ Hch].
    destruct Hch as (H12 & _).
    assert (E3 : RΔ0 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    etransitivity; [ exact (rel_sub_under_ctx_at' Hs HR1 HR _ _ _ _ Hρ HX E1) |].
    etransitivity; [ apply E3; exact H12 | exact (Hrel _ _ HR E2') ].
Qed.

(** Lifted under an assumption: [q τ] is [τ] weakened past the new entry,
    extended by its variable ([glu_rel_sub_extend_gen]). *)
Lemma glu_rel_sub_q : forall Γ τ Δ κ A (i : nat), all_assumptions Δ ->
    Γ ⊩ˢ τ : Δ -> Δ ⊩ A : abs_kind_sort κ Typeω@i -> Γ ▹{κ} A[τ] ⊩ˢ q τ : Δ ▹{κ} A.
Proof.
  intros * HassΔ Hτ HA.
  pose proof Hτ as [SbΓ HSbΓ _ _ Hτt Hτs _].
  pose proof (glu_rel_exp_sub Hτ HA) as HAτ; rewrite abs_kind_sort_sub in HAτ; cbn [exp_sub] in HAτ.
  pose proof (glu_rel_ctx_extend (ex_intro _ _ HSbΓ) HAτ (sort_kind_abs_kind_sort κ i)) as HΓA.
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt; pose proof (glu_rel_exp_to_wf_exp HAτ) as HAτt.
  pose proof (glu_rel_sub_wk _ _ _ _ _ (glu_rel_wk_shift _ _ HΓA) Hτ) as Hw.
  assert (H0 : Γ ▹{κ} A[τ] ⊩ sentry_exp (se_var 0) : A[sb_wk τ ↑]).
  { cbn [sentry_exp]; rewrite <- exp_wk_sub; exact (glu_rel_exp_vlookup HΓA (here _ _ _)). }
  exact (glu_rel_sub_extend_gen _ _ _ _ _ (se_var 0) i HassΔ Hw HA H0
           (wf_sub_q _ _ _ _ _ _ _ _ Hτt HAt (sort_kind_abs_kind_sort κ i) HAτt)
           (rel_sub_under_ctx_q Hτs (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HAt)))).
Qed.

(** ** Telescopes

    A telescope of assumptions whose entries are glued over the entries
    after them ([glu_tele_entries]), as [rel_ctx_wf] gives them in the PER
    model: lifted along a glued substitution ([glu_rel_sub_qn]), its
    entries glued along it ([glu_tele_entries_sub]), its [Π] glued
    ([glu_rel_exp_ctx_pi]), and an element of the [Π] applied to glued
    terms of its entries' instances glued ([glu_rel_exp_apps_ctx_pi_n],
    [rel_exp_apps_ctx_pi_n]). *)
Definition glu_tele_entries (Δ Γ : ctx) : Prop :=
  forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> exists j : nat, Δ2 ++ Γ ⊩ A : abs_kind_sort κ Typeω@j.

Lemma glu_tele_entries_tail : forall e Δ Γ, glu_tele_entries (e :: Δ) Γ -> glu_tele_entries Δ Γ.
Proof. intros * H Δ1 κ A Δ2 E; apply (H (e :: Δ1)); rewrite E; reflexivity. Qed.

Lemma glu_rel_sub_qn : forall Pre Γ0 τ Δ0, all_assumptions (Pre ++ Δ0) -> Γ0 ⊩ˢ τ : Δ0 -> glu_tele_entries Pre Δ0 ->
    tele_sub Pre τ ++ Γ0 ⊩ˢ sb_qn (List.length Pre) τ : Pre ++ Δ0.
Proof.
  induction Pre as [| e Pre IH]; intros * Hass Hτ HP; cbn [tele_sub List.app List.length sb_qn]; [ exact Hτ |].
  cbn [List.app] in Hass; apply List.Forall_cons_iff in Hass as [(κ & B & ->) Hass].
  destruct (HP nil κ B Pre eq_refl) as [j HB].
  exact (glu_rel_sub_q _ _ _ _ _ j Hass (IH _ _ _ Hass Hτ (glu_tele_entries_tail _ _ _ HP)) HB).
Qed.

Lemma glu_tele_entries_sub : forall Pre Γ0 τ Δ0, all_assumptions (Pre ++ Δ0) -> Γ0 ⊩ˢ τ : Δ0 -> glu_tele_entries Pre Δ0 ->
    glu_tele_entries (tele_sub Pre τ) Γ0.
Proof.
  induction Pre as [| e Pre IH]; intros * Hass Hτ HP Δ1 κ A Δ2 E; [ destruct Δ1; discriminate |].
  cbn [List.app] in Hass; pose proof Hass as Hass0; apply List.Forall_cons_iff in Hass as [(κ0 & B & ->) Hass].
  cbn [tele_sub centry_sub] in E.
  destruct Δ1 as [| e1 Δ1]; cbn [List.app] in E.
  - injection E as <- <- <-.
    destruct (HP nil κ0 B Pre eq_refl) as [j HB].
    exists j; pose proof (glu_rel_exp_sub (glu_rel_sub_qn _ _ _ _ Hass Hτ (glu_tele_entries_tail _ _ _ HP)) HB) as H.
    rewrite abs_kind_sort_sub in H; exact H.
  - injection E as _ E.
    exact (IH _ _ _ Hass Hτ (glu_tele_entries_tail _ _ _ HP) _ _ _ _ E).
Qed.

Lemma glu_rel_exp_ctx_pi : forall Δ Γ B (i : nat), all_assumptions Δ -> glu_tele_entries Δ Γ -> Δ ++ Γ ⊩ B : Typeω@i ->
    exists j : nat, Γ ⊩ ctx_pi Δ B : Typeω@j.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HB; [ exists i; exact HB |].
  apply List.Forall_cons_iff in HΔa as [(κ & A & ->) HΔa].
  destruct (HΔ nil κ A Δ eq_refl) as [k HA].
  cbn [ctx_pi_at].
  apply (IH _ _ (max k i) HΔa (glu_tele_entries_tail _ _ _ HΔ)).
  exact (glu_rel_exp_pi_large (glu_rel_exp_kind_sort_lift (Nat.le_max_l k i) HA)
           (glu_rel_exp_kind_sort_lift (κ := ak_relevant) (Nat.le_max_r k i) HB) (pi_kinds_relevant κ)).
Qed.

Lemma glu_rel_exp_apps_ctx_pi_n : forall n Δ Γ B (i : nat) M Ms,
    List.length Δ = n -> all_assumptions Δ -> all_assumptions Γ -> ⊩ Γ -> glu_tele_entries Δ Γ ->
    Δ ++ Γ ⊩ B : Typeω@i -> Γ ⊩ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Γ ⊩ N : T) ->
    Γ ⊩ apps M Ms : B[sb_of_list Id Ms].
Proof.
  induction n as [| n IH]; intros * Hn Hass HΓa HΓ HΔ HB HM Hl HMs.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; cbn; rewrite exp_sub_id; exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HB; cbn [List.app] in HB.
    destruct (HΔ Δ κ0 A0 nil eq_refl) as [j HA0]; cbn [List.app] in HA0.
    assert (HΔ' : glu_tele_entries Δ (Γ ▹{κ0} A0)).
    { intros Δ1 κ A Δ2 E; destruct (HΔ Δ1 κ A (Δ2 ++ ce_ass κ0 A0 :: nil)) as [j' H];
        [ rewrite E, <- List.app_assoc; reflexivity | exists j'; rewrite <- List.app_assoc in H; exact H ]. }
    assert (HΓA : ⊩ Γ ▹{κ0} A0) by exact (glu_rel_ctx_extend HΓ HA0 (sort_kind_abs_kind_sort κ0 j)).
    assert (HassΓA : all_assumptions (Γ ▹{κ0} A0)) by (constructor; [ eauto | exact HΓa ]).
    destruct (glu_rel_exp_ctx_pi _ _ _ _ Hass HΔ' HB) as [k HPi].
    assert (HM0 : Γ ⊩ M0 : A0)
      by (rewrite <- (exp_sub_id A0); apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    (** The application *)
    pose proof (glu_rel_exp_app HA0 (sort_kind_abs_kind_sort κ0 j) (glu_rel_exp_kind_sort_lift (κ := ak_relevant) (le_n k) HPi)
                  (pi_kinds_relevant κ0) HM HM0) as Happ.
    rewrite ctx_pi_sub in Happ.
    assert (Hg0 : Γ ⊩ˢ Id,,M0 : Γ ▹{κ0} A0)
      by (apply (glu_rel_sub_ext _ _ _ _ _ _ j HΓa (glu_rel_sub_id _ HΓ) HA0); rewrite exp_sub_id; exact HM0).
    assert (HassΔΓ : all_assumptions (Δ ++ Γ ▹{κ0} A0)) by (apply List.Forall_app; split; assumption).
    pose proof (glu_rel_sub_qn _ _ _ _ HassΔΓ Hg0 HΔ') as Hgq.
    pose proof (glu_rel_exp_sub Hgq HB) as HB'; cbn [exp_sub] in HB'.
    cbn [apps_exp sb_of_list].
    replace (B[sb_of_list (Id,,M0) Ms]) with (B[sb_qn (List.length Δ) (Id,,M0)][sb_of_list Id Ms])
      by (replace (List.length Δ) with (List.length Ms) by lia; apply exp_sub_qn_of_list).
    eapply (IH (tele_sub Δ (Id,,M0)) Γ (B[sb_qn (List.length Δ) (Id,,M0)]) i (M $ M0) Ms);
      [ rewrite length_tele_sub; lia | apply all_assumptions_sub; exact Hass | exact HΓa | exact HΓ
      | exact (glu_tele_entries_sub _ _ _ _ HassΔΓ Hg0 HΔ') | exact HB' | exact Happ | rewrite length_tele_sub; lia | ].
    intros k' N T HN HT; apply (HMs (S k')); [ exact HN |].
    rewrite tele_insts_snoc; cbn [List.nth_error].
    rewrite tele_insts_tele_sub in HT; rewrite <- HT; f_equal.
    apply tele_insts_sb_eq; symmetry; apply sb_compose_id_right.
Qed.

(** ** Types of a Group's Sort

    A type of the sort of a valid glued group, weakened past the
    parameters and an extension, is a type of a large universe: the sort
    is one, or small at a level glued over the parameters
    ([glu_ind_decl_lvlP]), weakened. *)
Section GroupSort.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (HG : glu_ind_decl D).

  Lemma glu_group_sort_large : forall Ψ k Mk κ A, ind_member D k = Some Mk -> ⊩ Ψ ++ im_params D Mk ->
      Ψ ++ im_params D Mk ⊩ A : abs_kind_sort κ (ind_sort D)[wk_shiftn (List.length Ψ + im_nn Mk)]ʷ ->
      exists i : nat, Ψ ++ im_params D Mk ⊩ A : abs_kind_sort κ Typeω@i.
  Proof.
    intros * HM HΨ HA.
    destruct (valid_group_sort _ _ Hg) as [[i0 Heq] | [t Heq]]; rewrite Heq in HA; cbn [exp_wk] in HA; [ exists i0; exact HA |].
    destruct (glu_ind_decl_lvlP _ HG _ _ HM) as [n Hn]; rewrite Heq in Hn; cbn [ind_sort_lvl] in Hn.
    pose proof (glu_rel_wk_shiftn Ψ (im_params D Mk) HΨ (glu_ind_decl_params _ HG _ _ HM)) as Hw.
    pose proof (glu_rel_exp_wk Hw Hn) as Hn'; cbn [exp_wk] in Hn'.
    rewrite (exp_wk_wk_ext _ _ _ (wk_shiftn (List.length Ψ + im_nn Mk))) in Hn' by (intros x; cbn; lia).
    exists 0; exact (glu_rel_exp_kind_sort_small_large Hn' HA).
  Qed.
End GroupSort.

(** ** The Contexts of the Arguments, Given the Weakening Before

    As [shape_domains_ctx_wk_gen] and [shape_domains_ctx_sem_gen]: the
    domains of a recursive argument's shape, over the arguments before it,
    from the weakening of those to their non-recursive ones. *)
Section GluArgsCtx.
  Variables (p : qname) (D : ind_decl) (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (Hg : valid_group p D) (HG : glu_ind_decl D) (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).

  (** A non-recursive argument's type, over the non-recursive arguments
      before it, is a type of a large universe of its kind *)
  Lemma glu_group_arg_large : forall gs1 r A gs2, gs = gs1 ++ ca_arg r A :: gs2 ->
      exists i : nat, cargs_nonrec_ctx gs1 ++ im_params D Mk ⊩ A : abs_kind_sort r Typeω@i.
  Proof.
    intros * Heq.
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    pose proof (nonrec_kind_at gs1 gs2 r A) as Hr; rewrite <- Heq in Hr.
    pose proof (glu_ind_decl_arg _ HG _ _ _ _ _ _ _ HM Hcon HA Hr) as HAg.
    rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HAg.
    pose proof HAg as [SbX HSbX _ _].
    assert (Hl : List.length (cargs_nonrec_ctx gs1) = List.length (cargs_nonrec gs1))
      by (rewrite cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele; reflexivity).
    rewrite <- Hl in HAg.
    exact (glu_group_sort_large p D Hg HG _ _ _ _ _ HM (ex_intro _ _ HSbX) HAg).
  Qed.

  (** A domain of a recursive argument's shape, over the domains before it
      and the non-recursive arguments before the argument, is a type of a
      large universe *)
  Lemma glu_group_dom_large : forall gs1 t gs2 j B, gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) j = Some B ->
      exists i : nat, doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk ⊩ B : Typeω@i.
  Proof.
    intros * Heq HB.
    pose proof (glu_ind_decl_dom _ HG _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as HBg.
    rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix, List.app_assoc in HBg.
    pose proof HBg as [SbX HSbX _ _].
    assert (Hj : j < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
    assert (Hl : List.length (doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1) = j + List.length (cargs_nonrec gs1))
      by (rewrite List.length_app, length_doms_ctx, List.length_firstn, cargs_nonrec_ctx_rev_tele, List.length_rev,
            length_cargs_nonrec_tele; lia).
    rewrite <- Hl in HBg.
    destruct (glu_group_sort_large p D Hg HG _ _ _ ak_relevant _ HM (ex_intro _ _ HSbX) HBg) as [i HB'].
    rewrite <- List.app_assoc in HB'; exists i; exact HB'.
  Qed.

  Lemma glu_shape_domains_ctx_wk_gen : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊩ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk ->
      forall j, j <= List.length (ptyp_doms t) ->
        shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
          ⊩ʷ (wk_pat (List.repeat false j ++ cargs_pat gs1))
          : doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk.
  Proof.
    intros * Heq Hw0; induction j as [| j IH]; intros Hj.
    - exact Hw0.
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      destruct (glu_group_dom_large _ _ _ _ _ Heq HB) as [i HBg].
      rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, doms_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.repeat List.app wk_pat].
      exact (glu_rel_wk_q _ _ _ ak_relevant _ i (IH ltac:(lia)) HBg).
  Qed.

  Lemma glu_shape_domains_ctx_gen : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      ⊩ cargs_ctx p D Mk gs1 ++ im_params D Mk ->
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊩ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk ->
      forall j, j <= List.length (ptyp_doms t) ->
        ⊩ shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk.
  Proof.
    intros * Heq HC0 Hw0; induction j as [| j IH]; intros Hj.
    - exact HC0.
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      pose proof (glu_shape_domains_ctx_wk_gen _ _ _ Heq Hw0 j ltac:(lia)) as Hw.
      destruct (glu_group_dom_large _ _ _ _ _ Heq HB) as [i HBg].
      pose proof (glu_rel_exp_wk Hw HBg) as HBw; cbn [exp_wk] in HBw.
      rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.app].
      exact (glu_rel_ctx_extend (IH ltac:(lia)) HBw (sort_kind_abs_kind_sort ak_relevant i)).
  Qed.
End GluArgsCtx.

End Fixed_GCtx.
