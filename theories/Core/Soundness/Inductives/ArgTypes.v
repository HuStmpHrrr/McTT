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
