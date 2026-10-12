From Stdlib Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Corollaries Substitution LevelEq IndCong.
From Mctt.Core.Semantic Require Import Realizability IndCanon.
From Mctt.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From Mctt.Core.Soundness.Weakening Require Export Lemmas.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma glu_nat_per_nat : forall Γ M a,
    glu_nat Γ M a ->
    Dom a ≈ a ∈ per_nat.
Proof.
  induction 1; mauto.
Qed.

#[local]
Hint Resolve glu_nat_per_nat : mctt.

Lemma glu_nat_escape : forall Γ M a,
    glu_nat Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : ℕ.
Proof.
  induction 1; intros;
    try match goal with
    | H : _ |- _ => solve [gen_presup H; mauto]
    end.
  assert (Γ ⊢k wk_id : Γ) by mauto 2.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert (Γ ⊢ M[wk_id]ʷ ≈ M' : ℕ) as HM by mauto.
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve glu_nat_escape : mctt.

(** [glu_nat] is stable under context refinement [Δ ⊆ Γ], which is what the
    [ctxsub_*] lemmas need. The other context-transport lemmas below are stated
    in the same refinement form. *)
Lemma glu_nat_resp_ctxsub : forall Γ M a Δ,
    glu_nat Γ M a ->
    Δ ⊆ Γ ->
    glu_nat Δ M a.
Proof.
  induction 1; intros.
  - mauto 4.
  - assert (Δ ⊢ M ≈ succ M' : ℕ) by mauto 3.
    econstructor; [ eassumption | mauto 2 ].
  - econstructor; trivial.
    intros; mauto 4.
Qed.

Hint Resolve glu_nat_resp_ctxsub : mctt.

Lemma glu_nat_resp_exp_eq : forall Γ M a,
    glu_nat Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : ℕ ->
    glu_nat Γ M' a.
Proof.
  induction 1; intros; mauto 4.
  econstructor; trivial.
  intros.
  transitivity M[φ]ʷ; mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_exp_eq : mctt.

Add Parametric Morphism Γ : (glu_nat Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ ℕ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; mauto using glu_nat_resp_exp_eq.
Qed.

Lemma glu_nat_readback : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ M',
      Δ ⊢k φ : Γ ->
      Rnf ⇓ ℕᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : ℕ.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - rewrite <- (exp_wk_zero φ); mauto 4.
  - assert (Δ ⊢ M'[φ]ʷ ≈ M0 : ℕ) by mauto 4.
    assert (Δ ⊢ M[φ]ʷ ≈ (succ M')[φ]ʷ : ℕ) as H' by mauto 4.
    rewrite exp_wk_succ in H'.
    etransitivity; [ eassumption | mauto 3 ].
  - mauto 4.
Qed.

(** The parameters of an inductive type, glued by their readback. *)
Lemma glu_params_top_resp_ctxsub : forall D Γ Ps as' Δ,
    glu_params_top D Γ Ps as' -> Δ ⊆ Γ -> glu_params_top D Δ Ps as'.
Proof.
  intros * (Hl & Ht & Hr) Hsub; split; [ exact Hl | split ].
  - intros * HP HA; eapply ctxsub_exp; [ exact (ctx_sub_escape _ _ _ _ Hsub) | eapply Ht; eassumption ].
  - intros * Hφ Hrb; eapply Hr; [ eapply kripke_ctxsub; eassumption | exact Hrb ].
Qed.

(** The same lemmas for [glu_lvl], which is the readback clause of a neutral at
    [Level]. *)
Lemma glu_lvl_escape : forall Γ M a n,
    Dom a ≈ a ∈ per_lvl ->
    glu_lvl n Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : Level@n.
Proof.
  intros * Hper H HΓ.
  assert (Γ ⊢k wk_id : Γ) by mauto 2.
  apply per_lvl_then_per_top in Hper; specialize (Hper (length Γ)) as [M' []].
  clear_dups.
  assert (Γ ⊢ M[wk_id]ʷ ≈ M' : Level@n) as HM by (eapply H; eassumption).
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve glu_lvl_escape : mctt.

(** The sort of a glued level moves up: the readback equation does, by
    subsumption between the types of levels. *)
Lemma glu_lvl_sort_le : forall Γ M a m n,
    m <= n ->
    glu_lvl m Γ M a ->
    glu_lvl n Γ M a.
Proof.
  intros * Hmn H Δ φ L Hφ Hr.
  assert (⊢ Δ) by (eapply kripke_dom; eassumption).
  destruct (H _ _ _ Hφ Hr) as [Heq Hws]; split.
  - eapply wf_exp_eq_subtyp'; [ exact Heq | apply wf_subtyp_level; assumption ].
  - destruct L; cbn in Hws |- *; try contradiction.
    destruct Hws; split; [ lia | eapply la_ws_mono; eassumption ].
Qed.

Lemma glu_lvl_resp_ctxsub : forall Γ M a n Δ,
    glu_lvl n Γ M a ->
    Δ ⊆ Γ ->
    glu_lvl n Δ M a.
Proof.
  intros * H ? Δ' φ L **; mauto 4.
Qed.

Hint Resolve glu_lvl_resp_ctxsub : mctt.

Lemma glu_lvl_resp_exp_eq : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : Level@n ->
    glu_lvl n Γ M' a.
Proof.
  intros * H * ? Δ φ L Hφ Hr.
  destruct (H _ _ _ Hφ Hr) as [Heq Hws]; split; [| exact Hws ].
  transitivity M[φ]ʷ; mauto 4.
Qed.

#[local]
Hint Resolve glu_lvl_resp_exp_eq : mctt.

(** ** Cumulativity of an Element of a Small Universe

    An element of a small universe is a type of that universe [Type⟨t⟩], and
    its type-level gluing is at the ambient large universe.  These two lemmas
    are where the gluing relies on cumulativity ([wf_subtyp_small_large]):
    they move the element's typing and its equations from [Type⟨t⟩] to every
    large universe. *)
Lemma suniv_elem_large : forall Γ M A t j k,
    Γ ⊢ M : A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    Γ ⊢ M : Typeω@k.
Proof.
  intros * HM HA.
  assert (Γ ⊢ Type⟨t⟩ : Typeω@j) by (gen_presups; eassumption).
  assert (exists n, Γ ⊢ t : Level@n) as [n' Ht] by (eapply wf_univ_lvl_inversion; eassumption).
  eapply wf_exp_subtyp'; [ eapply wf_conv'; eassumption | eapply wf_subtyp_small_large; mauto 3 ].
Qed.

Lemma suniv_elem_eq_large : forall Γ M M' A t j k,
    Γ ⊢ M ≈ M' : A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    Γ ⊢ M ≈ M' : Typeω@k.
Proof.
  intros * HM HA.
  assert (Γ ⊢ Type⟨t⟩ : Typeω@j) by (gen_presups; eassumption).
  assert (exists n, Γ ⊢ t : Level@n) as [n' Ht] by (eapply wf_univ_lvl_inversion; eassumption).
  eapply wf_exp_eq_subtyp';
    [ eapply wf_exp_eq_conv'; eassumption | eapply wf_subtyp_small_large; mauto 3 ].
Qed.

(** A glued small universe is the universe at a level term glued to the level
    value.  As an introduction lemma this is what every proof that moves such
    a type needs: the term is kept and the equation composed, and it is a hint
    so that the shared scripts of the gluing lemmas reach it. *)
Lemma suniv_glu_typ_pred_intro : forall l U Γ A t n,
    glu_lvl n Γ t l ->
    Γ ⊢ A ≈ Type⟨t⟩ : U ->
    suniv_glu_typ_pred l U Γ A.
Proof. intros; do 2 eexists; split; eassumption. Qed.

(** It is deliberately not a hint: its conclusion is an existential whose
    witness the search cannot guess, and as a hint it also fires on the goals
    of the other universe clauses, whose predicate is an evar. *)

Lemma glu_lvl_readback : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ M',
      Δ ⊢k φ : Γ ->
      Rnf ⇓ Levelᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : Level@n.
Proof.
  intros * H * Hφ Hr; exact (proj1 (H _ _ _ Hφ Hr)).
Qed.

(** The readback of a glued level is a canonical level of its sort. *)
Lemma glu_lvl_ws_readback : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ M',
      Δ ⊢k φ : Γ ->
      Rnf ⇓ Levelᵈ a in length Δ ↘ M' ->
      nf_lvl_ws n Δ M'.
Proof.
  intros * H * Hφ Hr; exact (proj2 (H _ _ _ Hφ Hr)).
Qed.

(** A literal level of a tier at most [n] is glued to its value: its readback
    is itself. *)
Lemma glu_lvl_lit : forall Γ o n,
    fst o <= n ->
    ⊢ Γ ->
    glu_lvl n Γ (𝕃ᵒ o) (dlvl_lit o).
Proof.
  intros * Ho HΓ Δ φ L Hφ Hr.
  assert (⊢ Δ) by (eapply kripke_dom; eassumption).
  assert (L = nf_lvl_of (lvl_lit o)) as -> by (eapply functional_read_nf; [ exact Hr | apply read_nf_dlvl_lit ]).
  cbn; split; [ apply wf_exp_eq_llit_cong; assumption | split; [ exact Ho | exact I ] ].
Qed.

(** The same lemmas for [glu_False], which is the neutral case of
    [glu_nat] at [⊥]. *)
Lemma glu_False_per_ne : forall Γ M a,
    glu_False Γ M a ->
    Dom a ≈ a ∈ per_ne.
Proof.
  destruct 1; mauto.
Qed.

#[local]
Hint Resolve glu_False_per_ne : mctt.

Lemma glu_False_escape : forall Γ M a,
    glu_False Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : ⊥.
Proof.
  destruct 1; intros.
  assert (Γ ⊢k wk_id : Γ) by mauto 2.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert (Γ ⊢ M[wk_id]ʷ ≈ M' : ⊥) as HM by mauto.
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve glu_False_escape : mctt.

Lemma glu_False_resp_ctxsub : forall Γ M a Δ,
    glu_False Γ M a ->
    Δ ⊆ Γ ->
    glu_False Δ M a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros; mauto 4.
Qed.

Hint Resolve glu_False_resp_ctxsub : mctt.

Lemma glu_False_resp_exp_eq : forall Γ M a,
    glu_False Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : ⊥ ->
    glu_False Γ M' a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros.
  transitivity M[φ]ʷ; mauto.
Qed.

#[local]
Hint Resolve glu_False_resp_exp_eq : mctt.

Lemma glu_False_readback : forall Γ M a,
    glu_False Γ M a ->
    forall Δ φ M',
      Δ ⊢k φ : Γ ->
      Rnf ⇓ ⊥ᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : ⊥.
Proof.
  destruct 1; intros; progressive_inversion; gen_presups.
  mauto 4.
Qed.

(** ** The Elements of an Inductive Type *)

Lemma nonrec_prefix_pre : forall tr gs vs gs1 g gs2,
    tele_full tr (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs) -> List.length vs = List.length gs ->
    gs = gs1 ++ g :: gs2 ->
    tele_pre tr (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 (List.firstn (List.length gs1) vs))
      (nonrec_vals gs1 (List.firstn (List.length gs1) vs)).
Proof.
  intros * H Hl Heq.
  assert (Hnv : List.firstn (List.length (cargs_nonrec gs1)) (nonrec_vals gs vs) = nonrec_vals gs1 (List.firstn (List.length gs1) vs)).
  { rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
    rewrite Heq at 1.
    rewrite nonrec_vals_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
    rewrite firstn_app_exact by (apply length_nonrec_vals; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
    reflexivity. }
  rewrite <- Hnv; apply tele_pre_of_full with (T := cargs_nonrec gs); [ exact H |].
  subst; rewrite cargs_nonrec_app, List.length_app; lia.
Qed.

Lemma nonrec_firstn : forall gs gs1 g gs2 vs, gs = gs1 ++ g :: gs2 -> List.length vs = List.length gs ->
    List.firstn (List.length (cargs_nonrec gs1)) (nonrec_vals gs vs) = nonrec_vals gs1 (List.firstn (List.length gs1) vs).
Proof.
  intros * Heq Hl.
  rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
  rewrite Heq at 1.
  rewrite nonrec_vals_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite firstn_app_exact by (apply length_nonrec_vals; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  reflexivity.
Qed.

Lemma nonrec_nth_arg : forall gs gs1 A gs2 vs v, gs = gs1 ++ ca_arg A :: gs2 -> List.length vs = List.length gs ->
    List.nth_error vs (List.length gs1) = Some v ->
    List.nth_error (nonrec_vals gs vs) (List.length (cargs_nonrec gs1)) = Some v.
Proof.
  intros * Heq Hl Hv; subst gs.
  rewrite <- (List.firstn_skipn (List.length gs1) vs) in Hv |- *.
  assert (Hl1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
    by (rewrite List.length_firstn; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite nonrec_vals_app by exact Hl1.
  rewrite List.nth_error_app2 in Hv by lia; rewrite Hl1 in Hv.
  replace (List.length gs1 - List.length gs1) with 0 in Hv by lia.
  rewrite List.nth_error_app2 by (rewrite length_nonrec_vals by exact Hl1; lia).
  rewrite length_nonrec_vals by exact Hl1.
  replace (List.length (cargs_nonrec gs1) - List.length (cargs_nonrec gs1)) with 0 by lia.
  destruct (List.skipn (List.length gs1) vs) as [| v0 ws]; cbn in Hv |- *; [ discriminate | exact Hv ].
Qed.

Lemma ind_case_N_helper : forall D ups (X : nat -> list domain -> Prop), tele_ass (ind_params D) ->
    (forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
    (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b -> X k vs) ->
    forall k vs, k < ind_nn D -> tele_pre (ind_nr D ups) k vs vs -> X k vs.
Proof.
  intros * Hass Hev HX k vs Hk Hp.
  destruct (nparams_lt_ass D k Hass ltac:(rewrite List.length_rev, length_nparams; exact Hk)) as [A HA].
  destruct (Hev _ _ _ HA Hp) as [b Hb]; exact (HX _ _ _ _ HA Hp Hb).
Qed.

Lemma ind_case_A_helper : forall D ups (X : list domain -> String.string -> nat -> list domain -> Prop),
    (forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
    (forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b -> X ms c k vs) ->
    forall ms c gs k vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
      k < List.length (cargs_nonrec gs) -> tele_pre (ind_ar D ups ms c) k vs vs -> X ms c k vs.
Proof.
  intros * Hev HX * Hms Hcon Hk Hp.
  destruct (nth_error_lt_some' (cargs_nonrec gs) k Hk) as [A HA].
  destruct (Hev _ _ _ _ _ _ Hms Hcon HA Hp) as [b Hb]; exact (HX _ _ _ _ _ _ _ Hms Hcon HA Hp Hb).
Qed.

Lemma map_wk_wk : forall (Ps : list exp) φ ψ,
    List.map (fun P => P[ψ]ʷ) (List.map (fun P => P[φ]ʷ) Ps) = List.map (fun P => P[φ ⊙ ψ]ʷ) Ps.
Proof. intros; rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_wk. Qed.

(** The readback of the parameters of related inductive types agrees. *)
Lemma glu_params_top_resp_per_top : forall p D as1 as2 Γ Ps, ind_lookup gc_deps gc_stack p = Some D ->
    Dom d_ind p as1 ≈ d_ind p as2 ∈ per_top_typ -> glu_params_top D Γ Ps as1 -> glu_params_top D Γ Ps as2.
Proof.
  intros * Hl Ht (L & Ht' & Hr); split; [ exact L | split; [ exact Ht' |] ].
  intros Δ φ Ms Hφ HR.
  destruct (Ht (length Δ)) as (C & HC1 & HC2).
  inversion HC2; subst; inversion HC1; subst.
  repeat match goal with H : ind_lookup _ _ p = Some ?D1 |- _ =>
    assert_fails (unify D1 D); rewrite Hl in H; injection H as <- end.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack)))))) as Fps.
  match goal with H : Rps as2 at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?P0 |- _ => assert_fails (unify P0 Ms); rewrite (Fps _ _ _ _ _ HR _ H) end.
  apply Hr; assumption.
Qed.

Lemma rps_ind_resp_per_top : forall p D as1 as2 s Ms, ind_lookup gc_deps gc_stack p = Some D ->
    Dom d_ind p as1 ≈ d_ind p as2 ∈ per_top_typ ->
    Rps as2 at List.rev (ind_params D) in gc_deps ⍮ gc_stack ⍮ nil ⍮ s ↘ Ms ->
    Rps as1 at List.rev (ind_params D) in gc_deps ⍮ gc_stack ⍮ nil ⍮ s ↘ Ms.
Proof.
  intros * Hl Ht HR.
  destruct (Ht s) as (C & HC1 & HC2).
  inversion HC2; subst; inversion HC1; subst.
  repeat match goal with H : ind_lookup _ _ p = Some ?D1 |- _ =>
    assert_fails (unify D1 D); rewrite Hl in H; injection H as <- end.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack)))))) as Fps.
  match goal with H : Rps as2 at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?P0 |- _ => assert_fails (unify P0 Ms); rewrite (Fps _ _ _ _ _ HR _ H) end.
  assumption.
Qed.

(** The components of an inductive type at a related representative of the
    uniform parameters, and at gluings that contain the given ones. *)
Lemma ind_glu_comps_move : forall p D ups ups' NP NEl AP AEl Γ Us,
    ind_fam_agree D (ind_nr D ups) (ind_nr D ups') (ind_ar D ups) (ind_ar D ups') ->
    ind_glu_comps p D ups NP NEl AP AEl Γ Us -> ind_glu_comps p D ups' NP NEl AP AEl Γ Us.
Proof.
  intros * [Hfn Hfa] [HCN HCA].
  assert (Hfn' : forall k vs vs1 vs2, k < List.length (List.rev (ind_nparams D)) -> tele_pre (ind_nr D ups') k vs vs1 ->
            tele_pre (ind_nr D ups) k vs vs2 -> (ind_nr D ups' k vs <~> ind_nr D ups k vs))
    by (intros; symmetry; eapply Hfn; eassumption).
  assert (Hfa' : forall ms ms1 ms2 c gs k vs vs1 vs2, tele_full (ind_nr D ups') (List.rev (ind_nparams D)) ms ms1 ->
            tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms2 ->
            ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) ->
            tele_pre (ind_ar D ups' ms c) k vs vs1 -> tele_pre (ind_ar D ups ms c) k vs vs2 ->
            (ind_ar D ups' ms c k vs <~> ind_ar D ups ms c k vs)) by (intros; symmetry; eapply Hfa; eassumption).
  split.
  - intros * Hl Hk HT Hpre Hp.
    eapply HCN; [ exact Hl | exact Hk | exact HT | exact Hpre |].
    eapply (tele_pre_nr_change' p D ups _ _ _ _ Hfn Hfa);
      [ rewrite List.length_rev, length_nparams; lia | exact Hp ].
  - intros * Hc Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (tele_full_nr_change p D ups _ _ _ _ Hfn' Hfa' _ _ Hns) as Hns'.
    eapply HCA; [ exact Hc | exact Heq | exact Hnp | exact Hns' | exact Hvl | exact HT | exact Hpre |].
    eapply (tele_pre_ar_change' p D ups _ _ _ _ Hfn Hfa); [ exact Hns' | exact Hns | exact Hc | | exact Hp ].
    rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia.
Qed.

Lemma ind_typ_at_resp_per_top : forall p D ups ns ups' ns' NP NEl AP AEl U Γ A Ps, ind_lookup gc_deps gc_stack p = Some D ->
    Dom d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_top_typ ->
    ind_fam_agree D (ind_nr D ups) (ind_nr D ups') (ind_ar D ups) (ind_ar D ups') ->
    ind_typ_at p D ups ns NP NEl AP AEl U Γ A Ps -> ind_typ_at p D ups' ns' NP NEl AP AEl U Γ A Ps.
Proof.
  intros * Hl Ht Hfa (HA & Hk); split; [ exact HA |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & Hs & Hc); split;
    [ eapply glu_params_top_resp_per_top; eassumption | split; [ exact Hs | intros Us HUs; eapply ind_glu_comps_move; eauto ] ].
Qed.


Lemma ind_args_rel_rec : forall p D ups nr ar ρ gs vs vs', ind_args_rel p D ups nr ar ρ gs vs vs' ->
    forall gs1 Pr gs2 v v', gs = gs1 ++ ca_rec Pr :: gs2 ->
      List.nth_error vs (List.length gs1) = Some v -> List.nth_error vs' (List.length gs1) = Some v' ->
      exists bsr, eval_exps gc_deps gc_stack Pr (env_args ρ (nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr /\
        ind_rel p D ups nr ar bsr v v'.
Proof.
  induction 1 as [ρ | ρ v0 gs vs vs' A v0' Hia IH | ρ Ps bs v0 v0' gs vs vs' Hb Hr Hia IH];
    intros [| g gs1] Pr gs2 v v' Heq Hv Hv'; cbn in *; try discriminate.
  - injection Heq as <- Heq; exact (IH _ _ _ _ _ Heq Hv Hv').
  - injection Heq as -> ->; injection Hv as <-; injection Hv' as <-.
    exists bs; split; assumption.
  - injection Heq as <- Heq; exact (IH _ _ _ _ _ Heq Hv Hv').
Qed.

Section GluIndProps.
  Variable (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> list domain -> glu_exp_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred).
  Hypothesis (Hass : tele_ass (ind_params D)) (Hcp : ind_canon_props D ups).
  Let T := List.rev (ind_nparams D).
  Let nr := ind_nr D ups.
  Let ar := ind_ar D ups.

  Lemma glu_nparams_mono : forall NEl' : nat -> list domain -> glu_exp_pred,
      (forall k vs, k < ind_nn D -> tele_pre nr k vs vs ->
         forall Γ A M m, NEl k vs Γ A M m -> NEl' k vs Γ A M m) ->
      forall Γ Us Ns ns, tele_full nr T ns ns -> glu_nparams D NEl Γ Us Ns ns -> glu_nparams D NEl' Γ Us Ns ns.
  Proof.
    intros NEl' HN * Hns (L1 & L2 & H); split; [ exact L1 | split; [ exact L2 |] ].
    intros k N A n HN0 HA HnK.
    assert (Hk : k < ind_nn D) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    eapply HN; [ exact Hk | | exact (H _ _ _ _ HN0 HA HnK) ].
    apply tele_pre_of_full with (T := T); [ exact Hns | unfold T; rewrite List.length_rev, length_nparams; lia ].
  Qed.

  Lemma glu_ind_resp_exp_eq : forall Γ Ps M m, glu_ind p D ups NEl AEl Γ Ps M m ->
      forall M', Γ ⊢ M ≈ M' : apps (a_ind p) Ps -> glu_ind p D ups NEl AEl Γ Ps M' m.
  Proof.
    intros * H; destruct H as [? ? ? ? ? ? ? ? Hcon HPl Hbl Hvl HAl HM | ? ? ? ? ? Hm Hr]; intros M' HMM.
    - eapply glu_ind_con; try eassumption.
      etransitivity; [ symmetry; exact HMM | exact HM ].
    - eapply glu_ind_neut; [ exact Hm |].
      intros * Hφ Hrb.
      etransitivity; [| eapply Hr; eassumption ].
      symmetry; mauto 4.
  Qed.

  (** [glu_ind] moves along a related representative [ups'] of the uniform
      parameters, and along gluings of the non-uniform parameters and of
      the non-recursive arguments that contain the given ones. *)
  Lemma glu_ind_move : forall ups' (NEl' : nat -> list domain -> glu_exp_pred)
      (AEl' : list domain -> String.string -> nat -> list domain -> glu_exp_pred),
      ind_lookup gc_deps gc_stack p = Some D ->
      ind_fam_agree D nr (ind_nr D ups') ar (ind_ar D ups') ->
      ind_adm D ups nr ar ups' ->
      (forall bs bs', tele_full nr T bs bs' -> Dom d_ind p (ups ++ bs) ≈ d_ind p (ups' ++ bs') ∈ per_top_typ) ->
      (forall k vs, k < ind_nn D -> tele_pre nr k vs vs ->
         forall Γ A M m, NEl k vs Γ A M m -> NEl' k vs Γ A M m) ->
      (forall ms c gs k vs, tele_full nr T ms ms -> ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) ->
         tele_pre (ar ms c) k vs vs -> forall Γ A M m, AEl ms c k vs Γ A M m -> AEl' ms c k vs Γ A M m) ->
      forall Γ Ps M m, glu_ind p D ups NEl AEl Γ Ps M m -> glu_ind p D ups' NEl' AEl' Γ Ps M m.
  Proof.
    intros ups' NEl' AEl' Hl [Hfn Hfa] Hadm Hrbt HN HA.
    pose proof (tele_full_nr_change p D ups _ _ _ _ Hfn Hfa) as F1.
    assert (Hfn' : forall k vs vs1 vs2, k < List.length T -> tele_pre (ind_nr D ups') k vs vs1 -> tele_pre nr k vs vs2 ->
              (ind_nr D ups' k vs <~> nr k vs)) by (intros; symmetry; eapply Hfn; eassumption).
    assert (Hfa' : forall ms ms1 ms2 c gs k vs vs1 vs2, tele_full (ind_nr D ups') T ms ms1 -> tele_full nr T ms ms2 ->
              ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) ->
              tele_pre (ind_ar D ups' ms c) k vs vs1 -> tele_pre (ar ms c) k vs vs2 ->
              (ind_ar D ups' ms c k vs <~> ar ms c k vs)) by (intros; symmetry; eapply Hfa; eassumption).
    pose proof (tele_full_nr_change p D ups _ _ _ _ Hfn' Hfa') as F2.
    destruct Hadm as (_ & _ & Hcl).
    induction 1 as [? ? ? ? ? ? ? ? Hcon HPl Hbl Hvl HAl HM Hb Hv Hnp HAs Harg Hrec Hrec' IH
                   | ? ? ? ? ? Hm Hr].
    - (** The arguments' values evaluated at [ups], for the ones at [ups']. *)
      assert (Hev : forall gs1 Pr gs2 bsr', gs = gs1 ++ ca_rec Pr :: gs2 ->
                 eval_exps gc_deps gc_stack Pr
                   (env_args nil (ups' ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr' ->
                 exists bsr, eval_exps gc_deps gc_stack Pr
                   (env_args nil (ups ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr /\
                   tele_full nr T bsr bsr').
      { intros * Heq Hbs'.
        destruct (Hcl _ _ _ _ _ _ _ _ _ Hb Hcon Heq (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq)) as (b0 & b1 & E0 & E1 & H01).
        pose proof (functional_eval_exps' _ _ _ _ E1 Hbs') as ->.
        exists b0; split; assumption. }
      eapply glu_ind_con; try eassumption.
      + exact (F1 _ _ Hb).
      + apply (tele_full_map _ (ar (List.skipn (ind_nu D) bs) c)); [| exact Hv ].
        intros k pa pb x y Hk Hp1 Hp2 Hr; apply (Hfa _ _ _ _ _ _ _ _ _ Hb (F1 _ _ Hb) Hcon Hk Hp1 Hp2); exact Hr.
      + eapply glu_nparams_mono; eassumption.
      + intros * Heq HN0 HA0 Hv0.
        eapply HA; [ exact Hb | exact Hcon | | eapply nonrec_prefix_pre; eassumption
                   | exact (Harg _ _ _ _ _ _ Heq HN0 HA0 Hv0) ].
        rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia.
      + intros * Heq HN0 HA0 Hv0 Hbs HQ.
        destruct (Hev _ _ _ _ Heq Hbs) as (bsr0 & E0 & H01).
        destruct (Hrec _ _ _ _ _ _ _ _ Heq HN0 HA0 Hv0 E0 HQ) as (HQl & Hbt & Hgn).
        split; [ exact HQl | split ].
        * exact (F1 _ _ (canon_tnr_refl_r' p D ups Hass Hcp _ _ H01)).
        * intros bsr' Hb'.
          pose proof (canon_tnr_trans p D ups Hass Hcp _ _ _ H01 (F2 _ _ Hb')) as H0'.
          pose proof (canon_tnr_refl_r' p D ups Hass Hcp _ _ H0') as H0''.
          destruct (Hgn _ H0') as [Hg1 Hg2]; split; [ eapply glu_nparams_mono; [ exact HN | exact H0'' | exact Hg1 ] |].
          intros Δ φ Hφ; eapply glu_params_top_resp_per_top; [ exact Hl | exact (Hrbt _ _ H0'') | exact (Hg2 Δ φ Hφ) ].
      + intros * Heq HN0 HA0 Hv0 Hbs HQ Δ φ Q' Hφ HQ'.
        destruct (Hev _ _ _ _ Heq Hbs) as (bsr0 & E0 & _).
        exact (IH _ _ _ _ _ _ _ _ Heq HN0 HA0 Hv0 E0 HQ Δ φ Q' Hφ HQ').
    - eapply glu_ind_neut; eassumption.
  Qed.

  Lemma glu_ind_mono : forall (NEl' : nat -> list domain -> glu_exp_pred)
      (AEl' : list domain -> String.string -> nat -> list domain -> glu_exp_pred),
      (forall k vs, k < ind_nn D -> tele_pre nr k vs vs ->
         forall Γ A M m, NEl k vs Γ A M m -> NEl' k vs Γ A M m) ->
      (forall ms c gs k vs, tele_full nr T ms ms -> ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) ->
         tele_pre (ar ms c) k vs vs -> forall Γ A M m, AEl ms c k vs Γ A M m -> AEl' ms c k vs Γ A M m) ->
      forall Γ Ps M m, glu_ind p D ups NEl AEl Γ Ps M m -> glu_ind p D ups NEl' AEl' Γ Ps M m.
  Proof.
    intros NEl' AEl' HN HA; induction 1 as [? ? ? ? ? ? ? ? Hcon HPl Hbl Hvl HAl HM Hb Hv Hnp HAs Harg Hrec Hrec' IH
                                 | ? ? ? ? ? Hm Hr].
    - eapply glu_ind_con; try eassumption.
      + eapply glu_nparams_mono; eassumption.
      + intros * Heq HN0 HA0 Hv0.
        eapply HA; [ exact Hb | exact Hcon | | eapply nonrec_prefix_pre; eassumption
                   | exact (Harg _ _ _ _ _ _ Heq HN0 HA0 Hv0) ].
        rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia.
      + intros * Heq HN0 HA0 Hv0 Hbs HQ.
        destruct (Hrec _ _ _ _ _ _ _ _ Heq HN0 HA0 Hv0 Hbs HQ) as (HQl & Hbt & Hgn).
        split; [ exact HQl | split; [ exact Hbt |] ].
        intros bsr' Hb'; destruct (Hgn _ Hb') as [Hg1 Hg2]; split; [| exact Hg2 ].
        eapply glu_nparams_mono; [ exact HN | exact (canon_tnr_refl_r' p D ups Hass Hcp _ _ Hb') | exact Hg1 ].
    - eapply glu_ind_neut; eassumption.
  Qed.
  Lemma glu_nparams_resp_per :
      (forall k vs vs', k < ind_nn D -> tele_pre nr k vs vs' ->
         forall Γ A N n n', NEl k vs Γ A N n -> nr k vs n n' -> NEl k vs' Γ A N n') ->
      forall Γ Us Ns ns ns', tele_full nr T ns ns' -> glu_nparams D NEl Γ Us Ns ns -> glu_nparams D NEl Γ Us Ns ns'.
  Proof.
    intros HNe * Hns (L1 & L2 & H).
    pose proof Hns as Hns'; rewrite tele_full_iff in Hns'; destruct Hns' as (Hl & Hl' & Hr).
    unfold T in Hl, Hl'; rewrite List.length_rev, length_nparams in Hl, Hl'.
    split; [ exact L1 | split; [ exact Hl' |] ].
    intros k N A n' HN0 HA Hn'.
    assert (Hk : k < ind_nn D) by (rewrite <- Hl'; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' ns k ltac:(lia)) as [n Hn].
    eapply HNe; [ exact Hk | | exact (H _ _ _ _ HN0 HA Hn) | exact (Hr _ _ _ Hn Hn') ].
    apply tele_pre_of_full with (T := T); [ exact Hns | unfold T; rewrite List.length_rev, length_nparams; lia ].
  Qed.

  Lemma glu_ind_resp_per : ind_adm D ups nr ar ups ->
      (forall k vs vs', k < ind_nn D -> tele_pre nr k vs vs' ->
         forall Γ A N n n', NEl k vs Γ A N n -> nr k vs n n' -> NEl k vs' Γ A N n') ->
      (forall ms ms' c gs k vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) ->
         tele_pre (ar ms c) k vs vs' -> forall Γ A N n n', AEl ms c k vs Γ A N n -> ar ms c k vs n n' -> AEl ms' c k vs' Γ A N n') ->
      forall Γ Ps M m, glu_ind p D ups NEl AEl Γ Ps M m ->
      forall ns m', ind_rel p D ups nr ar ns m m' -> glu_ind p D ups NEl AEl Γ Ps M m'.
  Proof.
    intros Hadm HNe HAe.
    destruct Hcp as (HnP & HnI & HaP & HaI).
    induction 1 as [? ? ? ? ? ? ? ? Hcon HPl Hbl Hvl HAl HM Hb Hv Hnp HAs Harg Hrec Hrec' IH
                   | ? ? ? ? ? Hm Hr]; intros ns m' Hrel.
    2:{ (** A neutral: related neutrals read back equally. *)
        inversion Hrel; subst.
        match goal with Hb : per_bot m ?m0 |- _ => rename m0 into e'; rename Hb into Hbe end.
        eapply glu_ind_neut; [ etransitivity; [ symmetry |]; exact Hbe |].
        intros Δ φ M' Hφ Hrb.
        destruct (Hbe (length Δ)) as (M0 & HM0 & HM0').
        pose proof (functional_read_ne _ _ _ _ Hrb HM0') as ->.
        exact (Hr _ _ _ Hφ HM0). }
    (** A constructor: the related one has the same arguments' gluings, at
        the related values. *)
    pose proof (tnr_sym p D ups nr ar Hass HnP HnI HaP HaI) as Sn.
    pose proof (tnr_trans p D ups nr ar Hass HnP HnI HaP HaI) as Tn.
    pose proof (tnr_refl_r p D ups nr ar Hass HnP HnI HaP HaI) as RnR.
    pose proof (tar_inst p D ups nr ar Hass HnP HnI HaP HaI) as Ia.
    pose proof (tar_trans p D ups nr ar Hass HnP HnI HaP HaI) as Ta.
    pose proof (tar_sym p D ups nr ar Hass HnP HnI HaP HaI) as Sa.
    pose proof (tarp_inst p D ups nr ar Hass HnP HnI HaP HaI) as Iap.
    pose proof (tar_pre_refl_l p D ups nr ar Hass HnP HnI HaP HaI) as RaL.
    destruct (ind_rel_con_inv p D ups nr ar Hass HnP HnI HaP HaI _ _ _ _ _ Hrel Hbl)
      as (gs0 & bs' & vs' & -> & Hns & Hc0 & Hbl' & Hs & Hs' & Ha & Hia).
    rewrite Hcon in Hc0; injection Hc0 as <-.
    assert (Hmm' : tele_full nr T (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs'))
      by exact (Tn _ _ _ (Sn _ _ Hs) Hs').
    assert (Hvl' : length vs' = length gs)
      by (clear - Hia Hvl; revert Hvl; induction Hia; cbn; intros;
          [ reflexivity | f_equal; apply IHHia; lia | f_equal; apply IHHia; lia ]).
    refine (glu_ind_con p D ups NEl AEl Hcon HPl Hbl' Hvl' HAl HM _ _ _ HAs _ _ _).
    clear Hrel Hb Hv.
    - exact (RnR _ _ Hmm').
    - exact (Ia _ _ _ _ _ _ Hs' Hcon (Ta _ _ _ Hns Hcon _ _ _ (Sa _ _ _ Hns Hcon _ _ Ha) Ha)).
    - exact (glu_nparams_resp_per HNe _ _ _ _ _ Hmm' Hnp).
    - intros gs1 A0 gs2 N A v' Heq HN0 HA0 Hv0'.
      assert (Hlt : length gs1 < length vs) by (rewrite Hvl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' vs (length gs1) Hlt) as [v Hv0].
      assert (HK : length (cargs_nonrec gs1) < length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
      assert (HK' : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by lia.
      assert (HA0' : List.nth_error (cargs_nonrec gs) (length (cargs_nonrec gs1)) = Some A0)
        by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2 by lia;
            replace (length (cargs_nonrec gs1) - length (cargs_nonrec gs1)) with 0 by lia; reflexivity).
      pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq Hvl Hv0) as Hn1.
      pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq Hvl' Hv0') as Hn2.
      pose proof Ha as Ha'; rewrite tele_full_iff in Ha'; destruct Ha' as (_ & _ & Har).
      pose proof (Har _ _ _ Hn1 Hn2) as Hvv.
      rewrite (nonrec_firstn _ _ _ _ _ Heq Hvl) in Hvv.
      pose proof (tele_pre_of_full _ _ _ _ (length (cargs_nonrec gs1)) Ha HK') as Hpre.
      rewrite (nonrec_firstn _ _ _ _ _ Heq Hvl), (nonrec_firstn _ _ _ _ _ Heq Hvl') in Hpre.
      pose proof (Iap _ _ _ _ _ _ _ Hs Hcon HK' Hpre) as Hpre'.
      pose proof (RaL _ _ _ Hns Hcon _ _ _ HK' Hpre) as Hpd.
      pose proof (HaI _ _ _ _ _ _ _ _ Hs Hcon HA0' Hpd) as Hiff.
      eapply HAe; [ exact Hmm' | exact Hcon | exact HK | exact Hpre'
                  | exact (Harg _ _ _ _ _ _ Heq HN0 HA0 Hv0) | apply Hiff; exact Hvv ].
    - intros gs1 Pr gs2 N A v' bsr' Q Heq HN0 HA0 Hv0' Hbs' HQ.
      assert (Hlt : length gs1 < length vs) by (rewrite Hvl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' vs (length gs1) Hlt) as [v Hv0].
      assert (HK' : length (cargs_nonrec gs1) <= length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
      pose proof (tele_pre_of_full _ _ _ _ (length (cargs_nonrec gs1)) Ha HK') as Hpre.
      rewrite (nonrec_firstn _ _ _ _ _ Heq Hvl), (nonrec_firstn _ _ _ _ _ Heq Hvl') in Hpre.
      pose proof (Iap _ _ _ _ _ _ _ Hs Hcon HK' Hpre) as Hpre1.
      destruct Hadm as (_ & _ & Hcl).
      destruct (Hcl _ _ _ _ _ _ _ _ _ Hmm' Hcon Heq Hpre1) as (b0 & b1 & E0 & E1 & H01).
      pose proof (functional_eval_exps' _ _ _ _ E1 Hbs') as ->.
      destruct (Hrec _ _ _ _ _ _ _ _ Heq HN0 HA0 Hv0 E0 HQ) as (HQl & _ & Hgn).
      split; [ exact HQl | split; [ exact (RnR _ _ H01) |] ].
      intros bsr'' Hb''; exact (Hgn _ (Tn _ _ _ H01 Hb'')).
    - intros gs1 Pr gs2 N A v' bsr' Q Heq HN0 HA0 Hv0' Hbs' HQ Δ φ Q' Hφ HQ'.
      assert (Hlt : length gs1 < length vs) by (rewrite Hvl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' vs (length gs1) Hlt) as [v Hv0].
      assert (HK' : length (cargs_nonrec gs1) <= length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
      pose proof (tele_pre_of_full _ _ _ _ (length (cargs_nonrec gs1)) Ha HK') as Hpre.
      rewrite (nonrec_firstn _ _ _ _ _ Heq Hvl), (nonrec_firstn _ _ _ _ _ Heq Hvl') in Hpre.
      pose proof (Iap _ _ _ _ _ _ _ Hs Hcon HK' Hpre) as Hpre1.
      destruct Hadm as (_ & _ & Hcl).
      destruct (Hcl _ _ _ _ _ _ _ _ _ Hmm' Hcon Heq Hpre1) as (b0 & b1 & E0 & E1 & H01).
      destruct (ind_args_rel_rec _ _ _ _ _ _ _ _ _ Hia _ _ _ _ _ Heq Hv0 Hv0') as (bt & _ & Hvv).
      exact (IH _ _ _ _ _ _ _ _ Heq HN0 HA0 Hv0 E0 HQ Δ φ Q' Hφ HQ' _ _ Hvv).
  Qed.

End GluIndProps.

Lemma ind_glu_comps_mono : forall p D ups NP NEl AP AEl NP' NEl' AP' AEl' Γ Us,
    (forall k vs, k < ind_nn D -> tele_pre (ind_nr D ups) k vs vs ->
       (forall Γ T, NP k vs Γ T -> NP' k vs Γ T) /\ (forall Γ T N n, NEl' k vs Γ T N n -> NEl k vs Γ T N n)) ->
    (forall ms c gs k vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       k < List.length (cargs_nonrec gs) -> tele_pre (ind_ar D ups ms c) k vs vs ->
       (forall Γ T, AP ms c k vs Γ T -> AP' ms c k vs Γ T) /\ (forall Γ T N n, AEl' ms c k vs Γ T N n -> AEl ms c k vs Γ T N n)) ->
    ind_glu_comps p D ups NP NEl AP AEl Γ Us -> ind_glu_comps p D ups NP' NEl' AP' AEl' Γ Us.
Proof.
  intros * HN HA [HCN HCA]; split.
  - intros k Ns ns T Hl Hk HT Hpre Hp.
    apply (proj1 (HN k ns Hk Hp)).
    apply (HCN k Ns ns T Hl Hk HT); [| exact Hp ].
    intros j N T' n Hj HN0 HT' Hn.
    assert (Hpj : tele_pre (ind_nr D ups) j (List.firstn j ns) (List.firstn j ns)) by exact (tele_pre_of_pre _ _ _ _ j Hp ltac:(lia)).
    apply (proj2 (HN j (List.firstn j ns) ltac:(lia) Hpj)).
    apply Hpre; assumption.
  - intros c gs gs1 A0 gs2 Ns ns As vs T Hc Heq Hnp Hns Hvl HT Hpre Hp.
    assert (HK : List.length (cargs_nonrec gs1) < List.length (cargs_nonrec gs))
      by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
    apply (proj1 (HA _ _ _ _ _ Hns Hc HK Hp)).
    eapply HCA; [ exact Hc | exact Heq | | exact Hns | exact Hvl | exact HT | | exact Hp ].
    + eapply (glu_nparams_mono D ups NEl'); [| exact Hns | exact Hnp ].
      intros k vs0 Hk Hp0 *; apply (proj2 (HN k vs0 Hk Hp0)).
    + intros hs1 B hs2 N T' v Heq1 HN0 HT' Hv.
      assert (HK1 : List.length (cargs_nonrec hs1) < List.length (cargs_nonrec gs))
        by (rewrite Heq, Heq1, !cargs_nonrec_app, !List.length_app; cbn; lia).
      assert (Hpre1 : tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec hs1))
                        (nonrec_vals hs1 (List.firstn (List.length hs1) vs)) (nonrec_vals hs1 (List.firstn (List.length hs1) vs))).
      { pose proof (tele_pre_of_pre _ _ _ _ (List.length (cargs_nonrec hs1)) Hp
                      ltac:(rewrite Heq1, cargs_nonrec_app, List.length_app; cbn; lia)) as Hq.
        rewrite (nonrec_firstn _ _ _ _ _ Heq1 Hvl) in Hq; exact Hq. }
      apply (proj2 (HA _ _ _ _ _ Hns Hc HK1 Hpre1)).
      eapply Hpre; eassumption.
Qed.

Lemma ind_typ_at_mono : forall p D ups ns NP NEl AP AEl NP' NEl' AP' AEl' U Γ A Ps,
    (forall k vs, k < ind_nn D -> tele_pre (ind_nr D ups) k vs vs ->
       (forall Γ T, NP k vs Γ T -> NP' k vs Γ T) /\ (forall Γ T N n, NEl' k vs Γ T N n -> NEl k vs Γ T N n)) ->
    (forall ms c gs k vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c = Some gs ->
       k < List.length (cargs_nonrec gs) -> tele_pre (ind_ar D ups ms c) k vs vs ->
       (forall Γ T, AP ms c k vs Γ T -> AP' ms c k vs Γ T) /\ (forall Γ T N n, AEl' ms c k vs Γ T N n -> AEl ms c k vs Γ T N n)) ->
    ind_typ_at p D ups ns NP NEl AP AEl U Γ A Ps -> ind_typ_at p D ups ns NP' NEl' AP' AEl' U Γ A Ps.
Proof.
  intros * HN HA (HA0 & Hk); split; [ exact HA0 |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & Hs & Hc).
  split; [ exact Hpt | split; [ exact Hs | intros Us HUs; eapply ind_glu_comps_mono; eauto ] ].
Qed.

(** The type predicate of an inductive type, along an equation, a context
    refinement and a weakening. *)
Lemma ind_typ_at_resp_exp_eq : forall p D ups ns NP NEl AP AEl k Γ A A' Ps,
    ind_typ_at p D ups ns NP NEl AP AEl Typeω@k Γ A Ps -> Γ ⊢ A ≈ A' : Typeω@k ->
    ind_typ_at p D ups ns NP NEl AP AEl Typeω@k Γ A' Ps.
Proof.
  intros * (HA & Hk) HAA; split; [ etransitivity; [ symmetry; exact HAA | exact HA ] | exact Hk ].
Qed.

Lemma ind_typ_at_resp_ctxsub : forall p D ups ns NP NEl AP AEl k Γ A Ps Δ,
    ind_typ_at p D ups ns NP NEl AP AEl Typeω@k Γ A Ps -> Δ ⊆ Γ ->
    ind_typ_at p D ups ns NP NEl AP AEl Typeω@k Δ A Ps.
Proof.
  intros * (HA & Hk) Hs; split; [ eapply ctxsub_exp_eq; [ exact (ctx_sub_escape _ _ _ _ Hs) | exact HA ] |].
  intros Θ ψ Hψ; apply Hk; eapply kripke_ctxsub; eassumption.
Qed.

Lemma ind_typ_at_wk : forall p D ups ns NP NEl AP AEl k Γ A Ps Δ φ,
    ind_typ_at p D ups ns NP NEl AP AEl Typeω@k Γ A Ps -> Δ ⊢k φ : Γ ->
    ind_typ_at p D ups ns NP NEl AP AEl Typeω@k Δ A[φ]ʷ (List.map (fun P => P[φ]ʷ) Ps).
Proof.
  intros * (HA & Hk) Hφ; split; [ rewrite <- wk_apps_ind; mauto 3 |].
  intros Θ ψ Hψ; rewrite !map_wk_wk; apply Hk; eapply kripke_compose; eassumption.
Qed.

(** The type at the parameters of a type predicate is the one at equal
    ones. *)
Lemma ind_typ_at_params_conv : forall p D ups ns NP NEl AP AEl k Γ A Ps Δ φ Ps',
    ind_lookup gc_deps gc_stack p = Some D ->
    ind_typ_at p D ups ns NP NEl AP AEl Typeω@k Γ A Ps -> Δ ⊢k φ : Γ ->
    exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Ps) Ps' ->
    Δ ⊢ apps (a_ind p) (List.map (fun P => P[φ]ʷ) Ps) ≈ apps (a_ind p) Ps' : Typeω@k.
Proof.
  intros * Hl (_ & Hk) Hφ [HlP HPP].
  destruct (Hk _ _ Hφ) as ((HPl & _) & Hs & _).
  assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
  eapply wf_exp_eq_subtyp'; [| exact Hs ].
  eapply wf_exp_eq_ind_apps; [ exact Hl | exact HΔ | exact HPl | lia | exact HPP ].
Qed.

Lemma ind_glu_typ_pred_resp_exp_eq : forall p D ups ns NP NEl AP AEl k Γ A A',
    ind_glu_typ_pred p D ups ns NP NEl AP AEl Typeω@k Γ A -> Γ ⊢ A ≈ A' : Typeω@k ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl Typeω@k Γ A'.
Proof. intros * (Ps & HPs) HAA; exists Ps; eapply ind_typ_at_resp_exp_eq; eassumption. Qed.

Lemma ind_glu_typ_pred_resp_ctxsub : forall p D ups ns NP NEl AP AEl k Γ A Δ,
    ind_glu_typ_pred p D ups ns NP NEl AP AEl Typeω@k Γ A -> Δ ⊆ Γ ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl Typeω@k Δ A.
Proof. intros * (Ps & HPs) Hs; exists Ps; eapply ind_typ_at_resp_ctxsub; eassumption. Qed.

Lemma ind_glu_typ_pred_wk : forall p D ups ns NP NEl AP AEl k Γ A Δ φ,
    ind_glu_typ_pred p D ups ns NP NEl AP AEl Typeω@k Γ A -> Δ ⊢k φ : Γ ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl Typeω@k Δ A[φ]ʷ.
Proof. intros * (Ps & HPs) Hφ; eexists; eapply ind_typ_at_wk; eassumption. Qed.

Lemma ind_glu_exp_pred_resp_typ_exp_eq : forall p D ups ns NP NEl AP AEl R k Γ A A' M m,
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Γ A M m -> Γ ⊢ A ≈ A' : Typeω@k ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Γ A' M m.
Proof.
  intros * (HM & Hm & Ps & HPs & Hk) HAA.
  split; [ eapply wf_conv'; [ exact HM | exact HAA ] | split; [ exact Hm |] ].
  exists Ps; split; [ eapply ind_typ_at_resp_exp_eq; eassumption | exact Hk ].
Qed.

Lemma ind_glu_exp_pred_resp_ctxsub : forall p D ups ns NP NEl AP AEl R k Γ A M m Δ,
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Γ A M m -> Δ ⊆ Γ ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Δ A M m.
Proof.
  intros * (HM & Hm & Ps & HPs & Hk) Hs.
  split; [ eapply ctxsub_exp; [ exact (ctx_sub_escape _ _ _ _ Hs) | exact HM ] | split; [ exact Hm |] ].
  exists Ps; split; [ eapply ind_typ_at_resp_ctxsub; eassumption |].
  intros Θ ψ Ps' Hψ HPs'; apply Hk; [ eapply kripke_ctxsub; eassumption | exact HPs' ].
Qed.

Lemma ind_glu_exp_pred_wk : forall p D ups ns NP NEl AP AEl R k Γ A M m Δ φ,
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Γ A M m -> Δ ⊢k φ : Γ ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Δ A[φ]ʷ M[φ]ʷ m.
Proof.
  intros * (HM & Hm & Ps & HPs & Hk) Hφ.
  split; [ mauto 3 | split; [ exact Hm |] ].
  exists (List.map (fun P => P[φ]ʷ) Ps); split; [ eapply ind_typ_at_wk; eassumption |].
  intros Θ ψ Ps' Hψ HPs'; rewrite map_wk_wk in HPs'; rewrite exp_wk_wk; apply Hk; [ eapply kripke_compose; eassumption | exact HPs' ].
Qed.

Lemma ind_glu_exp_pred_resp_exp_eq : forall p D ups ns NP NEl AP AEl R k Γ A M M' m,
    ind_lookup gc_deps gc_stack p = Some D ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Γ A M m -> Γ ⊢ M ≈ M' : A ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl R Typeω@k Γ A M' m.
Proof.
  intros * Hl (HM & Hm & Ps & HPs & Hk) HMM.
  split; [ mauto 3 | split; [ exact Hm |] ].
  exists Ps; split; [ exact HPs |].
  intros Δ φ Ps' Hφ HPs'.
  eapply glu_ind_resp_exp_eq; [ exact (Hk Δ φ Ps' Hφ HPs') |].
  pose proof (ind_typ_at_params_conv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HPs Hφ HPs') as HPP.
  rewrite <- wk_apps_ind in HPP.
  destruct HPs as [HA _].
  assert (Γ ⊢ M ≈ M' : apps (a_ind p) Ps) by (eapply wf_exp_eq_conv'; eassumption).
  eapply wf_exp_eq_conv'; [| exact HPP ].
  mauto 3.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_lvl_escape glu_lvl_resp_ctxsub : mctt.
(** Unlike [glu_nat], [glu_lvl] has one constructor, so [split] breaks a goal
    [glu_lvl Γ M m] into its premises; the readback clause is then
    [glu_lvl_readback], and it is a hint so that the shared scripts reach it. *)
#[local]
Hint Resolve glu_lvl_resp_exp_eq glu_lvl_readback glu_lvl_ws_readback : mctt.
#[export]
Hint Resolve glu_False_escape glu_False_resp_ctxsub : mctt.
#[local]
Hint Resolve glu_False_per_ne glu_False_resp_exp_eq : mctt.
#[export]
Hint Resolve glu_nat_escape : mctt.
#[export]
Hint Resolve glu_nat_resp_ctxsub : mctt.
#[export] Existing Instance glu_ctx_env_sub_morphism_iff2_Proper.
#[local]
Hint Resolve glu_nat_per_nat glu_nat_resp_exp_eq : mctt.
#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  (** The elements of a type of levels are related levels of its sort; the
      lemmas about glued levels need the first half. *)
  repeat match goal with
    | H : per_lvl_at _ ?m ?m' |- _ =>
        lazymatch goal with
        | _ : per_lvl m m' |- _ => fail
        | _ => pose proof (per_lvl_at_lvl _ _ _ H)
        end
    end;
  gen_presups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The large level a glued type is a type of.  It is given as an explicit
    argument, with the equation [ulvl i = l], so that the lemma applies to a
    goal [Γ ⊢ A : Typeω@l] whose level is known before the index is. *)
Lemma glu_univ_elem_univ_lvl_gen : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A : Typeω@(ulvl i).
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; match goal with H : exists Ps, ind_typ_at _ _ _ _ _ _ _ _ _ _ _ Ps |- _ => destruct H as (Ps & HA & _) end;
      gen_presups; assumption. }
  all: simpl_glu_rel; trivial.
Qed.

Lemma glu_univ_elem_univ_lvl : forall i U P El a,
    Typeω@(ulvl i) = U ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A : U.
Proof. intros * <- **; eapply glu_univ_elem_univ_lvl_gen; eassumption. Qed.

Lemma glu_univ_elem_typ_resp_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A A',
      Γ ⊢ A ® P ->
      Γ ⊢ A ≈ A' : Typeω@(ulvl i) ->
      Γ ⊢ A' ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply (ind_glu_typ_pred_resp_exp_eq p D ups ns NP NEl AP AEl); eassumption. }
  all: simpl_glu_rel;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ destruct_conjs; do 2 eexists; split;
                [ eassumption | transitivity A; mauto 4 ] ];
    mauto 4.

  split; [trivial |].
  intros.
  transitivity A[φ]ʷ; mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (P Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> iff as glu_univ_elem_typ_morphism_iff1.
Proof.
  split; intros; eapply glu_univ_elem_typ_resp_exp_eq; mauto 2.
Qed.

Lemma glu_univ_elem_trm_resp_typ_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m A',
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A ≈ A' : Typeω@(ulvl i) ->
      Γ ⊢ M : A' ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply (ind_glu_exp_pred_resp_typ_exp_eq p D ups ns NP NEl AP AEl elem_rel); eassumption. }
  all:
    simpl_glu_rel; repeat split; intros;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ do 2 eexists; split; [ eassumption | transitivity A; mauto 4 ] ];
    mauto 3.
  all: try solve [ firstorder ].
  all: try solve [ do 2 eexists; split; eassumption ].
  all: try solve [ eapply wf_conv'; eassumption ].
  all: try solve [ transitivity A[φ]ʷ; mauto 4 ].
  (** The readback clauses of a neutral and of an element of a small universe
      move their type by conversion in the ambient universe. *)
  all: try solve [ assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) by mauto 3;
                   eapply wf_exp_eq_conv'; [ eauto | eassumption ] ].
  (** The [Π] case moves the type the same way. *)
  econstructor; mauto 3; eapply wf_conv'; eassumption.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (El Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> eq ==> eq ==> iff as glu_univ_elem_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_typ_resp_ctxsub : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A Δ,
      Γ ⊢ A ® P ->
      Δ ⊆ Γ ->
      Δ ⊢ A ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply (ind_glu_typ_pred_resp_ctxsub p D ups ns NP NEl AP AEl); eassumption. }
  all:
    simpl_glu_rel;
    (** A small universe: its level term and its equation both move to the
        refined context. *)
    try solve [ do 2 eexists; split;
                [ eapply glu_lvl_resp_ctxsub; eassumption | mauto 3 ] ];
    mauto 3.

  - assert (Δ ⊢ IT : Typeω@(ulvl i)) by mauto 3.
    assert (Δ ▹ IT ⊆ Γ ▹ IT) by (eapply ctx_sub_extend; mauto 3 using wf_subtyp_refl_univ).
    econstructor; mauto 3; intros; mauto 4.

  - split; [ mauto 3 | intros; mauto 4 ].
Qed.

Lemma glu_univ_elem_trm_resp_ctxsub : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m Δ,
      Γ ⊢ M : A ® m ∈ El ->
      Δ ⊆ Γ ->
      Δ ⊢ M : A ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply (ind_glu_exp_pred_resp_ctxsub p D ups ns NP NEl AP AEl elem_rel); eassumption. }
  all:
    simpl_glu_rel.
  (** An element of a small universe: its type's level term moves to the
      refined context too. *)
  all: try solve [ repeat apply conj;
                   [ mauto 3
                   | do 2 eexists; split; [ eapply glu_lvl_resp_ctxsub; eassumption | mauto 3 ]
                   | do 2 eexists; split;
                     [ eassumption | eapply glu_univ_elem_typ_resp_ctxsub; eassumption ]
                   | intros; mauto 4 ] ].
  all: try solve [ repeat apply conj; [ mauto 3 | mauto 3 | ];
                   do 2 eexists; split; [ eassumption | eapply glu_univ_elem_typ_resp_ctxsub; eassumption ] ].
  all: try solve [ split; mauto 3 ].
  (** A [Π]: the context refinement extends over the domain.  A neutral: its
      readback clause is transported along it. *)
  1:{ assert (Δ ⊢ IT : Typeω@(ulvl i)) by mauto 3.
      assert (Δ ▹ IT ⊆ Γ ▹ IT) by (eapply ctx_sub_extend; mauto 3 using wf_subtyp_refl_univ).
      econstructor; mauto 3; intros; mauto 4. }
  1:{ econstructor; [ split | | | ]; mauto 3; intros; mauto 4. }
Qed.

Lemma glu_nat_resp_wk' : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ,
      Γ ⊢ M : ℕ ->
      Δ ⊢k φ : Γ ->
      glu_nat Δ M[φ]ʷ a.
Proof.
  induction 1; intros; gen_presups.
  - econstructor.
    rewrite <- (exp_wk_zero φ); mauto 4.
  - econstructor; [ |mauto].
    rewrite <- (exp_wk_succ φ); mauto 4.
  - econstructor; trivial.
    intros Δ' ψ M' **.
    rewrite exp_wk_wk.
    assert (Δ' ⊢k φ ⊙ ψ : Γ) by mauto 3.
    mauto 4.
Qed.

Lemma glu_nat_resp_wk : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ,
      Δ ⊢k φ : Γ ->
      glu_nat Δ M[φ]ʷ a.
Proof.
  intros * ? * ?.
  assert (⊢ Γ) by (eapply kripke_cod; eassumption).
  mauto using glu_nat_resp_wk'.
Qed.

Hint Resolve glu_nat_resp_wk : mctt.

Lemma glu_lvl_resp_wk : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ,
      Δ ⊢k φ : Γ ->
      glu_lvl n Δ M[φ]ʷ a.
Proof.
  intros * H * ? Δ' ψ M' Hψ Hr.
  rewrite exp_wk_wk.
  assert (Δ' ⊢k φ ⊙ ψ : Γ) by mauto 3.
  exact (H _ _ _ ltac:(eassumption) Hr).
Qed.

Hint Resolve glu_lvl_resp_wk : mctt.

Lemma glu_False_resp_wk : forall Γ M a,
    glu_False Γ M a ->
    forall Δ φ,
      Δ ⊢k φ : Γ ->
      glu_False Δ M[φ]ʷ a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros Δ' ψ M' **.
  rewrite exp_wk_wk.
  assert (Δ' ⊢k φ ⊙ ψ : Γ) by mauto 3.
  mauto 4.
Qed.

Hint Resolve glu_False_resp_wk : mctt.

Lemma glu_univ_elem_trm_escape : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M : A.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel; mauto 4.
Qed.

Lemma glu_univ_elem_per_univ : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Dom a ≈ a ∈ per_univ i.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ eexists; eassumption. }
  all: eexists;
    try solve [per_univ_elem_econstructor; try reflexivity; trivial].

  - subst. eapply per_univ_elem_core_univ'; trivial.
    reflexivity.
  - eapply per_univ_elem_core_suniv'; trivial.
    reflexivity.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    mauto.
Qed.

Hint Resolve glu_univ_elem_per_univ : mctt.

Lemma glu_univ_elem_per_elem : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m R,
      Γ ⊢ M : A ® m ∈ El ->
      DF a ≈ a ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m ∈ R.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ simpl_glu_rel. match goal with HR : per_univ_elem _ ?R (d_ind _ _) (d_ind _ _), HE : per_univ_elem _ ?E (d_ind _ _) (d_ind _ _), Hm : ?E ?m ?m |- ?R ?m ?m => assert (EE : E <~> R) by (eapply per_univ_elem_right_irrel; eassumption); apply EE; exact Hm end. }
  all:
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H);
    simpl_glu_rel;
    try fold (per_univ j m m); try fold (per_univ (us (dlvl_real l)) m m);
    mauto 4.

  intros.
  destruct_rel_mod_app.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  do_per_univ_elem_irrel_assert.

  econstructor; firstorder eauto.
Qed.

Lemma glu_univ_elem_trm_typ : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left;
      match goal with H : _ ⊢ _ : _ /\ _ /\ (exists Ps, _ /\ _) |- _ => destruct H as (_ & _ & Ps & HPs & _) end;
      exists Ps; exact HPs. }
  all:
    simpl_glu_rel;
    mauto 4.

  econstructor; eauto.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  intros ? ? N n ? ? equiv_n.
  destruct_rel_mod_eval.
  enough (exists mn : domain, $| m & n |↘ mn /\  Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv_n) as [? []]; eauto 3.
Qed.

Lemma glu_univ_elem_trm_univ_lvl : forall i U P El a,
    Typeω@(ulvl i) = U ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A : U.
Proof.
  intros. eapply glu_univ_elem_univ_lvl; [ eassumption | eassumption | eapply glu_univ_elem_trm_typ ]; eassumption.
Qed.

Lemma glu_univ_elem_trm_resp_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m M',
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M ≈ M' : A ->
      Γ ⊢ M' : A ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply (ind_glu_exp_pred_resp_exp_eq p D ups ns NP NEl AP AEl elem_rel); eassumption. }
  all:
    simpl_glu_rel;
    repeat split; mauto 3.

  (** The type of the element is unchanged, so a small universe's level term
      and its equation carry over. *)
  all: try solve [ eapply suniv_glu_typ_pred_intro; eassumption ].
  (** A level: the readback clause, by transitivity. *)
  all: try solve [ match goal with
    | H : glu_lvl ?n ?Γ ?M ?m |- ?Δ ⊢ ?M'[?φ]ʷ ≈ ?L : Level@?n =>
        transitivity M[φ]ʷ; [ symmetry; mauto 3 | eapply glu_lvl_readback; eassumption ]
    end ].

  - repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_exp_eq;
      [ eassumption | eassumption | eapply wf_exp_eq_conv'; [ eassumption |] ].
    eassumption.

  - (** An element of a small universe: its type-level gluing moves along
        the equation lifted to the ambient [Typeω@0] by cumulativity, and its
        readback clause by transitivity. *)
    repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_exp_eq;
      [ eassumption | eassumption | eapply suniv_elem_eq_large; eassumption ].

  - intros; transitivity M[φ]ʷ; [| eauto ].
    symmetry; mauto 3.

  - econstructor; eauto.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    intros.
    destruct_rel_mod_eval.
    assert (Δ ⊢ N : IT[φ]ʷ) by eauto using glu_univ_elem_trm_escape.
    assert (exists mn : domain, $| m & n |↘ mn /\  Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv_n) as [? []] by intuition.
    eexists; split; eauto.
    enough (Δ ⊢ M[φ]ʷ $ N ≈ M'[φ]ʷ $ N : OT[(ι φ),,N]) by eauto.
    assert (Γ ⊢ M ≈ M' : Π IT OT) as Hty by mauto.
    assert (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : (Π IT OT)[φ]ʷ) as Hty' by mauto 2.
    rewrite exp_wk_pi in Hty'.
    eapply wf_exp_eq_app_cong' with (N := N) (N' := N) in Hty'; [| mauto 2].
    rewrite exp_sub_wk_q_extend in Hty'.
    eassumption.
  - intros.
    enough (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ); mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ T : (El Γ T)
    with signature wf_exp_eq gc_deps gc_stack Γ T ==> eq ==> iff as glu_univ_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_core_univ' : forall j i typ_rel el_rel,
    uidx_lt (ul j) i ->
    (typ_rel <∙> univ_glu_typ_pred j (Typeω@(ulvl i))) ->
    (el_rel <∙> univ_glu_exp_pred j (Typeω@(ulvl i))) ->
    DG 𝕌ω@j ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

Hint Resolve glu_univ_elem_core_univ' : mctt.

Lemma glu_univ_elem_core_suniv' : forall l i typ_rel el_rel,
    Dom l ≈ l ∈ per_lvl ->
    uidx_lt (us (dlvl_real l)) i ->
    (typ_rel <∙> suniv_glu_typ_pred l (Typeω@(ulvl i))) ->
    (el_rel <∙> suniv_glu_exp_pred l (Typeω@(ulvl i))) ->
    DG 𝕌@l ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

Hint Resolve glu_univ_elem_core_suniv' : mctt.

(** The gluing of a universe at either tier, in one statement. *)
Lemma glu_univ_elem_univ_at : forall {u i},
    uidx_lt u i ->
    DG ulvl_val u ∈ glu_univ_elem i ↘ univ_glu_typ_pred_at u (Typeω@(ulvl i)) ↘ univ_glu_exp_pred_at u (Typeω@(ulvl i)).
Proof.
  intros [n | j] * Hlt; cbn [ulvl_val univ_glu_typ_pred_at univ_glu_exp_pred_at].
  - apply glu_univ_elem_core_suniv';
      [ apply per_lvl_lit | exact Hlt | reflexivity | reflexivity ].
  - apply glu_univ_elem_core_univ'; [ exact Hlt | reflexivity | reflexivity ].
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_univ_elem_typ_morphism_iff1_Proper.
#[export] Existing Instance glu_univ_elem_trm_morphism_iff1_Proper.
#[export]
Hint Resolve glu_nat_resp_wk glu_lvl_resp_wk glu_False_resp_wk : mctt.
#[export]
Hint Resolve glu_univ_elem_per_univ : mctt.
#[export] Existing Instance glu_univ_elem_trm_morphism_iff3_Proper.
#[export]
Hint Resolve glu_univ_elem_core_univ' glu_univ_elem_core_suniv' glu_univ_elem_univ_at : mctt.
Ltac glu_univ_elem_econstructor :=
  eapply glu_univ_elem_core_univ' + eapply glu_univ_elem_core_suniv' + basic_glu_univ_elem_econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_univ_elem_univ_simple_constructor : forall {i : nat},
    glu_univ_elem (S i) (univ_glu_typ_pred i Typeω@(S i)) (univ_glu_exp_pred i Typeω@(S i)) 𝕌ω@i.
Proof.
  intros.
  apply glu_univ_elem_core_univ'; [ cbn; lia | reflexivity | reflexivity ].
Qed.

Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.
Ltac rewrite_predicate_equivalence_left :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_predicate_equivalence_right :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_predicate_equivalence :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_predicate_equivalence :=
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_right;
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_left;
  clear_predicate_equivalence.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** *** Simple Morphism instance for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> iff as simple_glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' ? El El'.
  split; intro Horig; [gen El' P' | gen El P];
    glu_univ_elem_induction Horig; unshelve glu_univ_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

(** *** Morphism instances for [neut_glu_*_pred]s *)
Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> eq ==> eq ==> iff as neut_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition.
Qed.

Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> glu_typ_pred_equivalence as neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_typ_pred_morphism_iff; mauto.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> eq ==> eq ==> eq ==> eq ==> iff as neut_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition;
    match_by_head per_bot ltac:(fun H => rewrite H in *); eassumption.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> glu_exp_pred_equivalence as neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_exp_pred_morphism_iff; mauto.
Qed.

(** *** Morphism instances for [pi_glu_*_pred]s *)
Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> glu_typ_pred_equivalence as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Lemma functional_glu_univ_elem : forall i a P P' El El',
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem i ↘ P' ↘ El' ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  glu_univ_elem_induction Ha; intros.
  9:{ basic_invert_glu_univ_elem Ha'.
      assert (D0 = D) by congruence; subst D0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      assert (EE : elem_rel0 <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (HNq : forall k vs, k < ind_nn D -> tele_pre (ind_nr D ups) k vs vs ->
                    (NP k vs <∙> NP0 k vs) /\ (NEl k vs <∙> NEl0 k vs)).
      { refine (ind_case_N_helper D ups _ H1 H3 _); intros;
          eapply H6; [ eassumption | eassumption | eassumption | eapply H17; eassumption ]. }
      assert (HAq : forall ms c gs k vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
                    ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) -> tele_pre (ind_ar D ups ms c) k vs vs ->
                    (AP ms c k vs <∙> AP0 ms c k vs) /\ (AEl ms c k vs <∙> AEl0 ms c k vs)).
      { refine (ind_case_A_helper D ups _ H4 _); intros;
          eapply H8; [ eassumption | eassumption | eassumption | eassumption | eassumption | eapply H18; eassumption ]. }
      pose proof (ind_canon_of_per _ _ _ _ _ _ _ _ H2 H H0 H0) as Hcp.
      apply_predicate_equivalence.
      split.
      - intros Γ A; cbn [ind_glu_typ_pred pointwise_lifting].
        split; intros (Ps & HPs); exists Ps;
          (eapply ind_typ_at_mono; [ | | exact HPs ]);
          [ intros k vs Hk Hp; destruct (HNq k vs Hk Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption
          | intros ms c gs k vs Hm Hc Hk Hp; destruct (HAq ms c gs k vs Hm Hc Hk Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption
          | intros k vs Hk Hp; destruct (HNq k vs Hk Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption
          | intros ms c gs k vs Hm Hc Hk Hp; destruct (HAq ms c gs k vs Hm Hc Hk Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption ].
      - intros Γ A M m; cbn [ind_glu_exp_pred pointwise_lifting].
        split; intros (? & ? & Ps & HPs & Hk);
          (split; [ assumption | split; [ apply EE + apply EE; assumption | exists Ps; split ] ]).
        + eapply ind_typ_at_mono; [ | | exact HPs ];
            [ intros k vs Hk' Hp; destruct (HNq k vs Hk' Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption
            | intros ms c gs k vs Hm Hc Hk' Hp; destruct (HAq ms c gs k vs Hm Hc Hk' Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption ].
        + intros Δ φ Ps' Hφ HPs'; eapply (glu_ind_mono p D ups _ _ H1 Hcp); [ | | exact (Hk Δ φ Ps' Hφ HPs') ]; intros; [ eapply HNq | eapply HAq ]; eassumption.
        + eapply ind_typ_at_mono; [ | | exact HPs ];
            [ intros k vs Hk' Hp; destruct (HNq k vs Hk' Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption
            | intros ms c gs k vs Hm Hc Hk' Hp; destruct (HAq ms c gs k vs Hm Hc Hk' Hp) as [E1 E2]; split; intros; [ apply E1 | apply E2 ]; assumption ].
        + intros Δ φ Ps' Hφ HPs'; eapply (glu_ind_mono p D ups _ _ H1 Hcp); [ | | exact (Hk Δ φ Ps' Hφ HPs') ]; intros; [ eapply HNq | eapply HAq ]; eassumption. }
  all: basic_invert_glu_univ_elem Ha';
    apply_predicate_equivalence; try solve [split; reflexivity].
  assert ((IP <∙> IP0) /\ (IEl <∙> IEl0)) as [] by mauto.
  apply_predicate_equivalence.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  split; [intros Γ C | intros Γ M C m].
  - split; intros []; econstructor; intuition;
      [rename equiv_m into equiv0_m; assert (equiv_m : in_rel m m) by intuition
      | assert (equiv0_m : in_rel0 m m) by intuition ];
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      assert ((OP m equiv_m <∙> OP0 m equiv0_m) /\ (OEl m equiv_m <∙> OEl0 m equiv0_m)) as [] by mauto 3;
      intuition.
  - split; intros []; econstructor; intuition;
      [rename equiv_n into equiv0_n; assert (equiv_n : in_rel n n) by intuition
      | assert (equiv0_n : in_rel0 n n) by intuition];
      destruct_rel_mod_eval;
      [assert (exists m0n, $| m0 & n |↘ m0n /\ Δ ⊢ M0[φ]ʷ $ N : OT[(ι φ),,N] ® m0n ∈ OEl n equiv_n) by intuition
      | assert (exists m0n, $| m0 & n |↘ m0n /\ Δ ⊢ M0[φ]ʷ $ N : OT[(ι φ),,N] ® m0n ∈ OEl0 n equiv0_n) by intuition];
      destruct_conjs;
      assert ((OP n equiv_n <∙> OP0 n equiv0_n) /\ (OEl n equiv_n <∙> OEl0 n equiv0_n)) as [] by mauto 3;
      eexists; split; intuition.
Qed.

End Fixed_GCtx.

#[export] Existing Instance simple_glu_univ_elem_morphism_iff_Proper.
#[export] Existing Instance neut_glu_typ_pred_morphism_iff_Proper.
#[export] Existing Instance neut_glu_typ_pred_morphism_glu_typ_pred_equivalence_Proper.
#[export] Existing Instance neut_glu_exp_pred_morphism_iff_Proper.
#[export] Existing Instance neut_glu_exp_pred_morphism_glu_exp_pred_equivalence_Proper.
#[export] Existing Instance pi_glu_typ_pred_morphism_iff_Proper.
#[export] Existing Instance pi_glu_typ_pred_morphism_glu_typ_pred_equivalence_Proper.
#[export] Existing Instance pi_glu_exp_pred_morphism_iff_Proper.
#[export] Existing Instance pi_glu_exp_pred_morphism_glu_exp_pred_equivalence_Proper.
Ltac apply_functional_glu_univ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_univ_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (DG ?a ∈ glu_univ_elem ?i ↘ ?P1 ↘ ?El1),
      H2 : DG ?a ∈ glu_univ_elem ?i' ↘ ?P2 ↘ ?El2 |- _ =>
      unify i i';
      assert_fails (unify P1 P2; unify El1 El2);
      match goal with
      | H : P1 <∙> P2, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P1 <∙> P2, H0 : El2 <∙> El1 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El2 <∙> El1 |- _ => fail 1
      | _ => assert ((P1 <∙> P2) /\ (El1 <∙> El2)) as [] by (eapply functional_glu_univ_elem; [apply H1 | apply H2]) || tactic_error P1 P2
      end
  end.

Ltac apply_functional_glu_univ_elem :=
  repeat apply_functional_glu_univ_elem1.

Ltac handle_functional_glu_univ_elem :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_univ_elem;
  apply_predicate_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_univ_elem_pi_clean_inversion1 : forall {i a ρ B in_rel P El},
  DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
  DG Πᵈ a ρ B ∈ glu_univ_elem i ↘ P ↘ El ->
  exists IP IEl (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
     (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred) elem_rel,
      DG a ∈ glu_univ_elem i ↘ IP ↘ IEl /\
        (forall c (equiv_c : Dom c ≈ c ∈ in_rel) b,
            ⟦ B ⟧ ρ ↦ c ↘ b ->
            DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c) /\
        DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel /\
        (P <∙> pi_glu_typ_pred (Typeω@(ulvl i)) in_rel IP IEl OP) /\
        (El <∙> pi_glu_exp_pred (Typeω@(ulvl i)) in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split.
  1,3: eassumption.
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain) Pb Elb,
                          ⟦ B ⟧ ρ ↦ c ↘ b ->
                          DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                          Γ ⊢ M : A ® m ∈ Elb).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          ⟦ B ⟧ ρ ↦ c ↘ b ->
                          DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                          Γ ⊢ A ® Pb).
  2-5: intros []; econstructor; mauto.
  all: intros.
  - assert (Dom c ≈ c ∈ in_rel0) as equiv0_c by intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c) by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_univ_elem; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - assert (Dom m ≈ m ∈ in_rel0) as equiv0_m by intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP m equiv0_m ↘ OEl m equiv0_m) by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    intuition.
  - assert (Dom n ≈ n ∈ in_rel0) as equiv0_n by intuition.
    assert (exists mn : domain, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv0_n) by mauto 3.
    destruct_conjs.
    eexists.
    intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP n equiv0_n ↘ OEl n equiv0_n) by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - assert (exists mn : domain,
               $| m & n |↘ mn /\
                 (forall (b : domain) (Pb : glu_typ_pred) (Elb : glu_exp_pred),
                     ⟦ B ⟧ ρ ↦ n ↘ b ->
                     DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                     Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ Elb)) by intuition.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    eexists.
    intuition.
Qed.

Lemma glu_univ_elem_pi_clean_inversion2 : forall {i a ρ B in_rel IP IEl P El},
  DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
  DG a ∈ glu_univ_elem i ↘ IP ↘ IEl ->
  DG Πᵈ a ρ B ∈ glu_univ_elem i ↘ P ↘ El ->
  exists (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
     (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred) elem_rel,
    (forall c (equiv_c : Dom c ≈ c ∈ in_rel) b,
        ⟦ B ⟧ ρ ↦ c ↘ b ->
        DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c) /\
      DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel /\
      (P <∙> pi_glu_typ_pred (Typeω@(ulvl i)) in_rel IP IEl OP) /\
      (El <∙> pi_glu_exp_pred (Typeω@(ulvl i)) in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hinglu Hglu.
  unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in Hglu; shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]].
  handle_functional_glu_univ_elem.
  do 3 eexists.
  repeat split; try eassumption;
    intros []; econstructor; mauto.
Qed.

End Fixed_GCtx.

Ltac invert_glu_univ_elem H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_univ_elem H.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_lvl_read_left : forall d d' s L, Dom d ≈ d' ∈ per_lvl -> Rnf ⇓ Levelᵈ d' in s ↘ L -> Rnf ⇓ Levelᵈ d in s ↘ L.
Proof.
  intros * Hd%per_lvl_then_per_top Hr; destruct (Hd s) as (L' & HL & HL').
  pose proof (functional_read_nf _ _ _ _ HL' Hr) as ->; exact HL.
Qed.

Lemma glu_lvl_resp_per : forall Γ M m n, glu_lvl n Γ M m -> forall m', Dom m ≈ m' ∈ per_lvl -> glu_lvl n Γ M m'.
Proof.
  intros * H * Hm Δ φ L Hφ Hr.
  apply H; [ eassumption | eapply per_lvl_read_left; eassumption ].
Qed.

(** Related levels give equivalent small-universe predicates: a level term
    glued to one is glued to the other, and the two have the same realiser,
    which indexes the elements. *)
Lemma suniv_glu_typ_pred_resp_per : forall l l' U,
    Dom l ≈ l' ∈ per_lvl ->
    suniv_glu_typ_pred l U <∙> suniv_glu_typ_pred l' U.
Proof.
  intros * Hl Γ A; cbn; split; intros (t & n & Ht & Heq); exists t, n; split; try assumption;
    (eapply glu_lvl_resp_per; [ eassumption | first [ eassumption | symmetry; assumption ] ]).
Qed.

Lemma suniv_glu_exp_pred_resp_per : forall l l' U,
    Dom l ≈ l' ∈ per_lvl ->
    suniv_glu_exp_pred l U <∙> suniv_glu_exp_pred l' U.
Proof.
  intros * Hl Γ A M m; cbn.
  rewrite (per_lvl_real _ _ Hl).
  pose proof (suniv_glu_typ_pred_resp_per l l' U Hl Γ A) as Ht; cbn in Ht.
  split; intros (? & HA & ? & ?); repeat split; try assumption; apply Ht; assumption.
Qed.

Lemma glu_univ_elem_resp_per_univ : forall i a a' P El,
    Dom a ≈ a' ∈ per_univ i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  simpl.
  intros * [elem_rel Hper] Horig.
  pose proof Hper.
  gen P El.
  per_univ_elem_induction Hper; intros; subst.
  9:{ (** An inductive type: the same gluings of its telescopes, at the
          related uniform parameters. *)
      assert (Hag : ind_fam_agree D nr (ind_nr D ups) ar (ind_ar D ups)).
      { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact H0 | | ].
        - intros * HA Hp; destruct (H5 _ _ _ _ HA Hp) as [a a' Ea Ea' [HR _]]; eauto.
        - intros * Hm Hc HA Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc HA Hp) as [a a' Ea Ea' [HR _]]; eauto. }
      destruct Hag as [Hn0 Ha0].
      pose proof (tele_pre_nr_change' p D ups _ _ _ _ Hn0 Ha0) as P2.
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ H14 H H1 H2) as (_ & _ & Hcp & [Hfn Hfa] & Hadm & _ & _ & _).
      pose proof (tele_full_nr_change p D ups _ _ _ _
                    (fun k vs v1 v2 Hk Hp1 Hp2 => symmetry (Hfn k vs v2 v1 Hk Hp2 Hp1))
                    (fun ms m1 m2 c gs k vs v1 v2 Hm1 Hm2 Hc Hk Hp1 Hp2 => symmetry (Hfa ms m2 m1 c gs k vs v2 v1 Hm2 Hm1 Hc Hk Hp2 Hp1))) as G1.
      pose proof (tele_pre_nr_change' p D ups _ _ _ _ Hfn Hfa) as Q2.
      basic_invert_glu_univ_elem Horig.
      assert (D0 = D) by congruence; subst D0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      assert (HR' : per_univ_elem i elem_rel (d_ind p (ups' ++ ns')) (d_ind p (ups' ++ ns')))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact H14 | exact H14 ]).
      destruct (ind_fam_agree_sym _ _ _ _ _ (conj Hn0 Ha0)) as [Hn0' Ha0'].
      pose proof (tele_full_nr_change p D ups _ _ _ _ Hn0' Ha0') as F2.
      assert (Hpre : forall k vs, k < length (List.rev (ind_nparams D)) -> tele_pre (ind_nr D ups') k vs vs ->
                     tele_pre (ind_nr D ups) k vs vs /\ tele_pre nr k vs vs).
      { intros * Hk Hp. pose proof (Q2 k vs vs ltac:(lia) Hp) as Hp1.
        split; [ exact Hp1 | exact (P2 k vs vs ltac:(lia) Hp1) ]. }
      assert (Hpra : forall ms c gs k vs, tele_full (ind_nr D ups') (List.rev (ind_nparams D)) ms ms ->
                     ind_con D c = Some gs -> k < length (cargs_nonrec gs) -> tele_pre (ind_ar D ups' ms c) k vs vs ->
                     tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms /\ tele_full nr (List.rev (ind_nparams D)) ms ms /\
                     tele_pre (ind_ar D ups ms c) k vs vs /\ tele_pre (ar ms c) k vs vs).
      { intros * Hm Hc Hk Hp.
        pose proof (G1 _ _ Hm) as Hm1. pose proof (F2 _ _ Hm1) as Hm2.
        pose proof (tele_pre_ar_change' p D ups _ _ _ _ Hfn Hfa ms ms ms c gs k vs vs Hm1 Hm Hc ltac:(lia) Hp) as Hp1.
        pose proof (tele_pre_ar_change' p D ups _ _ _ _ Hn0 Ha0 ms ms ms c gs k vs vs Hm2 Hm1 Hc ltac:(lia) Hp1) as Hp2.
        exact (conj Hm1 (conj Hm2 (conj Hp1 Hp2))). }
      assert (ER : elem_rel0 <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ H14) H H2 H1) as (_ & _ & Hcp' & Hfa' & Hadm' & _).
      pose proof (per_univ_then_per_top_typ H14) as Htop.
      pose proof (per_univ_then_per_top_typ (per_univ_sym _ _ _ _ H14)) as Htop'.
      assert (Hrbt : forall bs bs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs' ->
                     Dom d_ind p (ups ++ bs) ≈ d_ind p (ups' ++ bs') ∈ per_top_typ)
        by (intros * Hb; destruct (per_univ_elem_ind_reinst _ _ _ _ _ _ _ _ H14 H H1 H2 _ _ Hb) as [Rr HRr];
            exact (per_univ_then_per_top_typ HRr)).
      assert (Hrbt' : forall bs bs', tele_full (ind_nr D ups') (List.rev (ind_nparams D)) bs bs' ->
                      Dom d_ind p (ups' ++ bs) ≈ d_ind p (ups ++ bs') ∈ per_top_typ)
        by (intros * Hb; destruct (per_univ_elem_ind_reinst _ _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ H14) H H2 H1 _ _ Hb) as [Rr HRr];
            exact (per_univ_then_per_top_typ HRr)).
      simp glu_univ_elem.
      refine (glu_univ_elem_core_indty i _ NP NEl AP AEl typ_rel el_rel elem_rel H H2 H0 HR' _ _ _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *.
      - intros k A vs HA Hp.
        assert (Hk : k < length (List.rev (ind_nparams D))) by (apply List.nth_error_Some; congruence).
        destruct (Hpre _ _ Hk Hp) as [_ Hp2]; destruct (H5 _ _ _ _ HA Hp2) as [a a' Ea Ea' _]; eauto.
      - intros ms c gs k A vs Hm Hc HA Hp.
        assert (Hk : k < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ _ _ _ Hm Hc Hk Hp) as (_ & Hm2 & _ & Hp2).
        destruct (H8 _ _ _ _ _ _ _ _ Hm2 Hc HA Hp2) as [a a' Ea Ea' _]; eauto.
      - intros k A vs b HA Hp Eb.
        assert (Hk : k < length (List.rev (ind_nparams D))) by (apply List.nth_error_Some; congruence).
        destruct (Hpre _ _ Hk Hp) as [Hp1 Hp2]; destruct (H5 _ _ _ _ HA Hp2) as [a a' Ea Ea' [HR IH]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        eapply IH; [ exact HR | eapply H21; eassumption ].
      - intros ms c gs k A vs b Hm Hc HA Hp Eb.
        assert (Hk : k < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ _ _ _ Hm Hc Hk Hp) as (Hm1 & Hm2 & Hp1 & Hp2).
        destruct (H8 _ _ _ _ _ _ _ _ Hm2 Hc HA Hp2) as [a a' Ea Ea' [HR IH]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        eapply IH; [ exact HR | eapply H22; eassumption ].
      - intros Γ A; destruct (H23 Γ A) as [Ha Hb]; split; intro HH.
        + destruct (Ha HH) as (Ps & HPs); exists Ps.
          eapply ind_typ_at_resp_per_top; [ eassumption | exact Htop | exact (conj Hfn Hfa) | exact HPs ].
        + apply Hb; destruct HH as (Ps & HPs); exists Ps.
          eapply ind_typ_at_resp_per_top; [ eassumption | exact Htop' | exact Hfa' | exact HPs ].
      - intros Γ A M m; destruct (H24 Γ A M m) as [Ha Hb]; cbn [ind_glu_exp_pred] in *; split; intro HH.
        + destruct (Ha HH) as (HM & Hm & Ps & HPs & Hk).
          split; [ exact HM | split; [ apply ER; exact Hm | exists Ps; split ] ].
          * eapply ind_typ_at_resp_per_top; [ eassumption | exact Htop | exact (conj Hfn Hfa) | exact HPs ].
          * intros Δ φ Ps' Hφ HPs'.
            eapply (glu_ind_move p D ups NEl AEl H0 Hcp ups' NEl AEl H (conj Hfn Hfa) Hadm Hrbt);
              [ intros; assumption | intros; assumption | exact (Hk Δ φ Ps' Hφ HPs') ].
        + apply Hb; destruct HH as (HM & Hm & Ps & HPs & Hk).
          split; [ exact HM | split; [ apply ER; exact Hm | exists Ps; split ] ].
          * eapply ind_typ_at_resp_per_top; [ eassumption | exact Htop' | exact Hfa' | exact HPs ].
          * intros Δ φ Ps' Hφ HPs'.
            eapply (glu_ind_move p D ups' NEl AEl H0 Hcp' ups NEl AEl H Hfa' Hadm' Hrbt');
              [ intros; assumption | intros; assumption | exact (Hk Δ φ Ps' Hφ HPs') ]. }
  all:
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Horig; glu_univ_elem_econstructor; try eassumption; mauto;
    handle_per_univ_elem_irrel;
    handle_functional_glu_univ_elem.
  (** A small universe at a related level: the same realiser, and equivalent
      predicates. *)
  all: try match goal with
         | H : per_lvl ?l ?l' |- uidx_lt (us (dlvl_real ?l')) _ =>
             rewrite <- (per_lvl_real _ _ H); assumption
         | H : per_lvl ?l ?l' |- suniv_glu_typ_pred ?l _ <∙> suniv_glu_typ_pred ?l' _ =>
             apply suniv_glu_typ_pred_resp_per; exact H
         | H : per_lvl ?l ?l' |- _ <∙> suniv_glu_exp_pred ?l' _ =>
             exact (suniv_glu_exp_pred_resp_per _ _ _ H)
         end.
  - intros.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
  - reflexivity.
  - apply neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
    eassumption.
  - apply neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
    eassumption.
Qed.

(** *** Morphism instances for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ i ==> iff as glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; eassumption.
Qed.

Add Parametric Morphism i R : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ_elem i R ==> iff as glu_univ_elem_morphism_iff'.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' **.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; mauto.
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_univ_elem_morphism_iff'_Proper.

Ltac saturate_glu_by_per1 :=
  match goal with
  | H : glu_univ_elem ?i ?P ?El ?a,
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a') by (rewrite <- H1; eassumption);
      fail_if_dup
  | H : glu_univ_elem ?i ?P ?El ?a',
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a) by (rewrite H1; eassumption);
      fail_if_dup
  end.

Ltac saturate_glu_by_per :=
  clear_dups;
  repeat saturate_glu_by_per1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_univ_glu_univ_elem : forall i a,
    Dom a ≈ a ∈ per_univ i ->
    exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  simpl.
  (** [per_univ_elem_induction] wants distinct indices; [induction] abstracted
      the right one. *)
  intros i a [R Hper].
  enough (forall a0, DF a0 ≈ a ∈ per_univ_elem i ↘ R -> exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) by eauto.
  clear Hper; intros a0 Hper.
  per_univ_elem_induction Hper; intros.
  9:{ (** An inductive type: its telescopes glue at their canonical
          gluings, at the right uniform parameters. *)
      assert (H14 : per_univ_elem i elem_rel (d_ind p (ups ++ ns)) (d_ind p (ups' ++ ns'))).
      { basic_per_univ_elem_econstructor; try eassumption.
        - intros * HA Hp; destruct (H5 _ _ _ _ HA Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto.
        - intros * Hm Hc HA Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc HA Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto. }
      assert (Hcan : forall b P El (E : domain -> Prop), (forall b', E b' -> b' = b) -> E b -> glu_univ_elem i P El b ->
                 glu_univ_elem i (fun Γ T => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> P' Γ T)
                                 (fun Γ T M m => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> El' Γ T M m) b).
      { intros * HE Eb Hg.
        eapply simple_glu_univ_elem_morphism_iff; [ | | reflexivity | exact Hg ].
        - intros Γ T; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [HPP _]; apply HPP; exact HP.
        - intros Γ T M m; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [_ HEE]; apply HEE; exact HP. }
      assert (Hag : ind_fam_agree D nr (ind_nr D ups) ar (ind_ar D ups)).
      { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact H0 | | ].
        - intros * HA Hp; destruct (H5 _ _ _ _ HA Hp) as [a a' Ea Ea' [HR _]]; eauto.
        - intros * Hm Hc HA Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc HA Hp) as [a a' Ea Ea' [HR _]]; eauto. }
      destruct Hag as [Hn0 Ha0].
      pose proof (tele_pre_nr_change' p D ups _ _ _ _ Hn0 Ha0) as P2.
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ H14 H H1 H2) as (_ & _ & Hcp & [Hfn Hfa] & Hadm & _ & _ & _).
      pose proof (tele_full_nr_change p D ups _ _ _ _
                    (fun k vs v1 v2 Hk Hp1 Hp2 => symmetry (Hfn k vs v2 v1 Hk Hp2 Hp1))
                    (fun ms m1 m2 c gs k vs v1 v2 Hm1 Hm2 Hc Hk Hp1 Hp2 => symmetry (Hfa ms m2 m1 c gs k vs v2 v1 Hm2 Hm1 Hc Hk Hp2 Hp1))) as G1.
      pose proof (tele_pre_nr_change' p D ups _ _ _ _ Hfn Hfa) as Q2.
      assert (HR' : per_univ_elem i elem_rel (d_ind p (ups' ++ ns')) (d_ind p (ups' ++ ns')))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact H14 | exact H14 ]).
      destruct (ind_fam_agree_sym _ _ _ _ _ (conj Hn0 Ha0)) as [Hn0' Ha0'].
      pose proof (tele_full_nr_change p D ups _ _ _ _ Hn0' Ha0') as F2.
      assert (Hpre : forall k vs, k < length (List.rev (ind_nparams D)) -> tele_pre (ind_nr D ups') k vs vs ->
                     tele_pre nr k vs vs).
      { intros * Hk Hp. exact (P2 k vs vs ltac:(lia) (Q2 k vs vs ltac:(lia) Hp)). }
      assert (Hpra : forall ms c gs k vs, tele_full (ind_nr D ups') (List.rev (ind_nparams D)) ms ms ->
                     ind_con D c = Some gs -> k < length (cargs_nonrec gs) -> tele_pre (ind_ar D ups' ms c) k vs vs ->
                     tele_full nr (List.rev (ind_nparams D)) ms ms /\ tele_pre (ar ms c) k vs vs).
      { intros * Hm Hc Hk Hp.
        pose proof (G1 _ _ Hm) as Hm1. pose proof (F2 _ _ Hm1) as Hm2.
        pose proof (tele_pre_ar_change' p D ups _ _ _ _ Hfn Hfa ms ms ms c gs k vs vs Hm1 Hm Hc ltac:(lia) Hp) as Hp1.
        exact (conj Hm2 (tele_pre_ar_change' p D ups _ _ _ _ Hn0 Ha0 ms ms ms c gs k vs vs Hm2 Hm1 Hc ltac:(lia) Hp1)). }
      set (NP := fun k vs Γ T => forall b P El, ⟦ nth_ctyp (List.rev (ind_nparams D)) k ⟧ env_args nil (ups' ++ vs) ↘ b ->
                                   glu_univ_elem i P El b -> P Γ T).
      set (NEl := fun k vs Γ T M m => forall b P El, ⟦ nth_ctyp (List.rev (ind_nparams D)) k ⟧ env_args nil (ups' ++ vs) ↘ b ->
                                        glu_univ_elem i P El b -> El Γ T M m).
      set (AP := fun ms c k vs Γ T => forall b P El, ⟦ nth_atyp D c k ⟧ env_args nil (ups' ++ ms ++ vs) ↘ b ->
                                        glu_univ_elem i P El b -> P Γ T).
      set (AEl := fun ms c k vs Γ T M m => forall b P El, ⟦ nth_atyp D c k ⟧ env_args nil (ups' ++ ms ++ vs) ↘ b ->
                                             glu_univ_elem i P El b -> El Γ T M m).
      do 2 eexists.
      simp glu_univ_elem.
      refine (glu_univ_elem_core_indty i _ NP NEl AP AEl _ _ elem_rel H H2 H0 HR' _ _ _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *; try reflexivity.
      - intros k A vs HA Hp.
        assert (Hk : k < length (List.rev (ind_nparams D))) by (apply List.nth_error_Some; congruence).
        destruct (H5 _ _ _ _ HA (Hpre _ _ Hk Hp)) as [a a' Ea Ea' _]; eauto.
      - intros ms c gs k A vs Hm Hc HA Hp.
        assert (Hk : k < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ _ _ _ Hm Hc Hk Hp) as (Hm2 & Hp2).
        destruct (H8 _ _ _ _ _ _ _ _ Hm2 Hc HA Hp2) as [a a' Ea Ea' _]; eauto.
      - intros k A vs b HA Hp Eb.
        assert (Hk : k < length (List.rev (ind_nparams D))) by (apply List.nth_error_Some; congruence).
        destruct (H5 _ _ _ _ HA (Hpre _ _ Hk Hp)) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold NP, NEl; rewrite (nth_ctyp_eq _ _ _ HA).
        eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ].
      - intros ms c gs k A vs b Hm Hc HA Hp Eb.
        assert (Hk : k < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ _ _ _ Hm Hc Hk Hp) as (Hm2 & Hp2).
        destruct (H8 _ _ _ _ _ _ _ _ Hm2 Hc HA Hp2) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold AP, AEl; rewrite (nth_atyp_eq _ _ _ _ _ Hc HA).
        eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ]. }
  all:
    try solve [do 2 eexists; unshelve (glu_univ_elem_econstructor; try reflexivity; subst; trivial)].
  (** A small universe at the right-hand level, which has the realiser of the
      left-hand one. *)
  all: try match goal with
         | H : per_lvl ?l ?l' |- exists _ _, glu_univ_elem _ _ _ 𝕌@?l' =>
             do 2 eexists; apply glu_univ_elem_core_suniv';
               [ etransitivity; [ symmetry |]; exact H
               | rewrite <- (per_lvl_real _ _ H); assumption
               | reflexivity | reflexivity ]
         end.

  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A M m =>
                          forall b P El,
                            ⟦ B' ⟧ ρ' ↦ c ↘ b ->
                            glu_univ_elem i P El b ->
                            Γ ⊢ M : A ® m ∈ El).
      instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A =>
                          forall b P El,
                            ⟦ B' ⟧ ρ' ↦ c ↘ b ->
                            glu_univ_elem i P El b ->
                            Γ ⊢ A ® P).
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough (DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel) by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
  - do 2 eexists.
    glu_univ_elem_econstructor; try reflexivity; mauto.
Qed.

Hint Resolve per_univ_glu_univ_elem : mctt.

Corollary per_univ_elem_glu_univ_elem : forall i a R,
    DF a ≈ a ∈ per_univ_elem i ↘ R ->
    exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  intros.
  apply per_univ_glu_univ_elem; mauto.
Qed.

Hint Resolve per_univ_elem_glu_univ_elem : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_glu_univ_elem per_univ_elem_glu_univ_elem : mctt.

Ltac saturate_glu_info1 :=
  match goal with
  | H : glu_univ_elem _ ?P _ _,
      H1 : ?P _ _ |- _ =>
      pose proof (glu_univ_elem_univ_lvl_gen _ _ _ _ H _ _ H1);
      fail_if_dup
  | H : glu_univ_elem _ _ ?El _,
      H1 : ?El _ _ _ _ |- _ =>
      pose proof (glu_univ_elem_trm_escape _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_info :=
  clear_dups;
  repeat saturate_glu_info1.

(** The type-level gluing of a small universe along a weakening [φ]: its level
    term is weakened with the type. *)
Ltac suniv_glu_typ_pred_wk :=
  match goal with
  | H : exists t n, glu_lvl n ?Γ t ?l /\ _,
      Hφ : ?Δ ⊢k ?φ : ?Γ
    |- exists t n, glu_lvl n ?Δ t ?l /\ _ =>
      let t := fresh "t" in
      let Heq := fresh "Heq" in
      destruct H as (t & ? & ? & Heq); exists t[φ]ʷ; eexists; split;
      [ eapply glu_lvl_resp_wk; eassumption
      | match type of Heq with
        | wf_exp_eq ?T ?X _ ?U ?A _ =>
            assert (wf_exp_eq T X Δ U A[φ]ʷ (Type⟨t⟩)[φ]ʷ) by mauto 2; eassumption
        end ]
  end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Gluing predicates are monotone along Kripke weakenings. Two weakenings
    collapse to a single [[φ ⊙ ψ]ʷ] by [exp_wk_wk], and the [q] of a [Π]
    codomain absorbs the extension of the second weakening by
    [exp_sub_wk_q_extend_wk]. Both are propositional equalities, so each case
    is a [rewrite] away from its hypothesis. *)

Lemma glu_univ_elem_typ_monotone : forall i a P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Δ φ Γ A,
      Γ ⊢ A ® P ->
      Δ ⊢k φ : Γ ->
      Δ ⊢ A[φ]ʷ ® P.
Proof.
  simpl. glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply (ind_glu_typ_pred_wk p D ups ns NP NEl AP AEl); eassumption. }
  all: saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    try solve [mauto 2].
  (** A small universe: the level term weakens with the type. *)
  all: try solve [ suniv_glu_typ_pred_wk ].
  - simpl_glu_rel.
    assert (Δ ⊢ A[φ]ʷ ≈ (Π IT OT)[φ]ʷ : Typeω@(ulvl i)) as HAeq by mauto 2.
    rewrite exp_wk_pi in HAeq.
    econstructor; [ eassumption | mauto 2 | mauto 2 | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.

  - destruct_conjs.
    split; [mauto 2 |].
    intros.
    rewrite exp_wk_wk.
    mauto 4.
Qed.

Lemma glu_univ_elem_exp_monotone : forall i a P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Δ φ Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Δ ⊢k φ : Γ ->
      Δ ⊢ M[φ]ʷ : A[φ]ʷ ® m ∈ El.
Proof.
  simpl. glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply (ind_glu_exp_pred_wk p D ups ns NP NEl AP AEl elem_rel); eassumption. }
  all: saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all.
  all: try solve [ repeat eexists; mauto 2; eapply glu_univ_elem_typ_monotone; eauto ].
  (** An element of a small universe: its type's level term weakens with it,
      and its readback clause composes the two weakenings. *)
  all: try solve [ repeat apply conj;
                   [ mauto 2
                   | do 2 eexists; split; [ eapply glu_lvl_resp_wk; eassumption | mauto 2 ]
                   | do 2 eexists; split;
                     [ eassumption | eapply glu_univ_elem_typ_monotone; eassumption ]
                   | intros; rewrite !exp_wk_wk; mauto 3 ] ].
  (** A level: its readback clause weakens. *)
  all: try solve [ split; [ mauto 2 | split; [ assumption | eapply glu_lvl_resp_wk; eassumption ] ] ].
  all: try solve [ repeat split; mauto 2 ].
  - simpl_glu_rel.
    assert (Δ ⊢ A[φ]ʷ ≈ (Π IT OT)[φ]ʷ : Typeω@(ulvl i)) as HAeq by mauto 2.
    rewrite exp_wk_pi in HAeq.
    econstructor; [ mauto 2 | eassumption | eassumption | mauto 2 | mauto 2 | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.

  - simpl_glu_rel.
    econstructor; [ split; [ mauto 2 | ] | mauto 2 | eassumption | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + do 2 rewrite exp_wk_wk; mauto 4.
Qed.

(** Transport along a context refinement, as in [glu_nat_resp_ctxsub]: a
    Kripke weakening into [Δ] extends to one into [Γ] by [kripke_ctxsub], which
    is all three lemmas need. *)

Lemma glu_elem_bot_resp_ctxsub : forall i a Γ A M m Δ,
    Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
    Δ ⊆ Γ ->
    Δ ⊢ M : A ® m ∈ glu_elem_bot i a.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_elem_top_resp_ctxsub : forall i a Γ A M m Δ,
    Γ ⊢ M : A ® m ∈ glu_elem_top i a ->
    Δ ⊆ Γ ->
    Δ ⊢ M : A ® m ∈ glu_elem_top i a.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_typ_top_resp_ctxsub : forall i a Γ A Δ,
    Γ ⊢ A ® glu_typ_top i a ->
    Δ ⊆ Γ ->
    Δ ⊢ A ® glu_typ_top i a.
Proof.
  intros * [] ?; econstructor; [ mauto 3 | eassumption | intros ]; mauto 4.
Qed.

Hint Resolve glu_elem_bot_resp_ctxsub glu_elem_top_resp_ctxsub glu_typ_top_resp_ctxsub : mctt.

Add Parametric Morphism i a Γ : (glu_elem_bot i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_bot i a Γ A)
    with signature wf_exp_eq gc_deps gc_stack Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ) as HMφM'φ by mauto 4;
    [rewrite <- HMφM'φ | rewrite -> HMφM'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_top i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_top i a Γ A)
    with signature wf_exp_eq gc_deps gc_stack Γ A ==> eq ==> iff as glu_elem_top_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ) as HMφM'φ by mauto 4;
    [rewrite <- HMφM'φ | rewrite -> HMφM'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ : (glu_typ_top i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (Typeω@(ulvl i)) ==> iff as glu_typ_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    try (gen_presup HAA'; eassumption);
    intros;
    assert (Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@(ulvl i)) as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

(** *** Simple Morphism instance for [glu_ctx_env] *)
Add Parametric Morphism : glu_ctx_env
    with signature glu_sub_pred_equivalence ==> eq ==> iff as simple_glu_ctx_env_morphism_iff.
Proof.
  intros Sb Sb' HSbSb' a.
  split; intro Horig; [gen Sb' | gen Sb];
    induction Horig; econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_univ_elem_morphism_iff_Proper.
#[export] Existing Instance glu_elem_bot_morphism_iff2_Proper.
#[export] Existing Instance glu_elem_bot_morphism_iff3_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff2_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff3_Proper.
#[export] Existing Instance glu_typ_top_morphism_iff2_Proper.
#[export] Existing Instance simple_glu_ctx_env_morphism_iff_Proper.
#[export]
Hint Resolve glu_elem_bot_resp_ctxsub glu_elem_top_resp_ctxsub glu_typ_top_resp_ctxsub : mctt.

(** *** Gluing respects the element PER

    A term glued to a value is glued to every value related to it: δ relates
    a member to its expansion by the element PER only. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_bot_read_left : forall d d' s M, Dom d ≈ d' ∈ per_bot -> Rne d' in s ↘ M -> Rne d in s ↘ M.
Proof.
  intros * Hd Hr; destruct (Hd s) as (L & HL & HL').
  pose proof (functional_read_ne _ _ _ _ HL' Hr) as ->; exact HL.
Qed.

(** The same for levels, whose readback is at the type [Level]. *)
(** The same for types: related types read back equally, so a readback of the
    right one is one of the left. *)
Lemma per_top_typ_read_left : forall d d' s W, Dom d ≈ d' ∈ per_top_typ -> Rtyp d' in s ↘ W -> Rtyp d in s ↘ W.
Proof.
  intros * Hd Hr; destruct (Hd s) as (L & HL & HL').
  pose proof (functional_read_typ _ _ _ _ HL' Hr) as ->; exact HL.
Qed.

Lemma glu_nat_resp_per : forall Γ M m, glu_nat Γ M m -> forall m', Dom m ≈ m' ∈ per_nat -> glu_nat Γ M m'.
Proof.
  induction 1 as [| ? ? ? ? HM Hg IH | ? ? ? ? Hb Hrb ]; intros m'' Hm; inversion Hm; subst.
  - constructor; assumption.
  - econstructor; [ eassumption | eapply IH; eassumption ].
  - constructor; [ etransitivity; [ symmetry |]; eassumption |].
    intros * Hk Hr; eapply Hrb; [ eassumption | eapply per_bot_read_left; eassumption ].
Qed.

Lemma glu_False_resp_per : forall Γ M m, glu_False Γ M m -> forall m', Dom m ≈ m' ∈ per_ne -> glu_False Γ M m'.
Proof.
  intros * [? ? ? ? Hb Hrb] m'' Hm; inversion Hm; subst.
  constructor; [ etransitivity; [ symmetry |]; eassumption |].
  intros * Hk Hr; eapply Hrb; [ eassumption | eapply per_bot_read_left; eassumption ].
Qed.

Lemma glu_univ_elem_trm_resp_per_elem : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall R, DF a ≈ a ∈ per_univ_elem i ↘ R ->
    forall Γ A M m m', Γ ⊢ M : A ® m ∈ El -> Dom m ≈ m' ∈ R -> Γ ⊢ M : A ® m' ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  9:{ (** An inductive type: [glu_ind] moves along the canonical relation,
          given that the telescopes' gluings move along theirs. *)
      apply_equiv_left.
      match goal with HE : _ ⊢ ?M : ?A /\ _ |- _ ⊢ ?M : ?A /\ _ => destruct HE as (H12 & H14 & H15 & HPt & H17) end.
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ H2 H H0 H0) as (_ & _ & Hcp & _ & _ & Hadm & _ & Herel).
      destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ H2 H H0 H0) as [HevN HevA].
      pose proof Hcp as (HnP & HnI & HaP & HaI).
      assert (Hhd : forall b P0 El0 S ρ, ⟦ S ⟧ ρ ↘ b -> glu_univ_elem i P0 El0 b ->
                    per_univ_elem i (per_head S S ρ ρ) b b).
      { intros * Eb Hg. destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [Rb HRb].
        eapply per_univ_elem_resp_iff; [ exact HRb | exact (per_head_iff Eb Eb HRb) ]. }
      assert (HNe : forall k vs vs', k < ind_nn D -> tele_pre (ind_nr D ups) k vs vs' ->
                forall Γ0 A0 N n n', NEl k vs Γ0 A0 N n -> ind_nr D ups k vs n n' -> NEl k vs' Γ0 A0 N n').
      { intros k vs vs' Hk Hp Γ0 A0 N n n' HN Hnn.
        assert (Hk' : k < length (List.rev (ind_nparams D))) by (rewrite List.length_rev, length_nparams; exact Hk).
        destruct (nparams_lt_ass D k H1 Hk') as [S HS].
        pose proof (tnrp_refl_l p D ups _ (ind_ar D ups) H1 HnP HnI HaP HaI k vs vs' ltac:(lia) Hp) as Hd.
        pose proof (tnrp_refl_r p D ups _ (ind_ar D ups) H1 HnP HnI HaP HaI k vs vs' ltac:(lia) Hp) as Hd'.
        destruct (H3 _ _ _ HS Hd) as [b Eb].
        pose proof (H5 _ _ _ _ HS Hd Eb) as Hgb.
        pose proof (Hhd _ _ _ _ _ Eb Hgb) as Hpb.
        assert (Hn2 : NEl k vs Γ0 A0 N n').
        { unfold ind_nr in Hnn; rewrite (nth_ctyp_eq _ _ _ HS) in Hnn.
          exact (H6 _ _ _ _ HS Hd Eb _ Hpb _ _ _ _ _ HN Hnn). }
        destruct (HevN _ _ _ _ HS Hp) as (a & a' & Ea & Ea' & Haa).
        assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R0 => per_univ_elem i R0 b a') _ Haa) Hgb) as Hga'.
        pose proof (H5 _ _ _ _ HS Hd' Ea') as Hgb'.
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [_ HEq].
        apply HEq; exact Hn2. }
      assert (HAe : forall ms ms' c gs k vs vs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
                ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) -> tele_pre (ind_ar D ups ms c) k vs vs' ->
                forall Γ0 A0 N n n', AEl ms c k vs Γ0 A0 N n -> ind_ar D ups ms c k vs n n' -> AEl ms' c k vs' Γ0 A0 N n').
      { clear HNe H3 H5 H6 H9 H10 H17.
        intros ms ms' c gs k vs vs' Hm Hc Hk Hp Γ0 A0 N n n' HN Hnn.
        destruct (nth_error_lt_some' _ _ Hk) as [S HS].
        pose proof (tnr_refl_l p D ups _ (ind_ar D ups) H1 HnP HnI HaP HaI _ _ Hm) as Hmm.
        pose proof (tnr_refl_r p D ups _ (ind_ar D ups) H1 HnP HnI HaP HaI _ _ Hm) as Hmm'.
        pose proof (tar_pre_refl_l p D ups _ (ind_ar D ups) H1 HnP HnI HaP HaI ms c gs Hmm Hc k vs vs' ltac:(lia) Hp) as Hd.
        pose proof (tarp_refl_r p D ups _ (ind_ar D ups) H1 HnP HnI HaP HaI ms ms' c gs k vs vs' Hm Hc ltac:(lia) Hp) as Hd'.
        destruct (H4 _ _ _ _ _ _ Hmm Hc HS Hd) as [b Eb].
        pose proof (H7 _ _ _ _ _ _ _ Hmm Hc HS Hd Eb) as Hgb.
        pose proof (Hhd _ _ _ _ _ Eb Hgb) as Hpb.
        assert (Hn2 : AEl ms c k vs Γ0 A0 N n').
        { unfold ind_ar in Hnn; rewrite (nth_atyp_eq _ _ _ _ _ Hc HS) in Hnn.
          exact (H8 _ _ _ _ _ _ _ Hmm Hc HS Hd Eb _ Hpb _ _ _ _ _ HN Hnn). }
        destruct (HevA _ _ _ _ _ _ _ _ Hm Hc HS Hp) as (a & a' & Ea & Ea' & Haa).
        assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R0 => per_univ_elem i R0 b a') _ Haa) Hgb) as Hga'.
        pose proof (H7 _ _ _ _ _ _ _ Hmm' Hc HS Hd' Ea') as Hgb'.
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [_ HEq].
        apply HEq; exact Hn2. }
      assert (ER : R <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (Hmm' : elem_rel m m') by (apply ER; exact H13).
      assert (HPe : PER elem_rel) by (eapply per_elem_PER; eassumption).
      split; [ exact H12 | split; [ etransitivity; [ symmetry |]; exact Hmm' | exists H15; split; [ exact HPt |] ] ].
      intros Δ φ Ps' Hφ HPs'; pose proof (H17 Δ φ Ps' Hφ HPs') as Hg.
      exact (glu_ind_resp_per p D ups NEl AEl H1 Hcp Hadm HNe HAe _ _ _ _ Hg _ _ (proj1 (Herel _ _) Hmm')). }
  7:{ handle_per_univ_elem_irrel.
      apply_predicate_equivalence.
      destruct_by_head pi_glu_exp_pred.
      assert (PER elem_rel) by (eapply per_elem_PER; eassumption).
      econstructor; try eassumption.
      - etransitivity; [ symmetry |]; eassumption.
      - intros Δ φ N n Hk HN equiv_n.
        destruct (H11 _ _ _ _ Hk HN equiv_n) as (mn & Happ & HO).
        pose proof H6 as H6'.
        invert_per_univ_elem H6'.
        handle_per_univ_elem_irrel.
        destruct_rel_mod_eval.
        destruct (H8 n n equiv_n) as [mn0 mn' Happ0 Happ' Hmn].
        functional_eval_rewrite_clear.
        exists mn'; split; [ exact Happ' |].
        eapply H2; [ eassumption | eassumption | exact HO | exact Hmn ]. }
  all: match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H);
       apply_predicate_equivalence; simpl in *; destruct_conjs.
  - repeat split; try assumption.
    destruct (proj1 (H3 m m') H4) as [R' HR'].
    exists H2, H5; split; [ eapply glu_univ_elem_resp_per_univ; [ exists R'; exact HR' | exact H6 ] | exact H7 ].
  (** A small universe: as the large one, and the readback clause moves along
      the two types, which read back equally. *)
  - match goal with E : elem_rel <~> _, Hm : elem_rel m m' |- _ =>
      destruct (proj1 (E m m') Hm) as [R' HR'] end.
    repeat split; try assumption.
    + do 2 eexists; split; eassumption.
    + do 2 eexists; split;
        [ eapply glu_univ_elem_resp_per_univ; [ exists R'; exact HR' | eassumption ] | eassumption ].
    + intros * Hk Hr.
      match goal with Hrb : forall _ _ _, _ -> Rtyp m in _ ↘ _ -> _ |- _ => apply Hrb; [ exact Hk |] end.
      eapply per_top_typ_read_left; [ eapply per_univ_then_per_top_typ; exact HR' | exact Hr ].
  (** [Level]: the readback moves along the level PER. *)
  - assert (Dom m ≈ m' ∈ per_lvl_at n) as Hmm'
      by (match goal with E : _ <~> per_lvl_at _ |- _ => apply E; eassumption end).
    split; [| split ];
      [ assumption
      | eapply per_lvl_at_trans; [ eapply per_lvl_at_sym; exact Hmm' | exact Hmm' ]
      | eapply glu_lvl_resp_per; [ eassumption | eapply per_lvl_at_lvl; exact Hmm' ] ].
  (** [ℕ] *)
  - split; [ assumption | eapply glu_nat_resp_per; [ eassumption | apply H1; eassumption ] ].
  - split; assumption.
  - split; [ assumption | eapply glu_False_resp_per; [ eassumption | apply H1; eassumption ] ].
  - destruct_by_head neut_glu_exp_pred.
    match goal with E : _ <~> per_ne, Hm : _ ?x ?y |- _ => apply E in Hm; inversion Hm; subst end.
    econstructor; [ assumption | assumption | etransitivity; [ symmetry |]; eassumption |].
    intros * Hk Hr; eauto using per_bot_read_left.
Qed.

End Fixed_GCtx.
