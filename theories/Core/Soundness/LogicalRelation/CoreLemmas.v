From Stdlib Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Corollaries Substitution.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Records Require Import Typing.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From Mctt.Core.Soundness.Weakening Require Export Lemmas.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The same lemmas for [glu_lvl], which is the readback clause of a neutral at
    [Level]. *)
Lemma glu_lvl_escape : forall Γ M a n,
    Dom a ≈ a ∈ per_lvl ->
    glu_lvl n Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : Level@n.
Proof.
  intros * Hper H HΓ.
  assert (Γ ⊢ᵏ wk_id : Γ) by mauto 2.
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
Proof. intros; econstructor; eassumption. Qed.

(** It is deliberately not a hint: its conclusion is an existential whose
    witness the search cannot guess, and as a hint it also fires on the goals
    of the other universe clauses, whose predicate is an evar. *)

Lemma glu_lvl_readback : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ M',
      Δ ⊢ᵏ φ : Γ ->
      Rnf ⇓ Levelᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : Level@n.
Proof.
  intros * H * Hφ Hr; exact (proj1 (H _ _ _ Hφ Hr)).
Qed.

(** The readback of a glued level is a canonical level of its sort. *)
Lemma glu_lvl_ws_readback : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ M',
      Δ ⊢ᵏ φ : Γ ->
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

(** The same lemmas for [False_glu_elem], whose values are all neutral. *)
Lemma False_glu_elem_per_ne : forall Γ M a,
    False_glu_elem Γ M a ->
    Dom a ≈ a ∈ per_ne.
Proof.
  destruct 1; mauto.
Qed.

#[local]
Hint Resolve False_glu_elem_per_ne : mctt.

Lemma False_glu_elem_escape : forall Γ M a,
    False_glu_elem Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : ⊥.
Proof.
  destruct 1; intros.
  assert (Γ ⊢ᵏ wk_id : Γ) by mauto 2.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert (Γ ⊢ M[wk_id]ʷ ≈ M' : ⊥) as HM by mauto.
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve False_glu_elem_escape : mctt.

Lemma False_glu_elem_resp_ctxsub : forall Γ M a Δ,
    False_glu_elem Γ M a ->
    Δ ⊆ Γ ->
    False_glu_elem Δ M a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros; mauto 4.
Qed.

Hint Resolve False_glu_elem_resp_ctxsub : mctt.

Lemma False_glu_elem_resp_exp_eq : forall Γ M a,
    False_glu_elem Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : ⊥ ->
    False_glu_elem Γ M' a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros.
  transitivity M[φ]ʷ; mauto.
Qed.

#[local]
Hint Resolve False_glu_elem_resp_exp_eq : mctt.

Lemma False_glu_elem_readback : forall Γ M a,
    False_glu_elem Γ M a ->
    forall Δ φ M',
      Δ ⊢ᵏ φ : Γ ->
      Rnf ⇓ ⊥ᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : ⊥.
Proof.
  destruct 1; intros; progressive_inversion; gen_presups.
  mauto 4.
Qed.

(** ** The Elements of an Inductive Type *)

Lemma nonrec_prefix_pre : forall tr gs vs gs1 g gs2,
    tele_rel tr (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs) -> List.length vs = List.length gs ->
    gs = gs1 ++ g :: gs2 ->
    tele_prefix_rel tr (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
      (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)).
Proof.
  intros * H Hl Heq.
  assert (Hnv : List.firstn (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs vs) = nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)).
  { rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
    rewrite Heq at 1.
    rewrite nonrec_arg_vals_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
    rewrite firstn_app_exact by (apply length_nonrec_arg_vals; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
    reflexivity. }
  rewrite <- Hnv; apply tele_prefix_rel_of_full with (T := cargs_nonrec gs); [ exact H |].
  subst; rewrite cargs_nonrec_app, List.length_app; lia.
Qed.

Lemma nonrec_firstn : forall gs gs1 g gs2 vs, gs = gs1 ++ g :: gs2 -> List.length vs = List.length gs ->
    List.firstn (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs vs) = nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs).
Proof.
  intros * Heq Hl.
  rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
  rewrite Heq at 1.
  rewrite nonrec_arg_vals_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite firstn_app_exact by (apply length_nonrec_arg_vals; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  reflexivity.
Qed.

Lemma nonrec_nth_arg : forall gs gs1 A gs2 vs v, gs = gs1 ++ ca_arg A :: gs2 -> List.length vs = List.length gs ->
    List.nth_error vs (List.length gs1) = Some v ->
    List.nth_error (nonrec_arg_vals gs vs) (List.length (cargs_nonrec gs1)) = Some v.
Proof.
  intros * Heq Hl Hv; subst gs.
  rewrite <- (List.firstn_skipn (List.length gs1) vs) in Hv |- *.
  assert (Hl1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
    by (rewrite List.length_firstn; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite nonrec_arg_vals_app by exact Hl1.
  rewrite List.nth_error_app2 in Hv by lia; rewrite Hl1 in Hv.
  replace (List.length gs1 - List.length gs1) with 0 in Hv by lia.
  rewrite List.nth_error_app2 by (rewrite length_nonrec_arg_vals by exact Hl1; lia).
  rewrite length_nonrec_arg_vals by exact Hl1.
  replace (List.length (cargs_nonrec gs1) - List.length (cargs_nonrec gs1)) with 0 by lia.
  destruct (List.skipn (List.length gs1) vs) as [| v0 ws]; cbn in Hv |- *; [ discriminate | exact Hv ].
Qed.

(** A declared member's type at its parameters, and the position of a
    declared member among the members. *)
Lemma im_ty_at_decl : forall p k Mk pm Us Ns, im_head Mk = mh_decl pm ->
    im_ty_at p k Mk Us Ns = apps (a_ind p k) (Us ++ Ns).
Proof. intros * Hh; unfold im_ty_at, im_ref, im_pre; rewrite Hh; reflexivity. Qed.

Lemma decl_member_lt : forall Γ p D k Mk pm, ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D k = Some Mk -> im_head Mk = mh_decl pm -> k < ind_ndecl D.
Proof.
  intros * HΓ Hl HM Hh; destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD _].
  apply (dt_order _ _ _ HD _ _ HM); unfold im_is_decl; rewrite Hh; reflexivity.
Qed.

(** The two premises of a gluing clause on a family, read at every
    position: its types evaluate, and their values glue. *)
Lemma ind_case_N_helper : forall D ups (X : nat -> nat -> list domain -> Prop), grp_tele_ass D ->
    (forall m Mm j A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
       tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
    (forall m Mm j A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
       tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b -> X m j vs) ->
    forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
      X m j vs.
Proof.
  intros * Hass Hev HX m Mm j vs HM Hj Hp.
  destruct (nparams_lt_ass D m Mm j Hass HM ltac:(rewrite List.length_rev; exact Hj)) as [A HA].
  destruct (Hev _ _ _ _ _ HM HA Hp) as [b Hb]; exact (HX _ _ _ _ _ _ HM HA Hp Hb).
Qed.

Lemma ind_case_A_helper : forall D ups (X : nat -> list domain -> String.string -> nat -> list domain -> Prop),
    (forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
    (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b -> X m ms c j vs) ->
    forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
      j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> X m ms c j vs.
Proof.
  intros * Hev HX * HM Hms Hcon Hj Hp.
  destruct (nth_error_lt_some' (cargs_nonrec gs) j Hj) as [A HA].
  destruct (Hev _ _ _ _ _ _ _ _ HM Hms Hcon HA Hp) as [b Hb]; exact (HX _ _ _ _ _ _ _ _ _ HM Hms Hcon HA Hp Hb).
Qed.

Lemma map_wk_wk : forall (Ps : list exp) φ ψ,
    List.map (fun P => P[ψ]ʷ) (List.map (fun P => P[φ]ʷ) Ps) = List.map (fun P => P[φ ⊙ ψ]ʷ) Ps.
Proof. intros; rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_wk. Qed.

(** The readback of the parameters of related inductive types agrees. *)
Lemma glu_params_top_resp_per_top_ps : forall Dh Mh as1 as2 Γ Ps,
    per_top_ps (List.rev (im_params Dh Mh)) as1 as2 -> glu_params_top Dh Mh Γ Ps as1 -> glu_params_top Dh Mh Γ Ps as2.
Proof.
  intros * Ht [L Ht' Hr]; constructor; [ exact L | exact Ht' |].
  intros Δ φ Ms Hφ HR.
  destruct (Ht (length Δ)) as (C & HC1 & HC2).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack)))))) as Fps.
  rewrite (Fps _ _ _ _ _ HR _ HC2); exact (Hr _ _ _ Hφ HC1).
Qed.

Lemma glu_params_top_resp_per_top : forall hd Dh k Mh as1 as2 Γ Ps, ind_lookup gc_deps gc_stack hd = Some Dh ->
    ind_member Dh k = Some Mh ->
    Dom d_ind hd k as1 ≈ d_ind hd k as2 ∈ per_top_typ -> glu_params_top Dh Mh Γ Ps as1 -> glu_params_top Dh Mh Γ Ps as2.
Proof.
  intros * Hl HM Ht; apply glu_params_top_resp_per_top_ps.
  intros s; destruct (Ht s) as (C & HC1 & HC2).
  inversion HC2; subst; inversion HC1; subst.
  repeat match goal with H : ind_lookup _ _ hd = Some ?D1 |- _ =>
    assert_fails (unify D1 Dh); rewrite Hl in H; injection H as <- end.
  repeat match goal with H : ind_member Dh k = Some ?M1 |- _ =>
    assert_fails (unify M1 Mh); rewrite HM in H; injection H as <- end.
  eexists; split; eassumption.
Qed.

(** The relations of the domains of a shape at two representatives of
    the uniform parameters whose families agree, on the diagonal of a
    shape's context. *)
Lemma canon_doms_rel_agree : forall (p : qname) D ups ups',
    ind_fam_agree D (canon_nparams_rel D ups) (canon_nparams_rel D ups') (canon_args_rel D ups) (canon_args_rel D ups') (canon_doms_rel ups) (canon_doms_rel ups') ->
    forall m Mm ms c gs gs1 t gs2 ws k B ys, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
      gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
      List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) k ys ys ->
      (canon_doms_rel ups m (ms ++ ws ++ ys) B <~> canon_doms_rel ups' m (ms ++ ws ++ ys) B).
Proof.
  intros p D ups ups' Hag; destruct Hag as [Hfn Hfa Hfd]; intros * HM Hm Hc Heq Hw HB Hy.
  pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM) as F1.
  assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
  assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
    by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
  pose proof (F1 _ _ Hm) as Hm2.
  pose proof (tele_prefix_rel_ar_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs _ ws ws Hm Hm2 Hc HK Hw) as Hw2.
  pose proof (tele_prefix_rel_sh_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws k ys ys
                Hm Hm2 Hc Heq Hw Hw2 ltac:(lia) Hy) as Hy2.
  pose proof (Hfd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hm2 Hc Heq Hw Hw2 Hkl Hy Hy2) as Hdd.
  unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd; exact Hdd.
Qed.

(** The gluing of the type of a recursive argument moves along a
    representative [ups'] of the uniform parameters whose domains'
    relations agree, and along gluings of the domains whose types'
    contain the given ones, and whose elements' are contained in the given
    ones at the given types. *)
Lemma glu_shape_typ_change : forall (p : qname) D ups ups' m Mm (DP DP' : list domain -> exp -> glu_typ_pred)
    (DEl DEl' : list domain -> exp -> glu_exp_pred),
    grp_tele_ass D -> ind_canon_props D ups -> ind_member D m = Some Mm ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) k ys ys ->
       (canon_doms_rel ups m (ms ++ ws ++ ys) B <~> canon_doms_rel ups' m (ms ++ ws ++ ys) B)) ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) k ys ys ->
       (forall Γ A, DP (ms ++ ws ++ ys) B Γ A -> DP' (ms ++ ws ++ ys) B Γ A) /\
       (forall Γ A M n, DP (ms ++ ws ++ ys) B Γ A -> DEl' (ms ++ ws ++ ys) B Γ A M n -> DEl (ms ++ ws ++ ys) B Γ A M n)) ->
    forall t Γ pre T, glu_shape_typ (canon_doms_rel ups m) DP DEl Γ pre t T ->
      forall ms c0 gs1 t0 gs2 ws k ys, pre = ms ++ ws ++ ys ->
        tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
        ind_con Mm c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_prefix_rel (canon_args_rel D ups m ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
        ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t0)) k ys ys ->
        glu_shape_typ (canon_doms_rel ups' m) DP' DEl' Γ pre t T.
Proof.
  intros p D ups ups' m Mm DP DP' DEl DEl' Hass Hcp HM Hdr HD t.
  pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
  induction t as [? ? | B t IH]; intros Γ pre T H ms c0 gs1 t0 gs2 ws k ys Hpre Hm Hc Hw Hsk Hk Hy;
    cbn [glu_shape_typ] in *; [ exact I |].
  intros IT OT HT; destruct (H _ _ HT) as [H1 H2].
  destruct (shape_pi_step p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) Hass HnP HnI HaP HaI HdP HdI
              m Mm ms c0 gs1 t0 gs2 ws ws k ys ys B t HM Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
  subst pre.
  destruct (HD _ _ _ _ _ _ _ _ _ _ Hm Hc eq_refl Hw HB Hy) as [HDP HDEl].
  pose proof (Hdr _ _ _ _ _ _ _ _ _ _ Hm Hc eq_refl Hw HB Hy) as Edr.
  split.
  - intros Δ φ Hφ; exact (HDP _ _ (H1 Δ φ Hφ)).
  - intros Δ φ b c Hφ Hc' Hb.
    pose proof (proj2 (Edr _ _) Hc') as Hc0.
    eapply (IH _ _ _ (H2 Δ φ b c Hφ Hc0 (HDEl _ _ _ _ (H1 Δ φ Hφ) Hb)) ms c0 gs1 t0 gs2 ws (S k) (ys ++ c :: nil));
      [ rewrite <- !List.app_assoc; reflexivity | exact Hm | exact Hc | exact Hw | exact Hs' | exact Hk'
      | exact (Hstep _ _ Hc0) ].
Qed.

(** The components of an inductive type at a related representative of the
    uniform parameters. *)
Lemma ind_glu_comps_move : forall p D ups ups' NP NEl AP AEl DP DEl Γ Us,
    grp_tele_ass D -> ind_canon_props D ups ->
    ind_fam_agree D (canon_nparams_rel D ups) (canon_nparams_rel D ups') (canon_args_rel D ups) (canon_args_rel D ups') (canon_doms_rel ups) (canon_doms_rel ups') ->
    ind_glu_comps p D ups NP NEl AP AEl DP DEl Γ Us -> ind_glu_comps p D ups' NP NEl AP AEl DP DEl Γ Us.
Proof.
  intros * Hass Hcp Hag [HCN HCA HCR].
  pose proof (canon_doms_rel_agree p D ups ups' Hag) as Hdr.
  destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hag) as [Hfn' Hfa' Hfd'].
  destruct Hag as [Hfn Hfa Hfd].
  constructor.
  - intros * HM Hl Hk HT Hpre Hp.
    eapply HCN; [ exact HM | exact Hl | exact Hk | exact HT | exact Hpre |].
    eapply (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM);
      [ rewrite List.length_rev; unfold im_nn in Hk; lia | exact Hp ].
  - intros * HM Hc Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn' Hfa' Hfd' m Mm HM _ _ Hns) as Hns'.
    eapply HCA; [ exact HM | exact Hc | exact Heq | exact Hnp | exact Hns' | exact Hvl | exact HT | exact Hpre |].
    eapply (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM); [ exact Hns' | exact Hns | exact Hc | | exact Hp ].
    rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia.
  - intros * HM Hc Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn' Hfa' Hfd' m Mm HM _ _ Hns) as Hns'.
    assert (Hp' : tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
                    (nonrec_arg_vals gs1 vs)).
    { eapply (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM); [ exact Hns' | exact Hns | exact Hc | | exact Hp ].
      rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia. }
    pose proof (HCR _ _ _ _ _ _ _ _ _ _ _ _ HM Hc Heq Hnp Hns' Hvl HT Hpre Hp') as H.
    subst gs.
    exact (glu_shape_typ_change p D ups ups' m Mm (DP m) (DP m) (DEl m) (DEl m) Hass Hcp HM
             (fun ms0 c1 gs0 gs3 t1 gs4 ws0 k0 B0 ys0 Hm0 Hc0 Heq0 Hw0 HB0 Hy0 =>
                Hdr m Mm ms0 c1 gs0 gs3 t1 gs4 ws0 k0 B0 ys0 HM Hm0 Hc0 Heq0 Hw0 HB0 Hy0)
             ltac:(intros; split; intros; assumption)
             t Γ _ T H ns c gs1 t gs2 (nonrec_arg_vals gs1 vs) 0 nil ltac:(rewrite List.app_nil_r; reflexivity)
             Hns' Hc Hp' eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
Qed.

Lemma ind_typ_at_resp_per_top : forall p D ups ns ups' ns' NP NEl AP AEl DP DEl k Mk U Γ A Ps,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    grp_tele_ass D -> ind_canon_props D ups ->
    Dom d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_top_typ ->
    ind_fam_agree D (canon_nparams_rel D ups) (canon_nparams_rel D ups') (canon_args_rel D ups) (canon_args_rel D ups') (canon_doms_rel ups) (canon_doms_rel ups') ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A Ps -> ind_typ_at p D ups' ns' NP NEl AP AEl DP DEl k Mk U Γ A Ps.
Proof.
  intros * Hl HM Hass Hcp Ht Hfa (HA & Hk); split; [ exact HA |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & Hs & Hc); split;
    [ eapply glu_params_top_resp_per_top; eassumption
    | split; [ exact Hs | intros Us HUs; eapply ind_glu_comps_move; [ exact Hass | exact Hcp | exact Hfa | eauto ] ] ].
Qed.

(** The relation of a recursive argument's values. *)
Lemma con_args_rel_shape : forall p D Ok nr ar dr k u u' pre pre' gs vs vs', con_args_rel p D Ok nr ar dr k u u' pre pre' gs vs vs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists x x', List.nth_error vs (List.length gs1) = Some x /\ List.nth_error vs' (List.length gs1) = Some x' /\
      rec_arg_rel p D Ok nr ar dr k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) t x x'.
Proof.
  induction 1; intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst;
    try match goal with IH : forall _ _ _, _ = _ -> _ |- _ => destruct (IH _ _ _ eq_refl) as (x & x' & Hx & Hx' & Hr0) end.
  - exists x, x'; cbn; rewrite <- !List.app_assoc in Hr0; repeat split; assumption.
  - do 2 eexists; cbn; rewrite !List.app_nil_r; repeat split; eassumption.
  - exists x, x'; cbn; repeat split; assumption.
Qed.

Lemma con_args_rel_rec : forall p D Ok nr ar dr k u u' pre pre' gs vs vs', con_args_rel p D Ok nr ar dr k u u' pre pre' gs vs vs' ->
    forall gs1 Pr gs2 v v', gs = gs1 ++ ca_rec Pr :: gs2 ->
      List.nth_error vs (List.length gs1) = Some v -> List.nth_error vs' (List.length gs1) = Some v' ->
      rec_arg_rel p D Ok nr ar dr k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) Pr v v'.
Proof.
  intros * H * Heq Hv Hv'.
  destruct (con_args_rel_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ Heq) as (x & x' & Hx & Hx' & Hr).
  rewrite Hv in Hx; injection Hx as <-; rewrite Hv' in Hx'; injection Hx' as <-; exact Hr.
Qed.

Lemma con_args_rel_len : forall p D Ok nr ar dr k u u' pre pre' gs vs vs', con_args_rel p D Ok nr ar dr k u u' pre pre' gs vs vs' ->
    List.length vs = List.length gs /\ List.length vs' = List.length gs.
Proof. induction 1; cbn; lia. Qed.

Section GluIndProps.
  Variable (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hass : grp_tele_ass D) (Hcp : ind_canon_props D ups).
  Let nr := canon_nparams_rel D ups.
  Let ar := canon_args_rel D ups.
  Let dr := canon_doms_rel ups.

  Lemma glu_nparams_mono : forall NEl' : nat -> nat -> list domain -> glu_exp_pred,
      (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs ->
         forall Γ A M n, NEl m j vs Γ A M n -> NEl' m j vs Γ A M n) ->
      forall k Mk Γ Us Ns ns, ind_member D k = Some Mk -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns ->
        glu_nparams k Mk NEl Γ Us Ns ns -> glu_nparams k Mk NEl' Γ Us Ns ns.
  Proof.
    intros NEl' HN * HMk Hns [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
    intros j N A n HN0 HA Hn.
    assert (Hj : j < im_nn Mk) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    eapply HN; [ exact HMk | exact Hj | | exact (H _ _ _ _ HN0 HA Hn) ].
    apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk));
      [ exact Hns | rewrite List.length_rev; unfold im_nn in Hj; lia ].
  Qed.

  Lemma ind_glu_elem_resp_exp_eq : forall k Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m ->
      forall Mk M', ind_member D k = Some Mk -> Γ ⊢ M ≈ M' : im_ty_at p k Mk Us Ns ->
      ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M' m.
  Proof.
    intros * H; destruct H; intros Mk1 M' HM1 HMM;
      match goal with HA : ind_member D _ = Some ?A |- _ => assert_fails (unify A Mk1); rewrite HM1 in HA; injection HA as -> end.
    - eapply ind_glu_elem_con; try eassumption.
      etransitivity; [ symmetry; exact HMM | eassumption ].
    - eapply ind_glu_elem_neut; [ eassumption | eassumption | eassumption |].
      intros * Hφ Hrb.
      etransitivity; [| match goal with Hr : forall _ _ _, _ -> _ -> _ |- _ => eapply Hr; eassumption end ].
      symmetry; mauto 4.
  Qed.

  (** [ind_glu_elem] moves along a related representative [ups'] of the uniform
      parameters, and along gluings of the non-uniform parameters and of
      the non-recursive arguments that contain the given ones, and of the
      domains of the shapes contained in the given ones, their types'
      gluings containing the given ones. *)
  Lemma ind_glu_elem_move : forall ups' (NEl' : nat -> nat -> list domain -> glu_exp_pred)
      (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
      (DP' : nat -> list domain -> exp -> glu_typ_pred) (DEl' : nat -> list domain -> exp -> glu_exp_pred),
      ind_fam_agree D nr (canon_nparams_rel D ups') ar (canon_args_rel D ups') dr (canon_doms_rel ups') ->
      adm_uparams D ups nr ar dr ups' ->
      (forall j Mj bs bs', ind_member D j = Some Mj -> tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs' ->
         per_top_ps (List.rev (im_params D Mj)) (ups ++ bs) (ups' ++ bs')) ->
      (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs ->
         forall Γ A M n, NEl m j vs Γ A M n -> NEl' m j vs Γ A M n) ->
      (forall m Mm ms c gs j vs, ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms ->
         ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) ->
         tele_prefix_rel (ar m ms c) j vs vs -> forall Γ A M n, AEl m ms c j vs Γ A M n -> AEl' m ms c j vs Γ A M n) ->
      (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
         tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws -> List.nth_error (ptyp_doms t) j = Some B ->
         tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) j ys ys ->
         (forall Γ A, DP m (ms ++ ws ++ ys) B Γ A -> DP' m (ms ++ ws ++ ys) B Γ A) /\
         (forall Γ A M n, DEl' m (ms ++ ws ++ ys) B Γ A M n -> DEl m (ms ++ ws ++ ys) B Γ A M n)) ->
      forall k Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m ->
        ind_glu_elem p D ups' NEl' AEl' DP' DEl' k Γ Us Ns M m.
  Proof.
    intros ups' NEl' AEl' DP' DEl' Hag Hadm Hrbt HN HA HD.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hag) as [Hfn' Hfa' Hfd'].
    pose proof (canon_doms_rel_agree p D ups ups' Hag) as Hdr.
    destruct Hag as [Hfn Hfa Hfd].
    pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd) as F1.
    pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn' Hfa' Hfd') as F2.
    destruct Hadm as [_ _ Hcl _].
    apply (ind_glu_elem_mut_ind p D ups NEl AEl DP DEl
             (fun k Γ Us Ns M m _ => ind_glu_elem p D ups' NEl' AEl' DP' DEl' k Γ Us Ns M m)
             (fun k Γ Us pre t A N v _ => forall Mk ms c0 gs1 t0 gs2 ws kk ys, ind_member D k = Some Mk -> pre = ms ++ ws ++ ys ->
                tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
                ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
                ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
                tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) kk ys ys ->
                glu_rec p D ups' NEl' AEl' DP' DEl' k Γ Us pre t A N v)).
    - intros k Mk hd k' c gs Us Ns bs vs As Γ M HMk Href Hc HUl HNl Hbl Hvl HAl Heq Hnr Har Hnp Htyp Harg Hrec IHrec.
      eapply ind_glu_elem_con; [ exact HMk | exact Href | exact Hc | exact HUl | exact HNl | exact Hbl | exact Hvl | exact HAl
                               | exact Heq | | | | exact Htyp | | ].
      + exact (F1 _ _ HMk _ _ Hnr).
      + apply (tele_rel_map _ (ar k (List.skipn (im_unu D Mk) bs) c)); [| exact Har ].
        intros j pa pb x y Hj Hp1 Hp2 Hr.
        apply (Hfa _ _ _ _ _ _ _ _ _ _ _ HMk Hnr (F1 _ _ HMk _ _ Hnr) Hc Hj Hp1 Hp2); exact Hr.
      + eapply glu_nparams_mono; [ exact HN | exact HMk | exact Hnr | exact Hnp ].
      + intros * Heq0 HN0 HA0 Hv0.
        eapply HA; [ exact HMk | exact Hnr | exact Hc | | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ]
                   | exact (Harg _ _ _ _ _ _ Heq0 HN0 HA0 Hv0) ].
        rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia.
      + intros * Heq0 HN0 HA0 Hv0.
        apply (IHrec _ _ _ _ _ _ Heq0 HN0 HA0 Hv0 Mk (List.skipn (im_unu D Mk) bs) c gs1 t gs2
                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil);
          [ exact HMk | rewrite List.app_nil_r; reflexivity | exact Hnr | rewrite <- Heq0; exact Hc
          | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ] | reflexivity | lia | apply tele_prefix_rel_nil ].
    - intros; eapply ind_glu_elem_neut; eassumption.
    - intros j Mj Ps pre A Us Γ N x k HMj Hc1 Hc2 IH2 Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre Hm Hc Hw Hsk Hk Hy.
      destruct (ptyp_skip_self _ _ _ _ Hsk) as (HkL & Hj & HPs).
      assert (Hk1 : k1 = List.length (ptyp_doms t0)) by lia.
      assert (Hys : tele_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) (ptyp_doms t0) ys ys)
        by (apply tele_rel_of_pre; rewrite <- Hk1; exact Hy).
      (** The shape's parameters at [ups'] are related to those at [ups]. *)
      assert (Hev : forall bsr', ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ pre) ↘ bsr' ->
                 exists bsr, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr /\
                   tele_rel (nr j) (List.rev (im_nparams Mj)) bsr bsr').
      { intros bsr' Hbs'.
        destruct (Hcl k Mk ms ms c0 _ gs1 t0 gs2 ws ws ys ys HMk Hm Hc eq_refl Hw Hys) as [b0 b1 E0 E1 H01].
        rewrite HPs in E0, E1; subst pre.
        pose proof (functional_eval_exps' _ _ _ _ E1 Hbs') as ->.
        rewrite Hj in H01; unfold ntele_rel in H01; rewrite HMj in H01.
        exists b0; split; assumption. }
      apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
      + intros bsr' Q Hbs' HQ.
        destruct (Hev _ Hbs') as (bsr0 & E0 & H01).
        destruct (Hc1 _ _ E0 HQ) as (HQl & Hbt & Hgn).
        split; [ exact HQl | split ].
        * exact (F1 _ _ HMj _ _ (canon_nparams_rel_refl_r' p D ups Hass Hcp _ _ _ _ HMj H01)).
        * intros bsr'' Hb'.
          pose proof (canon_nparams_rel_trans p D ups Hass Hcp _ _ _ _ _ HMj H01 (F2 _ _ HMj _ _ Hb')) as H0'.
          pose proof (canon_nparams_rel_refl_r' p D ups Hass Hcp _ _ _ _ HMj H0') as H0''.
          destruct (Hgn _ H0') as [Hg1 Hg2].
          split; [ eapply glu_nparams_mono; [ exact HN | exact HMj | exact H0'' | exact Hg1 ] |].
          intros Δ φ Hφ; eapply glu_params_top_resp_per_top_ps; [ exact (Hrbt _ _ _ _ HMj H0'') | exact (Hg2 Δ φ Hφ) ].
      + intros bsr' Q Hbs' HQ Δ φ Us' Q' Hφ HUl' HQ'.
        destruct (Hev _ Hbs') as (bsr0 & E0 & _).
        exact (IH2 _ _ E0 HQ Δ φ Us' Q' Hφ HUl' HQ').
    - intros A Γ k pre B x Us t N Hd He Hg IH Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre Hm Hc Hw Hsk Hk Hy.
      destruct (shape_pi_step p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk ms c0 gs1 t0 gs2 ws ws k1 ys ys B t
                  HMk Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
      subst pre.
      destruct (HD _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as [HDP HDEl].
      pose proof (Hdr _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as Edr.
      apply glu_rec_pi.
      + intros * HA0 Δ φ Hφ; exact (HDP _ _ (Hd _ _ HA0 Δ φ Hφ)).
      + intros * HA0 Δ φ b0 c Hφ Hc' Hb.
        exact (He _ _ HA0 Δ φ b0 c Hφ (proj2 (Edr _ _) Hc') (HDEl _ _ _ _ Hb)).
      + intros * HA0 Δ φ b0 c fc Hφ Hc' Hb Hfc.
        pose proof (proj2 (Edr _ _) Hc') as Hc0.
        apply (IH _ _ HA0 Δ φ b0 c fc Hφ Hc0 (HDEl _ _ _ _ Hb) Hfc Mk ms c0 gs1 t0 gs2 ws (S k1) (ys ++ c :: nil));
          [ exact HMk | rewrite <- !List.app_assoc; reflexivity | exact Hm | exact Hc | exact Hw | exact Hs' | exact Hk'
          | exact (Hstep _ _ Hc0) ].
  Qed.

  Lemma ind_glu_elem_mono : forall (NEl' : nat -> nat -> list domain -> glu_exp_pred)
      (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
      (DP' : nat -> list domain -> exp -> glu_typ_pred) (DEl' : nat -> list domain -> exp -> glu_exp_pred),
      (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs ->
         forall Γ A M n, NEl m j vs Γ A M n -> NEl' m j vs Γ A M n) ->
      (forall m Mm ms c gs j vs, ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms ->
         ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) ->
         tele_prefix_rel (ar m ms c) j vs vs -> forall Γ A M n, AEl m ms c j vs Γ A M n -> AEl' m ms c j vs Γ A M n) ->
      (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
         tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws -> List.nth_error (ptyp_doms t) j = Some B ->
         tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) j ys ys ->
         (forall Γ A, DP m (ms ++ ws ++ ys) B Γ A -> DP' m (ms ++ ws ++ ys) B Γ A) /\
         (forall Γ A M n, DP m (ms ++ ws ++ ys) B Γ A -> DEl' m (ms ++ ws ++ ys) B Γ A M n -> DEl m (ms ++ ws ++ ys) B Γ A M n)) ->
      forall k Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m ->
        ind_glu_elem p D ups NEl' AEl' DP' DEl' k Γ Us Ns M m.
  Proof.
    intros NEl' AEl' DP' DEl' HN HA HD.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    apply (ind_glu_elem_mut_ind p D ups NEl AEl DP DEl
             (fun k Γ Us Ns M m _ => ind_glu_elem p D ups NEl' AEl' DP' DEl' k Γ Us Ns M m)
             (fun k Γ Us pre t A N v _ => forall Mk ms c0 gs1 t0 gs2 ws kk ys, ind_member D k = Some Mk -> pre = ms ++ ws ++ ys ->
                tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
                ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
                ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
                tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) kk ys ys ->
                glu_rec p D ups NEl' AEl' DP' DEl' k Γ Us pre t A N v)).
    - intros k Mk hd k' c gs Us Ns bs vs As Γ M HMk Href Hc HUl HNl Hbl Hvl HAl Heq Hnr Har Hnp Htyp Harg Hrec IHrec.
      eapply ind_glu_elem_con; [ exact HMk | exact Href | exact Hc | exact HUl | exact HNl | exact Hbl | exact Hvl | exact HAl
                               | exact Heq | exact Hnr | exact Har | | exact Htyp | | ].
      + eapply glu_nparams_mono; [ exact HN | exact HMk | exact Hnr | exact Hnp ].
      + intros * Heq0 HN0 HA0 Hv0.
        eapply HA; [ exact HMk | exact Hnr | exact Hc | | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ]
                   | exact (Harg _ _ _ _ _ _ Heq0 HN0 HA0 Hv0) ].
        rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia.
      + intros * Heq0 HN0 HA0 Hv0.
        apply (IHrec _ _ _ _ _ _ Heq0 HN0 HA0 Hv0 Mk (List.skipn (im_unu D Mk) bs) c gs1 t gs2
                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil);
          [ exact HMk | rewrite List.app_nil_r; reflexivity | exact Hnr | rewrite <- Heq0; exact Hc
          | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ] | reflexivity | lia | apply tele_prefix_rel_nil ].
    - intros; eapply ind_glu_elem_neut; eassumption.
    - intros j Mj Ps pre A Us Γ N x k HMj Hc1 Hc2 IH2 Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre Hm Hc Hw Hsk Hk Hy.
      apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
      + intros bsr Q Hbs HQ.
        destruct (Hc1 _ _ Hbs HQ) as (HQl & Hbt & Hgn).
        split; [ exact HQl | split; [ exact Hbt |] ].
        intros bsr' Hb'; destruct (Hgn _ Hb') as [Hg1 Hg2]; split; [| exact Hg2 ].
        eapply glu_nparams_mono; [ exact HN | exact HMj | exact (canon_nparams_rel_refl_r' p D ups Hass Hcp _ _ _ _ HMj Hb')
                                 | exact Hg1 ].
      + intros bsr Q Hbs HQ Δ φ Us' Q' Hφ HUl' HQ'; exact (IH2 _ _ Hbs HQ Δ φ Us' Q' Hφ HUl' HQ').
    - intros A Γ k pre B x Us t N Hd He Hg IH Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre Hm Hc Hw Hsk Hk Hy.
      destruct (shape_pi_step p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk ms c0 gs1 t0 gs2 ws ws k1 ys ys B t
                  HMk Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
      subst pre.
      destruct (HD _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as [HDP HDEl].
      apply glu_rec_pi.
      + intros * HA0 Δ φ Hφ; exact (HDP _ _ (Hd _ _ HA0 Δ φ Hφ)).
      + intros * HA0 Δ φ b0 c Hφ Hc' Hb; exact (He _ _ HA0 Δ φ b0 c Hφ Hc' (HDEl _ _ _ _ (Hd _ _ HA0 Δ φ Hφ) Hb)).
      + intros * HA0 Δ φ b0 c fc Hφ Hc' Hb Hfc.
        apply (IH _ _ HA0 Δ φ b0 c fc Hφ Hc' (HDEl _ _ _ _ (Hd _ _ HA0 Δ φ Hφ) Hb) Hfc Mk ms c0 gs1 t0 gs2 ws (S k1)
                 (ys ++ c :: nil));
          [ exact HMk | rewrite <- !List.app_assoc; reflexivity | exact Hm | exact Hc | exact Hw | exact Hs' | exact Hk'
          | exact (Hstep _ _ Hc') ].
  Qed.

  Lemma glu_nparams_resp_per :
      (forall m Mm j vs vs', ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs' ->
         forall Γ A N n n', NEl m j vs Γ A N n -> nr m j vs n n' -> NEl m j vs' Γ A N n') ->
      forall k Mk Γ Us Ns ns ns', ind_member D k = Some Mk -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns' ->
        glu_nparams k Mk NEl Γ Us Ns ns -> glu_nparams k Mk NEl Γ Us Ns ns'.
  Proof.
    intros HNe * HMk Hns [L1 L2 H].
    pose proof Hns as Hns'; rewrite tele_rel_iff in Hns'; destruct Hns' as (Hl & Hl' & Hr).
    rewrite List.length_rev in Hl, Hl'.
    constructor; [ exact L1 | exact Hl' |].
    intros j N A n' HN0 HA Hn'.
    assert (Hj : j < im_nn Mk) by (unfold im_nn; rewrite <- Hl'; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' ns j ltac:(unfold im_nn in Hj; lia)) as [n Hn].
    eapply HNe; [ exact HMk | exact Hj | | exact (H _ _ _ _ HN0 HA Hn) | exact (Hr _ _ _ Hn Hn') ].
    apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk));
      [ exact Hns | rewrite List.length_rev; unfold im_nn in Hj; lia ].
  Qed.

  (** [ind_glu_elem] at [ups] moves along the relation of the elements at
      the canonical relations, both bases [ups]. *)
  Lemma ind_glu_elem_resp_per :
      (forall m Mm j vs vs', ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs' ->
         forall Γ A N n n', NEl m j vs Γ A N n -> nr m j vs n n' -> NEl m j vs' Γ A N n') ->
      (forall m Mm ms ms' c gs j vs vs', ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
         ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) ->
         tele_prefix_rel (ar m ms c) j vs vs' -> forall Γ A N n n', AEl m ms c j vs Γ A N n -> ar m ms c j vs n n' ->
         AEl m ms' c j vs' Γ A N n') ->
      (forall m Mm ms ms' c gs gs1 t gs2 ws ws' j B ys ys', ind_member D m = Some Mm ->
         tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> ind_con Mm c = Some gs ->
         gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         List.nth_error (ptyp_doms t) j = Some B -> tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) j ys ys' ->
         (forall Γ A, DP m (ms ++ ws ++ ys) B Γ A -> DP m (ms' ++ ws' ++ ys') B Γ A) /\
         (forall Γ A N n, DEl m (ms' ++ ws' ++ ys') B Γ A N n -> DEl m (ms ++ ws ++ ys) B Γ A N n)) ->
      forall k Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m ->
      forall ns ns' m', ind_rel p D (okr_at D ups nr) nr ar dr k ups ups ns ns' m m' ->
        ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m'.
  Proof.
    intros HNe HAe HDe.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Sn.
    pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Tn.
    pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as RnR.
    pose proof (args_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Ia.
    pose proof (args_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Ta.
    pose proof (args_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Sa.
    apply (ind_glu_elem_mut_ind p D ups NEl AEl DP DEl
             (fun k Γ Us Ns M m _ => forall ns ns' m', ind_rel p D (okr_at D ups nr) nr ar dr k ups ups ns ns' m m' ->
                ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m')
             (fun k Γ Us pre t A N v _ => forall Mk ms ms' c0 gs1 t0 gs2 ws ws' kk ys ys' v', ind_member D k = Some Mk ->
                pre = ms ++ ws ++ ys -> tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms' ->
                ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws' ->
                ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
                tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) kk ys ys' ->
                rec_arg_rel p D (okr_at D ups nr) nr ar dr k ups ups pre (ms' ++ ws' ++ ys') t v v' ->
                glu_rec p D ups NEl AEl DP DEl k Γ Us (ms' ++ ws' ++ ys') t A N v')).
    2:{ (** A neutral: related neutrals read back equally. *)
        intros k Mk hd k' m Γ Us Ns M as' HMk Href Hm Hr ns ns' m' Hrel.
        inversion Hrel; subst.
        match goal with Hb : per_bot m ?m0 |- _ => rename m0 into e'; rename Hb into Hbe end.
        eapply ind_glu_elem_neut; [ exact HMk | exact Href | etransitivity; [ symmetry |]; exact Hbe |].
        intros Δ φ M' Hφ Hrb.
        destruct (Hbe (length Δ)) as (M0 & HM0 & HM0').
        pose proof (functional_read_ne _ _ _ _ Hrb HM0') as ->.
        exact (Hr _ _ _ Hφ HM0). }
    - (** A constructor: the related one has the same arguments' gluings, at
          the related values. *)
      intros k Mk hd k' c gs Us Ns bs vs As Γ M HMk Href Hc HUl HNl Hbl Hvl HAl Heq Hnr Har Hnp Htyp Harg Hrec IHrec
        ns ns' m' Hrel.
      destruct (ind_rel_con_inv p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel HMk Hbl)
        as (gs0 & bs' & vs' & -> & _ & Hns & Hc0 & Hbl' & Ho & Ho' & Ha & Hia).
      rewrite Hc in Hc0; injection Hc0 as <-.
      set (ms := List.skipn (im_unu D Mk) bs) in *; set (ms' := List.skipn (im_unu D Mk) bs') in *.
      assert (Hmm' : tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms')
        by exact (Tn _ _ HMk _ _ _ (Sn _ _ HMk _ _ Ho) (Tn _ _ HMk _ _ _ Hns Ho')).
      pose proof (RnR _ _ HMk _ _ Ho) as Hbb.
      assert (Hvl' : length vs' = length gs) by exact (proj2 (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia)).
      eapply ind_glu_elem_con; [ exact HMk | exact Href | exact Hc | exact HUl | exact HNl | exact Hbl' | exact Hvl' | exact HAl
                               | exact Heq | | | | exact Htyp | | ].
      + exact (RnR _ _ HMk _ _ Hmm').
      + exact (Ia _ _ HMk _ _ _ _ _ _ Hmm' Hc (Ta _ _ HMk _ _ _ Hbb Hc _ _ _ (Sa _ _ HMk _ _ _ Hbb Hc _ _ Ha) Ha)).
      + exact (glu_nparams_resp_per HNe _ _ _ _ _ _ _ HMk Hmm' Hnp).
      + intros gs1 A0 gs2 N A v' Heq0 HN0 HA0 Hv0'.
        assert (Hlt : length gs1 < length vs) by (rewrite Hvl, Heq0, List.length_app; cbn; lia).
        destruct (nth_error_lt_some' vs (length gs1) Hlt) as [v Hv0].
        assert (HK : length (cargs_nonrec gs1) < length (cargs_nonrec gs))
          by (rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia).
        assert (HK' : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by lia.
        pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq0 Hvl Hv0) as Hn1.
        pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq0 Hvl' Hv0') as Hn2.
        pose proof Ha as Ha'; rewrite tele_rel_iff in Ha'; destruct Ha' as (_ & _ & Har').
        pose proof (Har' _ _ _ Hn1 Hn2) as Hvv.
        rewrite (nonrec_firstn _ _ _ _ _ Heq0 Hvl) in Hvv.
        pose proof (tele_prefix_rel_of_full _ _ _ _ (length (cargs_nonrec gs1)) Ha HK') as Hpre.
        rewrite (nonrec_firstn _ _ _ _ _ Heq0 Hvl), (nonrec_firstn _ _ _ _ _ Heq0 Hvl') in Hpre.
        eapply HAe; [ exact HMk | exact Hmm' | exact Hc | exact HK | exact Hpre
                    | exact (Harg _ _ _ _ _ _ Heq0 HN0 HA0 Hv0) | exact Hvv ].
      + intros gs1 t gs2 N A v' Heq0 HN0 HA0 Hv0'.
        assert (Hlt : length gs1 < length vs) by (rewrite Hvl, Heq0, List.length_app; cbn; lia).
        destruct (nth_error_lt_some' vs (length gs1) Hlt) as [v Hv0].
        assert (HK' : length (cargs_nonrec gs1) <= length (cargs_nonrec gs))
          by (rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia).
        pose proof (tele_prefix_rel_of_full _ _ _ _ (length (cargs_nonrec gs1)) Ha HK') as Hpre.
        rewrite (nonrec_firstn _ _ _ _ _ Heq0 Hvl), (nonrec_firstn _ _ _ _ _ Heq0 Hvl') in Hpre.
        pose proof (con_args_rel_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia _ _ _ _ _ Heq0 Hv0 Hv0') as Hsh.
        pose proof (IHrec _ _ _ _ _ _ Heq0 HN0 HA0 Hv0 Mk ms ms' c gs1 t gs2 _ _ 0 nil nil v' HMk
                      ltac:(rewrite List.app_nil_r; reflexivity) Hmm' ltac:(rewrite <- Heq0; exact Hc)
                      Hpre eq_refl ltac:(lia) (tele_prefix_rel_nil _) ltac:(rewrite List.app_nil_r; exact Hsh)) as H.
        rewrite List.app_nil_r in H; exact H.
    - intros j Mj Ps pre A Us Γ N x k HMj Hc1 Hc2 IH2 Mk ms ms' c0 gs1 t0 gs2 ws ws' k1 ys ys' v' HMk Hpre Hm Hc Hw Hsk Hk Hy
        Hsh.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs' & Ebs & Ebs' & _ & _ & Hvv).
      pose proof (ind_rel_ns p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ HMj Hvv) as H01.
      apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
      + intros bsr' Q Hbs' HQ.
        pose proof (functional_eval_exps' _ _ _ _ Ebs' Hbs') as ->.
        destruct (Hc1 _ _ Ebs HQ) as (HQl & _ & Hgn).
        split; [ exact HQl | split; [ exact (RnR _ _ HMj _ _ H01) |] ].
        intros bsr'' Hb''; exact (Hgn _ (Tn _ _ HMj _ _ _ H01 Hb'')).
      + intros bsr' Q Hbs' HQ Δ φ Us' Q' Hφ HUl' HQ'.
        pose proof (functional_eval_exps' _ _ _ _ Ebs' Hbs') as ->.
        exact (IH2 _ _ Ebs HQ Δ φ Us' Q' Hφ HUl' HQ' _ _ _ Hvv).
    - intros A Γ k pre B x Us t N Hd He Hg IH Mk ms ms' c0 gs1 t0 gs2 ws ws' k1 ys ys' v' HMk Hpre Hm Hc Hw Hsk Hk Hy Hsh.
      destruct (shape_pi_step p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk ms c0 gs1 t0 gs2 ws ws' k1 ys ys' B t
                  HMk (Tn _ _ HMk _ _ _ Hm (Sn _ _ HMk _ _ Hm)) Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
      subst pre.
      destruct (HDe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as [HDP HDEl].
      pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as Edr.
      apply glu_rec_pi.
      + intros * HA0 Δ φ Hφ; exact (HDP _ _ (Hd _ _ HA0 Δ φ Hφ)).
      + intros * HA0 Δ φ b0 c Hφ Hc' Hb.
        pose proof (proj2 (Edr _ _) Hc') as Hc0.
        destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hc0) as (r & r' & Er & Er' & _).
        exists r'; exact Er'.
      + intros * HA0 Δ φ b0 c fc' Hφ Hc' Hb Hfc'.
        pose proof (proj2 (Edr _ _) Hc') as Hc0.
        destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hc0) as (r & r' & Er & Er' & Hsh').
        pose proof (functional_eval_app _ _ _ _ Er' Hfc') as ->.
        replace ((ms' ++ ws' ++ ys') ++ c :: nil) with (ms' ++ ws' ++ ys' ++ c :: nil) in Hsh' |- *
          by (rewrite <- !List.app_assoc; reflexivity).
        apply (IH _ _ HA0 Δ φ b0 c r Hφ Hc0 (HDEl _ _ _ _ Hb) Er Mk ms ms' c0 gs1 t0 gs2 ws ws' (S k1)
                 (ys ++ c :: nil) (ys' ++ c :: nil) fc');
          [ exact HMk | rewrite <- !List.app_assoc; reflexivity | exact Hm | exact Hc | exact Hw | exact Hs' | exact Hk'
          | exact (Hstep _ _ Hc0) | exact Hsh' ].
  Qed.
End GluIndProps.


(** The monotonicity premises on the families of a group's clause: the
    types' gluings grow, the elements' shrink. *)
Lemma ind_glu_comps_mono : forall p D ups NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' Γ Us,
    grp_tele_ass D -> ind_canon_props D ups ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\ (forall Γ T N n, NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
       (forall Γ T N n, AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
       (forall Γ A, DP m (ms ++ ws ++ ys) B Γ A -> DP' m (ms ++ ws ++ ys) B Γ A) /\
       (forall Γ A M n, DP m (ms ++ ws ++ ys) B Γ A -> DEl' m (ms ++ ws ++ ys) B Γ A M n -> DEl m (ms ++ ws ++ ys) B Γ A M n)) ->
    ind_glu_comps p D ups NP NEl AP AEl DP DEl Γ Us -> ind_glu_comps p D ups NP' NEl' AP' AEl' DP' DEl' Γ Us.
Proof.
  intros * Hass Hcp HN HA HD [HCN HCA HCR].
  assert (HNm : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
                forall Γ A M n, NEl' m j vs Γ A M n -> NEl m j vs Γ A M n)
    by (intros * HM Hj Hp; exact (proj2 (HN _ _ _ _ HM Hj Hp))).
  (** The non-recursive arguments before an argument, glued at the given
      gluings. *)
  assert (Hargs : forall m Mm c gs gs1 gs2 g Ns ns As vs, ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
            gs = gs1 ++ g :: gs2 ->
            tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns -> List.length vs = List.length gs1 ->
            tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
              (nonrec_arg_vals gs1 vs) ->
            (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
               List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
               List.nth_error vs (List.length hs1) = Some v ->
               Γ ⊢ N : T' ® v ∈ AEl' m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
            (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
               List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
               List.nth_error vs (List.length hs1) = Some v ->
               Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)))).
  { intros m Mm c gs gs1 gs2 g Ns ns As vs HM Hc Heq Hns Hvl Hp Hpre hs1 B hs2 N T' v Heq1 HN0 HT' Hv.
    assert (HK1 : List.length (cargs_nonrec hs1) < List.length (cargs_nonrec gs))
      by (rewrite Heq, Heq1, !cargs_nonrec_app, !List.length_app; cbn; lia).
    assert (Hpre1 : tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec hs1))
                      (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
    { pose proof (tele_prefix_rel_of_pre _ _ _ _ (List.length (cargs_nonrec hs1)) Hp
                    ltac:(rewrite Heq1, cargs_nonrec_app, List.length_app; cbn; lia)) as Hq.
      rewrite (nonrec_firstn _ _ _ _ _ Heq1 Hvl) in Hq; exact Hq. }
    apply (proj2 (HA _ _ _ _ _ _ _ HM Hns Hc HK1 Hpre1)).
    eapply Hpre; eassumption. }
  constructor.
  - intros m Mm k Ns ns T HM Hl Hk HT Hpre Hp.
    apply (proj1 (HN m Mm k ns HM Hk Hp)).
    apply (HCN m Mm k Ns ns T HM Hl Hk HT); [| exact Hp ].
    intros j N T' n Hj HN0 HT' Hn.
    assert (Hpj : tele_prefix_rel (canon_nparams_rel D ups m) j (List.firstn j ns) (List.firstn j ns))
      by exact (tele_prefix_rel_of_pre _ _ _ _ j Hp ltac:(lia)).
    apply (proj2 (HN m Mm j (List.firstn j ns) HM ltac:(lia) Hpj)).
    apply Hpre; assumption.
  - intros m Mm c gs gs1 A0 gs2 Ns ns As vs T HM Hc Heq Hnp Hns Hvl HT Hpre Hp.
    assert (HK : List.length (cargs_nonrec gs1) < List.length (cargs_nonrec gs))
      by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
    apply (proj1 (HA _ _ _ _ _ _ _ HM Hns Hc HK Hp)).
    eapply HCA; [ exact HM | exact Hc | exact Heq | | exact Hns | exact Hvl | exact HT | | exact Hp ].
    + eapply (glu_nparams_mono D ups NEl'); [ exact HNm | exact HM | exact Hns | exact Hnp ].
    + exact (Hargs _ _ _ _ _ _ _ _ _ _ _ HM Hc Heq Hns Hvl Hp Hpre).
  - intros m Mm c gs gs1 t gs2 Ns ns As vs T HM Hc Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (HCR m Mm c gs gs1 t gs2 Ns ns As vs T HM Hc Heq
                  ltac:(eapply (glu_nparams_mono D ups NEl'); [ exact HNm | exact HM | exact Hns | exact Hnp ])
                  Hns Hvl HT (Hargs _ _ _ _ _ _ _ _ _ _ _ HM Hc Heq Hns Hvl Hp Hpre) Hp) as H.
    subst gs.
    exact (glu_shape_typ_change p D ups ups m Mm (DP m) (DP' m) (DEl m) (DEl' m) Hass Hcp HM ltac:(intros; reflexivity)
             (fun ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 Hm0 Hc0 Heq0 Hw0 HB0 Hy0 =>
                HD m Mm ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 HM Hm0 Hc0 Heq0 Hw0 HB0 Hy0)
             t Γ _ T H ns c gs1 t gs2 (nonrec_arg_vals gs1 vs) 0 nil ltac:(rewrite List.app_nil_r; reflexivity)
             Hns Hc Hp eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
Qed.

Lemma ind_typ_at_mono : forall p D ups ns NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' k Mk U Γ A Ps,
    grp_tele_ass D -> ind_canon_props D ups ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\ (forall Γ T N n, NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
       (forall Γ T N n, AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
       (forall Γ A, DP m (ms ++ ws ++ ys) B Γ A -> DP' m (ms ++ ws ++ ys) B Γ A) /\
       (forall Γ A M n, DP m (ms ++ ws ++ ys) B Γ A -> DEl' m (ms ++ ws ++ ys) B Γ A M n -> DEl m (ms ++ ws ++ ys) B Γ A M n)) ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A Ps -> ind_typ_at p D ups ns NP' NEl' AP' AEl' DP' DEl' k Mk U Γ A Ps.
Proof.
  intros * Hass Hcp HN HA HD (HA0 & Hk); split; [ exact HA0 |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as (Hpt & Hs & Hc).
  split; [ exact Hpt | split; [ exact Hs | intros Us HUs; eapply ind_glu_comps_mono;
                                           [ exact Hass | exact Hcp | exact HN | exact HA | exact HD | eauto ] ] ].
Qed.

(** The type predicate of an inductive type, along an equation, a context
    refinement and a weakening. *)
Lemma wk_apps_ind : forall p k Ps φ, (apps (a_ind p k) Ps)[φ]ʷ = apps (a_ind p k) (List.map (fun P => P[φ]ʷ) Ps).
Proof. intros; rewrite apps_exp_wk; reflexivity. Qed.

Lemma ind_typ_at_resp_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A A' Ps,
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Γ ⊢ A ≈ A' : Typeω@n ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A' Ps.
Proof.
  intros * (HA & Hk) HAA; split; [ etransitivity; [ symmetry; exact HAA | exact HA ] | exact Hk ].
Qed.

Lemma ind_typ_at_resp_ctxsub : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Ps Δ,
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Δ ⊆ Γ ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A Ps.
Proof.
  intros * (HA & Hk) Hs; split; [ eapply ctxsub_exp_eq; [ exact (ctx_sub_escape _ _ _ _ Hs) | exact HA ] |].
  intros Θ ψ Hψ; apply Hk; eapply kripke_ctxsub; eassumption.
Qed.

Lemma ind_typ_at_wk : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Ps Δ φ,
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Δ ⊢ᵏ φ : Γ ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A[φ]ʷ (List.map (fun P => P[φ]ʷ) Ps).
Proof.
  intros * (HA & Hk) Hφ; split; [ rewrite <- wk_apps_ind; mauto 3 |].
  intros Θ ψ Hψ; rewrite !map_wk_wk; apply Hk; eapply kripke_compose; eassumption.
Qed.

(** The type at the parameters of a type predicate is the one at equal
    ones. *)
Lemma ind_typ_at_params_conv : forall p D ups ns NP NEl AP AEl DP DEl k Mk pm n Γ A Ps Δ φ Ps',
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Δ ⊢ᵏ φ : Γ ->
    exps_eq_at Δ (im_params D Mk) (List.map (fun P => P[φ]ʷ) Ps) Ps' ->
    Δ ⊢ apps (a_ind p k) (List.map (fun P => P[φ]ʷ) Ps) ≈ apps (a_ind p k) Ps' : Typeω@n.
Proof.
  intros * Hl HMk Hh (_ & Hk) Hφ [HlP HPP].
  destruct (Hk _ _ Hφ) as ([HPl _ _] & Hs & _).
  assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
  eapply wf_exp_eq_subtyp'; [| exact Hs ].
  eapply wf_exp_eq_ind_apps; [ exact Hl | exact HMk | exact (decl_member_lt _ _ _ _ _ _ HΔ Hl HMk Hh) | exact HΔ
                             | exact HPl | lia | exact HPP ].
Qed.

Lemma ind_glu_typ_pred_resp_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A A',
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A -> Γ ⊢ A ≈ A' : Typeω@n ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A'.
Proof. intros * (Ps & HPs) HAA; exists Ps; eapply ind_typ_at_resp_exp_eq; eassumption. Qed.

Lemma ind_glu_typ_pred_resp_ctxsub : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Δ,
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A -> Δ ⊆ Γ ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A.
Proof. intros * (Ps & HPs) Hs; exists Ps; eapply ind_typ_at_resp_ctxsub; eassumption. Qed.

Lemma ind_glu_typ_pred_wk : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Δ φ,
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A -> Δ ⊢ᵏ φ : Γ ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A[φ]ʷ.
Proof. intros * (Ps & HPs) Hφ; eexists; eapply ind_typ_at_wk; eassumption. Qed.

Lemma ind_glu_exp_pred_resp_typ_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk R n Γ A A' M m,
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M m -> Γ ⊢ A ≈ A' : Typeω@n ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A' M m.
Proof.
  intros * [HM Hm Ps HPs Hk] HAA.
  refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Ps _ Hk);
    [ eapply wf_conv'; [ exact HM | exact HAA ] | eapply ind_typ_at_resp_exp_eq; eassumption ].
Qed.

Lemma ind_glu_exp_pred_wk : forall p D ups ns NP NEl AP AEl DP DEl k Mk R n Γ A M m Δ φ,
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M m -> Δ ⊢ᵏ φ : Γ ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Δ A[φ]ʷ M[φ]ʷ m.
Proof.
  intros * [HM Hm Ps HPs Hk] Hφ.
  refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm (List.map (fun P => P[φ]ʷ) Ps) _ _);
    [ mauto 3 | eapply ind_typ_at_wk; eassumption |].
  intros Θ ψ Ps' Hψ HPs'; rewrite map_wk_wk in HPs'; rewrite exp_wk_wk; apply Hk; [ eapply kripke_compose; eassumption | exact HPs' ].
Qed.

Lemma ind_glu_exp_pred_resp_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk pm R n Γ A M M' m,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M m -> Γ ⊢ M ≈ M' : A ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M' m.
Proof.
  intros * Hl HMk Hh [HM Hm Ps HPs Hk] HMM.
  refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Ps HPs _); [ mauto 3 |].
  intros Δ φ Ps' Hφ HPs'.
  eapply ind_glu_elem_resp_exp_eq; [ exact (Hk Δ φ Ps' Hφ HPs') | exact HMk |].
  rewrite (im_ty_at_decl _ _ _ _ _ _ Hh), List.firstn_skipn.
  pose proof (ind_typ_at_params_conv p D ups ns NP NEl AP AEl DP DEl k Mk pm n Γ A Ps Δ φ Ps' Hl HMk Hh HPs Hφ HPs') as HPP.
  rewrite <- wk_apps_ind in HPP.
  destruct HPs as [HA _].
  assert (Γ ⊢ M ≈ M' : apps (a_ind p k) Ps) by (eapply wf_exp_eq_conv'; eassumption).
  eapply wf_exp_eq_conv'; [| exact HPP ].
  mauto 3.
Qed.

(** ** Record Types

    The type and element predicates of a record type, along an equation, a
    context refinement and a weakening. *)
Lemma wk_apps_record : forall p Ps φ, (apps (a_record p) Ps)[φ]ʷ = apps (a_record p) (List.map (fun P => P[φ]ʷ) Ps).
Proof. intros; rewrite apps_exp_wk; reflexivity. Qed.

Lemma record_typ_at_resp_exp_eq : forall p R ns FP FEl n Γ A A' Ns,
    record_typ_at p R ns FP FEl Typeω@n Γ A Ns -> Γ ⊢ A ≈ A' : Typeω@n ->
    record_typ_at p R ns FP FEl Typeω@n Γ A' Ns.
Proof.
  intros * [HA Hk] HAA; constructor; [ etransitivity; [ symmetry; exact HAA | exact HA ] | exact Hk ].
Qed.

Lemma record_typ_at_resp_ctxsub : forall p R ns FP FEl n Γ A Ns Δ,
    record_typ_at p R ns FP FEl Typeω@n Γ A Ns -> Δ ⊆ Γ ->
    record_typ_at p R ns FP FEl Typeω@n Δ A Ns.
Proof.
  intros * [HA Hk] Hs; constructor; [ eapply ctxsub_exp_eq; [ exact (ctx_sub_escape _ _ _ _ Hs) | exact HA ] |].
  intros Θ ψ Hψ; apply Hk; eapply kripke_ctxsub; eassumption.
Qed.

Lemma record_typ_at_wk : forall p R ns FP FEl n Γ A Ns Δ φ,
    record_typ_at p R ns FP FEl Typeω@n Γ A Ns -> Δ ⊢ᵏ φ : Γ ->
    record_typ_at p R ns FP FEl Typeω@n Δ A[φ]ʷ (List.map (fun N => N[φ]ʷ) Ns).
Proof.
  intros * [HA Hk] Hφ; constructor; [ rewrite <- wk_apps_record; mauto 3 |].
  intros Θ ψ Hψ; rewrite !map_wk_wk; apply Hk; eapply kripke_compose; eassumption.
Qed.

Lemma record_glu_typ_pred_resp_exp_eq : forall p R ns FP FEl n Γ A A',
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A -> Γ ⊢ A ≈ A' : Typeω@n ->
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A'.
Proof. intros * (Ns & HNs) HAA; exists Ns; eapply record_typ_at_resp_exp_eq; eassumption. Qed.

Lemma record_glu_typ_pred_resp_ctxsub : forall p R ns FP FEl n Γ A Δ,
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A -> Δ ⊆ Γ ->
    record_glu_typ_pred p R ns FP FEl Typeω@n Δ A.
Proof. intros * (Ns & HNs) Hs; exists Ns; eapply record_typ_at_resp_ctxsub; eassumption. Qed.

Lemma record_glu_typ_pred_wk : forall p R ns FP FEl n Γ A Δ φ,
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A -> Δ ⊢ᵏ φ : Γ ->
    record_glu_typ_pred p R ns FP FEl Typeω@n Δ A[φ]ʷ.
Proof. intros * (Ns & HNs) Hφ; eexists; eapply record_typ_at_wk; eassumption. Qed.

Lemma record_glu_exp_pred_resp_typ_exp_eq : forall p R ns FP FEl elem_rel n Γ A A' M m,
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M m -> Γ ⊢ A ≈ A' : Typeω@n ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A' M m.
Proof.
  intros * [HM Hm Ns HNs vs Hvs Hk] HAA.
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm Ns _ vs Hvs Hk);
    [ eapply wf_conv'; [ exact HM | exact HAA ] | eapply record_typ_at_resp_exp_eq; eassumption ].
Qed.

Lemma record_glu_exp_pred_wk : forall p R ns FP FEl elem_rel n Γ A M m Δ φ,
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M m -> Δ ⊢ᵏ φ : Γ ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Δ A[φ]ʷ M[φ]ʷ m.
Proof.
  intros * [HM Hm Ns HNs vs Hvs Hk] Hφ.
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm (List.map (fun N => N[φ]ʷ) Ns) _ vs Hvs _);
    [ mauto 3 | eapply record_typ_at_wk; eassumption |].
  intros Θ ψ Ns' Hψ HNs'; rewrite map_wk_wk in HNs'; rewrite exp_wk_wk.
  apply Hk; [ eapply kripke_compose; eassumption | exact HNs' ].
Qed.

(** The predicates of a record type at two families of field gluings
    equivalent along related prefixes. *)
Definition record_fams_equiv (R : record_decl) (ns : list domain)
    (FP FP' : nat -> list domain -> glu_typ_pred) (FEl FEl' : nat -> list domain -> glu_exp_pred) : Prop :=
  forall k f T vs, List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel (canon_fields_rel R ns) k vs vs ->
    (FP k vs <∙> FP' k vs) /\ (FEl k vs <∙> FEl' k vs).

Lemma record_fields_glu_mono : forall R ns FP FEl FP' FEl' Γ Ns,
    record_fams_equiv R ns FP FP' FEl FEl' ->
    record_fields_glu R ns FP FEl Γ Ns -> record_fields_glu R ns FP' FEl' Γ Ns.
Proof.
  intros * Heq Hg k f T Ms ms Hk HMl Hml HMs Hp.
  destruct (Heq _ _ _ _ Hk Hp) as [EP _]; apply EP.
  apply (Hg k f T Ms ms); [ exact Hk | exact HMl | exact Hml | | exact Hp ].
  intros j g T' M m0 Hj HM Hm.
  assert (Hjk : j < k) by (rewrite <- Hml; apply List.nth_error_Some; congruence).
  destruct (Heq _ _ _ _ Hj (tele_prefix_rel_of_pre _ _ _ _ j Hp ltac:(lia))) as [_ EE]; apply EE.
  exact (HMs _ _ _ _ _ Hj HM Hm).
Qed.

Lemma record_typ_at_mono : forall p R ns FP FEl FP' FEl' U Γ A Ns,
    record_fams_equiv R ns FP FP' FEl FEl' ->
    record_typ_at p R ns FP FEl U Γ A Ns -> record_typ_at p R ns FP' FEl' U Γ A Ns.
Proof.
  intros * Heq [HA Hk]; constructor; [ exact HA |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hp Hs Hf]; constructor; [ exact Hp | exact Hs |].
  intros Ns' HNs'; exact (record_fields_glu_mono _ _ _ _ _ _ _ _ Heq (Hf Ns' HNs')).
Qed.

(** At related parameters: the readbacks agree, and the prefixes of the
    other side's canonical relations are the first side's. *)
Lemma params_glu_top_resp_per_top_ps : forall T ps ps' Γ Ps,
    per_top_ps (List.rev T) ps ps' -> params_glu_top T Γ Ps ps -> params_glu_top T Γ Ps ps'.
Proof.
  intros * Ht [L Ht' Hr]; constructor; [ exact L | exact Ht' |].
  intros Δ φ Ms Hφ HR.
  destruct (Ht (length Δ)) as (C & HC1 & HC2).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack)))))) as Fps.
  rewrite (Fps _ _ _ _ _ HR _ HC2); exact (Hr _ _ _ Hφ HC1).
Qed.

Lemma record_typ_at_resp_per : forall p R ns ns' FP FEl U Γ A Ns,
    per_top_ps (List.rev (record_params R)) ns ns' ->
    (forall k vs, k <= List.length (record_fields R) ->
       tele_prefix_rel (canon_fields_rel R ns') k vs vs -> tele_prefix_rel (canon_fields_rel R ns) k vs vs) ->
    record_typ_at p R ns FP FEl U Γ A Ns -> record_typ_at p R ns' FP FEl U Γ A Ns.
Proof.
  intros * Ht Hmv [HA Hk]; constructor; [ exact HA |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hp Hs Hf]; constructor;
    [ exact (params_glu_top_resp_per_top_ps _ _ _ _ _ Ht Hp) | exact Hs |].
  intros Ns' HNs' k f T Ms ms Hfk HMl Hml HMs Hpre.
  assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  exact (Hf Ns' HNs' k f T Ms ms Hfk HMl Hml HMs (Hmv k ms ltac:(lia) Hpre)).
Qed.

(** The projections of an element related to itself are related to
    themselves, prefix by prefix. *)
Lemma record_projs_prefix_diag : forall R ns m vs k,
    record_rel R (canon_fields_rel R ns) m m -> record_projs R m vs -> k <= List.length (record_fields R) ->
    tele_prefix_rel (canon_fields_rel R ns) k (List.firstn k vs) (List.firstn k vs).
Proof.
  intros * [vs1 vs2 H1 H2 Hrel] Hvs Hk.
  pose proof (record_projs_functional _ _ _ _ H1 Hvs) as ->; pose proof (record_projs_functional _ _ _ _ H2 Hvs) as ->.
  exact (tele_prefix_rel_of_full _ _ _ _ _ Hrel Hk).
Qed.

Lemma record_glu_exp_mono : forall p R ns FP FEl FP' FEl' elem_rel elem_rel' U Γ A M m,
    record_fams_equiv R ns FP FP' FEl FEl' -> (elem_rel <~> elem_rel') ->
    (elem_rel <~> record_rel R (canon_fields_rel R ns)) ->
    record_glu_exp p R ns FP FEl elem_rel U Γ A M m -> record_glu_exp p R ns FP' FEl' elem_rel' U Γ A M m.
Proof.
  intros * Heq HEE HE [HM Hm Ns HNs vs Hvs Hk].
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ (proj1 (HEE _ _) Hm) Ns
            (record_typ_at_mono _ _ _ _ _ _ _ _ _ _ _ Heq HNs) vs Hvs _); [ exact HM |].
  intros Δ φ Ns' Hφ HNs' k f T r Hfk Hr.
  assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  destruct (Heq _ _ _ _ Hfk (record_projs_prefix_diag _ _ _ _ k (proj1 (HE _ _) Hm) Hvs ltac:(lia))) as [_ EE].
  apply EE; exact (Hk Δ φ Ns' Hφ HNs' k f T r Hfk Hr).
Qed.

(** An element of a record type along an equation of terms: each field's
    projection moves along the congruence, at the field's type moved along
    the projections before it ([record_pre_eq]); the gluings of the fields
    move along both ([HFr] and [HFt]). *)
Lemma record_glu_exp_pred_resp_exp_eq : forall p R ns FP FEl elem_rel n Γ A M M' m,
    record_lookup gc_deps gc_stack p = Some R ->
    (forall k f T vs Δ T' N N' r, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs ->
       Δ ⊢ N : T' ® r ∈ FEl k vs -> Δ ⊢ N ≈ N' : T' -> Δ ⊢ N' : T' ® r ∈ FEl k vs) ->
    (forall k f T vs Δ T' T'' N r, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs ->
       Δ ⊢ N : T' ® r ∈ FEl k vs -> Δ ⊢ T' ≈ T'' : Typeω@n -> Δ ⊢ N : T'' ® r ∈ FEl k vs) ->
    elem_rel <~> record_rel R (canon_fields_rel R ns) ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M m -> Γ ⊢ M ≈ M' : A ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M' m.
Proof.
  intros * Hl HFr HFt HE [HM Hm Ns HNs vs Hvs Hk] HMM.
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm Ns HNs vs Hvs _); [ gen_presups; eassumption |].
  intros Δ φ Ns' Hφ HNs' k f T r Hfk Hr.
  assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  pose proof (record_projs_prefix_diag _ _ _ _ k (proj1 (HE _ _) Hm) Hvs ltac:(lia)) as Hpre.
  pose proof (Hk Δ φ Ns' Hφ HNs' k f T r Hfk Hr) as G.
  destruct HNs as [HAeq Hwk]; destruct (Hwk Δ φ Hφ) as [[HNl HNt _] HS _].
  destruct HNs' as [HNl' HNs'].
  assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
  assert (HMMa : Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)).
  { rewrite <- wk_apps_record.
    eapply wf_exp_eq_conv'; [ mauto 3 |]; mauto 3. }
  assert (Hrt : Δ ⊢ a_record p : record_ty R) by (gen_presups; eapply wf_record_own_apps; eassumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HSu HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΔ Hl) as Hc.
  rewrite List.length_map in HNl, HNl'.
  pose proof (wf_exp_eq_record_apps _ _ _ _ _ (List.map (fun N => N[φ]ʷ) Ns) Ns' Hrt Hl
                ltac:(rewrite List.length_map; exact HNl) ltac:(lia) HNs') as Happs.
  assert (HNt' : forall j Y T0, List.nth_error Ns' j = Some Y -> List.nth_error (tele_insts (record_params R) Id Ns') j = Some T0 ->
             Δ ⊢ Y : T0)
    by (eapply (record_params_eq_right _ _ _ R (List.map (fun N => N[φ]ʷ) Ns) Ns');
        [ exact Hc | exact Hass | exact HF | exact HΔ | rewrite List.length_map; exact HNl | lia | exact HNs' ]).
  destruct (record_sort_inst_cong _ _ _ R (List.map (fun N => N[φ]ʷ) Ns) Ns' Hc Hass HSu HΔ
              ltac:(rewrite List.length_map; exact HNl) ltac:(lia) HNs') as [is HSS].
  assert (HS' : Δ ⊢ (record_sort R)[sb_of_list Id Ns'] ⊆ Typeω@n).
  { eapply wf_subtyp_trans; [| exact HS ].
    eapply wf_subtyp_refl; [ gen_presups; eassumption | symmetry; exact HSS ]. }
  assert (HMMb : Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : apps_exp (a_record p) Ns').
  { eapply wf_exp_eq_conv'; [ exact HMMa |].
    eapply wf_exp_eq_subtyp'; [ exact Happs | eapply wf_subtyp_trans; [| exact HS ];
                                eapply wf_subtyp_refl; [ gen_presups; eassumption | apply wf_exp_eq_refl; gen_presups; eassumption ] ]. }
  pose proof (record_pre_eq _ _ _ _ _ _ _ _ HMMb Hrt Hl ltac:(lia) HNt' k ltac:(lia)) as Hpe.
  pose proof (record_field_sort_cong _ _ _ R k f T Ns' (record_pre R k M[φ]ʷ) (Ns' ++ record_pre R k M'[φ]ʷ)
                Hc Hass HFs HΔ Hfk ltac:(lia)
                ltac:(apply length_record_pre; lia) ltac:(rewrite List.length_app, length_record_pre by lia; lia) Hpe) as HTT.
  assert (HTTn : Δ ⊢ T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)] ≈ T[sb_of_list Id (Ns' ++ record_pre R k M'[φ]ʷ)] : Typeω@n)
    by (eapply wf_exp_eq_subtyp'; [ exact HTT | exact HS' ]).
  assert (Hp : Δ ⊢ a_proj f M[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)])
    by (eapply wf_proj; [ gen_presups; eassumption | exact Hrt | exact Hl | lia | exact HNt' | exact Hfk | gen_presups; eassumption ]).
  assert (Hp' : Δ ⊢ a_proj f M'[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M'[φ]ʷ)])
    by (eapply wf_proj; [ gen_presups; eassumption | exact Hrt | exact Hl | lia | exact HNt' | exact Hfk | gen_presups; eassumption ]).
  assert (Hpp : Δ ⊢ a_proj f M[φ]ʷ ≈ a_proj f M'[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)])
    by (eapply wf_exp_eq_proj_cong; [ exact HMMb | exact Hrt | exact Hl | lia | exact HNt' | exact Hfk | gen_presups; eassumption
                                    | eapply wf_conv'; [ exact Hp' | symmetry; exact HTTn ] ]).
  eapply HFt; [ exact Hfk | exact Hpre | eapply HFr; [ exact Hfk | exact Hpre | exact G | exact Hpp ] | exact HTTn ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_lvl_escape glu_lvl_resp_ctxsub : mctt.
(** [glu_lvl] has one constructor, so [split] breaks a goal
    [glu_lvl Γ M m] into its premises; the readback clause is then
    [glu_lvl_readback], and it is a hint so that the shared scripts reach it. *)
#[local]
Hint Resolve glu_lvl_resp_exp_eq glu_lvl_readback glu_lvl_ws_readback : mctt.
#[export]
Hint Resolve False_glu_elem_escape False_glu_elem_resp_ctxsub : mctt.
#[local]
Hint Resolve False_glu_elem_per_ne False_glu_elem_resp_exp_eq : mctt.
#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  destruct_ind_glu_exp;
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
  9:{ apply_equiv_left; match goal with H : exists Ns, record_typ_at _ _ _ _ _ _ _ _ Ns |- _ => destruct H as (Ns & [HA _]) end;
      gen_presups; assumption. }
  8:{ apply_equiv_left; match goal with H : exists Ps, ind_typ_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ps |- _ => destruct H as (Ps & HA & _) end;
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
  9:{ apply_equiv_left; eapply record_glu_typ_pred_resp_exp_eq; eassumption. }
  8:{ apply_equiv_left; eapply (ind_glu_typ_pred_resp_exp_eq p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all: simpl_glu_rel;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ destruct_conjs; glu_witness2;
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
  9:{ apply_equiv_left; eapply record_glu_exp_pred_resp_typ_exp_eq; eassumption. }
  8:{ apply_equiv_left; eapply (ind_glu_exp_pred_resp_typ_exp_eq p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all:
    simpl_glu_rel; repeat split; intros;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ glu_witness2; [ eassumption | transitivity A; mauto 4 ] ];
    mauto 3.
  all: try solve [ firstorder ].
  all: try solve [ glu_witness2; eassumption ].
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
  9:{ apply_equiv_left; eapply record_glu_typ_pred_resp_ctxsub; eassumption. }
  8:{ apply_equiv_left; eapply (ind_glu_typ_pred_resp_ctxsub p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all:
    simpl_glu_rel;
    (** A small universe: its level term and its equation both move to the
        refined context. *)
    try solve [ glu_witness2;
                [ eapply glu_lvl_resp_ctxsub; eassumption | mauto 3 ] ];
    mauto 3.

  - assert (Δ ⊢ IT : Typeω@(ulvl i)) by mauto 3.
    assert (Δ ▹ IT ⊆ Γ ▹ IT) by (eapply ctx_sub_extend; mauto 3 using wf_subtyp_refl_univ).
    econstructor; mauto 3; intros; mauto 4.

  - split; [ mauto 3 | intros; mauto 4 ].
Qed.

Lemma glu_lvl_resp_wk : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ,
      Δ ⊢ᵏ φ : Γ ->
      glu_lvl n Δ M[φ]ʷ a.
Proof.
  intros * H * ? Δ' ψ M' Hψ Hr.
  rewrite exp_wk_wk.
  assert (Δ' ⊢ᵏ φ ⊙ ψ : Γ) by mauto 3.
  exact (H _ _ _ ltac:(eassumption) Hr).
Qed.

Hint Resolve glu_lvl_resp_wk : mctt.

Lemma False_glu_elem_resp_wk : forall Γ M a,
    False_glu_elem Γ M a ->
    forall Δ φ,
      Δ ⊢ᵏ φ : Γ ->
      False_glu_elem Δ M[φ]ʷ a.
Proof.
  destruct 1; intros.
  econstructor; trivial.
  intros Δ' ψ M' **.
  rewrite exp_wk_wk.
  assert (Δ' ⊢ᵏ φ ⊙ ψ : Γ) by mauto 3.
  mauto 4.
Qed.

Hint Resolve False_glu_elem_resp_wk : mctt.

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
  8:{ eexists; eassumption. }
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
  9:{ simpl_glu_rel. match goal with HR : per_univ_elem _ ?R (d_record _ _) (d_record _ _), HE : per_univ_elem _ ?E (d_record _ _) (d_record _ _), Hm : ?E ?m ?m |- ?R ?m ?m => assert (EE : E <~> R) by (eapply per_univ_elem_right_irrel; eassumption); apply EE; exact Hm end. }
  8:{ simpl_glu_rel. match goal with HR : per_univ_elem _ ?R (d_ind _ _ _) (d_ind _ _ _), HE : per_univ_elem _ ?E (d_ind _ _ _) (d_ind _ _ _), Hm : ?E ?m ?m |- ?R ?m ?m => assert (EE : E <~> R) by (eapply per_univ_elem_right_irrel; eassumption); apply EE; exact Hm end. }
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
      match goal with H : record_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ _ Ns HNs _ _ _] end;
      exists Ns; exact HNs. }
  8:{ apply_equiv_left;
      match goal with H : ind_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ _ Ps HPs _] end;
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
  9:{ apply_equiv_left; eapply record_glu_exp_pred_resp_exp_eq; [ exact H | | | eapply record_rel_canon; eassumption | eassumption | eassumption ].
      - intros * Hk Hp HN HNN; destruct (H1 _ _ _ _ Hk Hp) as [b Hb]; eapply (H3 _ _ _ _ _ Hk Hp Hb); eassumption.
      - intros * Hk Hp HN HTT; destruct (H1 _ _ _ _ Hk Hp) as [b Hb];
          eapply (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ (H2 _ _ _ _ _ Hk Hp Hb)); eassumption. }
  8:{ apply_equiv_left; eapply (ind_glu_exp_pred_resp_exp_eq p D ups ns NP NEl AP AEl DP DEl); eassumption. }
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
Hint Resolve glu_lvl_resp_wk False_glu_elem_resp_wk : mctt.
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

(** Each component's gluings of two equivalent families are contained in
    the other's. *)
Local Ltac fam_tac HNq HAq HDq :=
  first
    [ intros mf Mf jf vsf HMf Hk' Hp; destruct (HNq mf Mf jf vsf HMf Hk' Hp) as [E1 E2];
      split; intros; [ apply E1 | apply E2 ]; assumption
    | intros mf Mf msf cf gsf jf vsf HMf Hm Hc Hk' Hp; destruct (HAq mf Mf msf cf gsf jf vsf HMf Hm Hc Hk' Hp) as [E1 E2];
      split; intros; [ apply E1 | apply E2 ]; assumption
    | intros mf Mf msf cf gsf gsf1 tf gsf2 wsf jf Bf ysf HMf Hm Hc Heq Hw HB Hy;
      destruct (HDq mf Mf msf cf gsf gsf1 tf gsf2 wsf jf Bf ysf HMf Hm Hc Heq Hw HB Hy) as [E1 E2];
      split; intros; [ apply E1 | apply E2 ]; assumption ].

Lemma functional_glu_univ_elem : forall i a P P' El El',
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem i ↘ P' ↘ El' ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  glu_univ_elem_induction Ha; intros.
  (** A record type: the field gluings agree, by the induction hypothesis,
      and so do the predicates built of them. *)
  9:{ basic_invert_glu_univ_elem Ha'.
      match goal with Hl2 : record_lookup _ _ p = Some ?R2 |- _ => assert_fails constr_eq R2 R;
        rewrite H in Hl2; injection Hl2 as <- end.
      assert (EE : elem_rel <~> elem_rel0) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (Heq : record_fams_equiv R ns FP FP0 FEl FEl0).
      { intros k f T vs Hk Hp; destruct (H1 _ _ _ _ Hk Hp) as [b Hb].
        eapply H3; [ exact Hk | exact Hp | exact Hb |]; eauto. }
      assert (Heq' : record_fams_equiv R ns FP0 FP FEl0 FEl)
        by (intros k f T vs Hk Hp; destruct (Heq _ _ _ _ Hk Hp) as [E1 E2]; split; symmetry; assumption).
      pose proof (record_rel_canon _ _ _ _ _ _ H H0) as HE.
      assert (HE0 : elem_rel0 <~> record_rel R (canon_fields_rel R ns)) by (rewrite <- EE; exact HE).
      apply_predicate_equivalence.
      split.
      - intros Γ A; cbn [record_glu_typ_pred pointwise_lifting].
        split; intros (Ns & HNs); exists Ns; eapply record_typ_at_mono; eassumption.
      - intros Γ A M' m; cbn [record_glu_exp_pred pointwise_lifting].
        split; intros HG; eapply record_glu_exp_mono; try eassumption; [ symmetry; exact EE ]. }
  8:{ basic_invert_glu_univ_elem Ha'.
      assert (D0 = D) by congruence; subst D0.
      assert (M0 = M) by congruence; subst M0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      assert (EE : elem_rel0 <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (HNq : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm ->
                    tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
                    (NP m j vs <∙> NP0 m j vs) /\ (NEl m j vs <∙> NEl0 m j vs)).
      { refine (ind_case_N_helper D ups _ H0 H5 _); intros;
          eapply H8; [ eassumption | eassumption | eassumption | eassumption | eapply H24; eassumption ]. }
      assert (HAq : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
                    tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
                    ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) ->
                    tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
                    (AP m ms c j vs <∙> AP0 m ms c j vs) /\ (AEl m ms c j vs <∙> AEl0 m ms c j vs)).
      { refine (ind_case_A_helper D ups _ H6 _); intros;
          eapply H10; [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                      | eapply H25; eassumption ]. }
      assert (HDq : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
                    tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
                    ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                    tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
                    List.nth_error (ptyp_doms t) j = Some B ->
                    tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
                    (DP m (ms ++ ws ++ ys) B <∙> DP0 m (ms ++ ws ++ ys) B) /\
                    (DEl m (ms ++ ws ++ ys) B <∙> DEl0 m (ms ++ ws ++ ys) B)).
      { intros * HM Hm Hc Heq Hw HB Hy.
        destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy) as [b Hb].
        eapply H13; [ exact HM | exact Hm | exact Hc | exact Heq | exact Hw | exact HB | exact Hy | exact Hb
                    | eapply H27; eassumption ]. }
      pose proof (ind_canon_of_per _ _ _ _ _ _ _ _ _ H4 H H3 H3) as Hcp.
      apply_predicate_equivalence.
      split.
      - intros Γ A; cbn [ind_glu_typ_pred pointwise_lifting].
        split; intros (Ps & HPs); exists Ps;
          (eapply ind_typ_at_mono; [ exact H0 | exact Hcp | | | | exact HPs ]); fam_tac HNq HAq HDq.
      - intros Γ A M' m; cbn [ind_glu_exp_pred pointwise_lifting].
        split; intros [? ? Ps HPs Hk];
          (econstructor; [ assumption | apply EE + apply EE; assumption | | ]).
        + eapply ind_typ_at_mono; [ exact H0 | exact Hcp | | | | exact HPs ]; fam_tac HNq HAq HDq.
        + intros Δ φ Ps' Hφ HPs'; eapply (ind_glu_elem_mono p D ups _ _ _ _ H0 Hcp); [ | | | exact (Hk Δ φ Ps' Hφ HPs') ];
            intros; [ eapply HNq | eapply HAq | ]; try eassumption.
          destruct (HDq _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [E1 E2].
          split; intros; [ apply E1 | apply E2 ]; assumption.
        + eapply ind_typ_at_mono; [ exact H0 | exact Hcp | | | | exact HPs ]; fam_tac HNq HAq HDq.
        + intros Δ φ Ps' Hφ HPs'; eapply (ind_glu_elem_mono p D ups _ _ _ _ H0 Hcp); [ | | | exact (Hk Δ φ Ps' Hφ HPs') ];
            intros; [ eapply HNq | eapply HAq | ]; try eassumption.
          destruct (HDq _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [E1 E2].
          split; intros; [ apply E1 | apply E2 ]; assumption. }
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
  intros * Hl Γ A; cbn; split; intros [t n Ht Heq]; apply (mk_suniv_glu_typ _ _ _ _ t n); try assumption;
    (eapply glu_lvl_resp_per; [ eassumption | first [ eassumption | symmetry; assumption ] ]).
Qed.

Lemma suniv_glu_exp_pred_resp_per : forall l l' U,
    Dom l ≈ l' ∈ per_lvl ->
    suniv_glu_exp_pred l U <∙> suniv_glu_exp_pred l' U.
Proof.
  intros * Hl Γ A M m; unfold suniv_glu_exp_pred; cbn.
  rewrite (per_lvl_real _ _ Hl).
  pose proof (suniv_glu_typ_pred_resp_per l l' U Hl Γ A) as Ht; cbn in Ht.
  split; intros [? HA ? ?]; constructor; try assumption; apply Ht; assumption.
Qed.

(** The parameters of every member of a group at two related types of one
    of its members, the non-uniform ones related at the canonical relation
    of the left: they read back alike at the member's telescope. *)
Lemma ind_params_per_top : forall i R p D k ups ups' ns ns',
    DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
    ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
    forall j Mj bs bs', ind_member D j = Some Mj -> tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs' ->
      per_top_ps (List.rev (im_params D Mj)) (ups ++ bs) (ups' ++ bs').
Proof.
  intros * HR Hl Hu Hu' j Mj bs bs' HMj Hbs s.
  destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HR Hl Hu Hu') as [Hass Hps _ _ _ _ _ _].
  destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ _ HR Hl Hu Hu') as (HevN & _ & _).
  destruct (Hps s) as (Ms1 & HM1 & HM1').
  assert (Hassn : tele_ass (List.rev (im_nparams Mj))) by (apply List.Forall_rev; exact (gta_nparams _ Hass _ _ HMj)).
  destruct (read_ps_tele (List.rev (im_nparams Mj)) (canon_nparams_rel D ups j) (env_args nil ups) (env_args nil ups') Hassn
              ltac:(intros j0 A pre pre' Hj0 Hp; rewrite <- !env_args_app;
                    destruct (HevN _ _ _ _ _ _ HMj Hj0 Hp) as [a a' Ea Ea' HRa];
                    exists a, a'; split; [ exact Ea | split; [ exact Ea' | intros b b' Hb; exact (per_elem_then_per_top HRa Hb) ] ])
              _ _ Hbs s) as (Ms2 & HM2 & HM2').
  exists (nfs_app Ms1 Ms2); rewrite rev_im_params_split; split; apply read_ps_app; assumption.
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
  9:{ (** A record type: the same gluings of its fields, at the related
          parameters. *)
      match goal with
      | HR : per_univ_elem _ ?er (d_record ?p ?ns) (d_record ?p ?ns'), Hl : record_lookup _ _ ?p = Some ?R,
        Hps : per_top_ps _ ?ns ?ns', Hn' : List.length ?ns' = _, HfP : fields_per ?R ?fr, HfI : fields_inv ?R ?fr,
        HfE : fields_evals _ ?R ?ns ?ns' ?fr |- _ =>
          rename HR into HRc, Hl into Hlc, Hps into Hpsc, Hn' into Hnc', HfP into HfPc, HfI into HfIc, HfE into HfEc
      end.
      basic_invert_glu_univ_elem Horig.
      match goal with Hl2 : record_lookup _ _ p = Some ?R2 |- _ => assert_fails constr_eq R2 R;
        rewrite Hlc in Hl2; injection Hl2 as <- end.
      match goal with
      | HR0 : per_univ_elem _ ?er0 (d_record p ns) (d_record p ns), HeB : forall k f T vs, _ -> _ -> exists b, _,
        HgB : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ b,
        HP : ?P <∙> record_glu_typ_pred _ _ _ _ _ _, HEl : ?El <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ =>
          rename HR0 into HR0c, HeB into HeBc, HgB into HgBc, HP into HPc, HEl into HElc
      end.
      assert (HR' : per_univ_elem i elem_rel (d_record p ns') (d_record p ns'))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact HRc | exact HRc ]).
      assert (ER : elem_rel0 <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      pose proof (record_canon_prefix_move _ _ _ _ _ _ Hlc HRc) as Hmv.
      pose proof (record_canon_prefix_move _ _ _ _ _ _ Hlc (per_univ_sym _ _ _ _ HRc)) as Hmv'.
      pose proof (record_canon_prefix_clause _ _ R ns ns' fr (fun _ _ _ H => proj1 H) HfPc HfIc HfEc) as Hcl.
      pose proof (record_rel_canon _ _ _ _ _ _ Hlc HR0c) as HE0.
      pose proof (record_rel_canon _ _ _ _ _ _ Hlc HR') as HE'.
      simp glu_univ_elem.
      refine (glu_univ_elem_core_record i _ FP FEl typ_rel el_rel elem_rel Hlc HR' _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *.
      - intros k f T vs Hk Hp.
        assert (Hkl : k < length (record_fields R)) by (apply List.nth_error_Some; congruence).
        destruct (Hcl k vs ltac:(lia) Hp) as [Hp1 _].
        destruct (HfEc _ _ _ _ _ Hk Hp1) as [a a' Ea Ea' _]; eauto.
      - intros k f T vs b Hk Hp Eb.
        assert (Hkl : k < length (record_fields R)) by (apply List.nth_error_Some; congruence).
        destruct (Hcl k vs ltac:(lia) Hp) as [Hp1 Hp2].
        destruct (HfEc _ _ _ _ _ Hk Hp1) as [a a' Ea Ea' [HR1 IH]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        eapply IH; [ exact HR1 | eapply HgBc; eassumption ].
      - intros Γ A; destruct (HPc Γ A) as [Hap Hbp]; split; intro HH.
        + destruct (Hap HH) as (Ns & HNs); exists Ns.
          eapply record_typ_at_resp_per; [ exact Hpsc | exact Hmv | exact HNs ].
        + apply Hbp; destruct HH as (Ns & HNs); exists Ns.
          eapply record_typ_at_resp_per; [ exact (per_top_ps_sym _ _ _ Hpsc) | exact Hmv' | exact HNs ].
      - intros Γ A M' m; destruct (HElc Γ A M' m) as [Hap Hbp]; cbn [record_glu_exp_pred] in *; split; intro HH.
        + destruct (Hap HH) as [HMt Hm Ns HNs vs Hvs Hk].
          refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ HMt (proj1 (ER _ _) Hm) Ns _ vs Hvs Hk).
          eapply record_typ_at_resp_per; [ exact Hpsc | exact Hmv | exact HNs ].
        + apply Hbp; destruct HH as [HMt Hm Ns HNs vs Hvs Hk].
          refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ HMt (proj2 (ER _ _) Hm) Ns _ vs Hvs Hk).
          eapply record_typ_at_resp_per; [ exact (per_top_ps_sym _ _ _ Hpsc) | exact Hmv' | exact HNs ]. }
  8:{ (** An inductive type: the same gluings of its telescopes, at the
          related uniform parameters. *)
      rename H into Hl, H0 into Hass, H1 into HMk, H2 into Hh, H3 into Hu, H4 into Hu', H19 into HR,
        H7 into Hn, H10 into Ha, H13 into Hd, H5 into Hps5, H6 into HnP6, H8 into HnI8, H9 into HaP9, H11 into HaI11,
        H12 into HdP12, H14 into HdI14, H15 into Hcl15, H16 into Hcd16, H17 into Hns17, H18 into HE18.
      assert (Hag : ind_fam_agree D nr (canon_nparams_rel D ups) ar (canon_args_rel D ups) dr (canon_doms_rel ups)).
      { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact Hass | | | ].
        - red; intros * HM0 HA Hp; destruct (Hn _ _ _ _ _ _ HM0 HA Hp) as [a a' Ea Ea' [HR0 _]]; econstructor; eassumption.
        - red; intros * HM0 Hm Hc HA Hp; destruct (Ha _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc HA Hp) as [a a' Ea Ea' [HR0 _]];
            econstructor; eassumption.
        - red; intros * HM0 Hm Hc Heq Hw HB Hy; destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc Heq Hw HB Hy)
            as [a a' Ea Ea' [HR0 _]]; econstructor; eassumption. }
      destruct Hag as [Hn0 Ha0 Hd0].
      pose proof (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0) as P2.
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HR Hl Hu Hu') as [_ _ Hcp Hfam Hadm _ _ _].
      destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hfam) as [Hfn' Hfa' Hfd'].
      pose proof Hfam as [Hfn Hfa Hfd].
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn' Hfa' Hfd') as G1.
      pose proof (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd) as Q2.
      basic_invert_glu_univ_elem Horig.
      rename H into Hl0, H0 into Hass0, H1 into HM0, H2 into Hh0, H3 into Hu0, H4 into HR0, H5 into HeN, H6 into HeA,
        H7 into HgN, H8 into HgA, H9 into HeD, H10 into HgD, H11 into HP, H12 into HEl.
      assert (D0 = D) by congruence; subst D0.
      assert (M0 = M) by congruence; subst M0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      assert (HR' : per_univ_elem i elem_rel (d_ind p k (ups' ++ ns')) (d_ind p k (ups' ++ ns')))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact HR | exact HR ]).
      destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (mk_ind_fam_agree _ _ _ _ _ _ _ Hn0 Ha0 Hd0)) as [Hn0' Ha0' Hd0'].
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0') as F2.
      (** The prefixes of the clause at [ups'] are on the diagonal of the
          canonical relations at [ups] and of the clause's own. *)
      assert (Hpre : forall m Mm j vs, ind_member D m = Some Mm -> j < length (List.rev (im_nparams Mm)) ->
                     tele_prefix_rel (canon_nparams_rel D ups' m) j vs vs ->
                     tele_prefix_rel (canon_nparams_rel D ups m) j vs vs /\ tele_prefix_rel (nr m) j vs vs).
      { intros * HM Hj Hp. pose proof (Q2 m Mm HM j vs vs ltac:(lia) Hp) as Hp1.
        split; [ exact Hp1 | exact (P2 m Mm HM j vs vs ltac:(lia) Hp1) ]. }
      assert (Hpra : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
                     tele_rel (canon_nparams_rel D ups' m) (List.rev (im_nparams Mm)) ms ms ->
                     ind_con Mm c = Some gs -> j <= length (cargs_nonrec gs) ->
                     tele_prefix_rel (canon_args_rel D ups' m ms c) j vs vs ->
                     tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms /\
                     tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms /\
                     tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs /\ tele_prefix_rel (ar m ms c) j vs vs).
      { intros * HM Hm Hc Hj Hp.
        pose proof (G1 m Mm HM _ _ Hm) as Hm1. pose proof (F2 m Mm HM _ _ Hm1) as Hm2.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs j vs vs Hm1 Hm Hc Hj Hp) as Hp1.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs j vs vs Hm2 Hm1 Hc Hj Hp1)
          as Hp2.
        exact (conj Hm1 (conj Hm2 (conj Hp1 Hp2))). }
      assert (Hprd : forall m Mm ms c gs gs1 t gs2 ws j ys, ind_member D m = Some Mm ->
                     tele_rel (canon_nparams_rel D ups' m) (List.rev (im_nparams Mm)) ms ms ->
                     ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                     tele_prefix_rel (canon_args_rel D ups' m ms c) (length (cargs_nonrec gs1)) ws ws ->
                     j <= length (ptyp_doms t) ->
                     tele_prefix_rel (shape_doms_rel (canon_doms_rel ups' m) ms ws (ptyp_doms t)) j ys ys ->
                     tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms /\
                     tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms /\
                     tele_prefix_rel (canon_args_rel D ups m ms c) (length (cargs_nonrec gs1)) ws ws /\
                     tele_prefix_rel (ar m ms c) (length (cargs_nonrec gs1)) ws ws /\
                     tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys /\
                     tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) j ys ys).
      { intros * HM Hm Hc Heq Hw Hj Hy.
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        destruct (Hpra _ _ _ _ _ _ _ HM Hm Hc HK Hw) as (Hm1 & Hm2 & Hw1 & Hw2).
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws j ys ys
                      Hm1 Hm Hc Heq Hw1 Hw Hj Hy) as Hy1.
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws j ys ys
                      Hm2 Hm1 Hc Heq Hw2 Hw1 Hj Hy1) as Hy2.
        exact (conj Hm1 (conj Hm2 (conj Hw1 (conj Hw2 (conj Hy1 Hy2))))). }
      assert (ER : elem_rel0 <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR) Hl Hu' Hu) as [_ _ Hcp' Hfam' Hadm' _ _ _].
      pose proof (per_univ_then_per_top_typ HR) as Htop.
      pose proof (per_univ_then_per_top_typ (per_univ_sym _ _ _ _ HR)) as Htop'.
      pose proof (ind_params_per_top _ _ _ _ _ _ _ _ _ HR Hl Hu Hu') as Hrbt.
      pose proof (ind_params_per_top _ _ _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR) Hl Hu' Hu) as Hrbt'.
      simp glu_univ_elem.
      refine (glu_univ_elem_core_indty i _ NP NEl AP AEl DP DEl typ_rel el_rel elem_rel Hl Hass HMk Hh Hu' HR' _ _ _ _ _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *.
      - intros m Mm j A vs HM HA Hp.
        assert (Hj : j < length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (Hpre _ _ _ _ HM Hj Hp) as [_ Hp2]; destruct (Hn _ _ _ _ _ _ HM HA Hp2) as [a a' Ea Ea' _]; eauto.
      - intros m Mm ms c gs j A vs HM Hm Hc HA Hp.
        assert (Hj : j < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ ms c gs j vs HM Hm Hc ltac:(lia) Hp) as (_ & Hm2 & _ & Hp2).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc HA Hp2) as [a a' Ea Ea' _]; eauto.
      - intros m Mm j A vs b HM HA Hp Eb.
        assert (Hj : j < length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (Hpre _ _ _ _ HM Hj Hp) as [Hp1 Hp2]; destruct (Hn _ _ _ _ _ _ HM HA Hp2) as [a a' Ea Ea' [HR1 IH]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        eapply IH; [ exact HR1 | eapply HgN; eassumption ].
      - intros m Mm ms c gs j A vs b HM Hm Hc HA Hp Eb.
        assert (Hj : j < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ ms c gs j vs HM Hm Hc ltac:(lia) Hp) as (Hm1 & Hm2 & Hp1 & Hp2).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc HA Hp2) as [a a' Ea Ea' [HR1 IH]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        eapply IH; [ exact HR1 | eapply HgA; eassumption ].
      - intros m Mm ms c gs gs1 t gs2 ws j B ys HM Hm Hc Heq Hw HB Hy.
        assert (Hjl : j < length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (Hprd _ _ ms c gs gs1 t gs2 ws j ys HM Hm Hc Heq Hw ltac:(lia) Hy) as (_ & Hm2 & _ & Hw2 & _ & Hy2).
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc Heq Hw2 HB Hy2) as [a a' Ea Ea' _]; eauto.
      - intros m Mm ms c gs gs1 t gs2 ws j B ys b HM Hm Hc Heq Hw HB Hy Eb.
        assert (Hjl : j < length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (Hprd _ _ ms c gs gs1 t gs2 ws j ys HM Hm Hc Heq Hw ltac:(lia) Hy) as (Hm1 & Hm2 & Hw1 & Hw2 & Hy1 & Hy2).
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc Heq Hw2 HB Hy2) as [a a' Ea Ea' [HR1 IH]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        eapply IH; [ exact HR1 | eapply HgD; eassumption ].
      - intros Γ A; destruct (HP Γ A) as [Hap Hbp]; split; intro HH.
        + destruct (Hap HH) as (Ps & HPs); exists Ps.
          eapply ind_typ_at_resp_per_top; [ exact Hl | exact HMk | exact Hass | exact Hcp | exact Htop | exact Hfam | exact HPs ].
        + apply Hbp; destruct HH as (Ps & HPs); exists Ps.
          eapply ind_typ_at_resp_per_top; [ exact Hl | exact HMk | exact Hass | exact Hcp' | exact Htop' | exact Hfam' | exact HPs ].
      - intros Γ A M' m; destruct (HEl Γ A M' m) as [Hap Hbp]; cbn [ind_glu_exp_pred] in *; split; intro HH.
        + destruct (Hap HH) as [HMt Hm Ps HPs Hk].
          refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMt _ Ps _ _); [ apply ER; exact Hm | |].
          * eapply ind_typ_at_resp_per_top; [ exact Hl | exact HMk | exact Hass | exact Hcp | exact Htop | exact Hfam | exact HPs ].
          * intros Δ φ Ps' Hφ HPs'.
            eapply (ind_glu_elem_move p D ups NEl AEl DP DEl Hass Hcp ups' NEl AEl DP DEl Hfam Hadm Hrbt);
              [ intros; assumption | intros; assumption | intros; split; intros; assumption | exact (Hk Δ φ Ps' Hφ HPs') ].
        + apply Hbp; destruct HH as [HMt Hm Ps HPs Hk].
          refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMt _ Ps _ _); [ apply ER; exact Hm | |].
          * eapply ind_typ_at_resp_per_top; [ exact Hl | exact HMk | exact Hass | exact Hcp' | exact Htop' | exact Hfam' | exact HPs ].
          * intros Δ φ Ps' Hφ HPs'.
            eapply (ind_glu_elem_move p D ups' NEl AEl DP DEl Hass Hcp' ups NEl AEl DP DEl Hfam' Hadm' Hrbt');
              [ intros; assumption | intros; assumption | intros; split; intros; assumption | exact (Hk Δ φ Ps' Hφ HPs') ]. }
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
  9:{ (** A record type: its fields glue at their canonical gluings, at the
          right parameters. *)
      match goal with
      | Hl : record_lookup _ _ ?p = Some ?R, Hnd : List.NoDup _, Hn : List.length ?ns = _, Hn' : List.length ?ns' = _,
        Hps : per_top_ps _ ?ns ?ns', HfP : fields_per ?R ?fr, HfI : fields_inv ?R ?fr,
        HfE : fields_evals _ ?R ?ns ?ns' ?fr, HE : ?er <~> record_rel ?R ?fr |- _ =>
          assert (Hpu : per_univ_elem i er (d_record p ns) (d_record p ns'));
          [ basic_per_univ_elem_econstructor; try eassumption;
            red; intros * Hk Hp; destruct (HfE _ _ _ _ _ Hk Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto |];
          rename Hl into Hlc, HfE into HfEc;
          pose proof (record_canon_prefix_clause _ _ R ns ns' fr (fun _ _ _ H => proj1 H) HfP HfI HfEc) as Hcl
      end.
      assert (HR' : per_univ_elem i elem_rel (d_record p ns') (d_record p ns'))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact Hpu | exact Hpu ]).
      assert (Hcan : forall b P El (E : domain -> Prop), (forall b', E b' -> b' = b) -> E b -> glu_univ_elem i P El b ->
                 glu_univ_elem i (fun Γ T => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> P' Γ T)
                                 (fun Γ T M m => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> El' Γ T M m) b).
      { intros * HE Eb Hg.
        eapply simple_glu_univ_elem_morphism_iff; [ | | reflexivity | exact Hg ].
        - intros Γ T; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [HPP _]; apply HPP; exact HP.
        - intros Γ T M' m; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [_ HEE]; apply HEE; exact HP. }
      set (FP := fun k vs Γ T => forall b P El, ⟦ nth_ftyp R k ⟧ env_args nil (ns' ++ vs) ↘ b ->
                                   glu_univ_elem i P El b -> P Γ T).
      set (FEl := fun k vs Γ T M m0 => forall b P El, ⟦ nth_ftyp R k ⟧ env_args nil (ns' ++ vs) ↘ b ->
                                         glu_univ_elem i P El b -> El Γ T M m0).
      do 2 eexists.
      simp glu_univ_elem.
      refine (glu_univ_elem_core_record i _ FP FEl _ _ elem_rel Hlc HR' _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *; try reflexivity.
      - intros k f T vs Hk Hp.
        assert (Hkl : k < length (record_fields R)) by (apply List.nth_error_Some; congruence).
        destruct (HfEc _ _ _ _ _ Hk (proj1 (Hcl k vs ltac:(lia) Hp))) as [a a' Ea Ea' _]; eauto.
      - intros k f T vs b Hk Hp Eb.
        assert (Hkl : k < length (record_fields R)) by (apply List.nth_error_Some; congruence).
        destruct (HfEc _ _ _ _ _ Hk (proj1 (Hcl k vs ltac:(lia) Hp))) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold FP, FEl; rewrite (nth_ftyp_eq _ _ _ _ Hk).
        eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ]. }
  8:{ (** An inductive type: its telescopes glue at their canonical
          gluings, at the right uniform parameters. *)
      rename H into Hl, H0 into Hass, H1 into HMk, H2 into Hh, H3 into Hu, H4 into Hu',
        H7 into Hn, H10 into Ha, H13 into Hd.
      assert (Hpu : per_univ_elem i elem_rel (d_ind p k (ups ++ ns)) (d_ind p k (ups' ++ ns'))).
      { basic_per_univ_elem_econstructor; try eassumption.
        - red; intros * HM0 HA Hp; destruct (Hn _ _ _ _ _ _ HM0 HA Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto.
        - red; intros * HM0 Hm Hc HA Hp; destruct (Ha _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc HA Hp) as [a a' Ea Ea' [HR _]];
            econstructor; eauto.
        - red; intros * HM0 Hm Hc Heq Hw HB Hy;
            destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' [HR _]];
            econstructor; eauto. }
      assert (Hcan : forall b P El (E : domain -> Prop), (forall b', E b' -> b' = b) -> E b -> glu_univ_elem i P El b ->
                 glu_univ_elem i (fun Γ T => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> P' Γ T)
                                 (fun Γ T M m => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> El' Γ T M m) b).
      { intros * HE Eb Hg.
        eapply simple_glu_univ_elem_morphism_iff; [ | | reflexivity | exact Hg ].
        - intros Γ T; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [HPP _]; apply HPP; exact HP.
        - intros Γ T M' m; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [_ HEE]; apply HEE; exact HP. }
      assert (Hag : ind_fam_agree D nr (canon_nparams_rel D ups) ar (canon_args_rel D ups) dr (canon_doms_rel ups)).
      { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact Hass | | | ].
        - red; intros * HM0 HA Hp; destruct (Hn _ _ _ _ _ _ HM0 HA Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto.
        - red; intros * HM0 Hm Hc HA Hp; destruct (Ha _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc HA Hp) as [a a' Ea Ea' [HR _]];
            econstructor; eauto.
        - red; intros * HM0 Hm Hc Heq Hw HB Hy;
            destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' [HR _]];
            econstructor; eauto. }
      destruct Hag as [Hn0 Ha0 Hd0].
      pose proof (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0) as P2.
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ Hpu Hl Hu Hu') as [_ _ Hcp Hfam Hadm _ _ _].
      destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hfam) as [Hfn' Hfa' Hfd'].
      pose proof Hfam as [Hfn Hfa Hfd].
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn' Hfa' Hfd') as G1.
      pose proof (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd) as Q2.
      assert (HR' : per_univ_elem i elem_rel (d_ind p k (ups' ++ ns')) (d_ind p k (ups' ++ ns')))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact Hpu | exact Hpu ]).
      destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (mk_ind_fam_agree _ _ _ _ _ _ _ Hn0 Ha0 Hd0)) as [Hn0' Ha0' Hd0'].
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0') as F2.
      assert (Hpre : forall m Mm j vs, ind_member D m = Some Mm -> j < length (List.rev (im_nparams Mm)) ->
                     tele_prefix_rel (canon_nparams_rel D ups' m) j vs vs -> tele_prefix_rel (nr m) j vs vs).
      { intros * HM Hj Hp. exact (P2 m Mm HM j vs vs ltac:(lia) (Q2 m Mm HM j vs vs ltac:(lia) Hp)). }
      assert (Hpra : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
                     tele_rel (canon_nparams_rel D ups' m) (List.rev (im_nparams Mm)) ms ms ->
                     ind_con Mm c = Some gs -> j <= length (cargs_nonrec gs) ->
                     tele_prefix_rel (canon_args_rel D ups' m ms c) j vs vs ->
                     tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms /\ tele_prefix_rel (ar m ms c) j vs vs).
      { intros * HM Hm Hc Hj Hp.
        pose proof (G1 m Mm HM _ _ Hm) as Hm1. pose proof (F2 m Mm HM _ _ Hm1) as Hm2.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs j vs vs Hm1 Hm Hc Hj Hp) as Hp1.
        exact (conj Hm2 (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs j vs vs Hm2 Hm1 Hc Hj Hp1)). }
      assert (Hprd : forall m Mm ms c gs gs1 t gs2 ws j ys, ind_member D m = Some Mm ->
                     tele_rel (canon_nparams_rel D ups' m) (List.rev (im_nparams Mm)) ms ms ->
                     ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                     tele_prefix_rel (canon_args_rel D ups' m ms c) (length (cargs_nonrec gs1)) ws ws ->
                     j <= length (ptyp_doms t) ->
                     tele_prefix_rel (shape_doms_rel (canon_doms_rel ups' m) ms ws (ptyp_doms t)) j ys ys ->
                     tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms /\
                     tele_prefix_rel (ar m ms c) (length (cargs_nonrec gs1)) ws ws /\
                     tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) j ys ys).
      { intros * HM Hm Hc Heq Hw Hj Hy.
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        pose proof (G1 m Mm HM _ _ Hm) as Hm1. pose proof (F2 m Mm HM _ _ Hm1) as Hm2.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs _ ws ws Hm1 Hm Hc HK Hw) as Hw1.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs _ ws ws Hm2 Hm1 Hc HK Hw1)
          as Hw2.
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws j ys ys
                      Hm1 Hm Hc Heq Hw1 Hw Hj Hy) as Hy1.
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws j ys ys
                      Hm2 Hm1 Hc Heq Hw2 Hw1 Hj Hy1) as Hy2.
        exact (conj Hm2 (conj Hw2 Hy2)). }
      set (NP := fun m j vs Γ T => forall b P El, ⟦ nth_ctyp (List.rev (member_nparams D m)) j ⟧ env_args nil (ups' ++ vs) ↘ b ->
                                     glu_univ_elem i P El b -> P Γ T).
      set (NEl := fun m j vs Γ T M m0 => forall b P El,
                    ⟦ nth_ctyp (List.rev (member_nparams D m)) j ⟧ env_args nil (ups' ++ vs) ↘ b ->
                    glu_univ_elem i P El b -> El Γ T M m0).
      set (AP := fun m ms c j vs Γ T => forall b P El, ⟦ nth_atyp D m c j ⟧ env_args nil (ups' ++ ms ++ vs) ↘ b ->
                                          glu_univ_elem i P El b -> P Γ T).
      set (AEl := fun m ms c j vs Γ T M m0 => forall b P El, ⟦ nth_atyp D m c j ⟧ env_args nil (ups' ++ ms ++ vs) ↘ b ->
                                                glu_univ_elem i P El b -> El Γ T M m0).
      set (DP := fun (m : nat) pre B Γ T => forall b P El, ⟦ B ⟧ env_args nil (ups' ++ pre) ↘ b -> glu_univ_elem i P El b -> P Γ T).
      set (DEl := fun (m : nat) pre B Γ T M m0 => forall b P El, ⟦ B ⟧ env_args nil (ups' ++ pre) ↘ b ->
                                                    glu_univ_elem i P El b -> El Γ T M m0).
      do 2 eexists.
      simp glu_univ_elem.
      refine (glu_univ_elem_core_indty i _ NP NEl AP AEl DP DEl _ _ elem_rel Hl Hass HMk Hh Hu' HR' _ _ _ _ _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *; try reflexivity.
      - intros m Mm j A vs HM HA Hp.
        assert (Hj : j < length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (Hn _ _ _ _ _ _ HM HA (Hpre _ _ _ _ HM Hj Hp)) as [a a' Ea Ea' _]; eauto.
      - intros m Mm ms c gs j A vs HM Hm Hc HA Hp.
        assert (Hj : j < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ ms c gs j vs HM Hm Hc ltac:(lia) Hp) as (Hm2 & Hp2).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc HA Hp2) as [a a' Ea Ea' _]; eauto.
      - intros m Mm j A vs b HM HA Hp Eb.
        assert (Hj : j < length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (Hn _ _ _ _ _ _ HM HA (Hpre _ _ _ _ HM Hj Hp)) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold NP, NEl; rewrite (nth_ctyp_eq _ _ _ _ _ HM HA).
        eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ].
      - intros m Mm ms c gs j A vs b HM Hm Hc HA Hp Eb.
        assert (Hj : j < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ ms c gs j vs HM Hm Hc ltac:(lia) Hp) as (Hm2 & Hp2).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc HA Hp2) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold AP, AEl; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hc HA).
        eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ].
      - intros m Mm ms c gs gs1 t gs2 ws j B ys HM Hm Hc Heq Hw HB Hy.
        assert (Hjl : j < length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (Hprd _ _ ms c gs gs1 t gs2 ws j ys HM Hm Hc Heq Hw ltac:(lia) Hy) as (Hm2 & Hw2 & Hy2).
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc Heq Hw2 HB Hy2) as [a a' Ea Ea' _]; eauto.
      - intros m Mm ms c gs gs1 t gs2 ws j B ys b HM Hm Hc Heq Hw HB Hy Eb.
        assert (Hjl : j < length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (Hprd _ _ ms c gs gs1 t gs2 ws j ys HM Hm Hc Heq Hw ltac:(lia) Hy) as (Hm2 & Hw2 & Hy2).
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc Heq Hw2 HB Hy2) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold DP, DEl.
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
  | H : suniv_glu_typ_pred ?l _ ?Γ _,
      Hφ : ?Δ ⊢ᵏ ?φ : ?Γ
    |- suniv_glu_typ_pred ?l _ ?Δ _ =>
      let t := fresh "t" in
      let Heq := fresh "Heq" in
      destruct H as [t ? ? Heq]; eapply (mk_suniv_glu_typ _ _ _ _ t[φ]ʷ _);
      [ eapply glu_lvl_resp_wk; eassumption
      | match type of Heq with
        | wf_exp_eq ?T ?X _ ?U ?A _ =>
            assert (T ⍮ X ⍮ Δ ⊢ A[φ]ʷ ≈ (Type⟨t⟩)[φ]ʷ : U) by mauto 2; eassumption
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
      Δ ⊢ᵏ φ : Γ ->
      Δ ⊢ A[φ]ʷ ® P.
Proof.
  simpl. glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply record_glu_typ_pred_wk; eassumption. }
  8:{ apply_equiv_left; eapply (ind_glu_typ_pred_wk p D ups ns NP NEl AP AEl DP DEl); eassumption. }
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
      Δ ⊢ᵏ φ : Γ ->
      Δ ⊢ M[φ]ʷ : A[φ]ʷ ® m ∈ El.
Proof.
  simpl. glu_univ_elem_induction1; intros.
  9:{ apply_equiv_left; eapply record_glu_exp_pred_wk; eassumption. }
  8:{ apply_equiv_left; eapply (ind_glu_exp_pred_wk p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all: saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all; destruct_glu_records.
  all: try solve [ repeat eexists; mauto 2; eapply glu_univ_elem_typ_monotone; eauto ].
  all: try solve [ econstructor; [ mauto 2 | mauto 2 | glu_witness2; [ eassumption | eapply glu_univ_elem_typ_monotone; eauto ] ] ].
  (** An element of a small universe: its type's level term weakens with it,
      and its readback clause composes the two weakenings. *)
  all: try solve [ econstructor;
                   [ mauto 2
                   | glu_witness2; [ eapply glu_lvl_resp_wk; eassumption | mauto 2 ]
                   | glu_witness2;
                     [ eassumption | eapply glu_univ_elem_typ_monotone; eassumption ]
                   | intros; rewrite !exp_wk_wk; mauto 3 ] ].
  (** A level: its readback clause weakens. *)
  all: try solve [ econstructor; [ mauto 2 | assumption | eapply glu_lvl_resp_wk; eassumption ] ].
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

(** Transport along a context refinement, as in [glu_lvl_resp_ctxsub]: a
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

Lemma False_glu_elem_resp_per : forall Γ M m, False_glu_elem Γ M m -> forall m', Dom m ≈ m' ∈ per_ne -> False_glu_elem Γ M m'.
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
  9:{ (** A record type: each projection moves along its field's canonical
          relation, and the field's gluing along the related projections
          before it. *)
      match goal with
      | HEl : El <∙> _, HE : El ?Γ0 ?A0 ?M0 ?m0 |- El ?Γ0 ?A0 ?M0 ?m1 =>
          apply HEl in HE; apply HEl; cbn [record_glu_exp_pred] in HE |- *; destruct HE as [HMt Hmr Ns HNs vs Hvs Hk]
      end.
      rename H into Hl, H0 into HR0, H1 into HeB, H2 into HgB, H3 into HtB.
      match goal with HR : per_univ_elem i ?R0 (d_record p ns) (d_record p ns), Hmm : ?R0 m m' |- _ =>
        rename HR into HRr, Hmm into Hmmr end.
      pose proof HR0 as HR0'; basic_invert_per_univ_elem HR0'.
      match goal with Hl2 : record_lookup _ _ p = Some ?R2 |- _ => assert_fails constr_eq R2 R;
        rewrite Hl in Hl2; injection Hl2 as <- end.
      match goal with HfE : fields_evals _ R ns ns ?fr |- _ => rename HfE into HfEc end.
      pose proof (record_canon_prefix_iff_clause _ _ R ns ns _ (fun _ _ _ H => H) HfEc) as Hiff.
      pose proof (record_rel_canon _ _ _ _ _ _ Hl HRr) as HE.
      pose proof (record_rel_canon _ _ _ _ _ _ Hl HR0) as HE0.
      assert (ER : R0 <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (HPe : PER elem_rel) by (eapply per_elem_PER; eassumption).
      assert (Hm' : elem_rel m m') by (apply ER; exact Hmmr).
      assert (Hm'm' : elem_rel m' m') by (etransitivity; [ symmetry |]; exact Hm').
      destruct (proj1 (HE0 _ _) Hm') as [vs1 vs' Hl1 Hr1 Hrel].
      pose proof (record_projs_functional _ _ _ _ Hl1 Hvs) as ->.
      refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ HMt Hm'm' Ns HNs vs' Hr1 _).
      intros Δ φ Ns' Hφ HNs' k f T r' Hfk Hr'.
      assert (Hkl : k < length (record_fields R)) by (apply List.nth_error_Some; congruence).
      pose proof Hrel as Hrel'; rewrite tele_rel_iff in Hrel'; destruct Hrel' as (Hlv & Hlv' & Hrr).
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [r Hr].
      pose proof (Hk Δ φ Ns' Hφ HNs' k f T r Hfk Hr) as G.
      pose proof (Hrr _ _ _ Hr Hr') as Hrr'.
      pose proof (tele_prefix_rel_of_full _ _ _ _ k Hrel ltac:(lia)) as Hpc.
      pose proof (proj1 (Hiff k _ _ ltac:(lia)) Hpc) as Hpf.
      destruct (HfEc _ _ _ _ _ Hfk Hpf) as [a a' Ea Ea' Haa].
      pose proof (record_projs_prefix_diag _ _ _ _ k (proj1 (HE0 _ _) Hmr) Hvs ltac:(lia)) as Hd.
      pose proof (record_projs_prefix_diag _ _ _ _ k (proj1 (HE0 _ _) Hm'm') Hr1 ltac:(lia)) as Hd'.
      pose proof (HgB _ _ _ _ _ Hfk Hd Ea) as Hga.
      pose proof (HgB _ _ _ _ _ Hfk Hd' Ea') as Hga'.
      assert (Hpaa : per_univ_elem i (canon_fields_rel R ns k (List.firstn k vs)) a a).
      { unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hfk).
        assert (Hpa : per_univ_elem i (fr k (List.firstn k vs)) a a)
          by (eapply per_univ_trans; [ exact Haa | apply per_univ_sym; exact Haa ]).
        exact (per_head_diag Ea Hpa). }
      (** the value moves along the field's relation *)
      pose proof (HtB _ _ _ _ _ Hfk Hd Ea _ Hpaa _ _ _ _ _ G Hrr') as G'.
      (** the gluing moves along the related projections before it *)
      pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R1 => per_univ_elem i R1 a a') _ Haa) Hga) as Hga2.
      destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga2 Hga') as [_ HEq].
      apply HEq; exact G'. }
  8:{ (** An inductive type: [ind_glu_elem] moves along the canonical relation,
          given that the telescopes' gluings move along theirs. *)
      match goal with
      | HEl : El <∙> _, HE : El ?Γ0 ?A0 ?M0 ?m0 |- El ?Γ0 ?A0 ?M0 ?m1 =>
          apply HEl in HE; apply HEl; cbn [ind_glu_exp_pred] in HE |- *; destruct HE as [HMt Hmr Ps0 HPt Hgl]
      end.
      rename H into Hl, H0 into Hass, H1 into HMk, H2 into Hh, H3 into Hu, H4 into HR0, H5 into HeN, H6 into HeA,
        H7 into HgN, H8 into HtN, H9 into HgA, H10 into HtA, H11 into HeD, H12 into HgD, H13 into HtD.
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as [_ _ Hcp _ _ Hadm _ Herel].
      destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as (HevN & HevA & HevD).
      pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
      set (nr := canon_nparams_rel D ups) in *; set (ar := canon_args_rel D ups) in *; set (dr := canon_doms_rel ups) in *.
      assert (Hhd : forall b P0 El0 S ρ, ⟦ S ⟧ ρ ↘ b -> glu_univ_elem i P0 El0 b ->
                    per_univ_elem i (per_head S S ρ ρ) b b).
      { intros * Eb Hg. destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [Rb HRb].
        eapply per_univ_elem_resp_iff; [ exact HRb | exact (per_head_iff Eb Eb HRb) ]. }
      assert (HNe : forall m Mm j vs vs', ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs' ->
                forall Γ0 A0 N n n', NEl m j vs Γ0 A0 N n -> nr m j vs n n' -> NEl m j vs' Γ0 A0 N n').
      { intros m0 Mm j vs vs' HM Hj Hp Γ0 A0 N n n' HN Hnn.
        assert (Hj' : j < length (List.rev (im_nparams Mm))) by (rewrite List.length_rev; exact Hj).
        destruct (nparams_lt_ass D m0 Mm j Hass HM Hj') as [S HS].
        pose proof (nparams_prefix_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM j vs vs' ltac:(lia) Hp) as Hd.
        pose proof (nparams_prefix_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM j vs vs' ltac:(lia) Hp) as Hd'.
        destruct (HeN _ _ _ _ _ HM HS Hd) as [b Eb].
        pose proof (HgN _ _ _ _ _ _ HM HS Hd Eb) as Hgb.
        pose proof (Hhd _ _ _ _ _ Eb Hgb) as Hpb.
        assert (Hn2 : NEl m0 j vs Γ0 A0 N n').
        { unfold nr, canon_nparams_rel in Hnn; rewrite (nth_ctyp_eq _ _ _ _ _ HM HS) in Hnn.
          exact (HtN _ _ _ _ _ _ HM HS Hd Eb _ Hpb _ _ _ _ _ HN Hnn). }
        destruct (HevN _ _ _ _ _ _ HM HS Hp) as [a a' Ea Ea' Haa].
        assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R0 => per_univ_elem i R0 b a') _ Haa) Hgb) as Hga'.
        pose proof (HgN _ _ _ _ _ _ HM HS Hd' Ea') as Hgb'.
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [_ HEq].
        apply HEq; exact Hn2. }
      assert (HAe : forall m Mm ms ms' c gs j vs vs', ind_member D m = Some Mm ->
                tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
                ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) -> tele_prefix_rel (ar m ms c) j vs vs' ->
                forall Γ0 A0 N n n', AEl m ms c j vs Γ0 A0 N n -> ar m ms c j vs n n' -> AEl m ms' c j vs' Γ0 A0 N n').
      { intros m0 Mm ms ms' c gs j vs vs' HM Hm Hc Hj Hp Γ0 A0 N n n' HN Hnn.
        destruct (nth_error_lt_some' _ _ Hj) as [S HS].
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM _ _ Hm) as Hmm.
        pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM _ _ Hm) as Hmm'.
        pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM ms c gs Hmm Hc j vs vs'
                      ltac:(lia) Hp) as Hd.
        pose proof (args_prefix_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM ms ms' c gs j vs vs' Hm Hc
                      ltac:(lia) Hp) as Hd'.
        destruct (HeA _ _ _ _ _ _ _ _ HM Hmm Hc HS Hd) as [b Eb].
        pose proof (HgA _ _ _ _ _ _ _ _ _ HM Hmm Hc HS Hd Eb) as Hgb.
        pose proof (Hhd _ _ _ _ _ Eb Hgb) as Hpb.
        assert (Hn2 : AEl m0 ms c j vs Γ0 A0 N n').
        { unfold ar, canon_args_rel in Hnn; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hc HS) in Hnn.
          exact (HtA _ _ _ _ _ _ _ _ _ HM Hmm Hc HS Hd Eb _ Hpb _ _ _ _ _ HN Hnn). }
        destruct (HevA _ _ _ _ _ _ _ _ _ _ HM Hm Hc HS Hp) as [a a' Ea Ea' Haa].
        assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R0 => per_univ_elem i R0 b a') _ Haa) Hgb) as Hga'.
        pose proof (HgA _ _ _ _ _ _ _ _ _ HM Hmm' Hc HS Hd' Ea') as Hgb'.
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [_ HEq].
        apply HEq; exact Hn2. }
      assert (HDe : forall m Mm ms ms' c gs gs1 t gs2 ws ws' j B ys ys', ind_member D m = Some Mm ->
                tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
                ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                List.nth_error (ptyp_doms t) j = Some B -> tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) j ys ys' ->
                (forall Γ0 A0, DP m (ms ++ ws ++ ys) B Γ0 A0 -> DP m (ms' ++ ws' ++ ys') B Γ0 A0) /\
                (forall Γ0 A0 N n, DEl m (ms' ++ ws' ++ ys') B Γ0 A0 N n -> DEl m (ms ++ ws ++ ys) B Γ0 A0 N n)).
      { intros m0 Mm ms ms' c gs gs1 t gs2 ws ws' j B ys ys' HM Hm Hc Heq Hw HB Hy.
        assert (Hjl : j < length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM _ _ Hm) as Hmm.
        pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM _ _ Hm) as Hmm'.
        pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM ms c gs Hmm Hc _ ws ws'
                      HK Hw) as Hww.
        pose proof (args_prefix_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM ms ms' c gs _ ws ws' Hm Hc HK Hw)
          as Hww'.
        pose proof (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM ms c gs gs1 t gs2 ws Hmm Hc Heq Hww
                      j ys ys' ltac:(lia) Hy) as Hyy.
        pose proof (doms_rel_refl_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m0 Mm HM ms ms' c gs gs1 t gs2 ws ws' j
                      ys ys' Hm Hc Heq Hw ltac:(lia) Hy) as Hyy'.
        destruct (HeD _ _ _ _ _ _ _ _ _ _ _ _ HM Hmm Hc Heq Hww HB Hyy) as [b Eb].
        pose proof (HgD _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hmm Hc Heq Hww HB Hyy Eb) as Hgb.
        destruct (HevD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' Haa].
        assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R0 => per_univ_elem i R0 b a') _ Haa) Hgb) as Hga'.
        pose proof (HgD _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hmm' Hc Heq Hww' HB Hyy' Ea') as Hgb'.
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [HPq HEq].
        split; intros; [ apply HPq | apply HEq ]; assumption. }
      assert (ER : R <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (Hmm' : elem_rel m m') by (apply ER; assumption).
      assert (HPe : PER elem_rel) by (eapply per_elem_PER; eassumption).
      refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMt _ Ps0 HPt _); [ etransitivity; [ symmetry |]; exact Hmm' |].
      intros Δ φ Ps' Hφ HPs'; pose proof (Hgl Δ φ Ps' Hφ HPs') as Hg.
      exact (ind_glu_elem_resp_per p D ups NEl AEl DP DEl Hass Hcp HNe HAe HDe _ _ _ _ _ _ Hg _ _ _ (proj1 (Herel _ _) Hmm')). }
  6:{ handle_per_univ_elem_irrel.
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
       apply_predicate_equivalence; simpl in *; destruct_conjs; destruct_glu_records.
  - match goal with E : elem_rel <~> _, Hm : elem_rel m m' |- _ =>
      destruct (proj1 (E m m') Hm) as [R' HR'] end.
    econstructor; try assumption.
    glu_witness2; [ eapply glu_univ_elem_resp_per_univ; [ exists R'; exact HR' | eassumption ] | eassumption ].
  (** A small universe: as the large one, and the readback clause moves along
      the two types, which read back equally. *)
  - match goal with E : elem_rel <~> _, Hm : elem_rel m m' |- _ =>
      destruct (proj1 (E m m') Hm) as [R' HR'] end.
    econstructor; try assumption.
    + glu_witness2; eassumption.
    + glu_witness2;
        [ eapply glu_univ_elem_resp_per_univ; [ exists R'; exact HR' | eassumption ] | eassumption ].
    + intros * Hk Hr.
      match goal with Hrb : forall _ _ _, _ -> Rtyp m in _ ↘ _ -> _ |- _ => apply Hrb; [ exact Hk |] end.
      eapply per_top_typ_read_left; [ eapply per_univ_then_per_top_typ; exact HR' | exact Hr ].
  (** [Level]: the readback moves along the level PER. *)
  - assert (Dom m ≈ m' ∈ per_lvl_at n) as Hmm'
      by (match goal with E : _ <~> per_lvl_at _ |- _ => apply E; eassumption end).
    econstructor;
      [ assumption
      | eapply per_lvl_at_trans; [ eapply per_lvl_at_sym; exact Hmm' | exact Hmm' ]
      | eapply glu_lvl_resp_per; [ eassumption | eapply per_lvl_at_lvl; exact Hmm' ] ].
  - split; assumption.
  - split; [ assumption | eapply False_glu_elem_resp_per; [ eassumption | apply H1; eassumption ] ].
  - destruct_by_head neut_glu_exp_pred.
    match goal with E : _ <~> per_ne, Hm : _ ?x ?y |- _ => apply E in Hm; inversion Hm; subst end.
    econstructor; [ assumption | assumption | etransitivity; [ symmetry |]; eassumption |].
    intros * Hk Hr; eauto using per_bot_read_left.
Qed.

End Fixed_GCtx.
