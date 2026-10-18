(** * Changing the Parameters of an Eliminator

    The contexts of an eliminator's motive and branches are instances at its
    uniform parameters; at equal parameters, they are equal telescopes.  A
    checker infers the parameters of the scrutinee's type, which are equal
    to, not the same as, those of a derivation, so it is what moves the
    premises of the eliminator to them. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Syntactic.System Require Import GlobalPresup IndTyping.
From Mctt.Core.Syntactic Require Import IndCong CoreInversions.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {Θ : gdeps} {Ξ : gstack}.

  (** ** Telescopes of Assumptions *)

  Lemma sb_qn_eq_ext : forall Ψ Δ Γ σ σ', tele_ass Ψ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
      Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ ⊢ˢ sb_qn (List.length Ψ) σ ≈ sb_qn (List.length Ψ) σ' : Ψ ++ Δ.
  Proof.
    intros * Hass HΨ Hσ.
    exact (proj1 (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 sub_eq_preserves_mut)))) _ _ _ _ _ (ctx_ext_refl _ _ _ _ Hass HΨ) _ _ _ Hσ) Hass)).
  Qed.

  Lemma tele_sub_eq_ext : forall Ψ Δ Γ σ σ', tele_ass Ψ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ σ'.
  Proof.
    induction Ψ as [| e Ψ IH]; intros * Hass HΨ Hσ.
    - cbn; constructor; gen_presups; assumption.
    - inversion Hass as [| ? ? [A ->] Hass']; subst.
      cbn [List.app] in HΨ; destruct (ctx_decomp HΨ) as [HΨ' [j HA]].
      assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ : Δ) by (gen_presups; mauto 2).
      assert (Hσσ' : Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ' ≈ σ' : Δ) by (gen_presups; mauto 2).
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσ) as Hq.
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσσ) as Hq1.
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσσ') as Hq2.
      assert (Hs1 : Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ ⊢ˢ sb_qn (List.length Ψ) σ : Ψ ++ Δ) by (gen_presups; assumption).
      assert (Hs2 : Θ ⍮ Ξ ⍮ tele_sub Ψ σ' ++ Γ ⊢ˢ sb_qn (List.length Ψ) σ' : Ψ ++ Δ) by (gen_presups; assumption).
      cbn [tele_sub centry_sub].
      eapply wf_ext_eq_ass; [ exact (IH _ _ _ _ Hass' HΨ' Hσ) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hs1)
                            | exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HA Hq) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hs2) ].
  Qed.

  (** ** The Motive's Context *)

  Lemma uparams_ctx_wf : forall Γ D, decl_typed Θ Ξ D -> decl_closed D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ.
  Proof.
    intros * HD Hc HΓ.
    pose proof (dt_params _ _ _ HD) as HΔ; rewrite params_split in HΔ.
    apply wf_ctx_closed_app; [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) | eapply ctx_app_wf_tail; exact HΔ | exact HΓ ].
  Qed.

  Lemma uvars_typed : forall Γ D, decl_typed Θ Ξ D -> decl_closed D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      forall k U T, List.nth_error (vars_from 0 (ind_nu D)) k = Some U ->
        List.nth_error (tele_insts (ind_uparams D) Id (vars_from 0 (ind_nu D))) k = Some T ->
        Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ ⊢ U : T.
  Proof.
    intros * HD Hc HΓ k U T HU HT.
    pose proof (dmv_params _ (dt_mvc _ _ _ HD)) as Hmv.
    pose proof (decl_closed_nu D Hc) as Hle.
    rewrite <- (length_ind_uparams D Hle) in HU, HT.
    change 0 with (List.length (@nil centry)) in HU, HT.
    pose proof (uparams_ctx_wf _ _ HD Hc HΓ) as HUΓ.
    rewrite <- (tele_sub_id (ind_uparams D)) in HUΓ |- *.
    eapply (wf_vars_tele_gen _ _ nil (ind_uparams D) Id Id Γ 0); try eassumption.
    - exact (decl_uparams_ass D Hc).
    - apply Forall_skipn'; exact Hmv.
    - exact (decl_uparams_closed D Hc).
    - intros; lia.
  Qed.

  Lemma elim_mctx_canon : forall p D V, decl_closed D -> List.length V = ind_nu D ->
      elim_mctx p D V = tele_sub (elim_mctx p D (vars_from 0 (ind_nu D))) (sb_of_list Id V).
  Proof.
    intros * Hc HV.
    rewrite elim_mctx_sub by (exact Hc || apply length_vars_from).
    rewrite <- HV, vars_from_sb_of_list; reflexivity.
  Qed.

  Lemma elim_mctx_canon_wf : forall Γ p D, decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (vars_from 0 (ind_nu D)) ++ ind_uparams D ++ Γ.
  Proof.
    intros * HD Hc Hl HΓ.
    eapply elim_mctx_wf; [ exact HD | exact Hc | exact Hl | exact (uparams_ctx_wf _ _ HD Hc HΓ) | apply length_vars_from |].
    exact (uvars_typed _ _ HD Hc HΓ).
  Qed.

  Lemma elim_mctx_us_eq : forall Γ p D Us Us', decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us'.
  Proof.
    intros * HD Hc Hl HΓ HUl HUl' Hσ.
    rewrite (elim_mctx_canon p D Us Hc HUl), (elim_mctx_canon p D Us' Hc HUl').
    eapply tele_sub_eq_ext; [ apply elim_mctx_ass, Hc | exact (elim_mctx_canon_wf _ _ _ HD Hc Hl HΓ) | exact Hσ ].
  Qed.

  (** ** The Recursive Results' Instances *)

Lemma wf_sub_eq_prefix : forall Ψ Δ Γ σ σ', Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : Δ.
Proof.
  intros * [Hl0 Hr0 Ha Hm] HΔ; constructor;
    [ exact (wf_sub_prefix _ _ _ _ _ _ Hl0 HΔ) | exact (wf_sub_prefix _ _ _ _ _ _ Hr0 HΔ) | |].
  - intros x A Hx; apply Ha, ctx_lookup_app_l; exact Hx.
  - intros x U Hx; eapply Hm, ctx_lookup_mod_app_l; exact Hx.
Qed.

(** The motive's instance at a shape's leaf, at equal substitutions of the
    shape's components. *)
Lemma ih_leaf_sub_eq : forall Γ p D Us Ψ Tc β σ σ' Ps x,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Tc -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : Tc ->
    shape_uc D Us Tc σ β ->
    List.length Ps = ind_nn D ->
    (forall k P T, List.nth_error Ps k = Some P ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))) Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Tc ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ x : apps (a_ind p) (List.map (fun U => U[β]) Us ++ List.map (fun P => P[σ]) Ps) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps ++ x :: nil)
      ≈ sb_of_list β (List.map (fun P => P[σ']) Ps ++ x :: nil) : elim_mctx p D Us ++ Γ.
Proof.
  intros * HD Hc Hl HUl HM Hβ Hσ Hσσ Huc HPl HP Hx.
  assert (HN : ⊢ Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ)
    by (unfold elim_mctx in HM; cbn [List.app] in HM; destruct (ctx_decomp HM) as [H0 _]; exact H0).
  assert (Hnn : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps) ≈ sb_of_list β (List.map (fun P => P[σ']) Ps)
                  : tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ).
  { apply wf_sub_eq_of_list; [ apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact HN | apply wf_sub_eq_refl; exact Hβ
                             | rewrite length_tele_sub, List.length_map, HPl, length_nparams; reflexivity
                             | rewrite length_tele_sub, List.length_map, HPl, length_nparams; reflexivity |].
    intros k N N' T HN1 HN2 HT.
    apply nth_error_map_inv in HN1 as (P & HPk & ->).
    apply nth_error_map_inv in HN2 as (P1 & HPk1 & ->); rewrite HPk in HPk1; injection HPk1 as <-.
    rewrite tele_insts_tele_sub in HT.
    set (σ0 := sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))).
    assert (HT0 : exists T0, List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k = Some T0).
    { destruct (List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k) as [T0 |] eqn:E0; [ eauto |].
      apply List.nth_error_None in E0; rewrite length_tele_insts in E0 by (apply decl_closed_nparams_ass, Hc).
      rewrite length_nparams, HPl in E0.
      assert (Hk : k < List.length Ps) by (apply List.nth_error_Some; congruence); lia. }
    destruct HT0 as [T0 HT0].
    pose proof (proj1 sub_eq_preserves_mut _ _ _ _ _ (HP _ _ _ HPk HT0) _ _ _ Hσσ) as HP1.
    replace T with T0[σ]; [ exact HP1 |].
    rewrite <- (tele_insts_sub_mvc (ind_nparams D) (ind_nu D) σ0 _ σ Ps) in HT.
    + apply nth_error_map_inv in HT as (T1 & HT1 & ->); rewrite HT0 in HT1; injection HT1 as ->; reflexivity.
    + apply decl_closed_nparams_ass, Hc.
    + apply (decl_nparams_mvc _ _ _ HD).
    + apply decl_closed_nparams_scoped, Hc.
    + intros y Hy; unfold σ0; cbn [sb_of_wk sentry_sub wk_shiftn]; exact (Huc y Hy). }
  destruct (elim_mctx_head_typed _ _ _ _ _ _ HM) as [j Hj].
  rewrite !sb_of_list_app; cbn [sb_of_list]; unfold elim_mctx; cbn [List.app].
  pose proof Hx as Hx'.
  rewrite <- (ind_head_inst p D Us (List.map (fun P => P[σ]) Ps) β) in Hx' by (rewrite List.length_map; exact HPl).
  pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ Hj Hnn) as Hhh.
  eapply wf_sub_eq_extend; [ exact Hnn | exact Hj | exact Hx'
                           | eapply wf_conv; [ exact Hx' | exact (sub_preserves_exp _ _ _ _ _ _ _ Hj (wf_sub_eq_right _ _ _ _ _ _ Hnn)) | exact Hhh ]
                           | apply wf_exp_eq_refl; exact Hx' ].
Qed.

(** The type of a recursive result of a shape, at equal substitutions of
    the shape's components. *)
Lemma ihty_sub_eq : forall Γ p D Us A i t Ψ Bs1 Tb β σ σ' x,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ ind_params D ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : doms_ctx Bs1 ++ Tb ++ ind_params D ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ ind_params D) σ β ->
    List.length (ptyp_ps t) = ind_nn D ->
    shape_doms_typed Θ Ξ D Bs1 Tb t -> shape_leaf_typed Θ Ξ D Bs1 Tb t ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ x : ptyp_ty_at p (List.map (fun U => U[β]) Us) σ t ->
    exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty A β σ x t ≈ ptyp_ihty A β σ' x t : Typeω@j.
Proof.
  intros Γ p D Us A i t; induction t as [k0 Ps | k0 Ps | B t IH];
    intros * HD Hc Hl HUl HM HA Hβ Hσ Hσσ Huc HPl HB HP Hx; cbn [ptyp_ihty ptyp_ty_at] in *.
  1, 2: exists i; exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HA
          (ih_leaf_sub_eq _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HM Hβ Hσ Hσσ Huc HPl
             (shape_leaf_at _ _ _ _ _ _ Hc HP eq_refl) Hx)).
  cbn [ptyp_ps] in HPl.
  destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
  pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ Hj1 Hσσ) as HBB.
  assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
  pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
  pose proof (wf_sub_eq_q _ _ _ _ _ _ _ _ Hσσ Hj1 HBB) as Hσσ'.
  assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
    by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
  replace ((doms_ctx Bs1 ++ Tb ++ ind_params D) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ ind_params D) in Hσ', Hσσ'
    by (rewrite doms_ctx_app_one; reflexivity).
  assert (Huc' : shape_uc D Us (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ ind_params D) (q σ) (β ⨟ ι ↑))
    by (rewrite doms_ctx_app_one; apply shape_uc_pi; [ exact (proj2 (length_shape_ctx D Bs1 Tb Hc)) | exact Huc ]).
  pose proof (shape_doms_typed_pi _ _ _ _ _ _ _ HB) as HB''.
  pose proof (shape_leaf_typed_pi _ _ _ _ _ _ _ HP) as HP''.
  assert (Hus : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[β]) Us) = List.map (fun U => U[β ⨟ ι ↑]) Us)
    by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
  rewrite Hus in Hx.
  destruct (ty_at_typed _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HM Hβ' Hσ' Huc' HPl HB'' HP'') as [j2 Hj2].
  pose proof (shape_arg_app _ _ _ _ _ _ _ _ Hj1' Hj2 Hx) as Hx'.
  destruct (IH _ _ _ _ _ _ _ HD Hc Hl HUl HM HA Hβ' Hσ' Hσσ' Huc' HPl HB'' HP'' Hx') as (j3 & H3).
  exists (max j1 j3).
  eapply wf_exp_eq_pi_cong_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_eq_max_left; exact HBB
                            | eapply lift_exp_eq_max_right; exact H3 ].
Qed.

(** The components of a recursive argument in a branch's context, at
    equal uniform parameters. *)
Lemma ihs_sub_us_eq : forall Γ p D Us Us' c gs gs1 t gs2 E,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
    List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ->
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ˢ ihs_sub D Us (List.length gs) (cargs_pat gs1) (List.length E)
      ≈ ihs_sub D Us' (List.length gs) (cargs_pat gs1) (List.length E) : doms_ctx nil ++ cargs_strat gs1 ++ ind_params D.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ Hσσ Hin Heq HΨ.
  pose proof HD as [Hass [Hmv Hmvs Hmvc] Hle HΔ HS _ _ _ _ _ _ _ _].
  set (pat := cargs_pat gs1) in *.
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  set (i := List.length pat) in *.
  set (j := List.length E) in *.
  set (na := List.length gs) in *.
  set (s := na - i + j).
  set (ρ := sb_qn (i + ind_nn D) (sb_of_list Id Us)).
  set (ρ' := sb_qn (i + ind_nn D) (sb_of_list Id Us')).
  destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs1 (ca_rec t :: gs2) Heq) as (HΨ1 & _ & Hφ).
  assert (Hw3 : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ʷ wk_shiftn s : cinst Γ p D Us gs1).
  { rewrite Heq in HΨ |- *; rewrite cinst_split in HΨ |- *; rewrite List.app_assoc in HΨ |- *.
    replace s with (List.length (E ++ tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                                     (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                                     ++ ce_ass (ptyp_ty p D (cargs_pat gs1) t)
                                          [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))] :: nil))
      by (rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; unfold s, na, i, j; rewrite Heq, List.length_app; cbn; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  assert (Hτ2e : Θ ⍮ Ξ ⍮ cinst Γ p D Us gs1 ⊢ˢ ρ ≈ ρ' : cargs_ctx p D gs1 ++ ind_params D ++ Γ).
  { assert (HΨΓ : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D gs1 ++ ind_params D) ++ Γ).
    { apply wf_ctx_closed_app; [| eapply cargs_ctx_closed; eassumption | exact HΨ1 | exact HΓ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]. }
    rewrite params_split, <- !List.app_assoc, (List.app_assoc (cargs_ctx p D gs1)) in HΨΓ.
    assert (Hass1 : tele_ass (cargs_ctx p D gs1 ++ ind_nparams D))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ]).
    pose proof (sb_qn_eq_ext _ _ _ _ _ Hass1 HΨΓ Hσσ) as H.
    rewrite <- cinst_eq in H; rewrite List.length_app, length_cargs_ctx, length_nparams in H.
    rewrite <- Hpat in H; fold i ρ ρ' in H.
    rewrite params_split, <- (List.app_assoc (ind_nparams D)), List.app_assoc; exact H. }
  change (ihs_sub D Us na pat j) with ((ι (wk_pat pat) ⨟ ρ) ⨟ ι (wk_shiftn s)).
  change (ihs_sub D Us' na pat j) with ((ι (wk_pat pat) ⨟ ρ') ⨟ ι (wk_shiftn s)).
  cbn [doms_ctx List.rev List.map List.app].
  eapply wf_sub_eq_compose_left; [| apply wf_sub_of_wk; exact Hw3 ].
  eapply wf_sub_eq_compose_right; [ apply wf_sub_of_wk; exact Hφ |].
  rewrite List.app_assoc in Hτ2e; exact (wf_sub_eq_prefix _ _ _ _ _ Hτ2e HΨ1).
Qed.

(** The type of the recursive result of a recursive argument, in a
    branch's context, at equal uniform parameters. *)
Lemma rec_ih_us_eq : forall Γ p D Us Us' A i c gs gs1 t gs2 E,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ->
    let T V := ptyp_ihty A (ι (wk_shiftn (List.length E + List.length gs + ind_nn D)))
                 (ihs_sub D V (List.length gs) (cargs_pat gs1) (List.length E))
                 (a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1))) t in
    exists j, Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ T Us ≈ T Us' : Typeω@j.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ Hσσ HM HA Hin Heq HΨ T.
  destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ Hin Heq HΨ) as (Hb & Hθ & Huc & Hx).
  destruct (decl_shape_facts _ _ _ _ _ _ _ _ HD Hc Hin Heq) as (HPl & HBt & HPt).
  pose proof (ihs_sub_us_eq _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl Hσ Hσσ Hin Heq HΨ) as Hθθ.
  exact (ihty_sub_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HM HA Hb Hθ Hθθ Huc HPl HBt HPt Hx).
Qed.


  Lemma ihs_ctx_us_eq : forall Γ p D Us Us' A i c gs,
      decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us' ++ Γ ->
      Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
      Θ ⍮ Ξ ⍮ elim_mctx p D Us' ++ Γ ⊢ A : Typeω@i ->
      List.In (c, gs) (ind_cons D) ->
      forall rest gs1 E E', gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 -> List.length E' = cargs_nrec gs1 ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ E ++ ctel p D Us gs ≈ E' ++ ctel p D Us' gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E ++ ctel p D Us gs
                 ≈ ihs_ctx_aux D A Us' (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E' ++ ctel p D Us' gs.
  Proof.
    intros * HD Hc Hl HΓ HUl HUl' Hσ Hσ' Hσσ HM HM' HA HA' Hin rest.
    induction rest as [| [B | Ps] rest IH]; intros gs1 E E' Heq HE HE' HEE; cbn [ihs_ctx_aux List.app]; [ exact HEE | |].
    - replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg B :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | rewrite cargs_nrec_snoc, HE'; lia | exact HEE ].
    - assert (HΨ : ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs)
        by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_left; exact HEE).
      assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ E' ++ cinst Γ p D Us' gs)
        by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_right; exact HEE).
      destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM HA HA (wf_exp_eq_refl HA) Hin Heq HΨ)
        as (j1 & Hj & _).
      destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' HD Hc Hl HΓ HUl' Hσ' HM' HA' HA' (wf_exp_eq_refl HA') Hin Heq HΨ')
        as (j2 & Hj' & _).
      destruct (rec_ih_us_eq _ _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ Hσσ HM HA Hin Heq HΨ) as (j3 & Hjj).
      cbv zeta in Hj, Hj', Hjj.
      rewrite HE', <- HE in Hj'.
      rewrite cinst_ctel, List.app_assoc in Hj, Hj', Hjj.
      replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
      rewrite <- !List.app_assoc.
      eapply (IH (gs1 ++ ca_rec Ps :: nil) (_ :: E) (_ :: E'));
        [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
        | cbn; rewrite cargs_nrec_snoc, HE'; lia |].
      cbn [List.app]; eapply wf_ext_eq_ass;
        [ exact HEE | exact (lift_exp_ge _ _ _ _ j1 (max j1 (max j2 j3)) ltac:(lia) Hj)
        | exact (lift_exp_eq_ge _ _ _ _ _ j3 (max j1 (max j2 j3)) ltac:(lia) Hjj)
        | exact (lift_exp_ge _ _ _ _ j2 (max j1 (max j2 j3)) ltac:(lia) Hj') ].
  Qed.

  (** ** The Branches' Contexts *)

  Lemma elim_bctx_us_eq : forall Γ p D Us Us' A i c gs,
      decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us' ++ Γ ->
      Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
      Θ ⍮ Ξ ⍮ elim_mctx p D Us' ++ Γ ⊢ A : Typeω@i ->
      ind_con D c = Some gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us'.
  Proof.
    intros * HD Hc Hl HΓ HUl HUl' Hσ Hσ' Hσσ HM HM' HA HA' Hcon.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (Hct : forall V, ctel p D V gs = tele_sub (cargs_ctx p D gs ++ ind_nparams D) (sb_of_list Id V))
      by (intros; unfold ctel; rewrite tele_sub_app, length_nparams; reflexivity).
    assert (H0 : Θ ⍮ Ξ ⍮ Γ ⊢ˣ nil ++ ctel p D Us gs ≈ nil ++ ctel p D Us' gs).
    { cbn [List.app]; rewrite !Hct.
      destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ1 & _ & _).
      assert (HΨΓ : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D gs ++ ind_params D) ++ Γ).
      { apply wf_ctx_closed_app; [| exact (cargs_ctx_closed p D c gs gs nil Hc Hin (eq_sym (List.app_nil_r gs))) | exact HΨ1 | exact HΓ ].
        apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]. }
      rewrite params_split, <- !List.app_assoc, (List.app_assoc (cargs_ctx p D gs)) in HΨΓ.
      eapply tele_sub_eq_ext; [| exact HΨΓ | exact Hσσ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ]. }
    exact (ihs_ctx_us_eq _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl HUl' Hσ Hσ' Hσσ HM HM' HA HA' Hin gs nil nil nil eq_refl eq_refl eq_refl H0).
  Qed.

  (** ** The Branches' Types *)

Lemma wf_bty_sub_eq : forall Γ p D Us Us' A i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    List.length Us' = ind_nu D ->
    (forall k U U' T, List.nth_error Us k = Some U -> List.nth_error Us' k = Some U' ->
       List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U ≈ U' : T) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    ind_con D c = Some gs ->
    Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ
      ⊢ˢ sb_of_list (ι (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)))
           (vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++
            apps (a_con p c) (List.map (fun U => U[wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)]ʷ) Us ++
                              vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++ vars_from (cargs_nrec gs) (List.length gs))
            :: nil)
      ≈ sb_of_list (ι (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)))
           (vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++
            apps (a_con p c) (List.map (fun U => U[wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)]ʷ) Us' ++
                              vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++ vars_from (cargs_nrec gs) (List.length gs))
            :: nil)
      : elim_mctx p D Us ++ Γ.
Proof.
  intros * HD Hc Hl HΓ HUl HUs HUl' HUU HM HA Hcon.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  pose proof (decl_closed_nu D Hc) as Hle.
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  pose proof (elim_bctx_wf _ _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl Hσ HM HA Hcon) as HB.
  set (n := ind_nn D + List.length gs + cargs_nrec gs).
  set (IHs := ihs_ctx_aux D A Us (List.length gs) nil 0 gs).
  set (Cs := tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us))).
  set (Ns := tele_sub (ind_nparams D) (sb_of_list Id Us)).
  assert (HBeq : elim_bctx p D gs A Us ++ Γ = (IHs ++ Cs) ++ Ns ++ Γ) by (unfold elim_bctx; rewrite <- !List.app_assoc; reflexivity).
  assert (HlI : List.length IHs = cargs_nrec gs) by (unfold IHs; apply length_ihs_ctx_aux).
  assert (HlC : List.length Cs = List.length gs) by (unfold Cs; rewrite length_tele_sub, length_cargs_ctx; reflexivity).
  assert (HlN : List.length Ns = ind_nn D) by (unfold Ns; apply length_ind_nparams_sub).
  assert (Hw : Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ʷ wk_shiftn n : Γ).
  { rewrite HBeq, List.app_assoc.
    replace n with (List.length ((IHs ++ Cs) ++ Ns)) by (rewrite !List.length_app, HlI, HlC, HlN; unfold n; lia).
    apply wf_wk_shiftn_app'; rewrite <- List.app_assoc, <- HBeq; exact HB. }
  (* the uniform parameters, shifted, and the non-uniform ones, as variables *)
  set (Uw := List.map (fun U => U[wk_shiftn n]ʷ) Us).
  assert (HUw : forall k U T, List.nth_error Uw k = Some U ->
             List.nth_error (tele_insts (ind_uparams D) Id Uw) k = Some T -> Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ U : T).
  { intros k U' T' HU HT; unfold Uw in *.
    rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
    apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    exact (wk_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hw). }
  assert (Hvars : forall τ, (forall y, y < ind_nu D -> sentry_exp (τ y) = (sentry_exp (sb_of_list Id Us y))[wk_shiftn n]ʷ) ->
             forall k N T, List.nth_error (vars_from (cargs_nrec gs + List.length gs) (ind_nn D)) k = Some N ->
               List.nth_error (tele_insts (ind_nparams D) τ (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) k = Some T ->
               Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ N : T).
  { intros τ Hτ k N T HN HT.
    replace (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))
      with (vars_from (List.length (IHs ++ Cs)) (List.length (ind_nparams D))) in HN, HT
      by (rewrite List.length_app, HlI, HlC, length_nparams; reflexivity).
    rewrite HBeq.
    eapply (wf_vars_tele_gen _ _ _ _ (sb_of_list Id Us) τ Γ (ind_nu D));
      [ apply decl_closed_nparams_ass, Hc | apply (decl_nparams_mvc _ _ _ HD) | apply decl_closed_nparams_scoped, Hc
      | fold Ns; rewrite <- HBeq; exact HB | | exact HN | exact HT ].
    intros y Hy; rewrite Hτ by exact Hy; rewrite List.length_app, HlI, HlC, length_nparams; unfold n; f_equal; f_equal; lia. }
  (* the substitution *)
  assert (HUUw : forall k U U' T, List.nth_error Uw k = Some U ->
             List.nth_error (List.map (fun U => U[wk_shiftn n]ʷ) Us') k = Some U' ->
             List.nth_error (tele_insts (ind_uparams D) Id Uw) k = Some T -> Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ U ≈ U' : T).
  { intros k U0 U0' T' HU HU' HT; unfold Uw in *.
    rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
    apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HU' as (U1 & HU1 & ->);
      apply nth_error_map_inv in HT as (T & HT & ->).
    exact (wk_preserves_exp_eq _ _ _ _ _ _ _ _ (HUU _ _ _ _ HU HU1 HT) Hw). }
  apply wf_sub_eq_of_list; [ apply elim_mctx_ass, Hc | exact HM | apply wf_sub_eq_refl, wf_sub_of_wk, Hw
                           | rewrite List.length_app, length_vars_from, length_elim_mctx; cbn; lia
                           | rewrite List.length_app, length_vars_from, length_elim_mctx; cbn; lia |].
  intros k N N' T HN HN' HT.
  unfold elim_mctx in HT.
  change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
  assert (Hrass : tele_ass Ns) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
  rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_vars_from; symmetry; exact HlN).
  fold Ns in HT.
  assert (Hl2 : List.length (tele_insts Ns (ι (wk_shiftn n)) (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) = ind_nn D)
    by (rewrite length_tele_insts by exact Hrass; rewrite HlN, length_vars_from; lia).
  destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HN by (rewrite length_vars_from; lia); rewrite List.nth_error_app1 in HT by lia.
    rewrite List.nth_error_app1 in HN' by (rewrite length_vars_from; lia); rewrite HN in HN'; injection HN' as <-.
    unfold Ns in HT; rewrite tele_insts_tele_sub in HT.
    apply wf_exp_eq_refl.
    apply (Hvars _ ltac:(intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; reflexivity) k); assumption.
  - rewrite List.nth_error_app2 in HN, HN', HT by (rewrite ?length_vars_from; lia); rewrite length_vars_from in HN, HN'; rewrite Hl2 in HT.
    destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HN', HT; [| destruct k'; discriminate ].
    injection HN as <-; injection HN' as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
    rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
    rewrite (List.map_ext _ (fun U => U[ι (wk_shiftn n)]))
      by (intros a; replace (ind_nn D) with (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) at 1
            by apply length_vars_from; exact (exp_shift_past a nil _ _)).
    replace (vars_from 0 (ind_nn D)) with (vars_from 0 (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))))
      by (rewrite length_vars_from; reflexivity).
    rewrite vars_from_sb_of_list.
    rewrite (List.map_ext (fun U => U[ι (wk_shiftn n)]) (fun U => U[wk_shiftn n]ʷ)) by (intros; apply exp_sub_of_wk); fold Uw.
    clear Hk' Hk Hl2 k.
    rewrite (List.app_assoc Uw), (List.app_assoc (List.map (fun U => U[wk_shiftn n]ʷ) Us')).
    apply (wf_exp_eq_con_apps _ p D c gs); [ exact Hl | exact Hcon | exact HB | | | | | | ].
    + rewrite List.length_app, length_vars_from; unfold Uw; rewrite List.length_map, HUl; unfold ind_nn; lia.
    + rewrite List.length_app, length_vars_from, List.length_map, HUl'; unfold ind_nn; lia.
    + rewrite params_split; intros k N N' T HN HN' HT.
      rewrite tele_insts_app in HT;
        [| exact (decl_uparams_ass D Hc) | unfold Uw; rewrite List.length_map, HUl, length_ind_uparams by exact Hle; reflexivity ].
      assert (Hl1 : List.length Uw = ind_nu D) by (unfold Uw; rewrite List.length_map; exact HUl).
      assert (Hl3 : List.length (tele_insts (ind_uparams D) Id Uw) = ind_nu D)
        by (rewrite length_tele_insts by exact (decl_uparams_ass D Hc); rewrite Hl1, length_ind_uparams by exact Hle; lia).
      destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk2 | Hk2].
      * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
        rewrite List.nth_error_app1 in HN' by (rewrite List.length_map; lia).
        exact (HUUw _ _ _ _ HN HN' HT).
      * rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl1 in HN; rewrite Hl3 in HT.
        rewrite List.nth_error_app2 in HN' by (rewrite List.length_map; lia); rewrite List.length_map, HUl' in HN'.
        rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl.
        apply (Hvars (sb_of_list Id Uw) ltac:(intros y Hy; unfold Uw; rewrite sb_of_list_map by lia; reflexivity) (k - ind_nu D)); [ exact HN | exact HT ].
    + rewrite length_vars_from; reflexivity.
    + rewrite length_vars_from; reflexivity.
    + intros k N N' T HN HN' HT.
      rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl.
      replace (vars_from (cargs_nrec gs) (List.length gs)) with (vars_from (List.length IHs) (List.length (cargs_ctx p D gs))) in HN, HT
        by (rewrite HlI, length_cargs_ctx; reflexivity).
      rewrite HBeq, <- List.app_assoc.
      eapply (wf_vars_tele_gen _ _ IHs (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)) _ (Ns ++ Γ) (ind_np D));
        [ apply cargs_ctx_aux_ass | eapply cargs_ctx_mvc; eassumption | eapply decl_closed_cargs_scoped; eassumption
        | fold Cs; rewrite List.app_assoc, <- HBeq; exact HB | | exact HN | exact HT ].
      intros y Hy; rewrite length_cargs_ctx, HlI.
      destruct (Nat.lt_ge_cases y (ind_nn D)) as [Hy1 | Hy1].
      * rewrite sb_of_list_app, sb_of_list_vars by lia; rewrite sb_qn_lt by exact Hy1; cbn; f_equal; lia.
      * replace y with (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D)) + (y - ind_nn D)) at 1
          by (rewrite length_vars_from; lia).
        rewrite sb_of_list_app, sb_of_list_ge; unfold Uw; rewrite sb_of_list_map by (rewrite HUl; unfold ind_nn in *; lia).
        rewrite sb_qn_ge by exact Hy1; rewrite <- sentry_exp_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold n; lia.
Qed.

(** ** Telescope Conversion *)

  (** ** The Parameters, Split *)

  Lemma params_eq_split : forall Γ D Ps Ps', decl_closed D ->
      List.length Ps = ind_np D -> List.length Ps' = ind_np D ->
      (forall k P P' T, List.nth_error Ps k = Some P -> List.nth_error Ps' k = Some P' ->
         List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T) ->
      (forall k U U' T, List.nth_error (List.firstn (ind_nu D) Ps) k = Some U -> List.nth_error (List.firstn (ind_nu D) Ps') k = Some U' ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U ≈ U' : T) /\
      (forall k N N' T, List.nth_error (List.skipn (ind_nu D) Ps) k = Some N -> List.nth_error (List.skipn (ind_nu D) Ps') k = Some N' ->
         List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T).
  Proof.
    intros * Hc Hl Hl' HPs.
    pose proof (decl_closed_nu D Hc) as Hle.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
    assert (HUl' : List.length (List.firstn (ind_nu D) Ps') = ind_nu D) by (rewrite List.length_firstn; lia).
    assert (Hti : tele_insts (ind_params D) Id Ps
                  = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                    ++ tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
    { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite params_split; apply tele_insts_app;
        [ apply (decl_uparams_ass D Hc) | rewrite HUl, length_ind_uparams by exact Hle; reflexivity ]. }
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
      by (rewrite length_tele_insts by apply (decl_uparams_ass D Hc); rewrite HUl, length_ind_uparams by exact Hle; lia).
    split; intros k N N' T HN HN' HT.
    - assert (Hk : k < ind_nu D) by (rewrite <- HUl; apply List.nth_error_Some; congruence).
      apply (HPs k);
        [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by lia; exact HN
        | rewrite <- (List.firstn_skipn (ind_nu D) Ps'), List.nth_error_app1 by lia; exact HN'
        | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    - apply (HPs (ind_nu D + k)).
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + k - ind_nu D) with k by lia; exact HN.
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps') at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl'; replace (ind_nu D + k - ind_nu D) with k by lia; exact HN'.
      + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + k - ind_nu D) with k by lia; exact HT.
  Qed.

  (** The type former at equal parameters, in a large universe. *)
  Lemma ind_apps_eq_large_syn : forall Γ p D Xs Ys, ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Xs = ind_np D -> List.length Ys = ind_np D ->
      (forall k X Y T, List.nth_error Xs k = Some X -> List.nth_error Ys k = Some Y ->
         List.nth_error (tele_insts (ind_params D) Id Xs) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      exists k, Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_ind p) Xs ≈ apps (a_ind p) Ys : Typeω@k.
  Proof.
    intros * Hl HΓ HXl HYl HXY.
    pose proof (wf_exp_eq_ind_apps _ _ _ _ _ Hl HΓ HXl HYl HXY) as Heq.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [[_ _ _ _ Hsu _ _ _ _ _ _ _ _] _].
    destruct Hsu as [[i0 Hs] | [t Hs]]; rewrite Hs in Heq; cbn in Heq.
    - exists i0; exact Heq.
    - exists 0.
      assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨t[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Xs]⟩ : Typeω@i) as [i HT] by (gen_presups; eauto).
      destruct (wf_univ_lvl_inversion HT) as [n Hn].
      eapply wf_exp_eq_subtyp'; [ exact Heq | eapply wf_subtyp_small_large; eassumption ].
  Qed.

  (** ** The Eliminator's Premises at Equal Parameters *)

  Lemma wf_elim_params_conv : forall Γ p D Ps Ps' M A i (Bs : list (String.string * nat * exp)),
      ind_lookup Θ Ξ p = Some D ->
      List.length Ps = ind_np D ->
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
      List.length Ps' = ind_np D ->
      (forall k P T, List.nth_error Ps' k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps') k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
      (forall k P P' T, List.nth_error Ps k = Some P -> List.nth_error Ps' k = Some P' ->
         List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
      Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
      (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs ->
         Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps' /\
      Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps') ++ Γ ⊢ A : Typeω@i /\
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps') ≈ elim_mctx p D (List.firstn (ind_nu D) Ps') /\
      (forall c gs, ind_con D c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps') ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps')) /\
      (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs ->
         Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps') ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps')) /\
      Θ ⍮ Ξ ⍮ Γ ⊢ A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ≈ A[sb_of_list Id (List.skipn (ind_nu D) Ps' ++ M :: nil)]
        : Typeω@i.
  Proof.
    intros * Hl HPl HPt HPl' HPt' HPP HM HA HBt.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    pose proof (decl_closed_nu D Hc) as Hle.
    pose proof (params_eq_sym _ p D Ps Ps' Hl HΓ HPl HPl' HPP) as HPP'.
    destruct (params_typed_split _ _ D Hc Γ Ps HPl HPt) as [HUt HNt].
    destruct (params_typed_split _ _ D Hc Γ Ps' HPl' HPt') as [HUt' HNt'].
    destruct (params_eq_split Γ D Ps Ps' Hc HPl HPl' HPP) as [HUe HNe].
    destruct (params_eq_split Γ D Ps' Ps Hc HPl' HPl HPP') as [HUe' _].
    set (Us := List.firstn (ind_nu D) Ps) in *; set (Us' := List.firstn (ind_nu D) Ps') in *.
    assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_firstn; lia).
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUt) as Hσ.
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl' HUt') as Hσ'.
    assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ).
    { eapply wf_sub_eq_of_list; [ exact (decl_uparams_ass D Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ)
                                | apply wf_sub_eq_refl, wf_sub_id, HΓ
                                | rewrite length_ind_uparams by exact Hle; exact HUl | rewrite length_ind_uparams by exact Hle; exact HUl' |].
      intros k N N' T HN HN' HT; eapply HUe; [ exact HN | exact HN' | exact HT ]. }
    pose proof (elim_mctx_us_eq _ _ _ _ _ HD Hc Hl HΓ HUl HUl' Hσσ) as HMc.
    pose proof (elim_mctx_ass p D Us Hc) as HMa; pose proof (elim_mctx_ass p D Us' Hc) as HMa'.
    pose proof (ext_eq_ctx_left _ _ _ _ _ HMc) as HMs; pose proof (ext_eq_ctx_right _ _ _ _ _ HMc) as HMs'.
    pose proof (ctxsub_ext _ _ _ _ _ HMc HMa) as HIdm.
    assert (HA' : Θ ⍮ Ξ ⍮ elim_mctx p D Us' ++ Γ ⊢ A : Typeω@i)
      by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA HIdm) as H; rewrite !exp_sub_id in H; exact H).
    (** The scrutinee at the other parameters. *)
    destruct (ind_apps_eq_large_syn _ _ _ _ _ Hl HΓ HPl HPl' HPP) as [k HTT].
    assert (HM' : Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps') by (eapply wf_conv'; eassumption).
    (** The branches. *)
    assert (HBc : forall c gs, ind_con D c = Some gs -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us')
      by (intros c gs Hcon; exact (elim_bctx_us_eq _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl HUl' Hσ Hσ' Hσσ HMs HMs' HA HA' Hcon)).
    split; [ exact HM' | split; [ exact HA' | split; [ exact (ctx_ext_refl _ _ _ _ HMa' HMs') | split; [| split ] ] ] ].
    - intros c gs Hcon; exact (ctx_ext_refl _ _ _ _ (elim_bctx_ass p D gs A Us' Hc) (ext_eq_ctx_right _ _ _ _ _ (HBc c gs Hcon))).
    - intros c gs n B Hcon Hin.
      pose proof (ctxsub_ext _ _ _ _ _ (HBc c gs Hcon) (elim_bctx_ass p D gs A Us Hc)) as HIdb.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HBt c gs n B Hcon Hin) HIdb) as HB'; rewrite !exp_sub_id in HB'.
      pose proof (wf_bty_sub_eq _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl' HUt' HUl HUe' HMs' HA' Hcon) as Hbs.
      pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HA' Hbs) as Hty.
      eapply wf_conv'; [ exact HB' | symmetry; exact Hty ].
    - assert (HNl : List.length (List.skipn (ind_nu D) Ps) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      assert (HNl' : List.length (List.skipn (ind_nu D) Ps') = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      eapply sub_eq_preserves_typ; [ exact HA |].
      assert (Hδδ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps) ≈ sb_of_list Id (List.skipn (ind_nu D) Ps')
                      : tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ).
      { eapply wf_sub_eq_of_list; [ apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact (wf_nparams_sub _ _ _ HD Hc _ _ HΓ Hσ)
                                  | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite length_tele_sub, length_nparams; exact HNl
                                  | rewrite length_tele_sub, length_nparams; exact HNl' |].
        intros k0 N N' T HN HN' HT; rewrite tele_insts_tele_sub in HT.
        rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT by (intros x; cbn; apply sentry_sub_id).
        exact (HNe _ _ _ _ HN HN' HT). }
      assert (Lmix : List.length (Us ++ List.skipn (ind_nu D) Ps') = ind_np D) by (rewrite List.length_app, HUl, HNl'; unfold ind_nn; lia).
      assert (HPmix : forall k0 P P' T, List.nth_error Ps k0 = Some P -> List.nth_error (Us ++ List.skipn (ind_nu D) Ps') k0 = Some P' ->
                 List.nth_error (tele_insts (ind_params D) Id Ps) k0 = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T).
      { intros k0 P P' T HP HP' HT.
        destruct (Nat.lt_ge_cases k0 (ind_nu D)) as [Hk | Hk].
        - rewrite List.nth_error_app1 in HP' by lia.
          pose proof HP as HP0; rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 in HP0
            by (rewrite List.length_firstn; lia); fold Us in HP0.
          rewrite HP0 in HP'; injection HP' as <-; apply wf_exp_eq_refl; eapply HPt; eassumption.
        - rewrite List.nth_error_app2 in HP' by lia; rewrite HUl, List.nth_error_skipn in HP'.
          replace (ind_nu D + (k0 - ind_nu D)) with k0 in HP' by lia; exact (HPP _ _ _ _ HP HP' HT). }
      destruct (ind_apps_eq_large_syn _ p D Ps (Us ++ List.skipn (ind_nu D) Ps') Hl HΓ HPl Lmix HPmix) as [k1 Hk1].
      assert (HM'' : Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) (Us ++ List.skipn (ind_nu D) Ps')) by (eapply wf_conv'; [ exact HM | exact Hk1 ]).
      rewrite !sb_of_list_app; cbn [sb_of_list].
      unfold elim_mctx in HMs |- *; cbn [List.app] in HMs |- *.
      destruct (ctx_decomp HMs) as [_ [j Hj]].
      assert (Hty : (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))
                      [sb_of_list Id (List.skipn (ind_nu D) Ps)] = apps (a_ind p) Ps)
        by (rewrite elim_mctx_head_inst by exact HNl; unfold Us; rewrite List.firstn_skipn; reflexivity).
      assert (Hty' : (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))
                      [sb_of_list Id (List.skipn (ind_nu D) Ps')] = apps (a_ind p) (Us ++ List.skipn (ind_nu D) Ps'))
        by (rewrite elim_mctx_head_inst by exact HNl'; reflexivity).
      eapply wf_sub_eq_extend; [ exact Hδδ | exact Hj | rewrite Hty; exact HM | rewrite Hty'; exact HM''
                               | rewrite Hty; apply wf_exp_eq_refl; exact HM ].
  Qed.

End Fixed_GCtx.
