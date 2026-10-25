(** * The Uniform Parameters of an Eliminator Varying

    The contexts of an eliminator's motives and branches are instances at
    its uniform parameters; at equal uniform parameters, they are equal
    telescopes.  So the blocks typed at the uniform parameters
    ([blocks_typed]) are typed at equal ones, and the motive's instance at
    the non-uniform parameters and the scrutinee is equal at equal ones.

    Two uses need this: the presupposition of the eliminator's congruence,
    whose right-hand side carries the uniform parameters of the right
    parameters ([wf_elim_cong_rhs], below), and a checker, which infers the
    parameters of the scrutinee's type, equal to, not the same as, those of
    a derivation.  Nothing here uses the presupposition of term equality:
    the lemmas come before it. *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Views.
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
    - cbn; constructor; exact (wf_sub_dom _ _ _ _ _ (wf_sub_eq_left _ _ _ _ _ _ Hσ)).
    - inversion Hass as [| ? ? [A ->] Hass']; subst.
      cbn [List.app] in HΨ; destruct (ctx_decomp HΨ) as [HΨ' [j HA]].
      pose proof (wf_sub_eq_refl _ _ _ _ _ (wf_sub_eq_left _ _ _ _ _ _ Hσ)) as Hσσ.
      pose proof (wf_sub_eq_refl _ _ _ _ _ (wf_sub_eq_right _ _ _ _ _ _ Hσ)) as Hσσ'.
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσ) as Hq.
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσσ) as Hq1.
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσσ') as Hq2.
      pose proof (wf_sub_eq_left _ _ _ _ _ _ Hq1) as Hs1.
      pose proof (wf_sub_eq_left _ _ _ _ _ _ Hq2) as Hs2.
      cbn [tele_sub centry_sub].
      eapply wf_ext_eq_ass; [ exact (IH _ _ _ _ Hass' HΨ' Hσ) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hs1)
                            | exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HA Hq) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hs2) ].
  Qed.

  (** Equal telescopes of assumptions, chained. *)
  Lemma ext_eq_trans_ass : forall Γ Ψ1 Ψ2 Ψ3, tele_ass Ψ1 -> tele_ass Ψ2 ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ1 ≈ Ψ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ2 ≈ Ψ3 -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ1 ≈ Ψ3.
  Proof.
    induction Ψ1 as [| e1 Ψ1 IH]; intros * Ha1 Ha2 H12 H23.
    - destruct Ψ2; [| apply ext_eq_length in H12; discriminate ]; exact H23.
    - destruct Ψ2 as [| e2 Ψ2]; [ apply ext_eq_length in H12; discriminate |].
      destruct Ψ3 as [| e3 Ψ3]; [ apply ext_eq_length in H23; discriminate |].
      inversion Ha1 as [| ? ? [A1 ->] Ha1']; subst; inversion Ha2 as [| ? ? [A2 ->] Ha2']; subst.
      destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H12) as (j1 & H12' & HA1 & HA12 & HA2).
      inversion H23 as [| ? ? ? ? ? ? ? ? H23' HA2b HA23 HA3 | | | ]; subst.
      pose proof (ctxsub_ext_rev _ _ _ _ _ H12' Ha1') as HId.
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HA23 HId) as HA23'; rewrite !exp_sub_id in HA23'.
      eapply wf_ext_eq_ass with (i := max j1 i);
        [ exact (IH _ _ Ha1' Ha2' H12' H23') | eapply lift_exp_ge; [| exact HA1 ]; lia
        | eapply wf_exp_eq_trans; [ eapply lift_exp_eq_ge; [| exact HA12 ]; lia | eapply lift_exp_eq_ge; [| exact HA23' ]; lia ]
        | eapply lift_exp_ge; [| exact HA3 ]; lia ].
  Qed.

  (** ** The Motives' Contexts *)

  Lemma uvars_typed : forall Γ p D, ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      forall k U T, List.nth_error (vars_from 0 (ind_nu D)) k = Some U ->
        List.nth_error (tele_insts (ind_uparams D) Id (vars_from 0 (ind_nu D))) k = Some T ->
        Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ ⊢ U : T.
  Proof.
    intros * Hl HΓ k U T HU HT.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    change 0 with (List.length (@nil centry)) in HU, HT.
    pose proof (wf_uparams_app _ _ _ HD Hc _ HΓ) as HUΓ.
    rewrite <- (tele_sub_id (ind_uparams D)) in HUΓ |- *.
    eapply (wf_vars_tele_gen _ _ nil (ind_uparams D) Id Id Γ 0); try eassumption.
    - exact (dc_ass _ Hc).
    - exact (dmv_uparams _ (dt_mvc _ _ _ HD)).
    - exact (dc_uparams _ Hc).
    - intros; lia.
  Qed.

  Lemma elim_mctx_canon : forall p D k M V, decl_closed D -> ind_member D k = Some M -> List.length V = ind_nu D ->
      elim_mctx p D k M V = tele_sub (elim_mctx p D k M (vars_from 0 (ind_nu D))) (sb_of_list Id V).
  Proof.
    intros * Hc Hk HV.
    rewrite elim_mctx_sub by (exact Hc || exact Hk || apply length_vars_from).
    rewrite <- HV, vars_from_sb_of_list; reflexivity.
  Qed.

  Lemma elim_mctx_canon_wf : forall Γ p D k M, ind_lookup Θ Ξ p = Some D -> ind_member D k = Some M -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D k M (vars_from 0 (ind_nu D)) ++ ind_uparams D ++ Γ.
  Proof.
    intros * Hl Hk HΓ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    eapply elim_mctx_wf; [ exact Hg | exact HDs | exact Hl | exact Hk | exact (wf_uparams_app _ _ _ HD Hc _ HΓ) | apply length_vars_from |].
    exact (uvars_typed _ _ _ Hl HΓ).
  Qed.

  Lemma elim_mctx_us_eq : forall Γ p D k M Us Us', ind_lookup Θ Ξ p = Some D -> ind_member D k = Some M -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k M Us ≈ elim_mctx p D k M Us'.
  Proof.
    intros * Hl Hk HΓ HUl HUl' Hσ.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    rewrite (elim_mctx_canon p D k M Us Hc Hk HUl), (elim_mctx_canon p D k M Us' Hc Hk HUl').
    eapply tele_sub_eq_ext; [ eapply elim_mctx_ass; eassumption | exact (elim_mctx_canon_wf _ _ _ _ _ Hl Hk HΓ) | exact Hσ ].
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
  Lemma ih_leaf_sub_eq : forall Γ p D j Mj Us Ψ Tc β σ σ' Ps x,
      decl_typed Θ Ξ D -> decl_closed D -> ind_member D j = Some Mj ->
      List.length Us = ind_nu D ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Tc -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : Tc ->
      shape_uc D Us Tc σ β ->
      List.length Ps = im_nn Mj ->
      (forall k P T, List.nth_error Ps k = Some P ->
         List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))) Ps) k = Some T ->
         Θ ⍮ Ξ ⍮ Tc ⊢ P : T) ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ x : ind_mty p D j (List.map (fun U => U[β]) Us) (List.map (fun P => P[σ]) Ps) ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps ++ x :: nil)
        ≈ sb_of_list β (List.map (fun P => P[σ']) Ps ++ x :: nil) : elim_mctx p D j Mj Us ++ Γ.
  Proof.
    intros * HD Hc Hj HUl HM Hβ Hσ Hσσ Huc HPl HP Hx.
    assert (HN : ⊢ Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)
      by (unfold elim_mctx in HM; cbn [List.app] in HM; destruct (ctx_decomp HM) as [H0 _]; exact H0).
    assert (Hnn : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps) ≈ sb_of_list β (List.map (fun P => P[σ']) Ps)
                    : tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ).
    { (* each instance is the parameter's own type moved by [σ] *)
      set (σ0 := sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))).
      assert (Hinst : forall k P T, List.nth_error Ps k = Some P ->
                 List.nth_error (tele_insts (tele_sub (im_nparams Mj) (sb_of_list Id Us)) β (List.map (fun P => P[σ]) Ps)) k = Some T ->
                 exists T0, List.nth_error (tele_insts (im_nparams Mj) σ0 Ps) k = Some T0 /\ T = T0[σ]).
      { intros k P T HPk HT; rewrite tele_insts_tele_sub in HT.
        assert (HT0 : exists T0, List.nth_error (tele_insts (im_nparams Mj) σ0 Ps) k = Some T0).
        { destruct (List.nth_error (tele_insts (im_nparams Mj) σ0 Ps) k) as [T0 |] eqn:E0; [ eauto |].
          apply List.nth_error_None in E0; rewrite length_tele_insts in E0 by (eapply decl_closed_nparams_ass; eassumption).
          rewrite length_im_nparams, HPl in E0.
          assert (Hk : k < List.length Ps) by (apply List.nth_error_Some; congruence); lia. }
        destruct HT0 as [T0 HT0]; exists T0; split; [ exact HT0 |].
        rewrite <- (tele_insts_sub_mvc (im_nparams Mj) (ind_nu D) σ0 _ σ Ps) in HT.
        + apply nth_error_map_inv in HT as (T1 & HT1 & ->); rewrite HT0 in HT1; injection HT1 as ->; reflexivity.
        + eapply decl_closed_nparams_ass; eassumption.
        + exact (decl_nparams_mvc _ _ _ HD _ _ Hj).
        + eapply decl_closed_nparams_scoped; eassumption.
        + intros y Hy; unfold σ0; cbn [sb_of_wk sentry_sub wk_shiftn]; exact (Huc y Hy). }
      pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσσ) as Hσ'.
      apply wf_sub_eq_of_list_left; [ apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption | exact HN | apply wf_sub_eq_refl; exact Hβ
                                    | rewrite length_tele_sub, List.length_map, HPl; reflexivity
                                    | rewrite length_tele_sub, List.length_map, HPl; reflexivity | | |].
      - intros k N T HN1 HT.
        apply nth_error_map_inv in HN1 as (P & HPk & ->).
        destruct (Hinst _ _ _ HPk HT) as (T0 & HT0 & ->).
        exact (sub_preserves_exp _ _ _ _ _ _ _ (HP _ _ _ HPk HT0) Hσ).
      - intros k N T HN2 HT.
        apply nth_error_map_inv in HN2 as (P & HPk & ->).
        destruct (Hinst _ _ _ HPk HT) as (T0 & HT0 & ->).
        pose proof (HP _ _ _ HPk HT0) as HP0; destruct (presup_exp HP0) as [_ [i0 HT0t]].
        eapply wf_conv; [ exact (sub_preserves_exp _ _ _ _ _ _ _ HP0 Hσ') | exact (sub_preserves_exp _ _ _ _ _ _ _ HT0t Hσ) |].
        apply wf_exp_eq_sym; exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HT0t Hσσ).
      - intros k N N' T HN1 HN2 HT.
        apply nth_error_map_inv in HN1 as (P & HPk & ->).
        apply nth_error_map_inv in HN2 as (P1 & HPk1 & ->); rewrite HPk in HPk1; injection HPk1 as <-.
        destruct (Hinst _ _ _ HPk HT) as (T0 & HT0 & ->).
        exact (proj1 sub_eq_preserves_mut _ _ _ _ _ (HP _ _ _ HPk HT0) _ _ _ Hσσ). }
    destruct (elim_mctx_head_typed _ _ _ _ _ _ _ _ HM) as [i Hi].
    rewrite !sb_of_list_app; cbn [sb_of_list]; unfold elim_mctx; cbn [List.app].
    pose proof Hx as Hx'.
    rewrite <- (ind_head_inst p D j Mj Us (List.map (fun P => P[σ]) Ps) β) in Hx' by (try assumption; rewrite List.length_map; exact HPl).
    pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ Hi Hnn) as Hhh.
    eapply wf_sub_eq_extend; [ exact Hnn | exact Hi | exact Hx'
                             | eapply wf_conv; [ exact Hx' | exact (sub_preserves_exp _ _ _ _ _ _ _ Hi (wf_sub_eq_right _ _ _ _ _ _ Hnn)) | exact Hhh ]
                             | apply wf_exp_eq_refl; exact Hx' ].
  Qed.

  (** The type of a recursive result of a shape, at equal substitutions of
      the shape's components. *)
  Lemma ihty_sub_eq : forall Γ p D Mk Us As i t Ψ Bs1 Tb β σ σ' x Mj,
      decl_typed Θ Ξ D -> decl_closed D ->
      List.length Us = ind_nu D ->
      (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
      motives_typed Θ Ξ Γ p D Us As i ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
      shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β ->
      ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t) = im_nn Mj ->
      shape_doms_typed Θ Ξ D Mk Bs1 Tb t -> shape_leaf_typed Θ Ξ D Mk Mj Bs1 Tb t ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => U[β]) Us) σ t ->
      exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty As β σ x t ≈ ptyp_ihty As β σ' x t : Typeω@j.
  Proof.
    intros Γ p D Mk Us As i t; induction t as [j0 Ps | B t IH];
      intros * HD Hc HUl HM HA Hβ Hσ Hσσ Huc Hj HPl HB HP Hx; cbn [ptyp_ihty ptyp_ty_at] in *.
    - cbn [ptyp_mem ptyp_ps] in Hj, HPl.
      exists i; exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ (HA _ _ Hj)
                         (ih_leaf_sub_eq _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hj HUl (HM _ _ Hj) Hβ Hσ Hσσ Huc HPl
                            (shape_leaf_at _ _ _ _ _ _ _ _ HP eq_refl) Hx)).
    - cbn [ptyp_ps ptyp_mem] in HPl, Hj.
      destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
      pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ Hj1 Hσσ) as HBB.
      assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
      pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
      pose proof (wf_sub_eq_q _ _ _ _ _ _ _ _ Hσσ Hj1 HBB) as Hσσ'.
      assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
        by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
      replace ((doms_ctx Bs1 ++ Tb ++ im_params D Mk) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) in Hσ', Hσσ'
        by (rewrite doms_ctx_app_one; reflexivity).
      assert (Huc' : shape_uc D Us (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) (q σ) (β ⨟ ι ↑))
        by (rewrite doms_ctx_app_one; apply shape_uc_pi; [ exact (proj2 (length_shape_ctx D Mk Bs1 Tb)) | exact Huc ]).
      pose proof (shape_doms_typed_pi _ _ _ _ _ _ _ _ HB) as HB''.
      pose proof (shape_leaf_typed_pi _ _ _ _ _ _ _ _ _ HP) as HP''.
      assert (Hus : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[β]) Us) = List.map (fun U => U[β ⨟ ι ↑]) Us)
        by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      rewrite Hus in Hx.
      destruct (ty_at_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc HUl HM Hβ' Hσ' Huc' Hj HPl HB'' HP'') as [j2 Hj2].
      pose proof (shape_arg_app _ _ _ _ _ _ _ _ Hj1' Hj2 Hx) as Hx'.
      destruct (IH _ _ _ _ _ _ _ _ HD Hc HUl HM HA Hβ' Hσ' Hσσ' Huc' Hj HPl HB'' HP'' Hx') as (j3 & H3).
      exists (max j1 j3).
      eapply wf_exp_eq_pi_cong_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_eq_max_left; exact HBB
                                      | eapply lift_exp_eq_max_right; exact H3 ].
  Qed.

  (** The components of a recursive argument in a branch's context, at
      equal uniform parameters. *)
  Lemma ihs_sub_us_eq : forall Γ p D k Mk Us Us' c gs gs1 t gs2 E,
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ->
      Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ˢ ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E)
        ≈ ihs_sub (im_nn Mk) Us' (List.length gs) (cargs_pat gs1) (List.length E) : doms_ctx nil ++ cargs_strat gs1 ++ im_params D Mk.
  Proof.
    intros * Hl Hk HΓ HUl Hσ Hσσ Hin Heq HΨ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    set (pat := cargs_pat gs1) in *.
    assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
    set (i := List.length pat) in *.
    set (j := List.length E) in *.
    set (na := List.length gs) in *.
    set (s := na - i + j).
    set (ρ := sb_qn (i + im_nn Mk) (sb_of_list Id Us)).
    set (ρ' := sb_qn (i + im_nn Mk) (sb_of_list Id Us')).
    destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs1 (ca_rec t :: gs2) Heq) as (HΨ1 & _ & Hφ).
    assert (Hw3 : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ʷ wk_shiftn s : cinst Γ p D Mk Us gs1).
    { rewrite Heq in HΨ |- *; rewrite cinst_split in HΨ |- *; rewrite List.app_assoc in HΨ |- *.
      match goal with |- _ ⍮ _ ⍮ ?L ++ _ ⊢ʷ wk_shiftn ?n : _ => replace n with (List.length L) end.
      - apply wf_wk_shiftn_app'; exact HΨ.
      - rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; unfold s, na, i, j; rewrite Heq, List.length_app; cbn; lia. }
    assert (Hτ2e : Θ ⍮ Ξ ⍮ cinst Γ p D Mk Us gs1 ⊢ˢ ρ ≈ ρ' : cargs_ctx p D Mk gs1 ++ im_params D Mk ++ Γ).
    { assert (HΨΓ : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D Mk gs1 ++ im_params D Mk) ++ Γ).
      { apply wf_ctx_closed_app; [| eapply cargs_ctx_closed; eassumption | exact HΨ1 | exact HΓ ].
        apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_params_ass; eassumption ]. }
      unfold im_params in HΨΓ; rewrite <- !List.app_assoc, (List.app_assoc (cargs_ctx p D Mk gs1)) in HΨΓ.
      assert (Hass1 : tele_ass (cargs_ctx p D Mk gs1 ++ im_nparams Mk))
        by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ]).
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass1 HΨΓ Hσσ) as H.
      rewrite <- cinst_eq in H; rewrite List.length_app, length_cargs_ctx, length_im_nparams in H.
      rewrite <- Hpat in H; fold i ρ ρ' in H.
      unfold im_params; rewrite <- (List.app_assoc (im_nparams Mk)), List.app_assoc; exact H. }
    change (ihs_sub (im_nn Mk) Us na pat j) with ((ι (wk_pat pat) ⨟ ρ) ⨟ ι (wk_shiftn s)).
    change (ihs_sub (im_nn Mk) Us' na pat j) with ((ι (wk_pat pat) ⨟ ρ') ⨟ ι (wk_shiftn s)).
    cbn [doms_ctx List.rev List.map List.app].
    eapply wf_sub_eq_compose_left; [| apply wf_sub_of_wk; exact Hw3 ].
    eapply wf_sub_eq_compose_right; [ apply wf_sub_of_wk; exact Hφ |].
    rewrite List.app_assoc in Hτ2e; exact (wf_sub_eq_prefix _ _ _ _ _ Hτ2e HΨ1).
  Qed.

  (** The type of the recursive result of a recursive argument, in a
      branch's context, at equal uniform parameters. *)
  Lemma rec_ih_us_eq : forall Γ p D k Mk Us Us' As i c gs gs1 t gs2 E,
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
      motives_typed Θ Ξ Γ p D Us As i ->
      List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ->
      let T V := ptyp_ihty As (ι (wk_shiftn (List.length E + List.length gs + im_nn Mk)))
                   (ihs_sub (im_nn Mk) V (List.length gs) (cargs_pat gs1) (List.length E))
                   (a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1))) t in
      exists j, Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ T Us ≈ T Us' : Typeω@j.
  Proof.
    intros * Hl Hk HΓ HUl Hσ Hσσ HM HA Hin Heq HΨ T.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hk HΓ HUl Hσ Hin Heq HΨ) as (Hb & Hθ & Huc & Hx).
    destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HD Hk Hin Heq) as (Mj & Hj & HPl & HBt & HPt).
    pose proof (ihs_sub_us_eq _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hk HΓ HUl Hσ Hσσ Hin Heq HΨ) as Hθθ.
    exact (ihty_sub_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc HUl HM HA Hb Hθ Hθθ Huc Hj HPl HBt HPt Hx).
  Qed.

  Lemma ihs_ctx_us_eq : forall Γ p D k Mk Us Us' As i c gs,
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
      (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us' ++ Γ) ->
      motives_typed Θ Ξ Γ p D Us As i -> motives_typed Θ Ξ Γ p D Us' As i ->
      List.In (c, gs) (im_cons Mk) ->
      forall rest gs1 E E', gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 -> List.length E' = cargs_nrec gs1 ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ E ++ ctel p D Mk Us gs ≈ E' ++ ctel p D Mk Us' gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ ihs_ctx_aux (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E ++ ctel p D Mk Us gs
                 ≈ ihs_ctx_aux (im_nn Mk) As Us' (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E' ++ ctel p D Mk Us' gs.
  Proof.
    intros * Hl Hk HΓ HUl HUl' Hσ Hσ' Hσσ HM HM' HA HA' Hin rest.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    assert (HAA : motives_eq Θ Ξ Γ p D Us As As i) by (intros j Mj Hj; apply wf_exp_eq_refl; exact (HA _ _ Hj)).
    assert (HAA' : motives_eq Θ Ξ Γ p D Us' As As i) by (intros j Mj Hj; apply wf_exp_eq_refl; exact (HA' _ _ Hj)).
    induction rest as [| [B | Ps] rest IH]; intros gs1 E E' Heq HE HE' HEE; cbn [ihs_ctx_aux List.app]; [ exact HEE | |].
    - replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg B :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | rewrite cargs_nrec_snoc, HE'; lia | exact HEE ].
    - assert (HΨ : ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs)
        by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_left; exact HEE).
      assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ E' ++ cinst Γ p D Mk Us' gs)
        by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_right; exact HEE).
      destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hk HΓ HUl Hσ HM HA HA HAA Hin Heq HΨ)
        as (j1 & Hj & _).
      destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' Hg HDs Hl Hk HΓ HUl' Hσ' HM' HA' HA' HAA' Hin Heq HΨ')
        as (j2 & Hj' & _).
      destruct (rec_ih_us_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hl Hk HΓ HUl Hσ Hσσ HM HA Hin Heq HΨ) as (j3 & Hjj).
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

  Lemma elim_bctx_us_eq : forall Γ p D k Mk Us Us' As i c gs,
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
      (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us' ++ Γ) ->
      motives_typed Θ Ξ Γ p D Us As i -> motives_typed Θ Ξ Γ p D Us' As i ->
      ind_con Mk c = Some gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs As Us ≈ elim_bctx p D Mk gs As Us'.
  Proof.
    intros * Hl Hk HΓ HUl HUl' Hσ Hσ' Hσσ HM HM' HA HA' Hcon.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (Hct : forall V, ctel p D Mk V gs = tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list Id V))
      by (intros; unfold ctel; rewrite tele_sub_app, length_im_nparams; reflexivity).
    assert (H0 : Θ ⍮ Ξ ⍮ Γ ⊢ˣ nil ++ ctel p D Mk Us gs ≈ nil ++ ctel p D Mk Us' gs).
    { cbn [List.app]; rewrite !Hct.
      destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ1 & _ & _).
      assert (HΨΓ : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D Mk gs ++ im_params D Mk) ++ Γ).
      { apply wf_ctx_closed_app; [| exact (cargs_ctx_closed p D k Mk c gs gs nil Hc Hk Hin (eq_sym (List.app_nil_r gs))) | exact HΨ1 | exact HΓ ].
        apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_params_ass; eassumption ]. }
      unfold im_params in HΨΓ; rewrite <- !List.app_assoc, (List.app_assoc (cargs_ctx p D Mk gs)) in HΨΓ.
      eapply tele_sub_eq_ext; [| exact HΨΓ | exact Hσσ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ]. }
    pose proof (ihs_ctx_us_eq _ _ _ _ _ _ _ _ _ _ _ Hl Hk HΓ HUl HUl' Hσ Hσ' Hσσ HM HM' HA HA' Hin gs nil nil nil eq_refl eq_refl eq_refl H0) as H.
    cbn [List.app List.length cargs_pat List.map List.rev] in H; unfold ctel in H; unfold elim_bctx; exact H.
  Qed.

  (** ** The Branches' Types *)

  (** The parameters and the arguments of a branch's context, as
      variables. *)
  Lemma bctx_base_typed : forall Γ p D k Mk Us As i c gs,
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D ->
      (forall j U T, nth_error Us j = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      motives_typed Θ Ξ Γ p D Us As i ->
      ind_con Mk c = Some gs ->
      let n := im_nn Mk + List.length gs + cargs_nrec gs in
      Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ
        ⊢ˢ sb_of_list (ι (wk_shiftn n)) (vars_from (cargs_nrec gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec gs) (List.length gs))
        : ctel p D Mk Us gs ++ Γ.
  Proof.
    intros * Hl Hk HΓ HUl HUs HA Hcon n.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
    assert (HM : forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ)
      by (intros j Mj Hj; exact (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hj HΓ HUl HUs)).
    pose proof (elim_bctx_wf _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ HUl Hσ HM HA Hcon) as HΔ.
    destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
    rewrite cinst_ctel in Hi.
    set (IHc := ihs_ctx_aux (im_nn Mk) As Us (List.length gs) nil 0 gs).
    assert (EΔ : elim_bctx p D Mk gs As Us ++ Γ = IHc ++ ctel p D Mk Us gs ++ Γ)
      by (unfold elim_bctx, ctel; rewrite <- !List.app_assoc; reflexivity).
    assert (HlI : List.length IHc = cargs_nrec gs) by (unfold IHc; apply length_ihs_ctx_aux).
    assert (Hlc : List.length (ctel p D Mk Us gs) = List.length gs + im_nn Mk)
      by (unfold ctel; rewrite List.length_app, !length_tele_sub, length_cargs_ctx; reflexivity).
    assert (Hw : Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ ⊢ʷ wk_shiftn n : Γ).
    { rewrite EΔ, List.app_assoc; replace n with (List.length (IHc ++ ctel p D Mk Us gs))
        by (rewrite List.length_app, HlI, Hlc; unfold n; lia).
      apply wf_wk_shiftn_app'; rewrite <- List.app_assoc, <- EΔ; exact HΔ. }
    apply wf_sub_of_list; [ unfold ctel; apply List.Forall_app; split; apply tele_ass_sub;
                              [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ HD _ _ Hk) ]
                          | exact Hi | apply wf_sub_of_wk; exact Hw
                          | rewrite List.length_app, !length_vars_from, Hlc; lia |].
    rewrite vars_from_app.
    assert (Ect : ctel p D Mk Us gs = tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list Id Us))
      by (unfold ctel; rewrite tele_sub_app, length_im_nparams; reflexivity).
    intros j N T HN HT.
    rewrite Ect, tele_insts_tele_sub in HT.
    replace (im_nn Mk + List.length gs) with (List.length (cargs_ctx p D Mk gs ++ im_nparams Mk)) in HN, HT
      by (rewrite List.length_app, length_cargs_ctx; change (List.length (im_nparams Mk)) with (im_nn Mk); lia).
    replace (cargs_nrec gs) with (List.length IHc) in HN, HT by exact HlI.
    rewrite EΔ, Ect.
    eapply (wf_vars_tele_gen _ _ IHc _ (sb_of_list Id Us) _ Γ (ind_nu D));
      [ apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ HD _ _ Hk) ]
      | apply List.Forall_app; split; [ eapply cargs_ctx_mvc; eassumption | exact (decl_nparams_mvc _ _ _ HD _ _ Hk) ]
      | apply ctx_scoped_app; split;
        [ rewrite length_im_nparams; eapply decl_closed_cargs_scoped; eassumption | eapply decl_closed_nparams_scoped; eassumption ]
      | rewrite <- Ect, <- EΔ; exact HΔ | | exact HN | exact HT ].
    intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; f_equal.
    rewrite List.length_app, length_cargs_ctx, HlI; change (List.length (im_nparams Mk)) with (im_nn Mk).
    unfold n; f_equal; lia.
  Qed.

  (** The instance of the motive's context the type of a branch
      substitutes, at equal uniform parameters: the constructor applied is
      equal, the member's own at a declared member, the container's at a
      view. *)
  Lemma wf_bty_sub_eq : forall Γ p D k Mk Us Us' As i c gs,
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D ->
      (forall j U T, nth_error Us j = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      List.length Us' = ind_nu D ->
      (forall j U T, nth_error Us' j = Some U -> nth_error (tele_insts (ind_uparams D) Id Us') j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      (forall j U U' T, nth_error Us j = Some U -> nth_error Us' j = Some U' ->
         nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U ≈ U' : T) ->
      motives_typed Θ Ξ Γ p D Us As i ->
      ind_con Mk c = Some gs ->
      let n := im_nn Mk + List.length gs + cargs_nrec gs in
      let ρ V := sb_of_list (ι (wk_shiftn n))
                   (vars_from (cargs_nrec gs + List.length gs) (im_nn Mk) ++
                    apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
                      (im_pre Mk (List.map (fun U => U[wk_shiftn n]ʷ) V) ++
                       vars_from (cargs_nrec gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec gs) (List.length gs))
                    :: nil) in
      Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ ⊢ˢ ρ Us ≈ ρ Us' : elim_mctx p D k Mk Us ++ Γ.
  Proof.
    intros * Hl Hk HΓ HUl HUs HUl' HUs' HUU HA Hcon n ρ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl' HUs') as Hσ'.
    assert (HM : forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ)
      by (intros j Mj Hj; exact (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hj HΓ HUl HUs)).
    pose proof (elim_bctx_wf _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ HUl Hσ HM HA Hcon) as HΔ.
    set (Δ := elim_bctx p D Mk gs As Us ++ Γ) in *.
    set (nvars := vars_from (cargs_nrec gs + List.length gs) (im_nn Mk)) in *.
    set (avars := vars_from (cargs_nrec gs) (List.length gs)) in *.
    (* the base, at both uniform parameters *)
    pose proof (bctx_base_typed _ _ _ _ _ _ _ _ _ _ Hl Hk HΓ HUl HUs HA Hcon) as Hb; cbv zeta in Hb; fold n nvars avars Δ in Hb.
    assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ).
    { eapply wf_sub_eq_of_list_conv; [ exact (dc_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ)
                                     | apply wf_sub_eq_refl, wf_sub_id, HΓ | exact HUl | exact HUl' | exact HUs | exact HUs' | exact HUU ]. }
    assert (Hct : forall V, ctel p D Mk V gs = tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list Id V))
      by (intros; unfold ctel; rewrite tele_sub_app, length_im_nparams; reflexivity).
    assert (Hctel : Θ ⍮ Ξ ⍮ Γ ⊢ˣ ctel p D Mk Us gs ≈ ctel p D Mk Us' gs).
    { rewrite !Hct.
      destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ1 & _ & _).
      assert (HΨΓ : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D Mk gs ++ im_params D Mk) ++ Γ).
      { apply wf_ctx_closed_app; [| exact (cargs_ctx_closed p D k Mk c gs gs nil Hc Hk Hin (eq_sym (List.app_nil_r gs))) | exact HΨ1 | exact HΓ ].
        apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_params_ass; eassumption ]. }
      unfold im_params in HΨΓ; rewrite <- !List.app_assoc, (List.app_assoc (cargs_ctx p D Mk gs)) in HΨΓ.
      eapply tele_sub_eq_ext; [| exact HΨΓ | exact Hσσ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ]. }
    assert (Hcta : tele_ass (ctel p D Mk Us gs))
      by (rewrite Hct; apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ]).
    pose proof (wf_sub_compose _ _ _ _ _ _ _ (ctxsub_ext_rev _ _ _ _ _ Hctel Hcta) Hb) as Hb'.
    rewrite sb_compose_id_left in Hb'.
    assert (HNl : List.length nvars = im_nn Mk) by (unfold nvars; apply length_vars_from).
    assert (HAl : List.length avars = List.length gs) by (unfold avars; apply length_vars_from).
    destruct (ctel_args_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc Hk Hin HUl HNl HAl Hb) as [HNs HAs].
    destruct (ctel_args_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc Hk Hin HUl' HNl HAl Hb') as [HNs' HAs'].
    set (Usw := List.map (fun U => U[wk_shiftn n]ʷ) Us) in *.
    set (Usw' := List.map (fun U => U[wk_shiftn n]ʷ) Us') in *.
    (* the weakening past the branch's context *)
    assert (Hw : Θ ⍮ Ξ ⍮ Δ ⊢ʷ wk_shiftn n : Γ).
    { set (IHc := ihs_ctx_aux (im_nn Mk) As Us (List.length gs) nil 0 gs).
      assert (EΔ : Δ = (IHc ++ ctel p D Mk Us gs) ++ Γ) by (unfold Δ, elim_bctx, ctel; rewrite <- !List.app_assoc; reflexivity).
      assert (Hlen : List.length (IHc ++ ctel p D Mk Us gs) = n).
      { unfold IHc, ctel; rewrite !List.length_app, length_ihs_ctx_aux, !length_tele_sub, length_cargs_ctx.
        change (List.length (im_nparams Mk)) with (im_nn Mk); unfold n; lia. }
      rewrite EΔ, <- Hlen; apply wf_wk_shiftn_app'; rewrite <- EΔ; exact HΔ. }
    pose proof (uparams_wk_typed _ _ _ _ _ _ _ Hc Hw HUs) as HUsw; fold Usw in HUsw.
    pose proof (uparams_wk_typed _ _ _ _ _ _ _ Hc Hw HUs') as HUsw'; fold Usw' in HUsw'.
    assert (HUlw : List.length Usw = ind_nu D) by (unfold Usw; rewrite List.length_map; exact HUl).
    assert (HUlw' : List.length Usw' = ind_nu D) by (unfold Usw'; rewrite List.length_map; exact HUl').
    assert (HUUw : forall j U U' T, nth_error Usw j = Some U -> nth_error Usw' j = Some U' ->
               nth_error (tele_insts (ind_uparams D) Id Usw) j = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ U ≈ U' : T).
    { intros j U0 U0' T' HU HU' HT; unfold Usw, Usw' in *.
      rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
      apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HU' as (U1 & HU1 & ->);
        apply nth_error_map_inv in HT as (T & HT & ->).
      exact (wk_preserves_exp_eq _ _ _ _ _ _ _ _ (HUU _ _ _ _ HU HU1 HT) Hw). }
    (* the constructors, equal *)
    assert (Hcc : Θ ⍮ Ξ ⍮ Δ ⊢ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Usw ++ nvars ++ avars)
                   ≈ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Usw' ++ nvars ++ avars)
                   : ind_mty p D k (List.map (fun U => U[ι (wk_shiftn n)]) Us) nvars).
    { rewrite map_sub_of_wk; fold Usw.
      unfold ind_mty; rewrite Hk; unfold im_ty_at, im_ref, im_pre.
      destruct (im_head Mk) as [pm | qc k' Is vm] eqn:Hh; cbn [fst snd].
      - (* a declared member: its own constructor *)
        pose proof (member_decl_lt _ _ _ _ _ _ HD Hk Hh) as Hlt.
        pose proof (params_typed_join _ _ _ Hc _ _ _ _ _ Hk HUlw HUsw HNs) as HPs.
        pose proof (params_typed_join _ _ _ Hc _ _ _ _ _ Hk HUlw' HUsw' HNs') as HPs'.
        assert (HPl : List.length (Usw ++ nvars) = im_np D Mk) by (rewrite List.length_app, HUlw, HNl; unfold im_np; lia).
        assert (HPl' : List.length (Usw' ++ nvars) = im_np D Mk) by (rewrite List.length_app, HUlw', HNl; unfold im_np; lia).
        assert (HPP : forall j N N' T, nth_error (Usw ++ nvars) j = Some N -> nth_error (Usw' ++ nvars) j = Some N' ->
                   nth_error (tele_insts (im_params D Mk) Id (Usw ++ nvars)) j = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : T).
        { unfold im_params; apply list_eq_app; [ exact (dc_ass _ Hc) | exact HUlw | exact HUlw' | exact HUUw |].
          intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HNs _ _ _ HN HT). }
        assert (HAA : forall j N N' T, nth_error avars j = Some N -> nth_error avars j = Some N' ->
                   nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Usw ++ nvars)) avars) j = Some T ->
                   Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : T).
        { intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HAs _ _ _ HN HT). }
        pose proof (con_apps_conv _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hlt Hcon HΔ HPl HPl' HAl HAl HPs HPs' HPP HAs HAs' HAA) as H.
        rewrite firstn_app_len, skipn_app_len in H by exact HUlw.
        unfold ind_mty in H; rewrite Hk in H; unfold im_ty_at, im_ref, im_pre in H; rewrite Hh in H; cbn [fst snd] in H.
        rewrite !List.app_assoc; exact H.
      - (* a view: the container's constructor, at the view's instances *)
        destruct (view_con_inst_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hh Hcon HΔ HUlw HUsw HNl HNs HAl HAs)
          as [D3 Mk3 gs3 Hl3 Hk3 Hlt3 Hcon3 HPl3 HAl3 HPs3 HAs3].
        destruct (view_con_inst_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hh Hcon HΔ HUlw' HUsw' HNl HNs' HAl HAs')
          as [D4 Mk4 gs4 Hl4 Hk4 Hlt4 Hcon4 HPl4 HAl4 HPs4 HAs4].
        rewrite Hl3 in Hl4; injection Hl4 as <-; rewrite Hk3 in Hk4; injection Hk4 as <-; rewrite Hcon3 in Hcon4; injection Hcon4 as <-.
        pose proof (HDs _ _ Hl3) as HD3; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl3) as Hc3.
        assert (Hσw : Θ ⍮ Ξ ⍮ Δ ⊢ˢ sb_of_list Id Usw ≈ sb_of_list Id Usw' : ind_uparams D).
        { rewrite <- (List.app_nil_r (ind_uparams D)).
          eapply wf_sub_eq_of_list_conv; [ exact (dc_ass _ Hc) | rewrite List.app_nil_r; exact (dt_uparams _ _ _ HD)
                                         | apply wf_sub_eq_refl, wf_sub_to_nil, HΔ | exact HUlw | exact HUlw'
                                         | exact HUsw | exact HUsw' | exact HUUw ]. }
        destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hk Hh) as (D0 & Mk0 & Hl0 & _ & _ & HIl & _).
        rewrite Hl3 in Hl0; injection Hl0 as <-.
        set (Ps := List.map (fun I => I[sb_of_list Id Usw]) Is ++ nvars) in *.
        set (Ps' := List.map (fun I => I[sb_of_list Id Usw']) Is ++ nvars) in *.
        assert (HPP : forall j N N' T, nth_error Ps j = Some N -> nth_error Ps' j = Some N' ->
                   nth_error (tele_insts (im_params D3 Mk3) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : T).
        { unfold Ps, Ps', im_params; apply list_eq_app;
            [ exact (dc_ass _ Hc3) | rewrite List.length_map; exact HIl | rewrite List.length_map; exact HIl | |].
          - intros j N N' T HN HN' HT.
            rewrite <- (tele_insts_sub (ind_uparams D3) 0 Id Id (sb_of_list Id Usw) Is (dc_ass _ Hc3) (dc_uparams _ Hc3)
                          ltac:(intros; lia)) in HT.
            apply nth_error_map_inv in HN as (I & HI & ->); apply nth_error_map_inv in HN' as (I1 & HI1 & ->).
            rewrite HI in HI1; injection HI1 as <-.
            apply nth_error_map_inv in HT as (T0 & HT0 & ->).
            exact (sub_eq_preserves_exp _ _ _ _ _ (dt_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ Hk Hh Hl3 HI HT0) _ _ _ Hσw).
          - intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl.
            apply (HPs3 (List.length (List.map (fun I => I[sb_of_list Id Usw]) Is) + j)).
            + unfold Ps; rewrite List.nth_error_app2 by lia; replace (_ + j - _) with j by lia; exact HN.
            + unfold Ps, im_params; rewrite tele_insts_app by (try exact (dc_ass _ Hc3); rewrite List.length_map; exact HIl).
              rewrite List.nth_error_app2 by (rewrite length_tele_insts by exact (dc_ass _ Hc3); rewrite !List.length_map; unfold ind_nu in *; lia).
              rewrite length_tele_insts by exact (dc_ass _ Hc3); rewrite !List.length_map.
              replace (List.length Is + j - Nat.min (List.length (ind_uparams D3)) (List.length Is)) with j
                by (unfold ind_nu in *; lia).
              exact HT. }
        assert (HAA : forall j N N' T, nth_error avars j = Some N -> nth_error avars j = Some N' ->
                   nth_error (tele_insts (cargs_ctx qc D3 Mk3 gs3) (sb_of_list Id Ps) avars) j = Some T ->
                   Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : T).
        { intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HAs3 _ _ _ HN HT). }
        pose proof (con_apps_conv _ _ _ _ _ _ _ _ _ Ps Ps' avars avars Hg HDs Hl3 Hk3 Hlt3 Hcon3 HΔ HPl3 HPl4 HAl3 HAl4
                      HPs3 HPs4 HPP HAs3 HAs4 HAA) as H.
        destruct (member_lt_decl _ _ _ _ _ HD3 Hk3 Hlt3) as [pm Hpm].
        unfold ind_mty in H; rewrite Hk3 in H; unfold im_ty_at, im_ref, im_pre in H; rewrite Hpm in H; cbn [fst snd] in H.
        rewrite List.firstn_skipn in H.
        unfold Ps, Ps' in H; rewrite <- !List.app_assoc in H; exact H. }
    (* the substitutions *)
    pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ HUl HUs HM HA Hcon) as Hρ; fold n nvars avars Usw Δ in Hρ.
    set (conU := apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Usw ++ nvars ++ avars)) in *.
    set (conU' := apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Usw' ++ nvars ++ avars)) in *.
    unfold ρ; fold Usw Usw' conU conU'.
    assert (Hlen : forall x, List.length (nvars ++ x :: nil) = List.length (elim_mctx p D k Mk Us))
      by (intros; rewrite List.length_app, length_elim_mctx, HNl; cbn; lia).
    pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_mctx_ass _ _ _ _ Us Hc Hk) (Hlen conU) Hρ) as HMs.
    pose proof (fun x => elim_mctx_insts p D k Mk Us (ι wk_shiftn n) nvars x Hc Hk HUl HNl) as E.
    assert (Hl2 : List.length (tele_insts (im_nparams Mk) (sb_of_list Id Us ⨟ ι wk_shiftn n) nvars) = im_nn Mk)
      by (rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption); rewrite HNl; unfold im_nn; lia).
    (* the right constructor, at the type of the left one: the member's types
       at the two uniform parameters are equal, the heads of the motive's
       contexts *)
    assert (Hcon' : Θ ⍮ Ξ ⍮ Δ ⊢ conU' : ind_mty p D k (List.map (fun U => U[ι (wk_shiftn n)]) Us) nvars).
    { pose proof (wf_con_apps_at _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon HΔ HUlw' HUsw' HNl HNs' HAl HAs') as H'.
      fold conU' in H'.
      pose proof (elim_mctx_us_eq _ _ _ _ _ _ _ Hl Hk HΓ HUl HUl' Hσσ) as HMe.
      unfold elim_mctx in HMe; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ HMe) as (j & _ & Hhd & Hhh & _).
      assert (HNΓ : ⊢ Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ)
        by (pose proof (HM _ _ Hk) as H0; unfold elim_mctx in H0; cbn [List.app] in H0; exact (proj1 (ctx_decomp H0))).
      assert (Hδ : Θ ⍮ Ξ ⍮ Δ ⊢ˢ sb_of_list (ι (wk_shiftn n)) nvars : tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ).
      { apply wf_sub_of_list; [ apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption | exact HNΓ
                              | apply wf_sub_of_wk; exact Hw | rewrite length_tele_sub, HNl; reflexivity |].
        intros j0 N T HN HT; rewrite tele_insts_tele_sub in HT.
        apply (HMs j0); [ rewrite List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HN |].
        rewrite E, List.nth_error_app1 by (rewrite Hl2, <- HNl; apply List.nth_error_Some; congruence); exact HT. }
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hhd Hδ) as HT1.
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hhh Hδ) as HTT.
      cbn [exp_sub] in HT1, HTT.
      rewrite !ind_head_inst in HT1, HTT by first [ exact Hc | exact HUl | exact HUl' | exact HNl ].
      rewrite (ind_head_inst p D k Mk Us' nvars (ι (wk_shiftn n)) Hc HUl' HNl) in HTT.
      assert (EU : Usw' = List.map (fun U => U[ι (wk_shiftn n)]) Us') by (unfold Usw'; symmetry; apply map_sub_of_wk).
      rewrite EU in H'.
      eapply wf_conv; [ exact H' | exact HT1 | apply wf_exp_eq_sym; exact HTT ]. }
    eapply wf_sub_eq_of_list_left; [ exact (elim_mctx_ass _ _ _ _ _ Hc Hk) | exact (HM _ _ Hk) | apply wf_sub_eq_refl, wf_sub_of_wk, Hw
                                   | exact (Hlen conU) | exact (Hlen conU') | exact HMs | |].
    - intros j N T HN HT; rewrite E in HT.
      destruct (Nat.lt_ge_cases j (im_nn Mk)) as [Hj | Hj].
      + rewrite List.nth_error_app1 in HN by lia.
        apply (HMs j); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite E; exact HT ].
      + rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
        rewrite HNl in HN; rewrite Hl2 in HT.
        destruct (j - im_nn Mk) as [| j0] eqn:Hj0; cbn in HN, HT; [| destruct j0; discriminate ].
        injection HN as <-; injection HT as <-; exact Hcon'.
    - intros j N N' T HN HN' HT; rewrite E in HT.
      destruct (Nat.lt_ge_cases j (im_nn Mk)) as [Hj | Hj].
      + rewrite List.nth_error_app1 in HN, HN' by lia; rewrite HN in HN'; injection HN' as <-.
        apply wf_exp_eq_refl; apply (HMs j); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite E; exact HT ].
      + rewrite List.nth_error_app2 in HN, HN' by lia; rewrite List.nth_error_app2 in HT by lia.
        rewrite HNl in HN, HN'; rewrite Hl2 in HT.
        destruct (j - im_nn Mk) as [| j0] eqn:Hj0; cbn in HN, HN', HT; [| destruct j0; discriminate ].
        injection HN as <-; injection HN' as <-; injection HT as <-; exact Hcc.
  Qed.

  (** ** Equal Instances of a Telescope *)

  (** Equal substitutions read back from lists of terms: equal terms, each
      at the instance of the type of its variable. *)
  Lemma wf_sub_eq_of_list_inv : forall Γ Δ Γ0 σ σ' Ms Ms',
      tele_ass Δ -> List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list σ Ms ≈ sb_of_list σ' Ms' : Δ ++ Γ0 ->
      forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
        List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T.
  Proof.
    intros * Hass Hl Hl' Hσ k N N' T HN HN' HT.
    apply tele_insts_nth in HT as (A & HA & ->).
    destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
    assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
      by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
    assert (Hlen : List.length Δ = List.length l2 + S k)
      by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
    assert (Hlk : Δ ++ Γ0 ∋ #(List.length l2) : A[wk_shiftn (List.length l2 + 1)]ʷ).
    { rewrite HΔeq, <- List.app_assoc.
      replace (List.length l2) with (0 + List.length (List.rev l2)) at 1 by (rewrite List.length_rev; lia).
      replace (A[wk_shiftn (List.length l2 + 1)]ʷ) with (A[↑]ʷ[wk_shiftn (List.length (List.rev l2))]ʷ).
      - apply ctx_lookup_app_r; constructor.
      - rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_rev; lia. }
    pose proof (wf_sub_eq_apply _ _ _ _ _ _ Hσ _ _ Hlk) as H.
    change (exp_sub (a_var ?x) ?s) with (sentry_exp (s x)) in H.
    rewrite (sb_of_list_nth _ _ _ N) in H by lia.
    rewrite (sb_of_list_nth _ _ _ N') in H by lia.
    replace (List.length Ms - 1 - List.length l2) with k in H by lia.
    replace (List.length Ms' - 1 - List.length l2) with k in H by lia.
    rewrite (List.nth_error_nth _ _ _ HN), (List.nth_error_nth _ _ _ HN') in H; cbn in H.
    replace (A[sb_of_list σ (List.firstn k Ms)]) with (A[wk_shiftn (List.length l2 + 1)]ʷ[sb_of_list σ Ms]); [ exact H |].
    rewrite exp_sub_wk; apply exp_sub_sb_eq; intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
    rewrite <- (List.firstn_skipn k Ms) at 1; rewrite sb_of_list_app.
    replace (x + (List.length l2 + 1)) with (List.length (List.skipn k Ms) + x) by (rewrite List.length_skipn; lia).
    rewrite sb_of_list_ge; reflexivity.
  Qed.

  Lemma wf_sub_eq_sb_eq : forall Γ Δ σ1 σ1' σ2 σ2', sb_eq σ1 σ2 -> sb_eq σ1' σ2' ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ1 ≈ σ1' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ2 ≈ σ2' : Δ.
  Proof.
    intros * E E' [Hl0 Hr0 Ha Hm]; constructor.
    - rewrite <- E; exact Hl0.
    - rewrite <- E'; exact Hr0.
    - intros x A Hx; rewrite <- !(exp_sub_sb_eq _ _ _ E), <- (exp_sub_sb_eq _ _ _ E'); exact (Ha _ _ Hx).
    - intros x U Hx; rewrite <- (E x), <- (E' x); exact (Hm _ _ Hx).
  Qed.

  (** Equal parameters of a member: equal uniform ones, and equal
      non-uniform ones at the instances at the first uniform ones. *)
  Lemma params_eq_split : forall Γ D k Mk Ps Ps', decl_closed D -> ind_member D k = Some Mk ->
      List.length Ps = im_np D Mk -> List.length Ps' = im_np D Mk ->
      (forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error Ps' j = Some P' ->
         List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T) ->
      (forall j U U' T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U -> List.nth_error (List.firstn (ind_nu D) Ps') j = Some U' ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U ≈ U' : T) /\
      (forall j N N' T, List.nth_error (List.skipn (ind_nu D) Ps) j = Some N -> List.nth_error (List.skipn (ind_nu D) Ps') j = Some N' ->
         List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) j = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T).
  Proof.
    intros * Hc Hk Hl Hl' HPs.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in Hl; lia).
    assert (HUl' : List.length (List.firstn (ind_nu D) Ps') = ind_nu D) by (rewrite List.length_firstn; unfold im_np in Hl'; lia).
    assert (Hti : tele_insts (im_params D Mk) Id Ps
                  = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                    ++ tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
    { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
        [ exact (dc_ass _ Hc) | exact HUl ]. }
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
      by (rewrite length_tele_insts by exact (dc_ass _ Hc); rewrite HUl; unfold ind_nu; lia).
    split; intros j N N' T HN HN' HT.
    - assert (Hj : j < ind_nu D) by (rewrite <- HUl; apply List.nth_error_Some; congruence).
      apply (HPs j);
        [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by lia; exact HN
        | rewrite <- (List.firstn_skipn (ind_nu D) Ps'), List.nth_error_app1 by lia; exact HN'
        | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    - apply (HPs (ind_nu D + j)).
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + j - ind_nu D) with j by lia; exact HN.
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps') at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl'; replace (ind_nu D + j - ind_nu D) with j by lia; exact HN'.
      + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + j - ind_nu D) with j by lia; exact HT.
  Qed.

  (** Parameters typed at the instances at other parameters: the uniform
      ones at the uniform parameters' instances, the non-uniform ones at
      theirs at the other uniform ones. *)
  Lemma params_typed_at_split : forall Γ D k Mk Ps Ps', decl_closed D -> ind_member D k = Some Mk ->
      List.length Ps = im_np D Mk -> List.length Ps' = im_np D Mk ->
      (forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error Ps' j = Some P' ->
         List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P' : T) ->
      (forall j U U' T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U -> List.nth_error (List.firstn (ind_nu D) Ps') j = Some U' ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U' : T) /\
      (forall j N N' T, List.nth_error (List.skipn (ind_nu D) Ps) j = Some N -> List.nth_error (List.skipn (ind_nu D) Ps') j = Some N' ->
         List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) j = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N' : T).
  Proof.
    intros * Hc Hk Hl Hl' HPs.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in Hl; lia).
    assert (HUl' : List.length (List.firstn (ind_nu D) Ps') = ind_nu D) by (rewrite List.length_firstn; unfold im_np in Hl'; lia).
    assert (Hti : tele_insts (im_params D Mk) Id Ps
                  = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                    ++ tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
    { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
        [ exact (dc_ass _ Hc) | exact HUl ]. }
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
      by (rewrite length_tele_insts by exact (dc_ass _ Hc); rewrite HUl; unfold ind_nu; lia).
    split; intros j N N' T HN HN' HT.
    - assert (Hj : j < ind_nu D) by (rewrite <- HUl; apply List.nth_error_Some; congruence).
      apply (HPs j N);
        [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by lia; exact HN
        | rewrite <- (List.firstn_skipn (ind_nu D) Ps'), List.nth_error_app1 by lia; exact HN'
        | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    - apply (HPs (ind_nu D + j) N).
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + j - ind_nu D) with j by lia; exact HN.
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps') at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl'; replace (ind_nu D + j - ind_nu D) with j by lia; exact HN'.
      + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + j - ind_nu D) with j by lia; exact HT.
  Qed.

  (** ** The Blocks at Equal Uniform Parameters *)

  (** An annotation equal to the motive's context's head stays so when
      the telescope before it changes to an equal one. *)
  Lemma ext_eq_ann_move : forall Γ Ψ Ψ' Z A A', tele_ass Ψ -> tele_ass Ψ' ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ Z ≈ Ψ ▹ A -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ A ≈ Ψ' ▹ A' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ' ▹ Z ≈ Ψ' ▹ A'.
  Proof.
    intros * Ha Ha' H1 H2.
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H1) as (j1 & _ & HZ & HZA & _).
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H2) as (j2 & H12 & _ & HAA & HA').
    pose proof (ctxsub_ext _ _ _ _ _ H12 Ha) as HId.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HZ HId) as HZ'.
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HZA HId) as HZA'.
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA HId) as HAA'.
    rewrite !exp_sub_id in HZ'; rewrite !exp_sub_id in HZA'; rewrite !exp_sub_id in HAA'.
    eapply wf_ext_eq_ass with (i := max j1 j2);
      [ exact (ctx_ext_refl _ _ _ _ Ha' (ext_eq_ctx_right _ _ _ _ _ H12)) | eapply lift_exp_max_left; exact HZ'
      | eapply wf_exp_eq_trans; [ eapply lift_exp_eq_max_left; exact HZA' | eapply lift_exp_eq_max_right; exact HAA' ]
      | eapply lift_exp_max_right; exact HA' ].
  Qed.

  (** The blocks of an eliminator typed at the uniform parameters [Us] are
      typed at equal ones. *)
  Lemma blocks_typed_us_conv : forall Γ p D Us Us' Bks i,
      ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D ->
      (forall j U T, nth_error Us j = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      List.length Us' = ind_nu D ->
      (forall j U T, nth_error Us' j = Some U -> nth_error (tele_insts (ind_uparams D) Id Us') j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      (forall j U U' T, nth_error Us j = Some U -> nth_error Us' j = Some U' ->
         nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U ≈ U' : T) ->
      blocks_typed Θ Ξ Γ p D Us Bks i -> blocks_typed Θ Ξ Γ p D Us' Bks i.
  Proof.
    intros * Hl HΓ HUl HUs HUl' HUs' HUU HBt.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl' HUs') as Hσ'.
    assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ).
    { eapply wf_sub_eq_of_list_conv; [ exact (dc_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ)
                                     | apply wf_sub_eq_refl, wf_sub_id, HΓ | exact HUl | exact HUl' | exact HUs | exact HUs' | exact HUU ]. }
    assert (HUU' : forall j U' U T, nth_error Us' j = Some U' -> nth_error Us j = Some U ->
               nth_error (tele_insts (ind_uparams D) Id Us') j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U' ≈ U : T).
    { intros j U' U T HU' HU HT.
      exact (wf_sub_eq_of_list_inv _ _ _ _ _ _ _ (dc_ass _ Hc) HUl' HUl (wf_sub_eq_sym _ _ _ _ _ _ Hσσ) _ _ _ _ HU' HU HT). }
    assert (HMc : forall k Mk, ind_member D k = Some Mk -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk Us ≈ elim_mctx p D k Mk Us')
      by (intros k Mk Hk; exact (elim_mctx_us_eq _ _ _ _ _ _ _ Hl Hk HΓ HUl HUl' Hσσ)).
    assert (HMv : forall k Mk, ind_member D k = Some Mk -> Θ ⍮ Ξ ⍮ elim_mctx p D k Mk Us' ++ Γ ⊢ˢ Id : elim_mctx p D k Mk Us ++ Γ)
      by (intros k Mk Hk; exact (ctxsub_ext _ _ _ _ _ (HMc _ _ Hk) (elim_mctx_ass _ _ _ _ _ Hc Hk))).
    pose proof (blocks_mctx_wf _ _ _ _ _ _ _ _ HBt) as HM.
    assert (HM' : forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us' ++ Γ)
      by (intros j Mj Hj; exact (ext_eq_ctx_right _ _ _ _ _ (HMc _ _ Hj))).
    pose proof (blocks_motives_typed _ _ _ _ _ _ _ _ HBt) as HA.
    assert (HA' : motives_typed Θ Ξ Γ p D Us' (blocks_motives Bks) i).
    { intros j Mj Hj; pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HA _ _ Hj) (HMv _ _ Hj)) as H.
      rewrite !exp_sub_id in H; exact H. }
    assert (HBc : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
               Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) Us ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us')
      by (intros k Mk c gs Hk Hcon; exact (elim_bctx_us_eq _ _ _ _ _ _ _ _ _ _ _ Hl Hk HΓ HUl HUl' Hσ Hσ' Hσσ HM HM' HA HA' Hcon)).
    destruct HBt as [HlB Hnm HZ HAb HΨ Hn HΨB Hk HB].
    constructor; try assumption.
    - intros k Mk b Z Hk' Hb HZb.
      pose proof (HZ _ _ _ _ Hk' Hb HZb) as HZ0; pose proof (HMc _ _ Hk') as HMk.
      unfold elim_mctx in HZ0, HMk |- *.
      eapply ext_eq_ann_move; [ apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HD _ _ Hk')
                              | apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HD _ _ Hk') | exact HZ0 | exact HMk ].
    - intros k Mk b Hk' Hb; pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HAb _ _ _ Hk' Hb) (HMv _ _ Hk')) as H.
      rewrite !exp_sub_id in H; exact H.
    - intros k Mk Hk'; exact (ctx_ext_refl _ _ _ _ (elim_mctx_ass _ _ _ _ _ Hc Hk') (HM' _ _ Hk')).
    - intros k Mk c gs Hk' Hcon.
      exact (ctx_ext_refl _ _ _ _ (elim_bctx_ass _ _ _ _ _ _ _ Hc Hk') (ext_eq_ctx_right _ _ _ _ _ (HBc _ _ _ _ Hk' Hcon))).
    - intros k Mk b c gs n B Hk' Hb Hcon Hin.
      pose proof (ctxsub_ext _ _ _ _ _ (HBc _ _ _ _ Hk' Hcon) (elim_bctx_ass _ _ _ _ _ _ _ Hc Hk')) as HIdb.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HB _ _ _ _ _ _ _ Hk' Hb Hcon Hin) HIdb) as HB'; rewrite !exp_sub_id in HB'.
      pose proof (wf_bty_sub_eq _ _ _ _ _ _ _ _ _ _ _ Hl Hk' HΓ HUl' HUs' HUl HUs HUU' HA' Hcon) as Hbs.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HAb _ _ _ Hk' Hb) (HMv _ _ Hk')) as HA0; rewrite !exp_sub_id in HA0.
      pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HA0 Hbs) as Hty.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA0 (wf_sub_eq_left _ _ _ _ _ _ Hbs)) as Hty'.
      eapply wf_conv; [ exact HB' | exact Hty' | apply wf_exp_eq_sym; exact Hty ].
  Qed.

End Fixed_GCtx.

(** ** The Right-Hand Side of [wf_exp_eq_elim_cong]

    The right eliminator carries the uniform parameters of the right
    parameters [Ps'], so it is typed at them: its blocks, typed at the left
    uniform parameters with the motives varying
    ([wf_elim_cong_rhs_blocks]), are typed at the right ones
    ([blocks_typed_us_conv]), and so is the scrutinee; its type is then
    moved to the equation's, at the left parameters and scrutinee.  The
    lemma takes the rule's premises, the right parameters typed at the
    instances at the left ones. *)
Lemma wf_elim_cong_rhs : forall Θ Ξ Γ p D oq' Us' m Mm (Bks Bks' : list eblock) bm Ps Ps' M M' i,
    ind_lookup Θ Ξ p = Some D ->
    elim_grp D oq' p m ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = List.length (ind_members D) ->
    List.length Bks' = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length Ps' = im_np D Mm ->
    (forall k P P' T, nth_error Ps k = Some P -> nth_error Ps' k = Some P' ->
       nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P' : T) ->
    (forall k P P' T, nth_error Ps k = Some P -> nth_error Ps' k = Some P' ->
       nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Us' = List.firstn (ind_nu D) Ps' ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_nm b = S (im_nn Mk)) ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_ann b = Some Z ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
    (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b' : Typeω@i) ->
    (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b ≈ eb_motive b' : Typeω@i) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' ->
       nth_error (eb_brs b) i = Some (c, n, B) -> nth_error (eb_brs b') i = Some (c, n, B') ->
       ind_con Mk c = Some gs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B'
         : elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq' Us' m Bks' M' : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hgr Hm Hbm HlB HlB' HPl HPs HPl' HPs'' HPP HM HM' HMM Hann' Hnm Hnm' HZ' HA HA'' HAA HΨ Hn Hf Hk HB.
  subst Us'.
  pose proof (presup_exp_ctx HM) as HΓ.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (wf_elim_cong_rhs_blocks _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm HlB HlB' HPl HPs Hnm Hnm' HZ' HA HA'' HAA HΨ Hn Hf Hk HB)
    as HBt.
  (* the right parameters, at the instances at themselves *)
  assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ps ≈ sb_of_list Id Ps' : im_params D Mm ++ Γ).
  { eapply wf_sub_eq_of_list_left;
      [ eapply decl_closed_params_ass; eassumption | exact (wf_params_app _ _ _ HD Hc _ _ _ Hm HΓ)
      | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite length_im_params; exact HPl | rewrite length_im_params; exact HPl'
      | exact HPs | | exact HPP ].
    intros k N T HN HT.
    assert (Hk' : k < List.length Ps) by (rewrite HPl, <- HPl'; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some Ps k Hk') as [P HP]; exact (HPs'' _ _ _ _ HP HN HT). }
  pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ ltac:(eapply decl_closed_params_ass; eassumption)
                ltac:(rewrite length_im_params; exact HPl') (wf_sub_eq_right _ _ _ _ _ _ Hσσ)) as HPs'.
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hm HPl HPs) as [HUs HNs].
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps' Hm HPl' HPs') as [HUs' HNs'].
  destruct (params_eq_split Γ D m Mm Ps Ps' Hc Hm HPl HPl' HPP) as [HUe HNe].
  destruct (params_typed_at_split Γ D m Mm Ps Ps' Hc Hm HPl HPl' HPs'') as [_ HNa].
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Us' := List.firstn (ind_nu D) Ps') in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *; set (Ns' := List.skipn (ind_nu D) Ps') in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_firstn; unfold im_np in HPl'; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  assert (HNl' : List.length Ns' = im_nn Mm) by (unfold Ns'; rewrite List.length_skipn; unfold im_np in HPl'; lia).
  pose proof (blocks_typed_us_conv _ _ _ _ _ _ _ Hl HΓ HUl HUs HUl' HUs' HUe HBt) as HBt'.
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  assert (Hσσu : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ).
  { eapply wf_sub_eq_of_list_conv; [ exact (dc_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ)
                                   | apply wf_sub_eq_refl, wf_sub_id, HΓ | exact HUl | exact HUl' | exact HUs | exact HUs' | exact HUe ]. }
  (* the non-uniform parameters, as a substitution *)
  assert (Hti : forall j T, nth_error (tele_insts (tele_sub (im_nparams Mm) (sb_of_list Id Us)) Id Ns) j = Some T ->
             nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T).
  { intros j T HT; rewrite tele_insts_tele_sub in HT.
    rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT by apply sb_compose_id_right; exact HT. }
  assert (Hδδ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ns ≈ sb_of_list Id Ns' : tele_sub (im_nparams Mm) (sb_of_list Id Us) ++ Γ).
  { eapply wf_sub_eq_of_list_left;
      [ apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HD _ _ Hm) | exact (wf_nparams_sub _ _ _ HD Hc _ _ _ _ Hm HΓ Hσ)
      | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite length_tele_sub; exact HNl | rewrite length_tele_sub; exact HNl' | | | ].
    - intros j N T HN HT; exact (HNs _ _ _ HN (Hti _ _ HT)).
    - intros j N' T HN' HT.
      assert (Hj : j < List.length Ns) by (rewrite HNl, <- HNl'; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some Ns j Hj) as [N HN]; exact (HNa _ _ _ _ HN HN' (Hti _ _ HT)).
    - intros j N N' T HN HN' HT; exact (HNe _ _ _ _ HN HN' (Hti _ _ HT)). }
  pose proof (wf_sub_eq_right _ _ _ _ _ _ Hδδ) as Hδ'.
  pose proof (wf_sub_nparams_inst _ _ _ _ _ _ _ _ Hl Hm HΓ HPl' HPs') as Hδ2; fold Us' Ns' in Hδ2.
  (* the member's type: at the right non-uniform, then uniform, parameters *)
  pose proof (elim_mctx_us_eq _ _ _ _ _ _ _ Hl Hm HΓ HUl HUl' Hσσu) as HMc_eq.
  unfold elim_mctx in HMc_eq.
  destruct (ext_eq_ass_inv _ _ _ _ _ _ _ HMc_eq) as (j & _ & Hhd & Hhh & Hhd').
  assert (Ehd : forall Vs Xs, List.length Vs = ind_nu D -> List.length Xs = im_nn Mm ->
             (ind_mty p D m (List.map (fun U => U[wk_shiftn (im_nn Mm)]ʷ) Vs) (vars_from 0 (im_nn Mm)))[sb_of_list Id Xs]
             = ind_mty p D m Vs Xs).
  { intros Vs Xs HVl HXl; rewrite ind_head_inst by assumption.
    rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id; reflexivity. }
  pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ Hhd Hδδ) as HT1.
  pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hhh Hδ') as HT2.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hhd Hδ') as HT1t.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hhd' Hδ2) as HT2t.
  rewrite !Ehd in HT1 by assumption; rewrite !Ehd in HT2 by assumption.
  rewrite !Ehd in HT1t by assumption; rewrite !Ehd in HT2t by assumption.
  assert (HM1 : Θ ⍮ Ξ ⍮ Γ ⊢ M' : ind_mty p D m Us Ns') by (eapply wf_conv; [ exact HM' | exact HT1t | exact HT1 ]).
  assert (HM2 : Θ ⍮ Ξ ⍮ Γ ⊢ M' : ind_mty p D m Us' Ns') by (eapply wf_conv; [ exact HM1 | exact HT2t | exact HT2 ]).
  destruct (blocks_nth _ _ _ _ HlB' Hm) as [bm' Hbm'].
  pose proof (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hgr Hm Hbm' HBt' HUl' HUs' HNl' HNs' HM2) as HE.
  (* the type: at the left parameters and scrutinee *)
  pose proof (fun j Mj Hj => ext_eq_ctx_left _ _ _ _ _ (HΨ j Mj Hj)) as HMx.
  pose proof (wf_elim_inst_sub _ _ _ _ _ _ _ _ _ Hc Hm HPl HPs HM (HMx _ _ Hm)) as Hτ; fold Us Ns in Hτ.
  assert (Hττ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (Ns ++ M :: nil) ≈ sb_of_list Id (Ns' ++ M' :: nil) : elim_mctx p D m Mm Us ++ Γ).
  { rewrite !sb_of_list_app; cbn [sb_of_list]; unfold elim_mctx; cbn [List.app].
    eapply wf_sub_eq_extend; [ exact Hδδ | exact Hhd | rewrite Ehd by assumption; exact HM | rewrite Ehd by assumption; exact HM1
                             | rewrite Ehd by assumption; exact HMM ]. }
  pose proof (sub_eq_preserves_exp _ _ _ _ _ (HA'' _ _ _ _ Hm Hbm Hbm') _ _ _ Hττ) as H1.
  pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ (HAA _ _ _ _ Hm Hbm Hbm') Hτ) as H2.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HA _ _ _ Hm Hbm) Hτ) as H3.
  eapply wf_conv; [ exact HE | exact H3 |].
  eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact H1 | apply wf_exp_eq_sym; exact H2 ].
Qed.
