(** * Congruences at the Instances of a Telescope

    Equal lists of terms instantiate a telescope to equal substitutions, and
    a term of a [Π] over a closed telescope applies to them equally.  The
    gluing model compares the parameters of an inductive type, and the
    arguments of a constructor, position by position, so these are what
    move a term along such a comparison. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {Θ : gdeps} {Ξ : gstack}.

  Lemma wf_sub_eq_of_list : forall Δ Γ Γ0 σ σ' Ms Ms',
      tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ0 -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Γ0 ->
      List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
      (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
         List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list σ Ms ≈ sb_of_list σ' Ms' : Δ ++ Γ0.
  Proof.
    induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ Hl Hl' HMs.
    - destruct Ms; [| discriminate ]; destruct Ms'; [| discriminate ]; exact Hσ.
    - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
      rewrite List.length_app in Hl, Hl'; cbn in Hl, Hl'.
      destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; destruct Ms' as [| M0' Ms']; [ cbn in Hl'; lia |]; cbn in Hl, Hl'.
      rewrite <- List.app_assoc in HΔ |- *; cbn [List.app] in HΔ |- *.
      destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [k HA0]].
      assert (HM0 : Θ ⍮ Ξ ⍮ Γ ⊢ M0 ≈ M0' : A0[σ]) by (apply (HMs 0); [ reflexivity | reflexivity | rewrite tele_insts_snoc; reflexivity ]).
      cbn [sb_of_list]; eapply IH; [ exact Hass | exact HΔ | | lia | lia |].
      + gen_presups.
        eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | assumption | | assumption ].
        eapply wf_conv'; [ eassumption | mauto 3 ].
      + intros k' N N' T HN HN' HT; apply (HMs (S k')); [ exact HN | exact HN' | rewrite tele_insts_snoc; exact HT ].
  Qed.

  Lemma wf_exp_eq_apps_ctx_pi_n : forall n Δ Γ B i M M' Ms Ms',
      List.length Δ = n ->
      tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : Typeω@i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ctx_pi Δ B ->
      List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
      (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
         List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ms ≈ apps M' Ms' : B[sb_of_list Id Ms].
  Proof.
    induction n as [| n IH]; intros * Hn Hass HΔ HB HM Hl Hl' HMs.
    - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; destruct Ms'; [| discriminate ].
      cbn; rewrite exp_sub_id; exact HM.
    - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
      rename Δ0 into Δ.
      rewrite List.length_app in Hn; cbn in Hn.
      unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
      rewrite List.length_app in Hl, Hl'; cbn in Hl, Hl'.
      destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; destruct Ms' as [| M0' Ms']; [ cbn in Hl'; lia |]; cbn in Hl, Hl'.
      rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
      destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [k HA0]].
      assert (HM0 : Θ ⍮ Ξ ⍮ Γ ⊢ M0 ≈ M0' : A0)
        by (rewrite <- (exp_sub_id A0); apply (HMs 0); [ reflexivity | reflexivity | rewrite tele_insts_snoc; reflexivity ]).
      assert (Happ : Θ ⍮ Ξ ⍮ Γ ⊢ M $ M0 ≈ M' $ M0' : (ctx_pi Δ B)[Id,,M0]) by (eapply wf_exp_eq_app_cong'; eassumption).
      rewrite ctx_pi_sub in Happ.
      assert (HM0t : Θ ⍮ Ξ ⍮ Γ ⊢ M0 : A0) by (gen_presups; assumption).
      pose proof (wf_sub_single _ _ _ _ _ _ HA0 HM0t) as Hs.
      assert (HΔ' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ (Id,,M0) ++ Γ) by (eapply ctx_sub_wf; eassumption).
      pose proof (wf_sub_ext _ _ _ _ _ _ Hs HΔ' HΔ) as Hs'.
      cbn [apps_exp sb_of_list].
      replace (B[sb_of_list (Id,,M0) Ms]) with (B[sb_qn (List.length Δ) (Id,,M0)][sb_of_list Id Ms])
        by (replace (List.length Δ) with (List.length Ms) by lia; apply exp_sub_qn_of_list).
      eapply (IH (tele_sub Δ (Id,,M0))); [ rewrite length_tele_sub; lia | apply tele_ass_sub; exact Hass | exact HΔ' | | exact Happ
                 | rewrite length_tele_sub; lia | rewrite length_tele_sub; lia |].
      + exact (sub_preserves_exp _ _ _ _ _ _ _ HB Hs').
      + intros k' N N' T HN HN' HT; apply (HMs (S k')); [ exact HN | exact HN' |].
        rewrite tele_insts_snoc; cbn [List.nth_error].
        rewrite tele_insts_tele_sub in HT; rewrite <- HT; f_equal.
        apply tele_insts_sb_eq; symmetry; apply sb_compose_id_right.
  Qed.

  (** A term of a [Π] over a closed telescope applies equally to equal terms
      of its types. *)
  Lemma wf_exp_eq_apps_closed_pi : forall Δ B i Ψ M M' Ms Ms',
      tele_ass Δ -> ctx_scoped 0 Δ -> exp_scoped (List.length Δ) B -> Θ ⍮ Ξ ⍮ Δ ⊢ B : Typeω@i ->
      ⊢ Θ ⍮ Ξ ⍮ Ψ -> Θ ⍮ Ξ ⍮ Ψ ⊢ M ≈ M' : ctx_pi Δ B ->
      List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
      (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
         List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ apps M Ms ≈ apps M' Ms' : B[sb_of_list Id Ms].
  Proof.
    intros * Hass Hs HsB HB HΨ HM Hl Hl' HMs.
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ Δ ++ ⋅) by (rewrite List.app_nil_r; eapply presup_exp_ctx; exact HB).
    pose proof (wf_wk_shiftn_app Θ Ξ Ψ ⋅) as Hw; rewrite List.app_nil_r in Hw.
    specialize (Hw HΨ ltac:(constructor; eapply ctx_wf_gctx; eassumption)).
    assert (HΔΨ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Ψ).
    { pose proof (wk_preserves_ext _ _ _ _ _ _ _ (ctx_ext_refl _ _ _ _ Hass HΔ0) Hw) as Hx.
      rewrite tele_closed_wk in Hx by exact Hs; eapply ext_eq_ctx_left; exact Hx. }
    eapply (wf_exp_eq_apps_ctx_pi_n (List.length Δ)); [ reflexivity | exact Hass | exact HΔΨ | | exact HM | exact Hl | exact Hl' | exact HMs ].
    pose proof (wf_wk_ext _ _ Δ _ _ _ Hw) as Hq.
    rewrite tele_closed_wk in Hq by exact Hs; specialize (Hq HΔΨ HΔ0).
    rewrite <- (exp_scoped_wk_id B (List.length Δ + 0) (wk_qn (List.length Δ) (wk_shiftn (List.length Ψ))))
      by (rewrite Nat.add_0_r; assumption || (intros; apply wk_qn_fix with (n := 0); [ lia | lia ])).
    assert (HB0 : Θ ⍮ Ξ ⍮ Δ ++ ⋅ ⊢ B : Typeω@i) by (rewrite List.app_nil_r; exact HB).
    exact (wk_preserves_exp _ _ _ _ _ _ _ HB0 Hq).
  Qed.

  (** The type former of a declared member applied to equal terms of its
      parameters' types. *)
  Lemma wf_exp_eq_ind_apps : forall Ψ p D k Mk Ms Ms',
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> k < ind_ndecl D -> ⊢ Θ ⍮ Ξ ⍮ Ψ ->
      List.length Ms = im_np D Mk -> List.length Ms' = im_np D Mk ->
      (forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
         List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind p k) Ms ≈ apps (a_ind p k) Ms' : (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms].
  Proof.
    intros * Hl Hk Hlt HΨ HMl HMl' HMs.
    destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
    destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([i Hi] & _).
    eapply wf_exp_eq_apps_closed_pi;
      [ eapply decl_closed_params_ass; eassumption | eapply decl_closed_params; eassumption | | exact Hi | exact HΨ
      | | rewrite length_im_params; exact HMl | rewrite length_im_params; exact HMl' | exact HMs ].
    - eapply exp_scoped_wk; [ exact (dc_sort _ Hc) |]; intros x Hx; rewrite length_im_params; unfold wk_shiftn, im_np; lia.
    - apply wf_exp_eq_refl; eapply wf_ind; eassumption.
  Qed.

  (** A constructor of a declared member applied to equal parameters and
      arguments. *)
  Lemma wf_exp_eq_con_apps : forall Γ p D k Mk c gs Ps Ps' As As',
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> k < ind_ndecl D -> ind_con Mk c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Ps = im_np D Mk -> List.length Ps' = im_np D Mk ->
      (forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error Ps' j = Some P' ->
         List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T) ->
      List.length As = List.length gs -> List.length As' = List.length gs ->
      (forall j N N' T, List.nth_error As j = Some N -> List.nth_error As' j = Some N' ->
         List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Ps) As) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_con p k c) (Ps ++ As) ≈ apps (a_con p k c) (Ps' ++ As')
        : ind_mty p D k (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps).
  Proof.
    intros * Hl Hk Hlt Hcon HΓ HPl HPl' HPs HAl HAl' HAs.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    destruct (con_cod_typed _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j Hj].
    destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j0 Hj0].
    destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ0 & _ & _).
    assert (HC : Θ ⍮ Ξ ⍮ Γ ⊢ a_con p k c : con_ty p D k Mk gs) by (eapply wf_con_of_lookup; eassumption).
    unfold con_ty in HC; rewrite <- ctx_pi_app in HC.
    destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ Hj) as (_ & Hscod & _).
    assert (Hass : tele_ass (cargs_ctx p D Mk gs ++ im_params D Mk))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_params_ass; eassumption ]).
    pose proof (wf_exp_eq_apps_closed_pi _ _ j _ _ _ (Ps ++ As) (Ps' ++ As') Hass
                  (cargs_ctx_closed p D k Mk c gs gs nil Hc Hk Hin (eq_sym (List.app_nil_r gs))) Hscod Hj HΓ (wf_exp_eq_refl HC)) as HR.
    set (Us := List.firstn (ind_nu D) Ps); set (Ns := List.skipn (ind_nu D) Ps).
    assert (HPs' : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
    assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
    assert (HNl : List.length Ns = im_nn Mk) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
    replace (ind_mty p D k Us Ns)
      with ((ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list Id (Ps ++ As)]).
    - apply HR.
      + rewrite !List.length_app, length_cargs_ctx, length_im_params, HPl, HAl; lia.
      + rewrite !List.length_app, length_cargs_ctx, length_im_params, HPl', HAl'; lia.
      + rewrite tele_insts_app by (try (eapply decl_closed_params_ass; eassumption); rewrite length_im_params; exact HPl).
        intros j1 N N' T HN HN' HT.
        assert (Hl2 : List.length (tele_insts (im_params D Mk) Id Ps) = List.length Ps)
          by (rewrite length_tele_insts by (eapply decl_closed_params_ass; eassumption); rewrite length_im_params; lia).
        destruct (Nat.lt_ge_cases j1 (List.length Ps)) as [Hj1 | Hj1].
        * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HN' by lia;
            rewrite List.nth_error_app1 in HT by lia; eauto.
        * rewrite List.nth_error_app2 in HN, HT by lia; rewrite List.nth_error_app2 in HN' by lia.
          rewrite Hl2 in HT; replace (j1 - List.length Ps') with (j1 - List.length Ps) in HN' by lia; eauto.
    - rewrite ind_mty_sub by (try exact Hc; apply length_ind_uvars).
      rewrite HPs', <- List.app_assoc; f_equal.
      + unfold ind_uvars.
        replace (vars_from (List.length gs + im_nn Mk) (ind_nu D)) with (vars_from (List.length (Ns ++ As)) (List.length Us))
          by (rewrite List.length_app, HNl, HAl, HUl; f_equal; lia).
        apply vars_from_sb_of_list_app.
      + replace (vars_from (List.length gs) (im_nn Mk)) with (vars_from (List.length As) (List.length Ns))
          by (rewrite HNl, HAl; reflexivity).
        apply vars_from_sb_of_list_mid.
  Qed.

  (** Equal instances of a telescope have equal types, position by
      position. *)
  Lemma tele_insts_cong : forall Δ Γ Γ0 σ σ' Ms Ms',
      tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ0 -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Γ0 ->
      List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
      (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
         List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T) ->
      forall k T T', List.nth_error (tele_insts Δ σ Ms) k = Some T -> List.nth_error (tele_insts Δ σ' Ms') k = Some T' ->
        exists i, Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ T' : Typeω@i.
  Proof.
    induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ Hl Hl' HMs k T T' HT HT'.
    - destruct Ms; [| discriminate ]; unfold tele_insts in HT; cbn in HT; destruct k; discriminate.
    - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
      rewrite List.length_app in Hl, Hl'; cbn in Hl, Hl'.
      destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; destruct Ms' as [| M0' Ms']; [ cbn in Hl'; lia |]; cbn in Hl, Hl'.
      rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
      destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [i0 HA0]].
      rewrite tele_insts_snoc in HT, HT'.
      destruct k as [| k]; cbn [List.nth_error] in HT, HT'.
      + injection HT as <-; injection HT' as <-; exists i0; eapply sub_eq_preserves_typ; eassumption.
      + assert (HM0 : Θ ⍮ Ξ ⍮ Γ ⊢ M0 ≈ M0' : A0[σ])
          by (apply (HMs 0); [ reflexivity | reflexivity | rewrite tele_insts_snoc; reflexivity ]).
        eapply (IH Γ (Γ0 ▹ A0) (σ,,M0) (σ',,M0') Ms Ms'); [ exact Hass | exact HΔ | | lia | lia | | exact HT | exact HT' ].
        * gen_presups.
          eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | assumption | | assumption ].
          eapply wf_conv'; [ eassumption | mauto 3 ].
        * intros k' N N' T0 HN HN' HT0; apply (HMs (S k')); [ exact HN | exact HN' | rewrite tele_insts_snoc; exact HT0 ].
  Qed.

  (** ** The Parameters of an Inductive Type *)

  Lemma params_ctx_wf : forall Γ p D k Mk, ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ im_params D Mk ++ Γ.
  Proof.
    intros * Hl Hk HΨ.
    destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
    exact (wf_params_app _ _ _ HD Hc _ _ _ Hk HΨ).
  Qed.

  Lemma params_types_cong : forall Γ p D k Mk Xs Ys, ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Xs = im_np D Mk -> List.length Ys = im_np D Mk ->
      (forall j X Y T, List.nth_error Xs j = Some X -> List.nth_error Ys j = Some Y ->
         List.nth_error (tele_insts (im_params D Mk) Id Xs) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      forall j T T', List.nth_error (tele_insts (im_params D Mk) Id Xs) j = Some T ->
        List.nth_error (tele_insts (im_params D Mk) Id Ys) j = Some T' -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ T' : Typeω@i.
  Proof.
    intros * Hl Hk HΓ HXl HYl HXY.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
    eapply (tele_insts_cong (im_params D Mk) Γ Γ Id Id);
      [ eapply decl_closed_params_ass; eassumption | eapply params_ctx_wf; eassumption
      | apply wf_sub_eq_refl; mauto 3 | rewrite length_im_params; exact HXl | rewrite length_im_params; exact HYl | exact HXY ].
  Qed.

  Lemma params_eq_trans : forall Γ p D k Mk Xs Ys Zs, ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Xs = im_np D Mk -> List.length Ys = im_np D Mk -> List.length Zs = im_np D Mk ->
      (forall j X Y T, List.nth_error Xs j = Some X -> List.nth_error Ys j = Some Y ->
         List.nth_error (tele_insts (im_params D Mk) Id Xs) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      (forall j Y Z T, List.nth_error Ys j = Some Y -> List.nth_error Zs j = Some Z ->
         List.nth_error (tele_insts (im_params D Mk) Id Ys) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ Y ≈ Z : T) ->
      (forall j X Z T, List.nth_error Xs j = Some X -> List.nth_error Zs j = Some Z ->
         List.nth_error (tele_insts (im_params D Mk) Id Xs) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Z : T).
  Proof.
    intros * Hl Hk HΓ HXl HYl HZl HXY HYZ j X Z T HX HZ HT.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
    destruct (nth_error_lt_some Ys j ltac:(rewrite HYl, <- HZl; apply List.nth_error_Some; congruence)) as [Y HY].
    destruct (nth_error_lt_some (tele_insts (im_params D Mk) Id Ys) j) as [T' HT'].
    { rewrite length_tele_insts_params by (try (eapply decl_closed_params_ass; eassumption); exact HYl).
      rewrite HYl, <- HZl; apply List.nth_error_Some; congruence. }
    destruct (params_types_cong _ _ _ _ _ _ _ Hl Hk HΓ HXl HYl HXY _ _ _ HT HT') as [i HTT].
    etransitivity; [ exact (HXY _ _ _ _ HX HY HT) |].
    eapply wf_exp_eq_conv'; [ exact (HYZ _ _ _ _ HY HZ HT') | symmetry; exact HTT ].
  Qed.

  Lemma params_eq_sym : forall Γ p D k Mk Xs Ys, ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Xs = im_np D Mk -> List.length Ys = im_np D Mk ->
      (forall j X Y T, List.nth_error Xs j = Some X -> List.nth_error Ys j = Some Y ->
         List.nth_error (tele_insts (im_params D Mk) Id Xs) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      (forall j Y X T, List.nth_error Ys j = Some Y -> List.nth_error Xs j = Some X ->
         List.nth_error (tele_insts (im_params D Mk) Id Ys) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ Y ≈ X : T).
  Proof.
    intros * Hl Hk HΓ HXl HYl HXY j Y X T HY HX HT.
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
    destruct (nth_error_lt_some (tele_insts (im_params D Mk) Id Xs) j) as [T0 HT0].
    { rewrite length_tele_insts_params by (try (eapply decl_closed_params_ass; eassumption); exact HXl).
      rewrite HXl, <- HYl; apply List.nth_error_Some; congruence. }
    destruct (params_types_cong _ _ _ _ _ _ _ Hl Hk HΓ HXl HYl HXY _ _ _ HT0 HT) as [i HTT].
    symmetry; eapply wf_exp_eq_conv'; [ exact (HXY _ _ _ _ HX HY HT0) | exact HTT ].
  Qed.

  (** The same for any closed telescope. *)
  Lemma tele_eq_trans : forall Γ C Xs Ys Zs, tele_ass C -> ⊢ Θ ⍮ Ξ ⍮ C ++ Γ ->
      List.length Xs = List.length C -> List.length Ys = List.length C -> List.length Zs = List.length C ->
      (forall k X Y T, List.nth_error Xs k = Some X -> List.nth_error Ys k = Some Y ->
         List.nth_error (tele_insts C Id Xs) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      (forall k Y Z T, List.nth_error Ys k = Some Y -> List.nth_error Zs k = Some Z ->
         List.nth_error (tele_insts C Id Ys) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ Y ≈ Z : T) ->
      (forall k X Z T, List.nth_error Xs k = Some X -> List.nth_error Zs k = Some Z ->
         List.nth_error (tele_insts C Id Xs) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Z : T).
  Proof.
    intros * Hass HC HXl HYl HZl HXY HYZ k X Z T HX HZ HT.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (eapply ctx_app_wf_tail; exact HC).
    destruct (nth_error_lt_some Ys k ltac:(rewrite HYl, <- HZl; apply List.nth_error_Some; congruence)) as [Y HY].
    destruct (nth_error_lt_some (tele_insts C Id Ys) k) as [T' HT'].
    { rewrite length_tele_insts by exact Hass.
      assert (k < List.length Zs) by (apply List.nth_error_Some; congruence); lia. }
    destruct (tele_insts_cong C Γ Γ Id Id Xs Ys Hass HC ltac:(apply wf_sub_eq_refl; mauto 3) HXl HYl HXY _ _ _ HT HT') as [i HTT].
    etransitivity; [ exact (HXY _ _ _ _ HX HY HT) |].
    eapply wf_exp_eq_conv'; [ exact (HYZ _ _ _ _ HY HZ HT') | symmetry; exact HTT ].
  Qed.

  Lemma uparams_ctx_wf : forall Γ p D, ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ.
  Proof.
    intros * Hl HΓ; destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    exact (wf_uparams_app _ _ _ HD Hc _ HΓ).
  Qed.

  (** The type of a recursive argument is the type of its shape. *)
  Lemma cargs_rec_type : forall p D Mk gs gs1 Pr gs2 σ As T, gs = gs1 ++ ca_rec Pr :: gs2 ->
      List.nth_error (tele_insts (cargs_ctx p D Mk gs) σ As) (List.length gs1) = Some T ->
      T = (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) Pr)[sb_of_list σ (List.firstn (List.length gs1) As)].
  Proof.
    intros * -> HT.
    destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
    unfold cargs_ctx in HA; rewrite cargs_ctx_aux_app in HA; cbn [cargs_ctx_aux] in HA.
    rewrite !List.rev_app_distr in HA; cbn [List.rev List.app] in HA.
    rewrite List.nth_error_app2 in HA by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
    rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag in HA; cbn in HA.
    injection HA as <-; rewrite List.app_nil_r; reflexivity.
  Qed.

  (** The sort of an inductive type at equal parameters. *)
  Lemma ind_sort_inst_cong : forall Ψ p D k Mk Ms Ms',
      ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Ψ ->
      List.length Ms = im_np D Mk -> List.length Ms' = im_np D Mk ->
      (forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
         List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
      exists i, Θ ⍮ Ξ ⍮ Ψ ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms]
                  ≈ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms'] : Typeω@i.
  Proof.
    intros * Hl Hk HΨ HMl HMl' HMs.
    destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
    destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([i Hi] & _).
    pose proof (decl_closed_params_ass _ _ _ Hc Hk) as Hass; pose proof (decl_closed_params _ _ _ Hc Hk) as Hs.
    assert (HsB : exp_scoped (List.length (im_params D Mk)) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)
      by (eapply exp_scoped_wk; [ exact (dc_sort _ Hc) |]; intros x Hx; rewrite length_im_params; unfold wk_shiftn, im_np; lia).
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ im_params D Mk ++ ⋅) by (rewrite List.app_nil_r; eapply presup_exp_ctx; exact Hi).
    pose proof (wf_wk_shiftn_app Θ Ξ Ψ ⋅) as Hw; rewrite List.app_nil_r in Hw.
    specialize (Hw HΨ ltac:(constructor; eapply ctx_wf_gctx; eassumption)).
    pose proof (params_ctx_wf _ _ _ _ _ Hl Hk HΨ) as HΔΨ.
    pose proof (wf_wk_ext _ _ (im_params D Mk) _ _ _ Hw) as Hq.
    rewrite tele_closed_wk in Hq by exact Hs; specialize (Hq HΔΨ HΔ0).
    assert (HB : Θ ⍮ Ξ ⍮ im_params D Mk ++ Ψ ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ : Typeω@i).
    { rewrite <- (exp_scoped_wk_id (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ (List.length (im_params D Mk) + 0)
                   (wk_qn (List.length (im_params D Mk)) (wk_shiftn (List.length Ψ))))
        by (rewrite Nat.add_0_r; assumption || (intros; apply wk_qn_fix with (n := 0); [ lia | lia ])).
      assert (HB0 : Θ ⍮ Ξ ⍮ im_params D Mk ++ ⋅ ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ : Typeω@i)
        by (rewrite List.app_nil_r; exact Hi).
      exact (wk_preserves_exp _ _ _ _ _ _ _ HB0 Hq). }
    exists i; eapply sub_eq_preserves_typ; [ exact HB |].
    eapply wf_sub_eq_of_list; [ exact Hass | exact HΔΨ | mauto 3 | rewrite length_im_params; exact HMl
                              | rewrite length_im_params; exact HMl' | exact HMs ].
  Qed.

  (** The pieces of a [Π] over a telescope are types at its level. *)
  Lemma ctx_pi_inv_outer : forall Δ2 Γ C j, tele_ass Δ2 ->
      Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ2 C : Typeω@j -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ C : Typeω@j.
  Proof.
    induction Δ2 as [| e Δ2 IH] using List.rev_ind; intros * Hass H; [ exact H |].
    unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite ctx_pi_snoc in H; apply wf_pi_inversion' in H as [_ H].
    rewrite <- List.app_assoc; exact (IH _ _ _ Hass H).
  Qed.

  Lemma ctx_pi_split_typed : forall Δt Γ B j, tele_ass Δt -> Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δt B : Typeω@j ->
      (forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ ctx_pi Δ1 B : Typeω@j) /\
      (forall Δ1 A Δ2, Δt = Δ1 ++ ce_ass A :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ A : Typeω@j).
  Proof.
    intros * Hass H; split.
    - intros Δ1 Δ2 ->; rewrite ctx_pi_app in H.
      unfold tele_ass in Hass; apply List.Forall_app in Hass as [_ Hass].
      exact (ctx_pi_inv_outer _ _ _ _ Hass H).
    - intros Δ1 A Δ2 ->.
      replace (Δ1 ++ ce_ass A :: Δ2) with ((Δ1 ++ ⋅ ▹ A) ++ Δ2) in H by (rewrite <- List.app_assoc; reflexivity).
      rewrite ctx_pi_app, ctx_pi_snoc in H.
      unfold tele_ass in Hass; apply List.Forall_app in Hass as [_ Hass]; apply List.Forall_cons_iff in Hass as [_ Hass].
      exact (proj1 (wf_pi_inversion' (ctx_pi_inv_outer _ _ _ _ Hass H))).
  Qed.

  Lemma apps_exp_snoc : forall Ms M N, apps M (Ms ++ N :: nil) = a_app (apps M Ms) N.
  Proof. induction Ms as [| M0 Ms IH]; intros; cbn; [ reflexivity | apply IH ]. Qed.

  Lemma apps_ind_inj : forall p k Q Q', apps (a_ind p k) Q = apps (a_ind p k) Q' -> Q = Q'.
  Proof.
    intros p k Q; induction Q as [| N Q IH] using List.rev_ind; intros Q' H;
      destruct Q' as [| N' Q' _] using List.rev_ind; try reflexivity;
      rewrite ?apps_exp_snoc in H; cbn in H; try discriminate.
    injection H as H ->; rewrite (IH _ H); reflexivity.
  Qed.

  (** The type of a recursive argument is the shape's type at the uniform
      parameters of the constructor's parameters. *)
  Lemma cargs_rec_type_at : forall p D Mk gs gs1 Pr gs2 Ps As T, gs = gs1 ++ ca_rec Pr :: gs2 ->
      decl_closed D -> List.length Ps = im_np D Mk ->
      List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Ps) As) (List.length gs1) = Some T ->
      T = ptyp_ty_at p D (List.firstn (ind_nu D) Ps)
            ((ι (wk_pat (cargs_pat gs1))) ⨟ sb_of_list Id (Ps ++ List.firstn (List.length gs1) As)) Pr.
  Proof.
    intros * Heq Hc HPl HT.
    assert (HAl : List.length gs1 < List.length As).
    { destruct (Nat.lt_ge_cases (List.length gs1) (List.length As)) as [| Hge]; [ assumption |].
      rewrite (proj2 (List.nth_error_None _ _)) in HT; [ discriminate |].
      rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; subst gs; lia. }
    rewrite (cargs_rec_type _ _ _ _ _ _ _ _ _ _ Heq HT), ptyp_ty_eq_at, ptyp_ty_at_sub, <- sb_of_list_app
      by (try exact Hc; apply length_ind_uvars).
    f_equal.
    rewrite length_cargs_pat.
    assert (HA1 : List.length (List.firstn (List.length gs1) As) = List.length gs1) by (rewrite List.length_firstn; lia).
    replace (Ps ++ List.firstn (List.length gs1) As)
      with (List.firstn (ind_nu D) Ps ++ (List.skipn (ind_nu D) Ps ++ List.firstn (List.length gs1) As))
      by (rewrite List.app_assoc, List.firstn_skipn; reflexivity).
    pose proof (vars_from_sb_of_list_app (List.firstn (ind_nu D) Ps)
                  (List.skipn (ind_nu D) Ps ++ List.firstn (List.length gs1) As) Id) as E.
    replace (List.length (List.skipn (ind_nu D) Ps ++ List.firstn (List.length gs1) As)) with (List.length gs1 + im_nn Mk) in E
      by (rewrite List.length_app, List.length_skipn, HA1; unfold im_np in HPl; lia).
    replace (List.length (List.firstn (ind_nu D) Ps)) with (ind_nu D) in E by (rewrite List.length_firstn; unfold im_np in HPl; lia).
    unfold ind_uvars; exact E.
  Qed.

  (** A weakened term under an extension of a weakening. *)
  Lemma exp_shift_extend_wk : forall U φ b, U[↑]ʷ[(ι φ),,b] = U[φ]ʷ.
  Proof. intros; rewrite exp_sub_shift; apply exp_sub_of_wk_ext; intros [|?]; reflexivity. Qed.
End Fixed_GCtx.
