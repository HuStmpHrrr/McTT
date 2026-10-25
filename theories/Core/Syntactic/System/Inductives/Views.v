(** * The Eliminator at a View Is Typed as the Container's

    The right-hand side of [wf_exp_eq_elim_view], the container's
    eliminator at the container's member, its blocks those of the group's
    members the view's group lists ([vwrap]), is of the type of the left.
    The container's blocks are typed at the view's instance: a view's
    contexts, types and branches are the container's at the instance, up to
    the view equations of the group's declaration ([decl_typed]). *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Inductives Require Export Typing.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Equal Instances of a Telescope

    Two lists of terms, each of the instances of a telescope at itself, and
    equal one by one at the instances at the first, are equal
    substitutions into it. *)
Lemma wf_sub_eq_of_list_conv : forall Θ Ξ Δ Ψ Γ0 σ σ' Ms Ms',
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ0 -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : Γ0 ->
    List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall k N T, List.nth_error Ms' k = Some N -> List.nth_error (tele_insts Δ σ' Ms') k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
       List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list σ Ms ≈ sb_of_list σ' Ms' : Δ ++ Γ0.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ Hl Hl' HMs HMs' HMM.
  - destruct Ms; [| discriminate ]; destruct Ms'; [| discriminate ]; exact Hσ.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in Hl, Hl'; cbn in Hl, Hl'.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; destruct Ms' as [| M0' Ms']; [ cbn in Hl'; lia |]; cbn in Hl, Hl'.
    rewrite <- List.app_assoc in HΔ |- *; cbn [List.app] in HΔ |- *.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [k HA0]].
    assert (HM0 : Θ ⍮ Ξ ⍮ Ψ ⊢ M0 : A0[σ]) by (apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (HM0' : Θ ⍮ Ξ ⍮ Ψ ⊢ M0' : A0[σ']) by (apply (HMs' 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (HMM0 : Θ ⍮ Ξ ⍮ Ψ ⊢ M0 ≈ M0' : A0[σ])
      by (apply (HMM 0); [ reflexivity | reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    cbn [sb_of_list]; eapply IH; [ exact Hass | exact HΔ | | lia | lia | | |].
    + eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | exact HM0 | exact HM0' | exact HMM0 ].
    + intros k' N T HN HT; apply (HMs (S k')); [ exact HN | rewrite tele_insts_snoc; exact HT ].
    + intros k' N T HN HT; apply (HMs' (S k')); [ exact HN | rewrite tele_insts_snoc; exact HT ].
    + intros k' N N' T HN HN' HT; apply (HMM (S k')); [ exact HN | exact HN' | rewrite tele_insts_snoc; exact HT ].
Qed.

(** Lists of terms typed at the instances of two telescopes, one over the
    other, joined, and the same for equal lists. *)
Lemma list_typed_app : forall Θ Ξ Ψ Δ1 Δ2 σ Ms Ns,
    tele_ass Δ2 -> List.length Ms = List.length Δ2 ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ2 σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall k N T, List.nth_error Ns k = Some N -> List.nth_error (tele_insts Δ1 (sb_of_list σ Ms) Ns) k = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    forall k N T, List.nth_error (Ms ++ Ns) k = Some N -> List.nth_error (tele_insts (Δ1 ++ Δ2) σ (Ms ++ Ns)) k = Some T ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ N : T.
Proof.
  intros * Hass Hl HMs HNs k N T HN HT; rewrite tele_insts_app in HT by assumption.
  assert (Hl2 : List.length (tele_insts Δ2 σ Ms) = List.length Ms) by (rewrite length_tele_insts by exact Hass; lia).
  destruct (Nat.lt_ge_cases k (List.length Ms)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; eauto.
  - rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia; rewrite Hl2 in HT; eauto.
Qed.

Lemma list_eq_app : forall Θ Ξ Ψ Δ1 Δ2 σ Ms Ns Ms' Ns',
    tele_ass Δ2 -> List.length Ms = List.length Δ2 -> List.length Ms' = List.length Δ2 ->
    (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
       List.nth_error (tele_insts Δ2 σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    (forall k N N' T, List.nth_error Ns k = Some N -> List.nth_error Ns' k = Some N' ->
       List.nth_error (tele_insts Δ1 (sb_of_list σ Ms) Ns) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    forall k N N' T, List.nth_error (Ms ++ Ns) k = Some N -> List.nth_error (Ms' ++ Ns') k = Some N' ->
      List.nth_error (tele_insts (Δ1 ++ Δ2) σ (Ms ++ Ns)) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T.
Proof.
  intros * Hass Hl Hl' HMs HNs k N N' T HN HN' HT; rewrite tele_insts_app in HT by assumption.
  assert (Hl2 : List.length (tele_insts Δ2 σ Ms) = List.length Ms) by (rewrite length_tele_insts by exact Hass; lia).
  destruct (Nat.lt_ge_cases k (List.length Ms)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HN' by lia;
      rewrite List.nth_error_app1 in HT by lia; eauto.
  - rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HN' by lia.
    rewrite List.nth_error_app2 in HT by lia; rewrite Hl2 in HT.
    replace (k - List.length Ms') with (k - List.length Ms) in HN' by lia; eauto.
Qed.

(** The variables of a closed telescope, in it, at its instances. *)
Lemma vars_closed_typed : forall Θ Ξ Δ,
    tele_ass Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ->
    forall k N T, List.nth_error (vars_from 0 (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from 0 (List.length Δ))) k = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ N : T.
Proof. intros * Ha Hs Hm HΔ; exact (wf_vars_tele _ _ nil Δ Ha Hs Hm HΔ). Qed.

Lemma apps_vars_sb_of_list : forall M Ms,
    exp_scoped 0 M -> (apps M (vars_from 0 (List.length Ms)))[sb_of_list Id Ms] = apps M Ms.
Proof.
  intros * HM; rewrite apps_exp_sub, vars_from_sb_of_list; f_equal.
  rewrite <- (exp_sub_id M) at 2; eapply exp_scoped_sub_agree; [ exact HM | intros; lia ].
Qed.

(** A declared member's type former at equal instances of its parameters,
    in a large universe. *)
Lemma ind_apps_conv_large : forall Θ Ξ Ψ pq D k Mk Lc Lv,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ pq = Some D -> ind_member D k = Some Mk -> k < ind_ndecl D ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ ->
    List.length Lc = im_np D Mk -> List.length Lv = im_np D Mk ->
    (forall j N T, List.nth_error Lc j = Some N -> List.nth_error (tele_insts (im_params D Mk) Id Lc) j = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall j N T, List.nth_error Lv j = Some N -> List.nth_error (tele_insts (im_params D Mk) Id Lv) j = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall j N N' T, List.nth_error Lc j = Some N -> List.nth_error Lv j = Some N' ->
       List.nth_error (tele_insts (im_params D Mk) Id Lc) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    exists i, Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind pq k) Lc : Typeω@i /\ Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind pq k) Lv : Typeω@i /\
      Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind pq k) Lc ≈ apps (a_ind pq k) Lv : Typeω@i.
Proof.
  intros * Hg HDs Hl Hk Hlt HΨ HLc HLv HTc HTv HTT.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  set (Δ := im_params D Mk) in *.
  assert (HΔa : tele_ass Δ) by (eapply decl_closed_params_ass; eassumption).
  assert (HΔs : ctx_scoped 0 Δ) by (eapply decl_closed_params; eassumption).
  pose proof (member_params_wf _ _ _ _ _ HD Hk) as HΔ.
  pose proof (vars_closed_typed _ _ _ HΔa HΔs (decl_params_mvc _ _ _ HD _ _ Hk) HΔ) as Hvars.
  pose proof (wf_ind_apps _ _ _ _ _ _ _ _ HD Hc Hl Hk Hlt HΔ ltac:(rewrite length_vars_from; unfold Δ; apply length_im_params) Hvars) as HT0.
  destruct (member_sort_typed _ _ _ _ _ HD Hk) as (_ & [n Hn] & HSu).
  rewrite exp_at_vars, (exp_wk_id_ext _ _ wk_shiftn_zero) in HT0.
  2:{ eapply exp_scoped_wk; [ exact (dc_sort _ Hc) |]; intros x Hx; unfold Δ; rewrite length_im_params; unfold wk_shiftn, im_np; lia. }
  2:{ apply exp_mvc_wk, (dmv_sort _ (dt_mvc _ _ _ HD)). }
  destruct (sort_large _ _ _ _ _ _ HSu Hn HT0) as [i HTi].
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ HTi) as (_ & HsT & _).
  pose proof (wf_exp_closed_app _ _ _ Ψ _ (Typeω@i) HΔa HΔs HsT ltac:(cbn; auto) HTi HΨ) as HTi'.
  assert (Hσ : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list Id Lc ≈ sb_of_list Id Lv : Δ ++ Ψ).
  { eapply wf_sub_eq_of_list_conv; [ exact HΔa | apply wf_ctx_closed_app; assumption | apply wf_sub_eq_refl, wf_sub_id, HΨ
                                   | unfold Δ; rewrite length_im_params; exact HLc | unfold Δ; rewrite length_im_params; exact HLv
                                   | exact HTc | exact HTv | exact HTT ]. }
  exists i; pose proof (sub_eq_preserves_exp _ _ _ _ _ HTi' _ _ _ Hσ) as H; cbn [exp_sub] in H.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HTi' (wf_sub_eq_left _ _ _ _ _ _ Hσ)) as H1; cbn [exp_sub] in H1.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HTi' (wf_sub_eq_right _ _ _ _ _ _ Hσ)) as H2; cbn [exp_sub] in H2.
  assert (E : forall L, List.length L = im_np D Mk ->
             (apps (a_ind pq k) (vars_from 0 (List.length (im_params D Mk))))[sb_of_list Id L] = apps (a_ind pq k) L)
    by (intros L HL; rewrite length_im_params, <- HL; apply apps_vars_sb_of_list; exact I).
  rewrite (E Lc HLc), (E Lv HLv) in H; rewrite (E Lc HLc) in H1; rewrite (E Lv HLv) in H2; auto.
Qed.

(** The codomain of a constructor's type at the parameters and arguments. *)
Lemma con_cod_inst : forall pq D k Mk (gs : list carg) Ps As,
    decl_closed D -> List.length Ps = im_np D Mk -> List.length As = List.length gs ->
    (ind_mty pq D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list Id (Ps ++ As)]
    = ind_mty pq D k (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps).
Proof.
  intros * Hc HPl HAl.
  set (Us := List.firstn (ind_nu D) Ps); set (Ns := List.skipn (ind_nu D) Ps).
  assert (HPs' : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mk) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  rewrite ind_mty_sub by (try exact Hc; apply length_ind_uvars).
  rewrite HPs', <- List.app_assoc; f_equal.
  - unfold ind_uvars.
    replace (vars_from (List.length gs + im_nn Mk) (ind_nu D)) with (vars_from (List.length (Ns ++ As)) (List.length Us))
      by (rewrite List.length_app, HNl, HAl, HUl; f_equal; lia).
    apply vars_from_sb_of_list_app.
  - replace (vars_from (List.length gs) (im_nn Mk)) with (vars_from (List.length As) (List.length Ns))
      by (rewrite HNl, HAl; reflexivity).
    apply vars_from_sb_of_list_mid.
Qed.

(** A declared member's constructor at equal parameters and arguments,
    each list at the instances at itself. *)
Lemma con_apps_conv : forall Θ Ξ Ψ pq D k Mk c gs Ps Ps' As As',
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ pq = Some D -> ind_member D k = Some Mk -> k < ind_ndecl D ->
    ind_con Mk c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Ψ ->
    List.length Ps = im_np D Mk -> List.length Ps' = im_np D Mk ->
    List.length As = List.length gs -> List.length As' = List.length gs ->
    (forall j N T, List.nth_error Ps j = Some N -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall j N T, List.nth_error Ps' j = Some N -> List.nth_error (tele_insts (im_params D Mk) Id Ps') j = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall j N N' T, List.nth_error Ps j = Some N -> List.nth_error Ps' j = Some N' ->
       List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    (forall j N T, List.nth_error As j = Some N ->
       List.nth_error (tele_insts (cargs_ctx pq D Mk gs) (sb_of_list Id Ps) As) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall j N T, List.nth_error As' j = Some N ->
       List.nth_error (tele_insts (cargs_ctx pq D Mk gs) (sb_of_list Id Ps') As') j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall j N N' T, List.nth_error As j = Some N -> List.nth_error As' j = Some N' ->
       List.nth_error (tele_insts (cargs_ctx pq D Mk gs) (sb_of_list Id Ps) As) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_con pq k c) (Ps ++ As) ≈ apps (a_con pq k c) (Ps' ++ As')
      : ind_mty pq D k (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps).
Proof.
  intros * Hg HDs Hl Hk Hlt Hcon HΨ HPl HPl' HAl HAl' HPs HPs' HPP HAs HAs' HAA.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  set (Δ := cargs_ctx pq D Mk gs ++ im_params D Mk).
  assert (HΔa : tele_ass Δ)
    by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_params_ass; eassumption ]).
  assert (HΔs : ctx_scoped 0 Δ) by (exact (cargs_ctx_closed pq D k Mk c gs gs nil Hc Hk Hin (eq_sym (List.app_nil_r gs)))).
  assert (HΔm : ctx_mvc Δ)
    by (unfold ctx_mvc, Δ; apply List.Forall_app; split; [ eapply cargs_ctx_mvc; eassumption | exact (decl_params_mvc _ _ _ HD _ _ Hk) ]).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΔ & _ & _); fold Δ in HΔ.
  destruct (con_cod_typed _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j Hj]; fold Δ in Hj.
  destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j0 Hj0].
  assert (HC : Θ ⍮ Ξ ⍮ Δ ⊢ a_con pq k c : con_ty pq D k Mk gs) by (eapply wf_con_of_lookup; eassumption).
  unfold con_ty in HC; rewrite <- ctx_pi_app in HC; fold Δ in HC.
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ Hj) as (_ & HsB & _).
  pose proof (vars_closed_typed _ _ _ HΔa HΔs HΔm HΔ) as Hvars.
  pose proof (wf_apps_closed_pi _ _ _ _ j _ _ _ HΔa HΔs HsB Hj HΔ HC ltac:(apply length_vars_from) Hvars) as HT0.
  rewrite exp_at_vars, (exp_wk_id_ext _ _ wk_shiftn_zero) in HT0 by
    first [ exact HsB | apply ind_mty_vars_mvc; [ exact Hc | exact (dt_mvc _ _ _ HD) | apply vars_from_mvc ] ].
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ HT0) as (_ & HsT & HsB').
  pose proof (wf_exp_closed_app _ _ _ Ψ _ _ HΔa HΔs HsT HsB' HT0 HΨ) as HT1.
  assert (HlΔ : List.length Δ = im_np D Mk + List.length gs)
    by (unfold Δ; rewrite List.length_app, length_cargs_ctx, length_im_params; lia).
  assert (Hσ : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list Id (Ps ++ As) ≈ sb_of_list Id (Ps' ++ As') : Δ ++ Ψ).
  { eapply wf_sub_eq_of_list_conv; [ exact HΔa | apply wf_ctx_closed_app; assumption | apply wf_sub_eq_refl, wf_sub_id, HΨ
                                   | rewrite List.length_app, HlΔ; lia | rewrite List.length_app, HlΔ; lia | | | ].
    - apply list_typed_app; [ eapply decl_closed_params_ass; eassumption | rewrite length_im_params; exact HPl | exact HPs | exact HAs ].
    - apply list_typed_app; [ eapply decl_closed_params_ass; eassumption | rewrite length_im_params; exact HPl' | exact HPs' | exact HAs' ].
    - apply list_eq_app; [ eapply decl_closed_params_ass; eassumption | rewrite length_im_params; exact HPl
                         | rewrite length_im_params; exact HPl' | exact HPP | exact HAA ]. }
  pose proof (sub_eq_preserves_exp _ _ _ _ _ HT1 _ _ _ Hσ) as H.
  rewrite con_cod_inst in H by assumption.
  assert (E : forall L, List.length L = im_np D Mk + List.length gs ->
             (apps (a_con pq k c) (vars_from 0 (List.length Δ)))[sb_of_list Id L] = apps (a_con pq k c) L)
    by (intros L HL; rewrite HlΔ, <- HL; apply apps_vars_sb_of_list; exact I).
  rewrite (E (Ps ++ As)), (E (Ps' ++ As')) in H by (rewrite List.length_app; lia); exact H.
Qed.

(** ** A View's Instance *)

(** The instance of terms over the uniform parameters, moved. *)
Lemma inst_sub_comm : forall (Is Us : list exp) n τ, List.Forall (exp_scoped n) Is -> List.length Us = n ->
    List.map (fun I => I[sb_of_list Id (List.map (fun U => U[τ]) Us)]) Is = List.map (fun I => I[sb_of_list Id Us][τ]) Is.
Proof.
  intros * Hs Hl; apply List.map_ext_in; intros I HI.
  rewrite exp_sub_sub; symmetry; eapply exp_scoped_sub_agree; [ exact (proj1 (List.Forall_forall _ _) Hs I HI) |].
  intros x Hx; cbn [sb_compose]; apply sb_of_list_lt_compose; lia.
Qed.

(** A view's uniform arguments at the uniform parameters [Us]: of the
    container's uniform parameters' types at them. *)
Lemma view_is_typed : forall Θ Ξ Ψ p D m Mm qc k' Is vm D' Us,
    ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ p = Some D ->
    decl_typed Θ Ξ D -> decl_closed D' -> ind_member D m = Some Mm -> im_head Mm = mh_view qc k' Is vm ->
    ind_lookup Θ Ξ qc = Some D' -> ⊢ Θ ⍮ Ξ ⍮ Ψ -> List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ U : T) ->
    forall k I T, nth_error (List.map (fun I => I[sb_of_list Id Us]) Is) k = Some I ->
      nth_error (tele_insts (ind_uparams D') Id (List.map (fun I => I[sb_of_list Id Us]) Is)) k = Some T ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ I : T.
Proof.
  intros * Hg Hl HD Hc' Hm Hh Hl' HΨ HUl HUs k I' T' HI HT.
  pose proof (wf_uparams_sub _ _ _ _ _ HD HΨ HUl HUs) as Hσ.
  rewrite <- (tele_insts_sub (ind_uparams D') 0 Id Id (sb_of_list Id Us) Is (dc_ass _ Hc') (dc_uparams _ Hc')
                ltac:(intros; lia)) in HT.
  apply nth_error_map_inv in HI as (I & HI & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
  exact (sub_preserves_exp _ _ _ _ _ _ _ (dt_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' HI HT0) Hσ).
Qed.

(** The uniform parameters moved along a weakening. *)
Lemma uparams_wk_typed : forall Θ Ξ Γ Ψ D Us φ,
    decl_closed D -> Θ ⍮ Ξ ⍮ Ψ ⊢ʷ φ : Γ ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    forall k U T, nth_error (List.map (fun U => U[φ]ʷ) Us) k = Some U ->
      nth_error (tele_insts (ind_uparams D) Id (List.map (fun U => U[φ]ʷ) Us)) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ U : T.
Proof.
  intros * Hc Hφ HUs k U' T' HU HT.
  rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
  apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
  exact (wk_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hφ).
Qed.

(** The non-uniform parameters as variables, in the motive's context. *)
Lemma mctx_vars_typed : forall Θ Ξ Γ D k M Us,
    decl_typed Θ Ξ D -> decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ tele_sub (im_nparams M) (sb_of_list Id Us) ++ Γ ->
    forall j N T, nth_error (vars_from 0 (im_nn M)) j = Some N ->
      nth_error (tele_insts (im_nparams M) (sb_of_list Id (List.map (fun U => U[wk_shiftn (im_nn M)]ʷ) Us))
                   (vars_from 0 (im_nn M))) j = Some T ->
      Θ ⍮ Ξ ⍮ tele_sub (im_nparams M) (sb_of_list Id Us) ++ Γ ⊢ N : T.
Proof.
  intros * HD Hc Hk HUl HΨ j N T HN HT.
  change (vars_from 0 (im_nn M)) with (vars_from (List.length (@nil centry)) (List.length (im_nparams M))) in HN, HT.
  change (tele_sub (im_nparams M) (sb_of_list Id Us) ++ Γ) with (nil ++ tele_sub (im_nparams M) (sb_of_list Id Us) ++ Γ).
  eapply (wf_vars_tele_gen _ _ nil _ _ _ Γ (ind_nu D));
    [ eapply decl_closed_nparams_ass; eassumption | exact (decl_nparams_mvc _ _ _ HD _ _ Hk)
    | eapply decl_closed_nparams_scoped; eassumption | exact HΨ | | exact HN | exact HT ].
  intros y Hy; rewrite sb_of_list_map by lia; reflexivity.
Qed.

(** ** The Motives' Contexts at a View

    The motive's context of the group's member [v] the view lists for the
    container's member [i'] is the container's at the view's instance. *)
Lemma view_mctx_ext : forall Θ Ξ Γ p D m Mm qc k' Is vm D' i' Mi' v Mv Us,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm -> ind_lookup Θ Ξ qc = Some D' ->
    ind_member D' i' = Some Mi' -> nth_error vm i' = Some v -> ind_member D v = Some Mv -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D v Mv Us ≈ elim_mctx qc D' i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is).
Proof.
  intros * Hg HDs Hl Hm Hh Hl' Hi' Hv Hmv HΓ HUl HUs.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (HDs _ _ Hl') as HD'; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
  destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D0 & Mk0 & Hl0 & _ & _ & HIl & _).
  rewrite Hl' in Hl0; injection Hl0 as <-.
  set (Is' := List.map (fun I => I[sb_of_list Id Us]) Is).
  assert (HIl' : List.length Is' = ind_nu D') by (unfold Is'; rewrite List.length_map; exact HIl).
  pose proof (view_is_typed _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HD Hc' Hm Hh Hl' HΓ HUl HUs) as HIs'; fold Is' in HIs'.
  pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
  pose proof (dt_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hv Hmv) as HNeq.
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as Htail.
  rewrite (nparams_sub D' i' Mi' Is (sb_of_list Id Us) Hc' Hi' HIl) in Htail; fold Is' in Htail.
  assert (Hnn : im_nn Mv = im_nn Mi')
    by (pose proof (ext_eq_length _ _ _ _ _ Htail) as E; rewrite !length_tele_sub in E; exact E).
  pose proof (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hmv HΓ HUl HUs) as HMv.
  pose proof (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl' Hi' HΓ HIl' HIs') as HMc.
  destruct (elim_mctx_head_typed _ _ _ _ _ _ _ _ HMv) as [j1 Hj1].
  destruct (elim_mctx_head_typed _ _ _ _ _ _ _ _ HMc) as [j2 Hj2].
  assert (Heq : exists j3, Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mv) (sb_of_list Id Us) ++ Γ
                  ⊢ ind_mty p D v (List.map (fun U => U[wk_shiftn (im_nn Mv)]ʷ) Us) (vars_from 0 (im_nn Mv))
                  ≈ ind_mty qc D' i' (List.map (fun U => U[wk_shiftn (im_nn Mi')]ʷ) Is') (vars_from 0 (im_nn Mi'))
                  : Typeω@j3).
  { rewrite <- Hnn.
    pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ Hm Hh) as HsIs.
    assert (EIs : List.map (fun I => I[sb_of_list Id (List.map (fun U => U[wk_shiftn (im_nn Mv)]ʷ) Us)]) Is
                  = List.map (fun U => U[wk_shiftn (im_nn Mv)]ʷ) Is').
    { rewrite <- map_sub_of_wk, (inst_sub_comm Is Us (ind_nu D)) by assumption.
      unfold Is'; rewrite List.map_map; apply List.map_ext; intros; apply exp_sub_of_wk. }
    unfold ind_mty in Hj1 |- *; rewrite Hmv, Hi' in *; unfold im_ty_at, im_ref, im_pre in Hj1 |- *.
    destruct (im_head Mi') as [pm | q'' k'' Is'' vm''] eqn:Hhi.
    - (* the container's member is declared: the view's is the same instance *)
      destruct (dt_view_decl _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hhi Hv) as (Mv0 & vm' & Hmv0 & Hhv).
      rewrite Hmv in Hmv0; injection Hmv0 as <-; rewrite Hhv in Hj1 |- *; cbn [fst snd] in Hj1 |- *.
      rewrite EIs in Hj1 |- *; exists j1; apply wf_exp_eq_refl; exact Hj1.
    - (* the container's member is a view: the view's instance is equal to its *)
      destruct (dt_view_view _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hhi Hv) as (Mv0 & X & vm' & Hmv0 & Hhv & HXl).
      rewrite Hmv in Hmv0; injection Hmv0 as <-; rewrite Hhv in Hj1 |- *; cbn [fst snd] in Hj1 |- *.
      destruct (dt_view _ _ _ HD' _ _ _ _ _ _ Hi' Hhi) as (D'' & Mk'' & Hl'' & Hk'' & Hlt'' & HIl'' & _ & Hself'' & _).
      destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hmv Hhv) as (D3 & Mk3 & Hl3 & Hk3 & _ & HXl3 & _ & Hself3 & _).
      rewrite Hl'' in Hl3; injection Hl3 as <-; rewrite Hk'' in Hk3; injection Hk3 as <-.
      pose proof (HDs _ _ Hl'') as HD''; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl'') as Hc''.
      set (nn := im_nn Mv) in *.
      set (wkUs := List.map (fun U => U[wk_shiftn nn]ʷ) Us) in *.
      set (wkIs := List.map (fun U => U[wk_shiftn nn]ʷ) Is') in *.
      set (Ψv := tele_sub (im_nparams Mv) (sb_of_list Id Us) ++ Γ) in *.
      set (Ψc := tele_sub (im_nparams Mi') (sb_of_list Id Is') ++ Γ) in *.
      assert (HΨv : ⊢ Θ ⍮ Ξ ⍮ Ψv) by (unfold elim_mctx in HMv; cbn [List.app] in HMv; destruct (ctx_decomp HMv) as [H0 _]; exact H0).
      assert (HΨc : ⊢ Θ ⍮ Ξ ⍮ Ψc) by (unfold elim_mctx in HMc; cbn [List.app] in HMc; destruct (ctx_decomp HMc) as [H0 _]; exact H0).
      assert (Hwv : Θ ⍮ Ξ ⍮ Ψv ⊢ʷ wk_shiftn nn : Γ)
        by (unfold Ψv, nn; rewrite <- (length_nparams_sub Mv (sb_of_list Id Us)); apply wf_wk_shiftn_app'; exact HΨv).
      assert (Hwc : Θ ⍮ Ξ ⍮ Ψc ⊢ʷ wk_shiftn nn : Γ)
        by (rewrite Hnn; unfold Ψc; rewrite <- (length_nparams_sub Mi' (sb_of_list Id Is')); apply wf_wk_shiftn_app'; exact HΨc).
      pose proof (ctxsub_ext_rev _ _ _ _ _ Htail (tele_ass_sub _ _ (dt_nparams_ass _ _ _ HD _ _ Hmv))) as HId.
      fold Ψv Ψc in HId.
      (* the two lists, each typed at its own instances *)
      destruct (view_params_typed _ _ Ψv _ _ _ _ _ _ _ _ _ _ wkUs (vars_from 0 nn) Hg Hl HDs HD Hc Hc'' Hmv Hhv Hl'' Hk'' Hself3 HXl3 HΨv
                  ltac:(unfold wkUs; rewrite List.length_map; exact HUl)
                  (uparams_wk_typed _ _ _ _ _ _ _ Hc Hwv HUs) ltac:(apply length_vars_from)
                  (mctx_vars_typed _ _ _ _ _ _ _ HD Hc Hmv HUl HΨv)) as [HnnV HLv].
      destruct (view_params_typed _ _ Ψc _ _ _ _ _ _ _ _ _ _ wkIs (vars_from 0 nn) Hg Hl' HDs HD' Hc' Hc'' Hi' Hhi Hl'' Hk'' Hself'' HIl'' HΨc
                  ltac:(unfold wkIs; rewrite List.length_map; exact HIl')
                  (uparams_wk_typed _ _ _ _ _ _ _ Hc' Hwc HIs') ltac:(rewrite Hnn; apply length_vars_from)
                  ltac:(unfold wkIs; rewrite Hnn; exact (mctx_vars_typed _ _ _ _ _ _ _ HD' Hc' Hi' HIl' HΨc))) as [_ HLc].
      assert (HLc' : forall j N T, nth_error (List.map (fun I => I[sb_of_list Id wkIs]) Is'' ++ vars_from 0 nn) j = Some N ->
                 nth_error (tele_insts (im_params D'' Mk'') Id (List.map (fun I => I[sb_of_list Id wkIs]) Is'' ++ vars_from 0 nn)) j
                   = Some T -> Θ ⍮ Ξ ⍮ Ψv ⊢ N : T).
      { intros j N T HN HT; pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HLc _ _ _ HN HT) HId) as H; rewrite !exp_sub_id in H; exact H. }
      (* the uniform arguments, equal by the view equation *)
      pose proof (wf_uparams_sub _ _ _ _ _ HD HΨv ltac:(unfold wkUs; rewrite List.length_map; exact HUl)
                    (uparams_wk_typed _ _ _ _ _ _ _ Hc Hwv HUs)) as Hσw.
      pose proof (decl_closed_head_scoped _ Hc' _ _ _ _ _ _ Hi' Hhi) as HsIs''.
      assert (EIs'' : List.map (fun I => I[sb_of_list Id Is][sb_of_list Id wkUs]) Is''
                      = List.map (fun I => I[sb_of_list Id wkIs]) Is'').
      { apply List.map_ext_in; intros I HI; rewrite exp_sub_sub.
        eapply exp_scoped_sub_agree; [ exact (proj1 (List.Forall_forall _ _) HsIs'' I HI) |].
        intros y Hy; cbn [sb_compose]; rewrite sb_of_list_lt_compose by lia.
        rewrite EIs; reflexivity. }
      assert (HLL : forall j N N' T,
                 nth_error (List.map (fun I => I[sb_of_list Id wkIs]) Is'' ++ vars_from 0 nn) j = Some N ->
                 nth_error (List.map (fun I => I[sb_of_list Id wkUs]) X ++ vars_from 0 nn) j = Some N' ->
                 nth_error (tele_insts (im_params D'' Mk'') Id (List.map (fun I => I[sb_of_list Id wkIs]) Is'' ++ vars_from 0 nn)) j
                   = Some T -> Θ ⍮ Ξ ⍮ Ψv ⊢ N ≈ N' : T).
      { intros j N N' T HN HN' HT.
        assert (HlIs : List.length (List.map (fun I => I[sb_of_list Id wkIs]) Is'') = ind_nu D'')
          by (rewrite List.length_map; exact HIl'').
        assert (HlX : List.length (List.map (fun I => I[sb_of_list Id wkUs]) X) = ind_nu D'')
          by (rewrite List.length_map, HXl; exact HIl'').
        destruct (Nat.lt_ge_cases j (ind_nu D'')) as [Hj | Hj].
        - rewrite List.nth_error_app1 in HN, HN' by lia.
          unfold im_params in HT; rewrite tele_insts_app in HT by (try exact (dc_ass _ Hc''); exact HlIs).
          rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (dc_ass _ Hc''); rewrite HlIs; unfold ind_nu in *; lia).
          apply nth_error_map_inv in HN' as (C & HC & ->).
          rewrite <- EIs'' in HN, HT.
          rewrite <- (List.map_map (fun I => I[sb_of_list Id Is]) (fun M => M[sb_of_list Id wkUs])) in HN, HT.
          rewrite <- (tele_insts_sub (ind_uparams D'') 0 Id Id (sb_of_list Id wkUs) _ (dc_ass _ Hc'') (dc_uparams _ Hc'')
                        ltac:(intros; lia)) in HT.
          rewrite <- (tele_insts_sub (ind_uparams D'') 0 Id Id (sb_of_list Id Is) _ (dc_ass _ Hc'') (dc_uparams _ Hc'')
                        ltac:(intros; lia)) in HT.
          apply nth_error_map_inv in HN as (C1 & HC1 & ->); apply nth_error_map_inv in HC1 as (C0 & HC0 & ->).
          apply nth_error_map_inv in HT as (T1 & HT1 & ->); apply nth_error_map_inv in HT1 as (T0 & HT0 & ->).
          assert (HC1' : nth_error (List.map (fun I => I[sb_of_list Id Is]) Is'') j = Some C0[sb_of_list Id Is])
            by (rewrite List.nth_error_map, HC0; reflexivity).
          pose proof (dt_view_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        Hm Hh Hl' Hi' Hhi Hl'' Hv Hmv Hhv HC HC1' HT0) as HE.
          apply wf_exp_eq_sym; exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HE Hσw).
        - rewrite List.nth_error_app2 in HN, HN' by lia; rewrite HlIs in HN; rewrite HlX in HN'.
          rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl.
          apply (HLc' j); [ rewrite List.nth_error_app2 by lia; rewrite HlIs; exact HN | exact HT ]. }
      assert (HlLc : List.length (List.map (fun I => I[sb_of_list Id wkIs]) Is'' ++ vars_from 0 nn) = im_np D'' Mk'')
        by (rewrite List.length_app, List.length_map, HnnV, HIl''; unfold im_np; lia).
      assert (HlLv : List.length (List.map (fun I => I[sb_of_list Id wkUs]) X ++ vars_from 0 nn) = im_np D'' Mk'')
        by (rewrite List.length_app, List.length_map, HnnV, HXl3; unfold im_np; lia).
      destruct (ind_apps_conv_large _ _ _ _ _ _ _ _ _ Hg HDs Hl'' Hk'' Hlt'' HΨv HlLc HlLv HLc' HLv HLL) as (j3 & _ & _ & Hj3).
      exists j3; apply wf_exp_eq_sym; exact Hj3. }
  destruct Heq as [j3 Hj3].
  unfold elim_mctx; eapply wf_ext_eq_ass with (i := max j1 (max j2 j3)); [ exact Htail | | |].
  - eapply lift_exp_ge; [| exact Hj1 ]; lia.
  - eapply lift_exp_eq_ge; [| exact Hj3 ]; lia.
  - eapply lift_exp_ge; [| exact Hj2 ]; lia.
Qed.

(** ** Equal Telescopes *)

(** The same as [wf_sub_eq_of_list_conv], the second list typed at the
    instances at the first. *)
Lemma wf_sub_eq_of_list_left : forall Θ Ξ Δ Ψ Γ0 σ σ' Ms Ms',
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ0 -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : Γ0 ->
    List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall k N T, List.nth_error Ms' k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) ->
    (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
       List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list σ Ms ≈ sb_of_list σ' Ms' : Δ ++ Γ0.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ Hl Hl' HMs HMs' HMM.
  - destruct Ms; [| discriminate ]; destruct Ms'; [| discriminate ]; exact Hσ.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in Hl, Hl'; cbn in Hl, Hl'.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; destruct Ms' as [| M0' Ms']; [ cbn in Hl'; lia |]; cbn in Hl, Hl'.
    rewrite <- List.app_assoc in HΔ |- *; cbn [List.app] in HΔ |- *.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [k HA0]].
    assert (HM0 : Θ ⍮ Ξ ⍮ Ψ ⊢ M0 : A0[σ]) by (apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (HM0' : Θ ⍮ Ξ ⍮ Ψ ⊢ M0' : A0[σ]) by (apply (HMs' 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (HMM0 : Θ ⍮ Ξ ⍮ Ψ ⊢ M0 ≈ M0' : A0[σ])
      by (apply (HMM 0); [ reflexivity | reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (HAA : Θ ⍮ Ξ ⍮ Ψ ⊢ A0[σ] ≈ A0[σ'] : Typeω@k) by exact (sub_eq_preserves_exp _ _ _ _ _ HA0 _ _ _ Hσ).
    assert (HA0' : Θ ⍮ Ξ ⍮ Ψ ⊢ A0[σ'] : Typeω@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA0 (wf_sub_eq_right _ _ _ _ _ _ Hσ)).
    cbn [sb_of_list]; eapply IH; [ exact Hass | exact HΔ | | lia | lia | | |].
    + eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | exact HM0 | eapply wf_conv; [ exact HM0' | exact HA0' | exact HAA ]
                               | exact HMM0 ].
    + intros k' N T HN HT; apply (HMs (S k')); [ exact HN | rewrite tele_insts_snoc; exact HT ].
    + intros k' N T HN HT; apply (HMs' (S k')); [ exact HN | rewrite tele_insts_snoc; exact HT ].
    + intros k' N N' T HN HN' HT; apply (HMM (S k')); [ exact HN | exact HN' | rewrite tele_insts_snoc; exact HT ].
Qed.

(** Equal telescopes of assumptions, the other way round. *)
Lemma ext_eq_sym_ass : forall Θ Ξ Γ Ψ Ψ', tele_ass Ψ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ' ≈ Ψ.
Proof.
  intros * Hass H; induction H as [| ? ? ? ? ? ? ? ? HΨ IH HA HAA HA' | | | ].
  - constructor; assumption.
  - inversion_clear Hass as [| ? ? _ Hass'].
    pose proof (ctxsub_ext _ _ _ _ _ HΨ Hass') as HId.
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA HId) as HAA'; rewrite !exp_sub_id in HAA'.
    eapply wf_ext_eq_ass; [ exact (IH Hass') | exact HA' | apply wf_exp_eq_sym; exact HAA' | exact HA ].
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
Qed.

(** Equal telescopes of assumptions over equal ones, joined. *)
Lemma ext_eq_app : forall Θ Ξ Γ N N' A A',
    tele_ass N -> tele_ass A -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ N ≈ N' -> Θ ⍮ Ξ ⍮ N ++ Γ ⊢ˣ A ≈ A' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ A ++ N ≈ A' ++ N'.
Proof.
  intros * HaN HaA HN HA; remember (N ++ Γ) as Γ1 eqn:EΓ1.
  revert HaA; induction HA as [| ? ? ? ? ? ? ? ? HΨ IH HB HBB HB' | | | ]; intros HaA; subst.
  - exact HN.
  - inversion_clear HaA as [| ? ? _ HaA'].
    specialize (IH HN eq_refl HaA').
    cbn [List.app]; eapply wf_ext_eq_ass; [ exact IH | rewrite <- List.app_assoc; exact HB | rewrite <- List.app_assoc; exact HBB |].
    pose proof (ctxsub_ext _ _ _ _ _ IH (proj2 (List.Forall_app _ _ _) (conj HaA' HaN) : tele_ass (Ψ ++ N))) as Hs1.
    pose proof (ctxsub_ext_rev _ _ _ _ _ HΨ HaA') as Hs2.
    rewrite <- !List.app_assoc in Hs1.
    pose proof (wf_sub_compose _ _ _ _ _ _ _ Hs2 Hs1) as Hs; rewrite sb_compose_id_left in Hs.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB' Hs) as H; rewrite !exp_sub_id in H; cbn in H.
    rewrite <- List.app_assoc; exact H.
  - inversion_clear HaA as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear HaA as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear HaA as [| ? ? [? Heq] _]; discriminate.
Qed.

(** The outer part of equal telescopes of the same length split alike. *)
Lemma ext_eq_app_inv : forall Θ Ξ Γ A A' N N',
    List.length A = List.length A' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ A ++ N ≈ A' ++ N' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ N ≈ N'.
Proof.
  induction A as [| e A IH]; intros [| e' A'] * Hl H; cbn in Hl; try discriminate; [ exact H |].
  injection Hl as Hl; cbn [List.app] in H; apply ext_eq_cons_inv in H; exact (IH _ _ _ Hl H).
Qed.

(** ** Shapes, Domain by Domain *)

Lemma sb_q_exp_agree_lt : forall σ σ' n,
    (forall y, y < n -> sentry_exp (σ y) = sentry_exp (σ' y)) ->
    forall y, y < S n -> sentry_exp ((q σ) y) = sentry_exp ((q σ') y).
Proof.
  intros * H [| y] Hy; [ rewrite !sb_q_zero; reflexivity |].
  rewrite !sb_q_succ, <- !sentry_exp_wk, H by lia; reflexivity.
Qed.

(** The type of a recursive result depends on the shape's components'
    substitution only through the terms it sends their variables to. *)
Lemma ptyp_ihty_scoped_agree : forall t As β σ σ' x n,
    ptyp_scoped n t -> List.Forall (exp_mvc 0) (ptyp_doms t) -> List.Forall (exp_mvc 0) (ptyp_ps t) ->
    (forall y, y < n -> sentry_exp (σ y) = sentry_exp (σ' y)) ->
    ptyp_ihty As β σ x t = ptyp_ihty As β σ' x t.
Proof.
  induction t as [j Ps | B t IH]; intros * Hs HmB HmP Hσ; cbn in *.
  - do 2 f_equal; f_equal; apply List.map_ext_in; intros P HP.
    eapply exp_scoped_mvc_agree;
      [ exact (proj1 (List.Forall_forall _ _) Hs P HP) | exact (proj1 (List.Forall_forall _ _) HmP P HP) | exact Hσ ].
  - destruct Hs as [HB Ht]; inversion_clear HmB as [| ? ? HmB1 HmB2].
    f_equal; [ eapply exp_scoped_mvc_agree; eassumption |].
    eapply IH; [ exact Ht | exact HmB2 | exact HmP | apply sb_q_exp_agree_lt; exact Hσ ].
Qed.

Lemma ptyp_skip_depth : forall t, ptyp_skip (ptyp_depth t) t = pt_self (ptyp_mem t) (ptyp_ps t).
Proof. induction t as [j Ps | B t IH]; cbn; [ reflexivity | exact IH ]. Qed.

Lemma ptyp_skip_lt : forall t d, d < ptyp_depth t ->
    ptyp_skip d t = pt_pi (List.nth d (ptyp_doms t) a_True) (ptyp_skip (S d) t).
Proof.
  induction t as [j Ps | B t IH]; intros d Hd; unfold ptyp_depth in Hd; cbn in Hd; [ lia |].
  destruct d as [| d]; cbn; [ reflexivity | apply IH; unfold ptyp_depth; lia ].
Qed.

Lemma sh_ctx_firstn_S : forall pat t d, d < ptyp_depth t ->
    sh_ctx pat (List.firstn (S d) (ptyp_doms t)) = ce_ass (ptyp_dom_at pat d t) :: sh_ctx pat (List.firstn d (ptyp_doms t)).
Proof.
  intros * Hd.
  destruct (nth_error_lt_some (ptyp_doms t) d Hd) as [B HB].
  destruct (doms_split_nth _ _ _ HB) as [_ Hf]; rewrite Hf, sh_ctx_snoc.
  unfold ptyp_dom_at; rewrite (List.nth_error_nth _ _ _ HB), List.length_firstn, Nat.min_l by (unfold ptyp_depth in Hd; lia).
  reflexivity.
Qed.

Lemma repeat_false_S : forall d (pat : list bool), List.repeat false (S d) ++ pat = false :: (List.repeat false d ++ pat).
Proof. reflexivity. Qed.

(** The recursive results' telescope, split after some arguments. *)
Lemma ihs_ctx_aux_app : forall nn As Us na gs1 gs2 pat j,
    ihs_ctx_aux nn As Us na pat j (gs1 ++ gs2)
    = ihs_ctx_aux nn As Us na (cargs_pat gs1 ++ pat) (j + cargs_nrec gs1) gs2 ++ ihs_ctx_aux nn As Us na pat j gs1.
Proof.
  induction gs1 as [| [A | t] gs1 IH]; intros; cbn [List.app ihs_ctx_aux cargs_nrec].
  - rewrite List.app_nil_r, Nat.add_0_r; reflexivity.
  - rewrite IH, cargs_pat_cons; cbn; rewrite <- List.app_assoc; reflexivity.
  - rewrite IH, cargs_pat_cons, <- List.app_assoc; cbn [List.app].
    replace (S j + cargs_nrec gs1) with (j + S (cargs_nrec gs1)) by lia; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma q_wk_compose : forall φ Sb, sb_eq (q (ι φ ⨟ Sb)) (ι (wk_q φ) ⨟ q Sb).
Proof. intros φ Sb [| z]; cbn; reflexivity. Qed.

Lemma q_compose_eq : forall σ τ, sb_eq (q (σ ⨟ τ)) (q σ ⨟ q τ).
Proof. intros; symmetry; apply sb_q_compose_ext; reflexivity. Qed.

Lemma sb_compose_cong_r : forall σ τ τ', sb_eq τ τ' -> sb_eq (σ ⨟ τ) (σ ⨟ τ').
Proof. intros * H x; cbn [sb_compose]; apply sentry_sub_sb_eq, H. Qed.

Lemma sb_compose_cong_l : forall σ σ' τ, sb_eq σ σ' -> sb_eq (σ ⨟ τ) (σ' ⨟ τ).
Proof. intros * H x; cbn [sb_compose]; rewrite H; reflexivity. Qed.

Lemma shape_sub_step : forall d (pat : list bool) Sb,
    sb_eq (q (ι (wk_pat (List.repeat false d ++ pat)) ⨟ Sb)) (ι (wk_pat (List.repeat false (S d) ++ pat)) ⨟ q Sb).
Proof. intros; apply q_wk_compose. Qed.

Lemma shape_sub_step' : forall d a (pat : list bool) τ Sb,
    sb_eq (q (ι (wk_pat (List.repeat false d ++ pat)) ⨟ (sb_qn (d + a) τ ⨟ Sb)))
          (ι (wk_pat (List.repeat false (S d) ++ pat)) ⨟ (sb_qn (S d + a) τ ⨟ q Sb)).
Proof. intros; etransitivity; [ apply q_wk_compose |]; apply sb_compose_cong_r, q_compose_eq. Qed.

(** The instances of a motive's context at a substitution into it. *)
Lemma elim_mctx_insts : forall pq D k M Us β Ns x,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D -> List.length Ns = im_nn M ->
    tele_insts (elim_mctx pq D k M Us) β (Ns ++ x :: nil)
    = tele_insts (im_nparams M) (sb_of_list Id Us ⨟ β) Ns ++ ind_mty pq D k (List.map (fun U => U[β]) Us) Ns :: nil.
Proof.
  intros * Hc Hk HUl HNl; unfold elim_mctx; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R).
  rewrite tele_insts_app by (try (apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption); rewrite length_tele_sub; exact HNl).
  rewrite tele_insts_tele_sub; f_equal.
  unfold tele_insts; cbn; f_equal; apply ind_head_inst; assumption.
Qed.

(** The shape's facts after some domains. *)
Lemma shape_doms_typed_skip : forall Θ Ξ D Mk Tb t d,
    shape_doms_typed Θ Ξ D Mk nil Tb t -> shape_doms_typed Θ Ξ D Mk (List.firstn d (ptyp_doms t)) Tb (ptyp_skip d t).
Proof.
  intros * H Bs1' B Bs2 E; rewrite ptyp_doms_skip in E.
  apply (H (List.firstn d (ptyp_doms t) ++ Bs1') B Bs2).
  rewrite <- List.app_assoc, <- E, List.firstn_skipn; reflexivity.
Qed.

Lemma shape_leaf_typed_skip : forall Θ Ξ D Mk Mj Tb t d, d <= ptyp_depth t ->
    shape_leaf_typed Θ Ξ D Mk Mj nil Tb t -> shape_leaf_typed Θ Ξ D Mk Mj (List.firstn d (ptyp_doms t)) Tb (ptyp_skip d t).
Proof.
  intros * Hd H k P T HP HT; rewrite ptyp_ps_skip in HP, HT.
  rewrite ptyp_doms_skip, List.firstn_skipn.
  apply (H k P T HP).
  unfold ptyp_depth in *; rewrite ptyp_doms_skip, List.length_skipn, List.length_firstn in HT.
  cbn [List.length List.app]; replace (Nat.min d (List.length (ptyp_doms t)) + (List.length (ptyp_doms t) - d)) with
    (List.length (ptyp_doms t)) in HT by lia; exact HT.
Qed.

(** ** The Recursive Result of a View's Argument, as the Container's

    An argument recursive in the view and in the container: the type of
    its recursive result, the view's, is the container's at the view's
    instance, the shapes' domains and the leaves' parameters equal by the
    view equations.  [S] instantiates the view's arguments' closed context
    [Ω d]; the view's shape's components are moved through the pattern of
    the arguments before, the container's also through the instance. *)

Section IhtyConv.
  Context (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (v : nat) (Mv : imember)
    (c : String.string) (gs gs1 gs2 : list carg) (tfull : ptyp) (Mj : imember) (Us As As' Is : list exp) (i : nat)
    (gs1' : list carg) (t'full : ptyp).
  Hypothesis (Hg : ⊢ᵍ Θ ⍮ Ξ) (HDs : decls_typed Θ Ξ) (Hl : ind_lookup Θ Ξ p = Some D) (Hmv : ind_member D v = Some Mv)
    (Hin : List.In (c, gs) (im_cons Mv)) (Heq : gs = gs1 ++ ca_rec tfull :: gs2)
    (HMj : ind_member D (ptyp_mem tfull) = Some Mj)
    (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T)
    (HAs : motives_typed Θ Ξ Γ p D Us As i)
    (Hdep : ptyp_depth t'full = ptyp_depth tfull)
    (Hpsl : List.length (ptyp_ps t'full) = List.length (ptyp_ps tfull))
    (Hmem : List.nth (ptyp_mem t'full) As' a_True = List.nth (ptyp_mem tfull) As a_True)
    (Hlen1 : List.length gs1' = List.length gs1)
    (Hdoms : forall d, d < ptyp_depth tfull -> exists i0,
       Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms tfull)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv
         ⊢ (ptyp_dom_at (cargs_pat gs1') d t'full)[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id Is)]
         ≈ ptyp_dom_at (cargs_pat gs1) d tfull : Typeω@i0)
    (Hps : forall j P' P T,
       nth_error (ptyp_ps_at (cargs_pat gs1') t'full) j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) tfull) j = Some P ->
       nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth tfull + List.length gs1)))
                    (ptyp_ps_at (cargs_pat gs1) tfull)) j = Some T ->
       Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (ptyp_doms tfull) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv
         ⊢ P'[sb_qn (ptyp_depth tfull + List.length gs1 + im_nn Mv) (sb_of_list Id Is)] : T /\
       Θ ⍮ Ξ ⍮ sh_ctx (cargs_pat gs1) (ptyp_doms tfull) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv
         ⊢ P'[sb_qn (ptyp_depth tfull + List.length gs1 + im_nn Mv) (sb_of_list Id Is)] ≈ P : T).

  Let nn := im_nn Mv.
  Let pat := cargs_pat gs1.
  Let pat' := cargs_pat gs1'.
  Let Ω (d : nat) : ctx := sh_ctx pat (List.firstn d (ptyp_doms tfull)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv.

  Lemma ihty_conv : forall n d, n + d = ptyp_depth tfull -> forall Ψ β Sb x,
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ Sb : Ω d ->
      (forall y, y < ind_nu D -> sentry_exp (Sb (y + d + List.length gs1 + nn)) = (sentry_exp (sb_of_list Id Us y))[β]) ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => U[β]) Us) (ι (wk_pat (List.repeat false d ++ pat)) ⨟ Sb)
                         (ptyp_skip d tfull) ->
      exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty As β (ι (wk_pat (List.repeat false d ++ pat)) ⨟ Sb) x (ptyp_skip d tfull)
                  ≈ ptyp_ihty As' β (ι (wk_pat (List.repeat false d ++ pat')) ⨟ (sb_qn (d + List.length gs1 + nn) (sb_of_list Id Is) ⨟ Sb))
                      x (ptyp_skip d t'full) : Typeω@j.
  Proof.
    pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
    destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HD Hmv Hin Heq) as (Mj0 & HMj0 & HPl & HBt & HPt).
    rewrite HMj in HMj0; injection HMj0 as <-.
    pose proof (dmv_members _ (dt_mvc _ _ _ HD) _ _ HMj) as (HmvN & _).
    pose proof (decl_closed_nparams_ass _ Hc _ _ HMj) as HaN.
    pose proof (decl_closed_nparams_scoped _ Hc _ _ HMj) as HsN.
    intros n; induction n as [| n IH]; intros d Hnd Ψ β Sb x Hβ HSb HSuc Hx.
    - assert (Ed : d = ptyp_depth tfull) by lia; subst d.
      rewrite (ptyp_skip_depth tfull) in Hx |- *.
      replace (ptyp_skip (ptyp_depth tfull) t'full) with (pt_self (ptyp_mem t'full) (ptyp_ps t'full))
        by (rewrite <- Hdep; symmetry; apply ptyp_skip_depth).
      cbn [ptyp_ihty ptyp_ty_at] in Hx |- *.
      rewrite Hmem.
      set (σ := ι (wk_pat (List.repeat false (ptyp_depth tfull) ++ pat)) ⨟ Sb) in *.
      set (σ' := ι (wk_pat (List.repeat false (ptyp_depth tfull) ++ pat')) ⨟ (sb_qn (ptyp_depth tfull + List.length gs1 + nn) (sb_of_list Id Is) ⨟ Sb)).
      set (Tc := doms_ctx (ptyp_doms tfull) ++ cargs_strat gs1 ++ im_params D Mv).
      destruct (shape_prefix_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hmv Hin gs1 tfull gs2 Heq (ptyp_depth tfull) ltac:(unfold ptyp_depth; lia))
        as (HΩ & HStr & Hφ).
      rewrite List.firstn_all2 in HΩ, HStr, Hφ by (unfold ptyp_depth; lia).
      assert (HSb' : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ Sb : sh_ctx pat (ptyp_doms tfull) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv)
        by (unfold Ω in HSb; rewrite List.firstn_all2 in HSb by (unfold ptyp_depth; lia); exact HSb).
      assert (Hσ : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Tc) by (eapply wf_sub_compose; [ apply wf_sub_of_wk; exact Hφ | exact HSb' ]).
      assert (Huc : shape_uc D Us Tc σ β).
      {
        intros y Hy; unfold σ; cbn [sb_compose sb_of_wk sentry_sub].
        destruct (length_shape_ctx D Mv (ptyp_doms tfull) (cargs_strat gs1)) as [E1 _]; fold Tc in E1; rewrite E1.
        replace (y + (List.length (ptyp_doms tfull) + List.length (cargs_strat gs1) + im_nn Mv))
          with (pat_nargs (List.repeat false (ptyp_depth tfull) ++ pat) + (nn + y))
          by (rewrite pat_nargs_falses; unfold pat; rewrite pat_nargs_cargs_pat; unfold ptyp_depth, nn; lia).
        rewrite wk_pat_ge, List.length_app, List.repeat_length; unfold pat; rewrite length_cargs_pat.
        cbn [sb_compose]; rewrite <- sentry_exp_sub.
        replace (ptyp_depth tfull + List.length gs1 + (nn + y)) with (y + ptyp_depth tfull + List.length gs1 + nn) by lia.
        rewrite HSuc by exact Hy; reflexivity.
      }
      pose proof (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl HMj HΓ HUl HUs) as HM.
      destruct (length_shape_ctx D Mv (ptyp_doms tfull) (cargs_strat gs1)) as [ETc _]; fold Tc in ETc.
      assert (HPs0 : forall k P T, nth_error (ptyp_ps tfull) k = Some P ->
                 nth_error (tele_insts (im_nparams Mj) (ι (wk_shiftn (List.length Tc - ind_nu D))) (ptyp_ps tfull)) k = Some T ->
                 Θ ⍮ Ξ ⍮ Tc ⊢ P : T).
      {
        intros k P T HP HT; rewrite ETc in HT; apply (HPt k P T HP); cbn [List.length List.app]; unfold ptyp_depth; exact HT.
      }
      pose proof (ih_leaf_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc HMj HUl HM Hβ Hσ Huc HPl HPs0 Hx) as Hleaf.
      exists i; pose proof (HAs _ _ HMj) as HA.
      eapply (sub_eq_preserves_exp _ _ _ _ _ HA).
      set (L1 := List.map (fun P => P[σ]) (ptyp_ps tfull)).
      set (L2 := List.map (fun P => P[σ']) (ptyp_ps t'full)).
      assert (HL1 : List.length L1 = im_nn Mj) by (unfold L1; rewrite List.length_map; exact HPl).
      assert (HL2 : List.length L2 = im_nn Mj) by (unfold L2; rewrite List.length_map, Hpsl; exact HPl).
      assert (Hlen : List.length (L1 ++ x :: nil) = List.length (elim_mctx p D (ptyp_mem tfull) Mj Us))
        by (rewrite List.length_app, HL1, length_elim_mctx; cbn; lia).
      pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_mctx_ass _ _ _ _ _ Hc HMj) Hlen Hleaf) as HL1t.
      rewrite (elim_mctx_insts _ _ _ _ _ _ _ _ Hc HMj HUl HL1) in HL1t.
      assert (Hcond : forall y, y < ind_nu D ->
                 sentry_exp (sentry_sub (sb_of_list Id (ind_uvars D nn (ptyp_depth tfull + List.length gs1)) y) Sb)
                 = sentry_exp ((sb_of_list Id Us ⨟ β) y)).
      {
        intros y Hy; unfold ind_uvars; rewrite sb_of_list_vars by lia; cbn [sentry_sub sentry_exp sb_compose].
        rewrite <- sentry_exp_sub, <- HSuc by exact Hy; cbn; f_equal; f_equal; lia.
      }
      assert (Hti : List.map (fun T => T[Sb]) (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D nn (ptyp_depth tfull + List.length gs1)))
                                                  (ptyp_ps_at pat tfull))
                    = tele_insts (im_nparams Mj) (sb_of_list Id Us ⨟ β) L1).
      {
        rewrite (tele_insts_sub_mvc _ (ind_nu D) _ (sb_of_list Id Us ⨟ β) Sb) by assumption.
        f_equal; unfold L1, ptyp_ps_at; rewrite List.map_map; apply List.map_ext; intros P.
        rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity.
      }
      assert (Ec : forall P, (P[wk_pat (List.repeat false (ptyp_depth t'full) ++ pat')]ʷ)[sb_qn (ptyp_depth tfull + List.length gs1 + im_nn Mv) (sb_of_list Id Is)][Sb] = P[σ'])
        by (intros; rewrite Hdep, <- exp_sub_of_wk, !exp_sub_sub; reflexivity).
      assert (Ev : forall P, (P[wk_pat (List.repeat false (ptyp_depth tfull) ++ pat)]ʷ)[Sb] = P[σ])
        by (intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      assert (HHps : forall k N, nth_error L2 k = Some N -> forall T, nth_error (tele_insts (im_nparams Mj) (sb_of_list Id Us ⨟ β) L1) k = Some T ->
                 Θ ⍮ Ξ ⍮ Ψ ⊢ N : T /\ (forall N1, nth_error L1 k = Some N1 -> Θ ⍮ Ξ ⍮ Ψ ⊢ N1 ≈ N : T)).
      {
        intros k N HN T HT.
        unfold L2 in HN; apply nth_error_map_inv in HN as (P'0 & HP'0 & ->).
        rewrite <- Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
        assert (HPa' : nth_error (ptyp_ps_at pat' t'full) k = Some (P'0[wk_pat (List.repeat false (ptyp_depth t'full) ++ pat')]ʷ))
          by (unfold ptyp_ps_at; rewrite List.nth_error_map, HP'0; reflexivity).
        assert (Hk : k < List.length (ptyp_ps tfull)) by (rewrite <- Hpsl; apply List.nth_error_Some; congruence).
        destruct (nth_error_lt_some _ _ Hk) as [P0 HP0].
        assert (HPa : nth_error (ptyp_ps_at pat tfull) k = Some (P0[wk_pat (List.repeat false (ptyp_depth tfull) ++ pat)]ʷ))
          by (unfold ptyp_ps_at; rewrite List.nth_error_map, HP0; reflexivity).
        destruct (Hps _ _ _ _ HPa' HPa HT0) as [HPt' HPe].
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ HPt' HSb') as H1; rewrite Ec in H1.
        pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HPe HSb') as H2; rewrite Ec, Ev in H2.
        split; [ exact H1 |].
        intros N1 HN1; unfold L1 in HN1; rewrite List.nth_error_map, HP0 in HN1; injection HN1 as <-.
        apply wf_exp_eq_sym; exact H2.
      }
      assert (Hl2 : List.length (tele_insts (im_nparams Mj) (sb_of_list Id Us ⨟ β) L1) = im_nn Mj)
        by (rewrite length_tele_insts by exact HaN; rewrite HL1; unfold im_nn; lia).
      pose proof (elim_mctx_insts p D (ptyp_mem tfull) Mj Us β L1 x Hc HMj HUl HL1) as E.
      eapply wf_sub_eq_of_list_left;
        [ exact (elim_mctx_ass _ _ _ _ _ Hc HMj) | exact HM | apply wf_sub_eq_refl; exact Hβ | exact Hlen
        | rewrite List.length_app, HL2, length_elim_mctx; cbn; lia | rewrite E; exact HL1t | rewrite E | rewrite E ].
      + intros k N T HN HT.
        destruct (Nat.lt_ge_cases k (im_nn Mj)) as [Hk | Hk].
        * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
          exact (proj1 (HHps _ _ HN _ HT)).
        * rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
          rewrite HL2 in HN; rewrite Hl2 in HT.
          destruct (k - im_nn Mj) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
          injection HN as <-; injection HT as <-; exact Hx.
      + intros k N N' T HN HN' HT.
        destruct (Nat.lt_ge_cases k (im_nn Mj)) as [Hk | Hk].
        * rewrite List.nth_error_app1 in HN, HN' by lia; rewrite List.nth_error_app1 in HT by lia.
          exact (proj2 (HHps _ _ HN' _ HT) _ HN).
        * rewrite List.nth_error_app2 in HN, HN' by lia; rewrite List.nth_error_app2 in HT by lia.
          rewrite HL1 in HN; rewrite HL2 in HN'; rewrite Hl2 in HT.
          destruct (k - im_nn Mj) as [| k'] eqn:Hk'; cbn in HN, HN', HT; [| destruct k'; discriminate ].
          injection HN as <-; injection HN' as <-; injection HT as <-; apply wf_exp_eq_refl; exact Hx.
    - assert (Hd : d < ptyp_depth tfull) by lia.
      assert (Hd' : d < ptyp_depth t'full) by lia.
      rewrite (ptyp_skip_lt tfull d Hd) in Hx |- *; rewrite (ptyp_skip_lt t'full d Hd').
      cbn [ptyp_ihty ptyp_ty_at] in Hx |- *.
      set (B := List.nth d (ptyp_doms tfull) a_True) in *.
      set (B' := List.nth d (ptyp_doms t'full) a_True).
      set (σ := ι (wk_pat (List.repeat false d ++ pat)) ⨟ Sb) in *.
      set (σ' := ι (wk_pat (List.repeat false d ++ pat')) ⨟ (sb_qn (d + List.length gs1 + nn) (sb_of_list Id Is) ⨟ Sb)).
      destruct (shape_prefix_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hmv Hin gs1 tfull gs2 Heq d ltac:(unfold ptyp_depth in Hd; lia))
        as (HΩd & HStrd & Hφd).
      assert (Hσ : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx (List.firstn d (ptyp_doms tfull)) ++ cargs_strat gs1 ++ im_params D Mv)
        by (eapply wf_sub_compose; [ apply wf_sub_of_wk; exact Hφd | exact HSb ]).
      destruct (nth_error_lt_some (ptyp_doms tfull) d ltac:(unfold ptyp_depth in Hd; lia)) as [B0 HB0].
      assert (EB : B = B0) by (unfold B; apply List.nth_error_nth; exact HB0).
      destruct (doms_split_nth _ _ _ HB0) as [Hsp Hf].
      destruct (HBt (List.firstn d (ptyp_doms tfull)) B0 (List.skipn (S d) (ptyp_doms tfull)) Hsp) as [j1 Hj1].
      cbn [List.app] in Hj1; rewrite <- EB in Hj1.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
      destruct (Hdoms d Hd) as [i0 Hi0].
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hi0 HSb) as HBB; cbn [exp_sub] in HBB.
      assert (EBv : (ptyp_dom_at (cargs_pat gs1) d tfull)[Sb] = B[σ])
        by (unfold ptyp_dom_at; fold B pat; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      assert (EBc : (ptyp_dom_at (cargs_pat gs1') d t'full)[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id Is)][Sb] = B'[σ'])
        by (unfold ptyp_dom_at; fold B' pat'; rewrite <- exp_sub_of_wk, !exp_sub_sub; reflexivity).
      rewrite EBv, EBc in HBB.
      assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
      destruct (shape_prefix_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hmv Hin gs1 tfull gs2 Heq (S d) ltac:(unfold ptyp_depth in Hd; lia))
        as (HΩS & _ & _).
      rewrite (sh_ctx_firstn_S _ _ _ Hd) in HΩS; cbn [List.app] in HΩS.
      destruct (ctx_decomp HΩS) as [_ [j0 Hj0]].
      assert (HSbq : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ q Sb : Ω (S d)).
      {
        unfold Ω; rewrite (sh_ctx_firstn_S _ _ _ Hd); cbn [List.app].
        rewrite <- EBv; eapply wf_sub_q; [ exact HSb | exact Hj0 |].
        exact (sub_preserves_exp _ _ _ _ _ _ _ Hj0 HSb).
      }
      assert (HSuc' : forall y, y < ind_nu D ->
                 sentry_exp ((q Sb) (y + S d + List.length gs1 + nn)) = (sentry_exp (sb_of_list Id Us y))[β ⨟ ι ↑]).
      {
        intros y Hy; replace (y + S d + List.length gs1 + nn) with (S (y + d + List.length gs1 + nn)) by lia.
        rewrite sb_q_succ, <- sentry_exp_wk, HSuc by exact Hy.
        rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity.
      }
      assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
        by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
      pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hqσ.
      replace ((doms_ctx (List.firstn d (ptyp_doms tfull)) ++ cargs_strat gs1 ++ im_params D Mv) ▹ B)
        with (doms_ctx (List.firstn (S d) (ptyp_doms tfull)) ++ cargs_strat gs1 ++ im_params D Mv) in Hqσ
        by (rewrite Hf, doms_ctx_app_one, EB; reflexivity).
      assert (Huc : shape_uc D Us (doms_ctx (List.firstn d (ptyp_doms tfull)) ++ cargs_strat gs1 ++ im_params D Mv) σ β).
      {
        intros y Hy; unfold σ; cbn [sb_compose sb_of_wk sentry_sub].
        destruct (length_shape_ctx D Mv (List.firstn d (ptyp_doms tfull)) (cargs_strat gs1)) as [E1 _]; rewrite E1.
        replace (y + (List.length (List.firstn d (ptyp_doms tfull)) + List.length (cargs_strat gs1) + im_nn Mv))
          with (pat_nargs (List.repeat false d ++ pat) + (nn + y))
          by (rewrite pat_nargs_falses, List.length_firstn; unfold pat; rewrite pat_nargs_cargs_pat; unfold ptyp_depth, nn in *; lia).
        rewrite wk_pat_ge, List.length_app, List.repeat_length; unfold pat; rewrite length_cargs_pat.
        cbn [sb_compose]; rewrite <- sentry_exp_sub.
        replace (d + List.length gs1 + (nn + y)) with (y + d + List.length gs1 + nn) by lia.
        rewrite HSuc by exact Hy; reflexivity.
      }
      assert (Huc' : shape_uc D Us (doms_ctx (List.firstn (S d) (ptyp_doms tfull)) ++ cargs_strat gs1 ++ im_params D Mv) (q σ) (β ⨟ ι ↑))
        by (rewrite Hf, doms_ctx_app_one; apply shape_uc_pi; [ exact (proj2 (length_shape_ctx D Mv _ _)) | exact Huc ]).
      pose proof (shape_doms_typed_skip _ _ _ _ _ _ (S d) HBt) as HBt'.
      pose proof (shape_leaf_typed_skip _ _ _ _ _ _ tfull (S d) ltac:(lia) HPt) as HPt'.
      destruct (ty_at_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc HUl
                  (fun j Mj' Hj => elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hj HΓ HUl HUs)
                  Hβ' Hqσ Huc' ltac:(rewrite ptyp_mem_skip; exact HMj) ltac:(rewrite ptyp_ps_skip; exact HPl) HBt' HPt')
        as [j2 Hj2].
      assert (Hus : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[β]) Us) = List.map (fun U => U[β ⨟ ι ↑]) Us)
        by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      rewrite Hus in Hx.
      pose proof (shape_arg_app _ _ _ _ _ _ _ _ Hj1' Hj2 Hx) as Hx'.
      rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ _ (shape_sub_step d pat Sb)) in Hx'.
      destruct (IH (S d) ltac:(lia) _ _ _ _ Hβ' HSbq HSuc' Hx') as [j3 Hj3].
      rewrite <- (ptyp_ihty_sb_eq _ _ _ _ _ _ _ (fun z => eq_refl) (shape_sub_step d pat Sb)) in Hj3.
      replace (S d + List.length gs1 + nn) with (S d + (List.length gs1 + nn)) in Hj3 by lia.
      rewrite <- (ptyp_ihty_sb_eq _ _ _ _ _ _ _ (fun z => eq_refl)
                    (shape_sub_step' d (List.length gs1 + nn) pat' (sb_of_list Id Is) Sb)) in Hj3.
      replace (d + (List.length gs1 + nn)) with (d + List.length gs1 + nn) in Hj3 by lia.
      exists (max j1 (max i0 j3)).
      eapply wf_exp_eq_pi_cong_large;
        [ eapply lift_exp_ge; [| exact Hj1' ]; lia
        | eapply lift_exp_eq_ge; [| apply wf_exp_eq_sym; exact HBB ]; lia
        | eapply lift_exp_eq_ge; [| exact Hj3 ]; lia ].
  Qed.
End IhtyConv.

(** ** A View's Branch, as the Container's

    The parameters and arguments of the view's constructor are the
    container's at the view's instance. *)
Lemma view_ctel_ext : forall Θ Ξ Γ p D m Mm qc k' Is vm D' i' Mi' v Mv Us c gs' gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm -> ind_lookup Θ Ξ qc = Some D' ->
    ind_member D' i' = Some Mi' -> nth_error vm i' = Some v -> ind_member D v = Some Mv ->
    ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ ctel p D Mv Us gs ≈ ctel qc D' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) gs'.
Proof.
  intros * Hg HDs Hl Hm Hh Hl' Hi' Hv Hmv Hcon' Hcon HΓ HUl HUs.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (HDs _ _ Hl') as HD'; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
  destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D0 & Mk0 & Hl0 & _ & _ & HIl & _).
  rewrite Hl' in Hl0; injection Hl0 as <-.
  set (Is' := List.map (fun I => I[sb_of_list Id Us]) Is).
  pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ'.
  pose proof (dt_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hv Hmv) as HNeq.
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as Htail.
  rewrite (nparams_sub D' i' Mi' Is (sb_of_list Id Us) Hc' Hi' HIl) in Htail; fold Is' in Htail.
  assert (Hnn : im_nn Mv = im_nn Mi')
    by (pose proof (ext_eq_length _ _ _ _ _ Htail) as E; rewrite !length_tele_sub in E; exact E).
  pose proof (dt_view_args _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hm Hh Hl' Hi' Hv Hmv Hcon' Hcon) as HV.
  pose proof (wf_nparams_sub _ _ _ HD Hc _ _ _ _ Hmv HΓ Hσ') as HΨv.
  pose proof (wf_sub_ext _ _ (im_nparams Mv) _ _ _ Hσ HΨv (member_params_wf _ _ _ _ _ HD Hmv)) as Hσ1.
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ HV Hσ1) as HV'.
  rewrite tele_sub_sub in HV'.
  change (List.length (im_nparams Mv)) with (im_nn Mv) in HV'.
  assert (E : tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id Is) ⨟ sb_qn (im_nn Mv) (sb_of_list Id Us))
              = tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mi') (sb_of_list Id Is'))).
  { rewrite <- Hnn.
    erewrite tele_sub_sb_eq by (apply sb_qn_compose_ext; reflexivity).
    eapply (tele_scoped_sub_agree _ (im_np D' Mi'));
      [ eapply decl_closed_cargs_scoped; [ exact Hc' | exact Hi' | exact (cons_lookup_in _ _ _ Hcon') ] |].
    unfold im_np; rewrite <- Hnn; apply sb_qn_agree; intros x Hx; cbn [sb_compose].
    unfold Is'; apply sb_of_list_lt_compose; unfold ind_nu in *; lia. }
  rewrite E in HV'.
  unfold ctel; apply ext_eq_app;
    [ apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HD _ _ Hmv) | apply tele_ass_sub, cargs_ctx_aux_ass | exact Htail |].
  apply ext_eq_sym_ass; [ apply tele_ass_sub, cargs_ctx_aux_ass | exact HV' ].
Qed.

(** The container's blocks: the one of the container's member [i'] is the
    block of the group's member [vm] lists for it, its branches wrapped. *)
Lemma nth_error_vwrap : forall pq D D' vm Us Bks i' Mi', ind_member D' i' = Some Mi' ->
    List.nth_error (vwrap pq D D' vm Us Bks) i' = Some (vwrap_block pq D vm Us Bks i' Mi').
Proof.
  intros * H; unfold vwrap, ind_member in *.
  enough (forall ms s k M, List.nth_error ms k = Some M ->
            List.nth_error (vwrap_from pq D vm Us Bks s ms) k = Some (vwrap_block pq D vm Us Bks (s + k) M))
    by (rewrite <- (Nat.add_0_l i') at 2; auto).
  induction ms as [| M0 ms IH]; intros s [| k] M Hk; cbn in Hk |- *; try discriminate.
  - injection Hk as <-; rewrite Nat.add_0_r; reflexivity.
  - rewrite (IH (S s) k M Hk); do 2 f_equal; lia.
Qed.

Lemma vwrap_block_eq : forall pq D vm Us Bks i' Mi' v Mv b,
    List.nth_error vm i' = Some v -> List.nth_error Bks v = Some b -> ind_member D v = Some Mv ->
    vwrap_block pq D vm Us Bks i' Mi'
    = eb_mk (eb_nm b) None (eb_motive b) (List.map (fun cg => wrap_br pq D Us Bks Mv (eb_brs b) (fst cg) (snd cg)) (im_cons Mi')).
Proof.
  intros * Hv Hb Hm; unfold vwrap_block; rewrite (List.nth_error_nth _ _ _ Hv), Hb, Hm; destruct b; reflexivity.
Qed.

Lemma vwrap_motive_nth : forall pq D D' vm Us Bks i' Mi' v b,
    ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v -> List.nth_error Bks v = Some b ->
    (exists Mv, ind_member D v = Some Mv) ->
    List.nth i' (blocks_motives (vwrap pq D D' vm Us Bks)) a_True = eb_motive b.
Proof.
  intros * Hi Hv Hb [Mv Hm].
  rewrite (blocks_motives_nth _ _ _ (nth_error_vwrap pq D D' vm Us Bks _ _ Hi)).
  rewrite (vwrap_block_eq _ _ _ _ _ _ _ _ _ _ Hv Hb Hm); reflexivity.
Qed.

Lemma sb_of_list_id_wk : forall Us φ, sb_eq (sb_of_list Id Us ⨟ ι φ) (sb_of_list (ι φ) (List.map (fun U => U[φ]ʷ) Us)).
Proof.
  intros; etransitivity; [ apply sb_of_list_compose_gen |].
  rewrite map_sub_of_wk; apply sb_of_list_cong, sb_compose_id_left.
Qed.

Lemma tele_insts_agree : forall Δ k σ σ' Ms, tele_ass Δ -> ctx_scoped k Δ -> (forall x, x < k -> σ x = σ' x) ->
    tele_insts Δ σ Ms = tele_insts Δ σ' Ms.
Proof.
  intros * Ha Hs H.
  pose proof (tele_insts_sub Δ k σ σ' Id Ms Ha Hs ltac:(intros; rewrite sentry_sub_id; auto)) as E.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), (List.map_ext (fun M => M[Id]) (fun M => M) exp_sub_id), !List.map_id in E.
  exact E.
Qed.

Lemma sb_of_list_agree : forall Ms σ σ' x, x < List.length Ms -> sb_of_list σ Ms x = sb_of_list σ' Ms x.
Proof. intros * Hx; rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by exact Hx; reflexivity. Qed.

(** Terms instantiating the parameters and the arguments of a
    constructor, read off a substitution into them: at the instances of
    the non-uniform parameters at the uniform ones moved, and of the
    arguments at all of them. *)
Lemma ctel_args_typed : forall Θ Ξ Ψ Γ pq D k Mk Us c gs φ Ns As,
    decl_closed D -> ind_member D k = Some Mk -> List.In (c, gs) (im_cons Mk) ->
    List.length Us = ind_nu D -> List.length Ns = im_nn Mk -> List.length As = List.length gs ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list (ι φ) (Ns ++ As) : ctel pq D Mk Us gs ++ Γ ->
    (forall j N T, nth_error Ns j = Some N ->
       nth_error (tele_insts (im_nparams Mk) (sb_of_list Id (List.map (fun U => U[φ]ʷ) Us)) Ns) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T) /\
    (forall j N T, nth_error As j = Some N ->
       nth_error (tele_insts (cargs_ctx pq D Mk gs) (sb_of_list Id (List.map (fun U => U[φ]ʷ) Us ++ Ns)) As) j = Some T ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ N : T).
Proof.
  intros * Hc Hk Hin HUl HNl HAl Hσ.
  assert (Ect : ctel pq D Mk Us gs = tele_sub (cargs_ctx pq D Mk gs ++ im_nparams Mk) (sb_of_list Id Us))
    by (unfold ctel; rewrite tele_sub_app, length_im_nparams; reflexivity).
  assert (Ha : tele_ass (cargs_ctx pq D Mk gs ++ im_nparams Mk))
    by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ]).
  rewrite Ect in Hσ.
  assert (Hlen : List.length (Ns ++ As) = List.length (tele_sub (cargs_ctx pq D Mk gs ++ im_nparams Mk) (sb_of_list Id Us)))
    by (rewrite length_tele_sub, !List.length_app, length_cargs_ctx; change (List.length (im_nparams Mk)) with (im_nn Mk); lia).
  pose proof (wf_sub_of_list_inv Θ Ξ Ψ _ Γ _ _ (tele_ass_sub _ _ Ha) Hlen Hσ) as H.
  rewrite tele_insts_tele_sub in H.
  rewrite tele_insts_app in H by (first [ eapply decl_closed_nparams_ass; eassumption | change (List.length (im_nparams Mk)) with (im_nn Mk); exact HNl ]).
  rewrite (tele_insts_sb_eq _ _ _ _ (sb_of_list_id_wk Us φ)) in H.
  rewrite (tele_insts_sb_eq (cargs_ctx pq D Mk gs) _ _ _ (sb_of_list_cong Ns _ _ (sb_of_list_id_wk Us φ))) in H.
  rewrite <- sb_of_list_app in H.
  set (Usφ := List.map (fun U => U[φ]ʷ) Us) in *.
  assert (HUφ : List.length Usφ = ind_nu D) by (unfold Usφ; rewrite List.length_map; exact HUl).
  rewrite (tele_insts_agree (im_nparams Mk) (ind_nu D) _ (sb_of_list Id Usφ)) in H
    by (first [ eapply decl_closed_nparams_ass; eassumption | eapply decl_closed_nparams_scoped; eassumption
              | intros; apply sb_of_list_agree; lia ]).
  rewrite (tele_insts_agree (cargs_ctx pq D Mk gs) (im_np D Mk) _ (sb_of_list Id (Usφ ++ Ns))) in H
    by (first [ apply cargs_ctx_aux_ass | eapply decl_closed_cargs_scoped; eassumption
              | intros; apply sb_of_list_agree; rewrite List.length_app; unfold im_np in *; lia ]).
  assert (Hl2 : List.length (tele_insts (im_nparams Mk) (sb_of_list Id Usφ) Ns) = List.length Ns)
    by (rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption); rewrite HNl; unfold im_nn; lia).
  split.
  - intros j N T HN HT; apply (H j); [ rewrite List.nth_error_app1; [ exact HN | apply List.nth_error_Some; congruence ]
                                     | rewrite List.nth_error_app1; [ exact HT | rewrite Hl2; apply List.nth_error_Some; congruence ] ].
  - intros j N T HN HT; apply (H (List.length Ns + j)).
    + rewrite List.nth_error_app2 by lia; replace (List.length Ns + j - List.length Ns) with j by lia; exact HN.
    + rewrite List.nth_error_app2 by lia; rewrite Hl2; replace (List.length Ns + j - List.length Ns) with j by lia; exact HT.
Qed.

(** [ihs_sub] followed by an instance of a branch's context whose base is
    a weakening: the shape's components instantiated by the uniform
    parameters weakened, the non-uniform ones and the non-recursive
    arguments before. *)
Lemma ihs_sub_view : forall nn Us na (gs1 : list carg) φ Ns As L,
    List.length Ns = nn -> List.length As = na -> List.length gs1 <= na ->
    sb_eq (ihs_sub nn Us na (cargs_pat gs1) (List.length L) ⨟ sb_of_list (ι φ) (Ns ++ As ++ L))
          (cargs_sub (sb_of_list (ι φ) (List.map (fun U => U[φ]ʷ) Us ++ Ns)) gs1 As).
Proof.
  intros * HNl HAl Hg.
  set (i := List.length gs1).
  assert (Hpi : List.length (cargs_pat gs1) = i) by apply length_cargs_pat.
  unfold ihs_sub; rewrite Hpi, !sb_compose_assoc.
  rewrite <- (List.firstn_skipn i As), <- !List.app_assoc, List.app_assoc.
  replace (na - i + List.length L) with (List.length (List.skipn i As ++ L))
    by (rewrite List.length_app, List.length_skipn; lia).
  rewrite sb_shift_of_list_app.
  replace (i + nn) with (List.length (Ns ++ List.firstn i As))
    by (rewrite List.length_app, List.length_firstn; lia).
  rewrite sb_qn_of_list, (sb_of_list_cong _ _ _ (sb_of_list_id_wk Us φ)), <- !sb_of_list_app, List.app_assoc.
  rewrite sb_of_list_app, cargs_sub_pat by (rewrite List.length_firstn; lia).
  rewrite List.firstn_skipn; unfold i; rewrite cargs_sub_firstn; reflexivity.
Qed.

(** The parameters and the non-recursive arguments before a recursive
    argument, in the branch's context: the instance of the uniform
    parameters, past the arguments after it and the results before it. *)
Lemma rec_arg_base : forall Θ Ξ Γ p D k Mk Us c gs gs1 t gs2 E,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ->
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs
      ⊢ˢ sb_qn (List.length gs1 + im_nn Mk) (sb_of_list Id Us) ⨟ ι (wk_shiftn (List.length gs - List.length gs1 + List.length E))
      : cargs_ctx p D Mk gs1 ++ im_params D Mk.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl Hσ Hin Heq HΨ.
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ Hσ c gs gs1 (ca_rec t :: gs2) Hin Heq) as (Hi1 & Hτ2).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs1 (ca_rec t :: gs2) Heq) as (HΨ1 & _ & _).
  assert (Hw3 : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ʷ wk_shiftn (List.length gs - List.length gs1 + List.length E)
                  : cinst Γ p D Mk Us gs1).
  { rewrite Heq in HΨ |- *; rewrite cinst_split in HΨ |- *; rewrite List.app_assoc in HΨ |- *.
    match goal with |- _ ⍮ _ ⍮ ?L ++ _ ⊢ʷ wk_shiftn ?n : _ => replace n with (List.length L) end.
    - apply wf_wk_shiftn_app'; exact HΨ.
    - rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; lia. }
  rewrite List.app_assoc in Hτ2; apply wf_sub_prefix in Hτ2; [| exact HΨ1 ].
  eapply wf_sub_compose; [ exact Hτ2 | apply wf_sub_of_wk; exact Hw3 ].
Qed.

(** The container's substitution of a recursive argument's shape's
    components into a branch of the container's eliminator, and the view's
    instance followed by the view's, send the same terms: the parameters
    and the arguments before as the same variables, the uniform parameters
    as the view's instance weakened. *)
Lemma view_rec_sub_agree : forall (Is Us L : list exp) nuD nn na i r' nr' z,
    List.Forall (exp_scoped nuD) Is -> List.length Us = nuD -> i <= na -> r' < nr' ->
    z < i + nn + List.length Is ->
    sentry_exp (((sb_qn (i + nn) (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)) ⨟ ι (wk_shiftn (na - i + r')))
                  ⨟ ι (wk_shiftn (nr' - r'))) z)
    = sentry_exp ((sb_qn (i + nn) (sb_of_list Id Is) ⨟
                   ((sb_qn (i + nn) (sb_of_list Id Us) ⨟ ι (wk_shiftn (na - i + List.length L)))
                      ⨟ sb_of_list (ι (wk_shiftn (nn + na + nr'))) (vars_from nr' (nn + na) ++ L))) z).
Proof.
  intros * HIs HUl Hi Hr Hz.
  set (δ := sb_of_list (ι (wk_shiftn (nn + na + nr'))) (vars_from nr' (nn + na) ++ L)).
  assert (Hδ : forall w, w < nn + na -> δ (List.length L + w) = se_exp (a_var (nr' + w))).
  { intros w Hw; unfold δ; rewrite sb_of_list_app, sb_of_list_ge, sb_of_list_vars by exact Hw; reflexivity. }
  destruct (Nat.lt_ge_cases z (i + nn)) as [Hz1 | Hz1].
  - cbn [sb_compose]; rewrite !sb_qn_lt by exact Hz1; cbn [sentry_sub sb_of_wk sentry_exp wk_shiftn].
    cbn [sb_compose]; rewrite sb_qn_lt by exact Hz1; cbn [sentry_sub sb_of_wk wk_shiftn].
    replace (z + (na - i + List.length L)) with (List.length L + (z + na - i)) by lia.
    rewrite Hδ by lia; cbn; f_equal; lia.
  - cbn [sb_compose]; rewrite !sb_qn_ge by exact Hz1.
    set (y := z - (i + nn)) in *.
    assert (Hy : y < List.length Is) by (unfold y; lia).
    rewrite <- sb_of_list_lt_compose by exact Hy.
    rewrite (sb_of_list_nth _ _ _ (a_var 0)) by exact Hy.
    set (I := List.nth (List.length Is - 1 - y) Is (a_var 0)).
    cbn [sentry_sub sentry_wk sentry_exp].
    assert (HsI : exp_scoped nuD I).
    { unfold I; apply (proj1 (List.Forall_forall _ _) HIs), List.nth_In; lia. }
    rewrite <- !exp_sub_of_wk, !exp_sub_sub.
    apply (exp_scoped_sub_agree _ nuD); [ exact HsI |].
    intros x Hx; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
    rewrite sb_qn_ge by lia; replace (x + (i + nn) - (i + nn)) with x by lia.
    rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia.
    cbn [sentry_sub sentry_wk sentry_exp].
    f_equal; rewrite <- !exp_sub_of_wk, !exp_sub_sub; apply exp_sub_sb_eq.
    intros w; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
    replace (w + (i + nn) + (na - i + List.length L)) with (List.length (vars_from nr' (nn + na) ++ L) + w)
      by (rewrite List.length_app, length_vars_from; lia).
    unfold δ; rewrite sb_of_list_ge; cbn; f_equal; lia.
Qed.

(** ** The Container's Blocks Typed

    The blocks of the group's eliminator, typed at the uniform parameters
    [Us]; the container's blocks [vwrap], at the view's instance. *)
Section ViewBlocks.
  Context (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (m : nat) (Mm : imember)
    (qc : qname) (k' : nat) (Is : list exp) (vm : list nat) (D' : ind_decl) (Us : list exp) (Bks : list eblock) (i : nat).
  Hypothesis (Hg : ⊢ᵍ Θ ⍮ Ξ) (HDs : decls_typed Θ Ξ) (Hl : ind_lookup Θ Ξ p = Some D) (Hm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm) (Hl' : ind_lookup Θ Ξ qc = Some D') (Hvw : vwrap_ok D D' vm)
    (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T)
    (HBt : blocks_typed Θ Ξ Γ p D Us Bks i).

  Let Is' := List.map (fun I => I[sb_of_list Id Us]) Is.
  Let Bks' := vwrap p D D' vm Us Bks.

  Lemma vw_member : forall i' Mi', ind_member D' i' = Some Mi' ->
      exists v Mv b, List.nth_error vm i' = Some v /\ ind_member D v = Some Mv /\ List.nth_error Bks v = Some b /\
        im_nn Mv = im_nn Mi' /\ List.map fst (im_cons Mv) = List.map fst (im_cons Mi') /\
        (forall c gs' gs, In (c, gs') (im_cons Mi') -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs).
  Proof.
    intros * Hi.
    destruct (nth_error_lt_some vm i') as [v Hv].
    { rewrite (vwo_length _ _ _ Hvw); exact (ind_member_lt _ _ _ Hi). }
    destruct (vwo_members _ _ _ Hvw _ _ _ Hi Hv) as (Mv & Hmv & Hnn & Hnames & Hcorr).
    destruct (blocks_nth _ _ _ _ (bt_len _ _ _ _ _ _ _ _ HBt) Hmv) as [b Hb].
    exists v, Mv, b; auto 7.
  Qed.

  Lemma vw_facts : decl_typed Θ Ξ D /\ decl_closed D /\ decl_typed Θ Ξ D' /\ decl_closed D' /\
      List.length Is' = ind_nu D' /\
      (forall k I T, nth_error Is' k = Some I -> nth_error (tele_insts (ind_uparams D') Id Is') k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ I : T).
  Proof.
    pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
    pose proof (HDs _ _ Hl') as HD'; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
    destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D0 & Mk0 & Hl0 & _ & _ & HIl & _).
    rewrite Hl' in Hl0; injection Hl0 as <-.
    refine (conj HD (conj Hc (conj HD' (conj Hc' (conj _ _))))).
    - unfold Is'; rewrite List.length_map; exact HIl.
    - exact (view_is_typed _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HD Hc' Hm Hh Hl' HΓ HUl HUs).
  Qed.

  Lemma vw_motives_typed : motives_typed Θ Ξ Γ qc D' Is' (blocks_motives Bks') i.
  Proof.
    intros j' Mj' Hj'.
    destruct (vw_member _ _ Hj') as (v & Mv & b & Hv & Hmv & Hb & _).
    unfold Bks'; rewrite (vwrap_motive_nth _ _ _ _ _ _ _ _ _ _ Hj' Hv Hb ltac:(eauto)).
    pose proof (view_mctx_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hj' Hv Hmv HΓ HUl HUs) as Hx.
    destruct vw_facts as (HD & Hc & _).
    pose proof (ctxsub_ext _ _ _ _ _ Hx (elim_mctx_ass _ _ _ _ _ Hc Hmv)) as Hs.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ (bt_motive _ _ _ _ _ _ _ _ HBt _ _ _ Hmv Hb) Hs) as H.
    rewrite !exp_sub_id in H; exact H.
  Qed.

  (** A branch of the container's constructor [c] of the member [i'], the
      group's member [v] the view lists for it. *)
  Section ViewBranch.
    Context (i' : nat) (Mi' : imember) (v : nat) (Mv : imember) (c : String.string) (gs' gs : list carg).
    Hypothesis (Hi' : ind_member D' i' = Some Mi') (Hv : nth_error vm i' = Some v) (Hmv : ind_member D v = Some Mv)
      (Hcon' : ind_con Mi' c = Some gs') (Hcon : ind_con Mv c = Some gs) (Hcorr : cargs_corr vm gs' gs).

    Let nn := im_nn Mv.
    Let na := List.length gs'.
    Let nr' := cargs_nrec gs'.
    Let n' := nn + na + nr'.
    Let Δc := elim_bctx qc D' Mi' gs' (blocks_motives Bks') Is' ++ Γ.

    Lemma vb_nn : im_nn Mi' = nn.
    Proof.
      destruct (vw_member _ _ Hi') as (v0 & Mv0 & b0 & Hv0 & Hmv0 & _ & Hnn & _).
      rewrite Hv in Hv0; injection Hv0 as <-; rewrite Hmv in Hmv0; injection Hmv0 as <-; symmetry; exact Hnn.
    Qed.

    Lemma vb_na : List.length gs = na.
    Proof. symmetry; exact (cargs_corr_length _ _ _ Hcorr). Qed.

    Lemma vb_ctx : ⊢ Θ ⍮ Ξ ⍮ Δc.
    Proof.
      destruct vw_facts as (HD & Hc & HD' & Hc' & HIl & HIs).
      eapply elim_bctx_wf; [ exact Hg | exact HDs | exact Hl' | exact Hi' | exact HΓ | exact HIl
                           | exact (wf_sub_uparams _ _ _ HD' Hc' _ _ HΓ HIl HIs)
                           | intros j Mj Hj; exact (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl' Hj HΓ HIl HIs)
                           | exact vw_motives_typed | exact Hcon' ].
    Qed.

    (** The parameters and the arguments, as variables: of the container's
        constructor, and of the view's. *)
    Lemma vb_base_c : Θ ⍮ Ξ ⍮ Δc ⊢ˢ sb_of_list (ι (wk_shiftn n')) (vars_from (nr' + na) nn ++ vars_from nr' na)
                        : ctel qc D' Mi' Is' gs' ++ Γ.
    Proof.
      destruct vw_facts as (HD & Hc & HD' & Hc' & HIl & HIs).
      pose proof vb_ctx as HΔ.
      pose proof (cons_lookup_in _ _ _ Hcon') as Hin'.
      pose proof (wf_sub_uparams _ _ _ HD' Hc' _ _ HΓ HIl HIs) as Hσc.
      destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl' Hi' HΓ Hσc c gs' gs' nil Hin' (eq_sym (List.app_nil_r gs'))) as [Hi _].
      rewrite cinst_ctel in Hi.
      set (IHc := ihs_ctx_aux (im_nn Mi') (blocks_motives Bks') Is' (List.length gs') nil 0 gs').
      assert (EΔ : Δc = IHc ++ ctel qc D' Mi' Is' gs' ++ Γ) by (unfold Δc, elim_bctx, ctel; rewrite <- !List.app_assoc; reflexivity).
      assert (HlI : List.length IHc = nr') by (unfold IHc; apply length_ihs_ctx_aux).
      assert (Hlc : List.length (ctel qc D' Mi' Is' gs') = na + nn)
        by (unfold ctel; rewrite List.length_app, !length_tele_sub, length_cargs_ctx;
            change (List.length (im_nparams Mi')) with (im_nn Mi'); rewrite vb_nn; reflexivity).
      assert (Hw : Θ ⍮ Ξ ⍮ Δc ⊢ʷ wk_shiftn n' : Γ).
      { rewrite EΔ, List.app_assoc; replace n' with (List.length (IHc ++ ctel qc D' Mi' Is' gs'))
          by (rewrite List.length_app, HlI, Hlc; unfold n'; lia).
        apply wf_wk_shiftn_app'; rewrite <- List.app_assoc, <- EΔ; exact HΔ. }
      { apply wf_sub_of_list; [ unfold ctel; apply List.Forall_app; split; apply tele_ass_sub;
                                [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ HD' _ _ Hi') ]
                              | exact Hi | apply wf_sub_of_wk; exact Hw
                              | rewrite List.length_app, !length_vars_from, Hlc; lia |].
        rewrite vars_from_app.
        assert (Ect : ctel qc D' Mi' Is' gs' = tele_sub (cargs_ctx qc D' Mi' gs' ++ im_nparams Mi') (sb_of_list Id Is'))
          by (unfold ctel; rewrite tele_sub_app, length_im_nparams; reflexivity).
        intros k N T HN HT.
        rewrite Ect, tele_insts_tele_sub in HT.
        replace (nn + na) with (List.length (cargs_ctx qc D' Mi' gs' ++ im_nparams Mi')) in HN, HT
          by (rewrite List.length_app, length_cargs_ctx; change (List.length (im_nparams Mi')) with (im_nn Mi'); rewrite vb_nn; unfold na; lia).
        replace nr' with (List.length IHc) in HN, HT by exact HlI.
        rewrite EΔ, Ect.
        eapply (wf_vars_tele_gen _ _ IHc _ (sb_of_list Id Is') _ Γ (ind_nu D'));
          [ apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ HD' _ _ Hi') ]
          | apply List.Forall_app; split; [ eapply cargs_ctx_mvc; eassumption | exact (decl_nparams_mvc _ _ _ HD' _ _ Hi') ]
          | apply ctx_scoped_app; split;
            [ rewrite length_im_nparams; eapply decl_closed_cargs_scoped; eassumption | eapply decl_closed_nparams_scoped; eassumption ]
          | rewrite <- Ect, <- EΔ; exact HΔ | | exact HN | exact HT ].
        intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; f_equal.
        rewrite List.length_app, length_cargs_ctx, HlI; change (List.length (im_nparams Mi')) with (im_nn Mi'); rewrite vb_nn.
        unfold n', na; f_equal; lia. }
    Qed.

    Lemma vb_base : Θ ⍮ Ξ ⍮ Δc ⊢ˢ sb_of_list (ι (wk_shiftn n')) (vars_from (nr' + na) nn ++ vars_from nr' na)
                      : ctel p D Mv Us gs ++ Γ.
    Proof.
      destruct vw_facts as (HD & Hc & HD' & Hc' & HIl & HIs).
      pose proof vb_base_c as H1.
      pose proof (view_ctel_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hi' Hv Hmv Hcon' Hcon HΓ HUl HUs) as Hx.
      pose proof (ctxsub_ext _ _ _ _ _ Hx ltac:(unfold ctel; apply List.Forall_app; split; apply tele_ass_sub;
                                                 [ apply cargs_ctx_aux_ass | exact (dt_nparams_ass _ _ _ HD _ _ Hmv) ])) as HId.
      pose proof (wf_sub_compose _ _ _ _ _ _ _ HId H1) as H2.
      rewrite sb_compose_id_left in H2; exact H2.
    Qed.

    (** The view's branch's context, instantiated in the container's:
        the parameters and arguments as variables, followed by the
        recursive results so far [L]. *)
    Let nvars := vars_from (nr' + na) nn.
    Let avars := vars_from nr' na.
    Let σ0 := sb_of_list (ι (wk_shiftn n')) (List.map (fun U => U[wk_shiftn n']ʷ) Us ++ nvars).
    Let δ L := sb_of_list (ι (wk_shiftn n')) (nvars ++ avars ++ L).

    Lemma vb_shift : forall L j, j = nn + na + List.length L -> sb_eq (ι (wk_shiftn j) ⨟ δ L) (ι (wk_shiftn n')).
    Proof.
      intros * ->; intros w; unfold δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      replace (w + (nn + na + List.length L)) with (List.length (nvars ++ avars ++ L) + w)
        by (unfold nvars, avars; rewrite !List.length_app, !length_vars_from; lia).
      rewrite sb_of_list_ge; reflexivity.
    Qed.

    Lemma vb_arg_var : forall L x, x < na -> (a_var (List.length L + x))[δ L] = a_var (nr' + x).
    Proof.
      intros * Hx; unfold δ; change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)).
      rewrite List.app_assoc, sb_of_list_app, sb_of_list_ge.
      unfold nvars, avars; rewrite vars_from_app, sb_of_list_vars by lia; reflexivity.
    Qed.

    Lemma vb_theta_eq : forall (gs1 : list carg) L, List.length gs1 <= na ->
        sb_eq (ihs_sub nn Us na (cargs_pat gs1) (List.length L) ⨟ δ L) (cargs_sub σ0 gs1 avars).
    Proof.
      intros * Hg1; apply ihs_sub_view; [ unfold nvars; apply length_vars_from | unfold avars; apply length_vars_from | exact Hg1 ].
    Qed.

    Lemma vb_Sb_eq : forall (gs1 : list carg) L, List.length gs1 <= na ->
        sb_eq (ι (wk_pat (cargs_pat gs1))
                 ⨟ ((sb_qn (List.length gs1 + nn) (sb_of_list Id Us) ⨟ ι (wk_shiftn (na - List.length gs1 + List.length L))) ⨟ δ L))
              (cargs_sub σ0 gs1 avars).
    Proof.
      intros gs1 L Hg1; etransitivity; [| exact (vb_theta_eq gs1 L Hg1) ].
      unfold ihs_sub; rewrite length_cargs_pat; symmetry; rewrite !sb_compose_assoc; reflexivity.
    Qed.

    Lemma vb_Sb_uc : forall (gs1 : list carg) L y, List.length gs1 <= na ->
        sentry_exp (((sb_qn (List.length gs1 + nn) (sb_of_list Id Us) ⨟ ι (wk_shiftn (na - List.length gs1 + List.length L)))
                      ⨟ δ L) (y + 0 + List.length gs1 + nn))
        = (sentry_exp (sb_of_list Id Us y))[ι (wk_shiftn n')].
    Proof.
      intros * Hg1; cbn [sb_compose].
      rewrite sb_qn_ge by lia; replace (y + 0 + List.length gs1 + nn - (List.length gs1 + nn)) with y by lia.
      rewrite <- !sentry_exp_sub, <- sentry_exp_wk, <- !exp_sub_of_wk, !exp_sub_sub; apply exp_sub_sb_eq.
      intros w; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      pose proof (vb_shift L (nn + na + List.length L) eq_refl w) as E; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn] in E.
      rewrite <- E; f_equal; lia.
    Qed.

    Lemma vb_gs1_lt : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1 < na.
    Proof. intros * Heq; rewrite <- vb_na, Heq, List.length_app; cbn; lia. Qed.

    (** A recursive argument of the view's constructor: the instance of
        its shape's components and of the arguments before it. *)
    Lemma vb_rec_Sb : forall gs1 t gs2 E L,
        gs = gs1 ++ ca_rec t :: gs2 -> List.length L = List.length E ->
        ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ L : E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ (sb_qn (List.length gs1 + nn) (sb_of_list Id Us) ⨟ ι (wk_shiftn (na - List.length gs1 + List.length L))) ⨟ δ L
          : cargs_ctx p D Mv gs1 ++ im_params D Mv.
    Proof.
      intros * Heq HL HΨ Hδ.
      destruct vw_facts as (HD & Hc & _).
      pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
      pose proof (rec_arg_base _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hmv HΓ HUl Hσ (cons_lookup_in _ _ _ Hcon) Heq HΨ) as H.
      rewrite vb_na, <- HL in H.
      eapply wf_sub_compose; [ exact H | exact Hδ ].
    Qed.

    Lemma vb_rec_arg : forall gs1 t gs2 E L,
        gs = gs1 ++ ca_rec t :: gs2 -> List.length L = List.length E ->
        ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ L : E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ cargs_sub σ0 gs1 avars : doms_ctx nil ++ cargs_strat gs1 ++ im_params D Mv /\
        shape_uc D Us (doms_ctx nil ++ cargs_strat gs1 ++ im_params D Mv) (cargs_sub σ0 gs1 avars) (ι (wk_shiftn n')) /\
        Θ ⍮ Ξ ⍮ Δc ⊢ a_var (nr' + (na - 1 - List.length gs1))
          : ptyp_ty_at p D (List.map (fun U => U[ι (wk_shiftn n')]) Us) (cargs_sub σ0 gs1 avars) t.
    Proof.
      intros * Heq HL HΨ Hδ.
      destruct vw_facts as (HD & Hc & _).
      pose proof (vb_gs1_lt _ _ _ Heq) as Hlt.
      pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
      destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hmv HΓ HUl Hσ (cons_lookup_in _ _ _ Hcon) Heq HΨ)
        as (Hb & Hθ & Huc & Hx).
      rewrite vb_na, <- HL in Hb, Hθ, Huc, Hx.
      pose proof (vb_theta_eq gs1 L ltac:(lia)) as Hθδ.
      pose proof (vb_shift L (List.length L + na + nn) ltac:(lia)) as Hbδ.
      refine (conj _ (conj _ _)).
      - rewrite <- Hθδ; eapply wf_sub_compose; [ exact Hθ | exact Hδ ].
      - intros y Hy; rewrite <- (Hθδ (y + _)); cbn [sb_compose].
        fold nn in Huc; rewrite <- sentry_exp_sub, (Huc y Hy), sentry_exp_sub; cbn [sb_compose].
        rewrite sentry_sub_sub; f_equal; apply sentry_sub_sb_eq; exact Hbδ.
      - pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hx Hδ) as H.
        rewrite ptyp_ty_at_sub, List.map_map in H by (try exact Hc; rewrite List.length_map; exact HUl).
        fold nn in H; rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ _ Hθδ) in H.
        rewrite length_cargs_pat in H.
        replace (List.length L + na - 1 - List.length gs1) with (List.length L + (na - 1 - List.length gs1)) in H by lia.
        rewrite vb_arg_var in H by lia.
        replace (List.map (fun U => U[ι wk_shiftn n']) Us) with (List.map (fun U => U[ι wk_shiftn (List.length L + na + nn)][δ L]) Us);
          [ exact H |].
        apply List.map_ext; intros U; rewrite !exp_sub_sub; apply exp_sub_sb_eq; exact Hbδ.
    Qed.

    (** The type of the recursive result of a recursive argument of the
        view's constructor, instantiated. *)
    Lemma vb_ihty_view : forall As gs1 t gs2 (E : ctx) (L : list exp),
        gs = gs1 ++ ca_rec t :: gs2 -> List.length L = List.length E ->
        (ptyp_ihty As (ι (wk_shiftn (List.length E + List.length gs + im_nn Mv)))
                   (ihs_sub (im_nn Mv) Us (List.length gs) (cargs_pat gs1) (List.length E))
                   (a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1))) t)[δ L]
        = ptyp_ihty As (ι (wk_shiftn n')) (cargs_sub σ0 gs1 avars) (a_var (nr' + (na - 1 - List.length gs1))) t.
    Proof.
      intros * Heq HL.
      pose proof (vb_gs1_lt _ _ _ Heq) as Hlt.
      rewrite ptyp_ihty_sub, vb_na, <- HL, length_cargs_pat.
      replace (List.length L + na - 1 - List.length gs1) with (List.length L + (na - 1 - List.length gs1)) by lia.
      rewrite vb_arg_var by lia; fold nn.
      apply ptyp_ihty_sb_eq; [ apply vb_shift; lia | apply vb_theta_eq; lia ].
    Qed.

    Lemma cargs_nrec_app : forall gs1 gs2, cargs_nrec (gs1 ++ gs2) = cargs_nrec gs1 + cargs_nrec gs2.
    Proof. induction gs1 as [| [] gs1 IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

    Lemma vb_wkw : Θ ⍮ Ξ ⍮ Δc ⊢ʷ wk_shiftn n' : Γ.
    Proof.
      pose proof vb_ctx as HΔ.
      set (IHc := ihs_ctx_aux (im_nn Mi') (blocks_motives Bks') Is' (List.length gs') nil 0 gs').
      assert (EΔ : Δc = (IHc ++ ctel qc D' Mi' Is' gs') ++ Γ) by (unfold Δc, elim_bctx, ctel; rewrite <- !List.app_assoc; reflexivity).
      assert (Hlen : List.length (IHc ++ ctel qc D' Mi' Is' gs') = n').
      { unfold IHc, ctel; rewrite !List.length_app, length_ihs_ctx_aux, !length_tele_sub, length_cargs_ctx.
        change (List.length (im_nparams Mi')) with (im_nn Mi'); rewrite vb_nn; unfold n', na, nr'; lia. }
      rewrite EΔ, <- Hlen; apply wf_wk_shiftn_app'; rewrite <- EΔ; exact HΔ.
    Qed.

    Lemma vb_wk : Θ ⍮ Ξ ⍮ Δc ⊢ˢ ι (wk_shiftn n') : Γ.
    Proof. apply wf_sub_of_wk, vb_wkw. Qed.

    (** An argument recursive in the container and in the view: the
        container's recursive result, a variable of the container's
        branch's context, is of the type of the view's, by the view
        equations ([ihty_conv]). *)
    Lemma vb_recrec : forall gs1' t' rest1' gs1 t rest1 (E : ctx) (L : list exp),
        gs' = gs1' ++ ca_rec t' :: rest1' -> gs = gs1 ++ ca_rec t :: rest1 -> List.length gs1' = List.length gs1 ->
        List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) -> ptyp_depth t' = ptyp_depth t ->
        List.length L = List.length E ->
        ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ L : E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ a_var (nr' - 1 - cargs_nrec gs1')
          : ptyp_ihty (blocks_motives Bks) (ι (wk_shiftn n')) (cargs_sub σ0 gs1 avars) (a_var (nr' + (na - 1 - List.length gs1))) t.
    Proof.
      intros * Heq' Heq Hlen Hmt Hdt HL HΨ Hδ.
      destruct vw_facts as (HD & Hc & HD' & Hc' & HIl & HIs).
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin; pose proof (cons_lookup_in _ _ _ Hcon') as Hin'.
      pose proof (vb_gs1_lt _ _ _ Heq) as Hlt.
      set (r' := cargs_nrec gs1').
      assert (Hnr : nr' = r' + S (cargs_nrec rest1')) by (unfold nr', r'; rewrite Heq', cargs_nrec_app; cbn; lia).
      destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HD Hmv Hin Heq) as (Mj & HMj & HPl & HBt0 & HPt0).
      destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HD' Hi' Hin' Heq') as (Mj' & HMj' & HPl' & _ & _).
      destruct (vw_member _ _ HMj') as (v0 & Mv0 & b0 & Hv0 & Hmv0 & Hb0 & Hnn0 & _).
      rewrite Hmt in Hv0; injection Hv0 as <-; rewrite HMj in Hmv0; injection Hmv0 as <-.
      assert (Hpsl : List.length (ptyp_ps t') = List.length (ptyp_ps t)) by lia.
      assert (Hmem : List.nth (ptyp_mem t') (blocks_motives Bks') a_True = List.nth (ptyp_mem t) (blocks_motives Bks) a_True).
      { unfold Bks'; rewrite (vwrap_motive_nth _ _ _ _ _ _ _ _ _ _ HMj' Hmt Hb0 ltac:(eauto)).
        symmetry; apply blocks_motives_nth; exact Hb0. }
      pose proof (ind_lookup_mpath _ _ _ _ Hg Hl) as Hmp.
      pose proof (fun d Hd => dt_view_doms _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d
                                Hm Hh Hl' Hi' Hv Hmv Hcon' Hcon Heq' Heq Hlen Hd) as Hdoms.
      pose proof (fun j P' P T HP' HP HT => dt_view_ps _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j P' P T
                                Hm Hh Hl' Hi' Hv Hmv Hcon' Hcon Heq' Heq Hlen HMj HP' HP HT) as Hps.
      pose proof (blocks_motives_typed _ _ _ _ _ _ _ _ HBt) as HAs.
      pose proof vb_wk as Hβ.
      pose proof (vb_rec_Sb _ _ _ _ _ Heq HL HΨ Hδ) as HSb.
      destruct (vb_rec_arg _ _ _ _ _ Heq HL HΨ Hδ) as (Hσg & Huc & Hx).
      pose proof (vb_Sb_eq gs1 L ltac:(lia)) as HSbe.
      rewrite <- (ptyp_ty_at_sb_eq _ _ _ _ _ _ HSbe) in Hx.
      (* the view's type and the container's, equal *)
      destruct (ihty_conv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hmv Hin Heq HMj HΓ HUl HUs HAs Hdt Hpsl Hmem Hlen
                  Hdoms Hps (ptyp_depth t) 0 (Nat.add_0_r _) Δc _ _ _ Hβ HSb (fun y Hy => vb_Sb_uc gs1 L y ltac:(lia)) Hx) as [j Hj].
      cbn [ptyp_skip List.repeat List.app Nat.add] in Hj.
      rewrite (ptyp_ihty_sb_eq _ _ _ _ _ _ _ (fun z => eq_refl) HSbe) in Hj.
      (* the container's recursive result *)
      pose proof (ihs_ctx_aux_app (im_nn Mi') (blocks_motives Bks') Is' (List.length gs') gs1' (ca_rec t' :: rest1') nil 0) as Hsplit.
      rewrite <- Heq' in Hsplit; cbn [ihs_ctx_aux] in Hsplit.
      rewrite List.app_nil_r, Nat.add_0_l in Hsplit; fold r' in Hsplit.
      set (R := ihs_ctx_aux (im_nn Mi') (blocks_motives Bks') Is' (List.length gs') (true :: cargs_pat gs1') (S r') rest1') in Hsplit.
      set (Tc := ptyp_ihty (blocks_motives Bks') (ι wk_shiftn (r' + List.length gs' + im_nn Mi'))
                   (ihs_sub (im_nn Mi') Is' (List.length gs') (cargs_pat gs1') r')
                   (a_var (r' + List.length gs' - 1 - List.length (cargs_pat gs1'))) t') in Hsplit.
      assert (HlR : List.length R = cargs_nrec rest1') by (unfold R; apply length_ihs_ctx_aux).
      assert (Hlk : Δc ∋ #(nr' - 1 - r') : Tc[↑]ʷ[wk_shiftn (List.length R)]ʷ).
      { unfold Δc, elim_bctx; rewrite Hsplit, <- !List.app_assoc; cbn [List.app].
        replace (nr' - 1 - r') with (0 + List.length R) by lia.
        apply ctx_lookup_app_r; constructor. }
      pose proof (wf_vlookup _ _ _ _ _ vb_ctx Hlk) as Hvar.
      assert (Hx' : (a_var (r' + List.length gs' - 1 - List.length (cargs_pat gs1')))[ι wk_shift ⨟ ι wk_shiftn (List.length R)]
                    = a_var (nr' + (na - 1 - List.length gs1))).
      { cbn [exp_sub sb_compose sb_of_wk sentry_sub sentry_exp]; rewrite length_cargs_pat, Hlen; f_equal.
        unfold wk_shiftn, wk_shift; cbn; unfold na in *; lia. }
      assert (Hbeq : sb_eq (ι wk_shiftn (r' + List.length gs' + im_nn Mi') ⨟ (ι wk_shift ⨟ ι wk_shiftn (List.length R))) (ι wk_shiftn n')).
      { intros w; cbn [sb_compose sb_of_wk sentry_sub]; f_equal; unfold wk_shiftn, wk_shift; cbn; rewrite vb_nn; unfold n', na in *; lia. }
      assert (ET : Tc[↑]ʷ[wk_shiftn (List.length R)]ʷ
                   = ptyp_ihty (blocks_motives Bks') (ι wk_shiftn n')
                       (ihs_sub (im_nn Mi') Is' (List.length gs') (cargs_pat gs1') r' ⨟ (ι wk_shift ⨟ ι wk_shiftn (List.length R)))
                       (a_var (nr' + (na - 1 - List.length gs1))) t').
      { unfold Tc; rewrite <- !exp_sub_of_wk, exp_sub_sub, ptyp_ihty_sub, Hx'.
        apply ptyp_ihty_sb_eq; [ exact Hbeq | reflexivity ]. }
      rewrite ET in Hvar.
      (* the container's components' substitution, as the view's instance's *)
      assert (Hmc' := dc_members _ Hc' _ _ Hi').
      pose proof (mc_recs _ _ Hmc' _ _ _ _ _ Hin' Heq') as Hst'.
      destruct (dmv_members _ (dt_mvc _ _ _ HD') _ _ Hi') as (_ & _ & Hmvc').
      pose proof (Hmvc' _ _ Hin') as Hmg; rewrite Heq' in Hmg; apply List.Forall_app in Hmg as [_ Hmg].
      apply List.Forall_cons_iff in Hmg as [Hmt' _]; destruct Hmt' as [HmB HmP].
      assert (Hw1 : sb_eq (ι wk_shift ⨟ ι wk_shiftn (List.length R)) (ι wk_shiftn (nr' - r'))).
      { intros w; cbn [sb_compose sb_of_wk sentry_sub]; f_equal; unfold wk_shiftn, wk_shift; cbn; lia. }
      assert (EA : ptyp_ihty (blocks_motives Bks') (ι wk_shiftn n')
                     (ihs_sub (im_nn Mi') Is' (List.length gs') (cargs_pat gs1') r' ⨟ (ι wk_shift ⨟ ι wk_shiftn (List.length R)))
                     (a_var (nr' + (na - 1 - List.length gs1))) t'
                   = ptyp_ihty (blocks_motives Bks') (ι wk_shiftn n')
                       (ι wk_pat (cargs_pat gs1') ⨟ (sb_qn (List.length gs1 + im_nn Mv) (sb_of_list Id Is) ⨟
                          ((sb_qn (List.length gs1 + nn) (sb_of_list Id Us) ⨟ ι wk_shiftn (na - List.length gs1 + List.length L)) ⨟ δ L)))
                       (a_var (nr' + (na - 1 - List.length gs1))) t').
      { eapply ptyp_ihty_scoped_agree; [ exact Hst' | exact HmB | exact HmP |].
        intros y Hy.
        unfold ihs_sub; rewrite length_cargs_pat, Hlen, vb_nn.
        cbn [sb_compose sb_of_wk sentry_sub].
        rewrite (sentry_sub_sb_eq _ _ _ Hw1).
        assert (Hz : wk_pat (cargs_pat gs1') y < List.length gs1 + nn + List.length Is).
        { pose proof (wk_pat_bound (cargs_pat gs1') (im_np D' Mi') y) as Hb.
          rewrite pat_nargs_cargs_pat, length_cargs_pat, Hlen in Hb.
          specialize (Hb Hy); unfold im_np in Hb; rewrite vb_nn in Hb.
          unfold Is' in HIl; rewrite List.length_map in HIl; unfold ind_nu in *; lia. }
        pose proof (view_rec_sub_agree Is Us L (ind_nu D) nn na (List.length gs1) r' nr' _
                      (decl_closed_head_scoped _ Hc _ _ _ _ _ _ Hm Hh) HUl ltac:(lia) ltac:(lia) Hz) as EZ.
        cbn [sb_compose sb_of_wk sentry_sub] in EZ.
        unfold δ, nvars, avars; rewrite List.app_assoc, vars_from_app.
        fold Is'; exact EZ. }
      rewrite EA in Hvar.
      (* the view's type is a type *)
      pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
      assert (HAA : motives_eq Θ Ξ Γ p D Us (blocks_motives Bks) (blocks_motives Bks) i)
        by (intros j1 Mj1 Hj1; apply wf_exp_eq_refl; exact (HAs _ _ Hj1)).
      destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hmv HΓ HUl Hσ (blocks_mctx_wf _ _ _ _ _ _ _ _ HBt)
                  HAs HAs HAA Hin Heq HΨ) as (j0 & HAj & _).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HAj Hδ) as HT; cbn [exp_sub] in HT.
      rewrite (vb_ihty_view _ _ _ _ _ _ Heq HL) in HT.
      eapply wf_conv; [ exact Hvar | eapply lift_exp_ge; [| exact HT ]; apply (Nat.le_max_l j0 j) |].
      eapply lift_exp_eq_ge; [| apply wf_exp_eq_sym; exact Hj ]; lia.
    Qed.

    (** An argument non-recursive in the container and recursive in the
        view: its recursive result is the group's eliminator at it. *)
    Lemma vb_argrec : forall gs1 t gs2 (E : ctx) (L : list exp),
        gs = gs1 ++ ca_rec t :: gs2 -> List.length L = List.length E ->
        ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ L : E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ ptyp_ih p D (Some p) (List.map (fun U => U[wk_shiftn n']ʷ) Us) (blocks_wk Bks (wk_shiftn n'))
                        (cargs_sub σ0 gs1 avars) (a_var (nr' + (na - 1 - List.length gs1))) t
          : ptyp_ihty (blocks_motives Bks) (ι (wk_shiftn n')) (cargs_sub σ0 gs1 avars) (a_var (nr' + (na - 1 - List.length gs1))) t.
    Proof.
      intros * Heq HL HΨ Hδ.
      destruct vw_facts as (HD & Hc & _).
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
      destruct (vb_rec_arg _ _ _ _ _ Heq HL HΨ Hδ) as (Hσg & Huc & Hx).
      destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HD Hmv Hin Heq) as (Mj & HMj & HPl & HBt0 & HPt0).
      pose proof (ih_tm_typed _ _ _ _ _ _ _ _ _ Hl (or_introl eq_refl) HBt HUl HUs Mv t Δc _ nil (cargs_strat gs1) _ _ Mj
                    vb_wk Hσg Huc HMj HPl HBt0 HPt0 Hx) as H.
      rewrite blocks_sub_of_wk, map_sub_of_wk in H; exact H.
    Qed.

    Lemma vb_avar : forall gs1 g rest, gs = gs1 ++ g :: rest ->
        List.skipn (List.length gs1) avars = a_var (nr' + (na - 1 - List.length gs1)) :: List.skipn (S (List.length gs1)) avars.
    Proof.
      intros * Heq.
      assert (Hlt : List.length gs1 < na) by (rewrite <- vb_na, Heq, List.length_app; cbn; lia).
      apply skipn_nth_cons.
      assert (E : List.length gs1 = na - 1 - (na - 1 - List.length gs1)) by lia.
      rewrite E at 1; unfold avars.
      rewrite (List.nth_error_nth' _ (a_var 0)) by (rewrite length_vars_from; lia).
      rewrite vars_from_nth by lia; reflexivity.
    Qed.

    Lemma vb_cargs_sub_arg : forall gs1 A rest, gs = gs1 ++ ca_arg A :: rest ->
        cargs_sub σ0 (gs1 ++ ca_arg A :: nil) avars = (cargs_sub σ0 gs1 avars ,, a_var (nr' + (na - 1 - List.length gs1))).
    Proof.
      intros * Heq.
      assert (Hlt : List.length gs1 < na) by (rewrite <- vb_na, Heq, List.length_app; cbn; lia).
      pose proof (vb_avar _ _ _ Heq) as Ha.
      rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r.
      rewrite (firstn_S_nth _ _ (a_var (nr' + (na - 1 - List.length gs1)))).
      - apply cargs_sub_snoc_arg; rewrite List.length_firstn; unfold avars; rewrite length_vars_from; lia.
      - rewrite <- (List.firstn_skipn (List.length gs1) avars), Ha, List.nth_error_app2
          by (rewrite List.length_firstn; unfold avars; rewrite length_vars_from; lia).
        rewrite List.length_firstn, Nat.min_l by (unfold avars; rewrite length_vars_from; lia).
        rewrite Nat.sub_diag; reflexivity.
    Qed.

    Lemma vb_cargs_sub_rec : forall gs1 t rest, gs = gs1 ++ ca_rec t :: rest ->
        cargs_sub σ0 (gs1 ++ ca_rec t :: nil) avars = cargs_sub σ0 gs1 avars.
    Proof.
      intros * Heq.
      assert (Hlt : List.length gs1 < na) by (rewrite <- vb_na, Heq, List.length_app; cbn; lia).
      pose proof (vb_avar _ _ _ Heq) as Ha.
      rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r.
      rewrite (firstn_S_nth _ _ (a_var (nr' + (na - 1 - List.length gs1)))).
      - apply cargs_sub_snoc_rec; rewrite List.length_firstn; unfold avars; rewrite length_vars_from; lia.
      - rewrite <- (List.firstn_skipn (List.length gs1) avars), Ha, List.nth_error_app2
          by (rewrite List.length_firstn; unfold avars; rewrite length_vars_from; lia).
        rewrite List.length_firstn, Nat.min_l by (unfold avars; rewrite length_vars_from; lia).
        rewrite Nat.sub_diag; reflexivity.
    Qed.

    (** The recursive results of the view's branch: those after the
        arguments [gs1] and [gs1'] so far. *)
    Lemma vb_ihs : forall rest' rest gs1' gs1 (E : ctx) (L : list exp),
        gs' = gs1' ++ rest' -> gs = gs1 ++ rest -> List.length gs1' = List.length gs1 -> cargs_corr vm rest' rest ->
        List.length E = cargs_nrec gs1 -> List.length L = List.length E ->
        ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ L : E ++ cinst Γ p D Mv Us gs ->
        Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ (L ++ wrap_ihs rest' rest
                              (elim_ihs p D (Some p) (List.map (fun U => U[wk_shiftn n']ʷ) Us) (blocks_wk Bks (wk_shiftn n'))
                                 (cargs_sub σ0 gs1 avars) rest (List.skipn (List.length gs1) avars))
                              (cargs_nrec gs1') nr')
          : ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) rest
              ++ E ++ cinst Γ p D Mv Us gs.
    Proof.
      induction rest' as [| g' rest' IH]; intros [| g rest] gs1' gs1 E L Heq' Heq Hlen Hc HE HL HΨ Hδ; cbn in Hc;
        try contradiction.
      - cbn [wrap_ihs ihs_ctx_aux List.app]; rewrite List.app_nil_r; exact Hδ.
      - destruct g'; contradiction.
      - destruct g' as [A' | t'], g as [A | t]; cbn in Hc; try contradiction.
        + (* both non-recursive *)
          rewrite (vb_avar _ _ _ Heq); cbn [wrap_ihs elim_ihs ihs_ctx_aux].
          rewrite <- (vb_cargs_sub_arg _ _ _ Heq).
          replace (S (List.length gs1)) with (List.length (gs1 ++ ca_arg A :: nil)) by (rewrite List.length_app; cbn; lia).
          replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg A :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
          replace (cargs_nrec gs1') with (cargs_nrec (gs1' ++ ca_arg A' :: nil)) by (rewrite cargs_nrec_snoc; lia).
          apply IH; try assumption.
          * rewrite Heq', <- List.app_assoc; reflexivity.
          * rewrite Heq, <- List.app_assoc; reflexivity.
          * rewrite !List.length_app; cbn; lia.
          * rewrite cargs_nrec_snoc; cbn; lia.
        + (* non-recursive in the container, recursive in the view *)
          destruct vw_facts as (HD & Hc0 & _).
          pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
          pose proof (wf_sub_uparams _ _ _ HD Hc0 _ _ HΓ HUl HUs) as Hσ.
          pose proof (blocks_motives_typed _ _ _ _ _ _ _ _ HBt) as HAs.
          assert (HAA : motives_eq Θ Ξ Γ p D Us (blocks_motives Bks) (blocks_motives Bks) i)
            by (intros j1 Mj1 Hj1; apply wf_exp_eq_refl; exact (HAs _ _ Hj1)).
          destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hmv HΓ HUl Hσ (blocks_mctx_wf _ _ _ _ _ _ _ _ HBt)
                      HAs HAs HAA Hin Heq HΨ) as (j0 & HAj & _).
          pose proof (vb_argrec _ _ _ _ _ Heq HL HΨ Hδ) as Hih.
          rewrite (vb_avar _ _ _ Heq); cbn [wrap_ihs elim_ihs ihs_ctx_aux List.hd List.tl].
          rewrite <- (vb_cargs_sub_rec _ _ _ Heq) at 2.
          replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec t :: nil)) by (rewrite List.length_app; cbn; lia).
          replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec t :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
          replace (cargs_nrec gs1') with (cargs_nrec (gs1' ++ ca_arg A' :: nil)) by (rewrite cargs_nrec_snoc; lia).
          set (ih := ptyp_ih p D (Some p) _ _ _ _ t).
          set (TV := ptyp_ihty (blocks_motives Bks) _ _ _ t) in HAj |- *.
          rewrite <- List.app_assoc; cbn [List.app].
          replace (L ++ ih :: _) with ((L ++ ih :: nil) ++ wrap_ihs rest' rest
             (elim_ihs p D (Some p) (List.map (fun U => U[wk_shiftn n']ʷ) Us) (blocks_wk Bks (wk_shiftn n'))
                (cargs_sub σ0 (gs1 ++ ca_rec t :: nil) avars) rest (List.skipn (List.length (gs1 ++ ca_rec t :: nil)) avars))
             (cargs_nrec (gs1' ++ ca_arg A' :: nil)) nr') by (rewrite <- List.app_assoc; reflexivity).
          change (S (List.length E)) with (List.length (ce_ass TV :: E)).
          change (ce_ass TV :: E ++ cinst Γ p D Mv Us gs) with ((ce_ass TV :: E) ++ cinst Γ p D Mv Us gs).
          apply IH; try assumption.
          * rewrite Heq', <- List.app_assoc; reflexivity.
          * rewrite Heq, <- List.app_assoc; reflexivity.
          * rewrite !List.length_app; cbn; lia.
          * rewrite cargs_nrec_snoc; cbn; lia.
          * rewrite List.length_app; cbn; lia.
          * cbn [List.app]; econstructor; exact HAj.
          * unfold δ; rewrite !List.app_assoc, sb_of_list_app; cbn [sb_of_list].
            rewrite <- !List.app_assoc; fold (δ L).
            eapply wf_sub_extend; [ exact Hδ | exact HAj |].
            unfold TV; rewrite (vb_ihty_view _ _ _ _ _ _ Heq HL); exact Hih.
        + (* recursive in both *)
          destruct Hc as (Hmt & Hdt & Hc).
          destruct vw_facts as (HD & Hc0 & _).
          pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
          pose proof (wf_sub_uparams _ _ _ HD Hc0 _ _ HΓ HUl HUs) as Hσ.
          pose proof (blocks_motives_typed _ _ _ _ _ _ _ _ HBt) as HAs.
          assert (HAA : motives_eq Θ Ξ Γ p D Us (blocks_motives Bks) (blocks_motives Bks) i)
            by (intros j1 Mj1 Hj1; apply wf_exp_eq_refl; exact (HAs _ _ Hj1)).
          destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hmv HΓ HUl Hσ (blocks_mctx_wf _ _ _ _ _ _ _ _ HBt)
                      HAs HAs HAA Hin Heq HΨ) as (j0 & HAj & _).
          pose proof (vb_recrec _ _ _ _ _ _ _ _ Heq' Heq Hlen Hmt Hdt HL HΨ Hδ) as Hih.
          rewrite (vb_avar _ _ _ Heq); cbn [wrap_ihs elim_ihs ihs_ctx_aux List.hd List.tl].
          rewrite <- (vb_cargs_sub_rec _ _ _ Heq).
          replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec t :: nil)) by (rewrite List.length_app; cbn; lia).
          replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec t :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
          replace (S (cargs_nrec gs1')) with (cargs_nrec (gs1' ++ ca_rec t' :: nil)) by (rewrite cargs_nrec_snoc; lia).
          set (TV := ptyp_ihty (blocks_motives Bks) _ _ _ t) in HAj |- *.
          rewrite <- List.app_assoc; cbn [List.app].
          set (x := a_var (nr' - 1 - cargs_nrec gs1')) in Hih |- *.
          replace (L ++ x :: _) with ((L ++ x :: nil) ++ wrap_ihs rest' rest
             (elim_ihs p D (Some p) (List.map (fun U => U[wk_shiftn n']ʷ) Us) (blocks_wk Bks (wk_shiftn n'))
                (cargs_sub σ0 (gs1 ++ ca_rec t :: nil) avars) rest (List.skipn (List.length (gs1 ++ ca_rec t :: nil)) avars))
             (cargs_nrec (gs1' ++ ca_rec t' :: nil)) nr') by (rewrite <- List.app_assoc; reflexivity).
          change (S (List.length E)) with (List.length (ce_ass TV :: E)).
          change (ce_ass TV :: E ++ cinst Γ p D Mv Us gs) with ((ce_ass TV :: E) ++ cinst Γ p D Mv Us gs).
          apply IH; try assumption.
          * rewrite Heq', <- List.app_assoc; reflexivity.
          * rewrite Heq, <- List.app_assoc; reflexivity.
          * rewrite !List.length_app; cbn; lia.
          * rewrite cargs_nrec_snoc; cbn; lia.
          * rewrite List.length_app; cbn; lia.
          * cbn [List.app]; econstructor; exact HAj.
          * unfold δ; rewrite !List.app_assoc, sb_of_list_app; cbn [sb_of_list].
            rewrite <- !List.app_assoc; fold (δ L).
            eapply wf_sub_extend; [ exact Hδ | exact HAj |].
            unfold TV; rewrite (vb_ihty_view _ _ _ _ _ _ Heq HL); exact Hih.
    Qed.

    (** The view's branch's context, instantiated in the container's
        ([wrap_br]). *)
    Lemma vb_sub : Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ (wrap_ihs gs' gs
                                     (elim_ihs p D (Some p) (List.map (fun U => U[wk_shiftn n']ʷ) Us) (blocks_wk Bks (wk_shiftn n'))
                                        σ0 gs avars) 0 nr')
                      : elim_bctx p D Mv gs (blocks_motives Bks) Us ++ Γ.
    Proof.
      destruct vw_facts as (HD & Hc & _).
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
      pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
      destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hmv HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
      assert (Hδ : Θ ⍮ Ξ ⍮ Δc ⊢ˢ δ nil : nil ++ cinst Γ p D Mv Us gs)
        by (unfold δ; rewrite List.app_nil_r, cinst_ctel; exact vb_base).
      pose proof (vb_ihs gs' gs nil nil nil nil eq_refl eq_refl eq_refl Hcorr eq_refl eq_refl Hi Hδ) as H.
      cbn [List.app List.length cargs_sub List.skipn cargs_nrec] in H.
      replace (cargs_pat nil) with (@nil bool) in H by reflexivity.
      unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
    Qed.

    (** The view's branch's type, instantiated: the motive at the view's
        constructor applied to the container's branch's variables. *)
    Lemma vb_bty_view : forall A (W : list exp), List.length W = cargs_nrec gs ->
        (elim_bty p v Mv c gs A Us)[δ W]
        = A[sb_of_list (ι (wk_shiftn n'))
              (nvars ++ apps (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                              (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us) ++ nvars ++ avars) :: nil)].
    Proof.
      intros * HW.
      destruct vw_facts as (HD & Hc & _).
      assert (Hm' : nn + List.length gs + cargs_nrec gs = nn + na + List.length W) by (rewrite vb_na, HW; lia).
      assert (Hvn : List.map (fun M => M[δ W]) (vars_from (cargs_nrec gs + List.length gs) nn) = nvars).
      { unfold δ; replace (vars_from (cargs_nrec gs + List.length gs) nn) with (vars_from (List.length (avars ++ W)) (List.length nvars))
          by (unfold nvars, avars; rewrite List.length_app, !length_vars_from, vb_na, HW; f_equal; lia).
        apply vars_from_sb_of_list_app. }
      assert (Hva : List.map (fun M => M[δ W]) (vars_from (cargs_nrec gs) (List.length gs)) = avars).
      { unfold δ; replace (vars_from (cargs_nrec gs) (List.length gs)) with (vars_from (List.length W) (List.length avars))
          by (unfold avars; rewrite length_vars_from, vb_na, HW; reflexivity).
        apply vars_from_sb_of_list_mid. }
      unfold elim_bty; fold nn; rewrite exp_sub_sub; apply exp_sub_sb_eq.
      etransitivity; [ apply sb_of_list_compose_gen |].
      etransitivity; [ apply sb_of_list_cong; rewrite Hm'; apply vb_shift; reflexivity |].
      rewrite List.map_app; cbn [List.map]; rewrite apps_exp_sub, !List.map_app; cbn [exp_sub].
      rewrite (im_pre_sub D v Mv) by (try assumption; rewrite List.length_map; exact HUl).
      rewrite List.map_map, Hvn, Hva.
      replace (List.map (fun x => x[wk_shiftn (nn + List.length gs + cargs_nrec gs)]ʷ[δ W]) Us)
        with (List.map (fun U => U[wk_shiftn n']ʷ) Us); [ reflexivity |].
      apply List.map_ext; intros U; rewrite <- !exp_sub_of_wk, exp_sub_sub; apply exp_sub_sb_eq.
      rewrite Hm'; symmetry; apply vb_shift; reflexivity.
    Qed.

    Lemma vb_bty_cont : forall A,
        elim_bty qc i' Mi' c gs' A Is'
        = A[sb_of_list (ι (wk_shiftn n'))
              (nvars ++ apps (a_con (fst (im_ref qc i' Mi')) (snd (im_ref qc i' Mi')) c)
                              (im_pre Mi' (List.map (fun U => U[wk_shiftn n']ʷ) Is') ++ nvars ++ avars) :: nil)].
    Proof. intros; unfold elim_bty; rewrite vb_nn; reflexivity. Qed.

    (** At a container's member that is itself a view, the view's
        constructor applied is the container's: the view's instance of the
        container's container is the container's instance, by the view
        equation ([dt_view_view_is]). *)
    Lemma vb_con_conv : forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
        let T := ind_mty qc D' i' (List.map (fun U => U[ι (wk_shiftn n')]) Is') nvars in
        Θ ⍮ Ξ ⍮ Δc ⊢ apps (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                        (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us) ++ nvars ++ avars) : T /\
        Θ ⍮ Ξ ⍮ Δc ⊢ apps (a_con (fst (im_ref qc i' Mi')) (snd (im_ref qc i' Mi')) c)
                        (im_pre Mi' (List.map (fun U => U[wk_shiftn n']ʷ) Is') ++ nvars ++ avars)
                   ≈ apps (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                        (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us) ++ nvars ++ avars) : T.
    Proof.
      intros * Hhi T.
      destruct vw_facts as (HD & Hc & HD' & Hc' & HIl & HIs).
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin; pose proof (cons_lookup_in _ _ _ Hcon') as Hin'.
      pose proof vb_ctx as HΔ.
      destruct (dt_view _ _ _ HD' _ _ _ _ _ _ Hi' Hhi) as (D'' & Mk'' & Hl'' & Hk'' & Hlt'' & HIl'' & _ & Hself'' & _).
      destruct (dt_view_view _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hhi Hv) as (Mv0 & X & vm' & Hmv0 & Hhv & HXl).
      rewrite Hmv in Hmv0; injection Hmv0 as <-.
      pose proof (HDs _ _ Hl'') as HD''; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl'') as Hc''.
      set (Usw := List.map (fun U => U[wk_shiftn n']ʷ) Us) in *.
      set (Isw := List.map (fun U => U[wk_shiftn n']ʷ) Is') in *.
      pose proof vb_wkw as Hw.
      pose proof (uparams_wk_typed _ _ _ _ _ _ _ Hc Hw HUs) as HUsw; fold Usw in HUsw.
      pose proof (uparams_wk_typed _ _ _ _ _ _ _ Hc' Hw HIs) as HIsw; fold Isw in HIsw.
      assert (HUlw : List.length Usw = ind_nu D) by (unfold Usw; rewrite List.length_map; exact HUl).
      assert (HIlw : List.length Isw = ind_nu D') by (unfold Isw; rewrite List.length_map; exact HIl).
      assert (HNl : List.length nvars = im_nn Mv) by (unfold nvars; apply length_vars_from).
      assert (HNl' : List.length nvars = im_nn Mi') by (rewrite vb_nn; exact HNl).
      assert (HAl : List.length avars = List.length gs) by (unfold avars; rewrite length_vars_from, vb_na; reflexivity).
      assert (HAl' : List.length avars = List.length gs') by (unfold avars; rewrite length_vars_from; reflexivity).
      (* the two constructors' parameters and arguments, at the container's container *)
      destruct (ctel_args_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc Hmv Hin HUl HNl HAl vb_base) as [HNv HAv].
      destruct (ctel_args_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc' Hi' Hin' HIl HNl' HAl' vb_base_c) as [HNc HAc].
      fold Usw in HNv, HAv; fold Isw in HNc, HAc.
      destruct (view_con_inst_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hmv Hhv Hcon HΔ HUlw HUsw HNl HNv HAl HAv)
        as [D3 Mk3 gs3 Hl3 Hk3 Hlt3 Hcon3 HPl3 HAl3 HPs3 HAs3].
      destruct (view_con_inst_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl' Hi' Hhi Hcon' HΔ HIlw HIsw HNl' HNc HAl' HAc)
        as [D4 Mk4 gs4 Hl4 Hk4 Hlt4 Hcon4 HPl4 HAl4 HPs4 HAs4].
      rewrite Hl4 in Hl3; injection Hl3 as <-; rewrite Hk4 in Hk3; injection Hk3 as <-; rewrite Hcon4 in Hcon3; injection Hcon3 as <-.
      rewrite Hl'' in Hl4; injection Hl4 as <-; rewrite Hk'' in Hk4; injection Hk4 as <-.
      (* the instances, equal by the view equation *)
      pose proof (wf_uparams_sub _ _ _ _ _ HD HΔ HUlw HUsw) as Hσw.
      pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ Hm Hh) as HsIs.
      pose proof (decl_closed_head_scoped _ Hc' _ _ _ _ _ _ Hi' Hhi) as HsIs''.
      assert (EIs : List.map (fun I => I[sb_of_list Id Usw]) Is = Isw).
      { unfold Usw; rewrite <- map_sub_of_wk, (inst_sub_comm Is Us (ind_nu D)) by assumption.
        unfold Isw, Is'; rewrite List.map_map; apply List.map_ext; intros; apply exp_sub_of_wk. }
      assert (EIs'' : List.map (fun I => I[sb_of_list Id Is][sb_of_list Id Usw]) Is''
                      = List.map (fun I => I[sb_of_list Id Isw]) Is'').
      { apply List.map_ext_in; intros I HI; rewrite exp_sub_sub.
        eapply exp_scoped_sub_agree; [ exact (proj1 (List.Forall_forall _ _) HsIs'' I HI) |].
        intros y Hy; cbn [sb_compose]; rewrite sb_of_list_lt_compose by (unfold Is' in HIl; rewrite List.length_map in HIl; lia).
        rewrite EIs; reflexivity. }
      set (Ps := List.map (fun I => I[sb_of_list Id Isw]) Is'' ++ nvars) in *.
      set (Ps' := List.map (fun I => I[sb_of_list Id Usw]) X ++ nvars) in *.
      assert (HPP : forall j N N' T0, nth_error Ps j = Some N -> nth_error Ps' j = Some N' ->
                 nth_error (tele_insts (im_params D'' Mk'') Id Ps) j = Some T0 -> Θ ⍮ Ξ ⍮ Δc ⊢ N ≈ N' : T0).
      { intros j N N' T0 HN HN' HT.
        assert (HlIs : List.length (List.map (fun I => I[sb_of_list Id Isw]) Is'') = ind_nu D'')
          by (rewrite List.length_map; exact HIl'').
        assert (HlX : List.length (List.map (fun I => I[sb_of_list Id Usw]) X) = ind_nu D'')
          by (rewrite List.length_map, HXl; exact HIl'').
        destruct (Nat.lt_ge_cases j (ind_nu D'')) as [Hj | Hj].
        - unfold Ps, Ps' in *.
          rewrite List.nth_error_app1 in HN, HN' by lia.
          unfold im_params in HT; rewrite tele_insts_app in HT by (try exact (dc_ass _ Hc''); exact HlIs).
          rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (dc_ass _ Hc''); rewrite HlIs; unfold ind_nu in *; lia).
          apply nth_error_map_inv in HN' as (C & HC & ->).
          rewrite <- EIs'' in HN, HT.
          rewrite <- (List.map_map (fun I => I[sb_of_list Id Is]) (fun M => M[sb_of_list Id Usw])) in HN, HT.
          rewrite <- (tele_insts_sub (ind_uparams D'') 0 Id Id (sb_of_list Id Usw) _ (dc_ass _ Hc'') (dc_uparams _ Hc'')
                        ltac:(intros; lia)) in HT.
          rewrite <- (tele_insts_sub (ind_uparams D'') 0 Id Id (sb_of_list Id Is) _ (dc_ass _ Hc'') (dc_uparams _ Hc'')
                        ltac:(intros; lia)) in HT.
          apply nth_error_map_inv in HN as (C1 & HC1 & ->); apply nth_error_map_inv in HC1 as (C0 & HC0 & ->).
          apply nth_error_map_inv in HT as (T1 & HT1 & ->); apply nth_error_map_inv in HT1 as (T2 & HT2 & ->).
          assert (HC1' : nth_error (List.map (fun I => I[sb_of_list Id Is]) Is'') j = Some C0[sb_of_list Id Is])
            by (rewrite List.nth_error_map, HC0; reflexivity).
          pose proof (dt_view_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        Hm Hh Hl' Hi' Hhi Hl'' Hv Hmv Hhv HC HC1' HT2) as HE.
          apply wf_exp_eq_sym; exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HE Hσw).
        - unfold Ps, Ps' in *.
          rewrite List.nth_error_app2 in HN, HN' by lia; rewrite HlIs in HN; rewrite HlX in HN'.
          rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl.
          apply (HPs4 j); [ rewrite List.nth_error_app2 by lia; rewrite HlIs; exact HN | exact HT ]. }
      assert (HAA : forall j N N' T0, nth_error avars j = Some N -> nth_error avars j = Some N' ->
                 nth_error (tele_insts (cargs_ctx q'' D'' Mk'' gs4) (sb_of_list Id Ps) avars) j = Some T0 ->
                 Θ ⍮ Ξ ⍮ Δc ⊢ N ≈ N' : T0).
      { intros j N N' T0 HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HAs4 j N T0 HN HT). }
      (* the constructors, and their types *)
      pose proof (con_apps_conv _ _ _ _ _ _ _ _ _ Ps Ps' avars avars Hg HDs Hl'' Hk'' Hlt'' Hcon4 HΔ HPl4 HPl3 HAl4 HAl3
                    HPs4 HPs3 HPP HAs4 HAs3 HAA) as Hcc.
      pose proof (wf_con_apps_decl _ _ _ _ _ _ _ _ _ Ps' avars Hg HDs Hl'' Hk'' Hlt'' Hcon4 HΔ HPl3 HPs3 HAl3 HAs3) as HcV.
      destruct (ind_apps_conv_large _ _ _ _ _ _ _ _ _ Hg HDs Hl'' Hk'' Hlt'' HΔ HPl4 HPl3 HPs4 HPs3 HPP) as (j & Hj1 & Hj2 & Hj3).
      destruct (member_lt_decl _ _ _ _ _ HD'' Hk'' Hlt'') as [pm Hpm].
      assert (Emty : forall L, ind_mty q'' D'' k'' (List.firstn (ind_nu D'') L) (List.skipn (ind_nu D'') L) = apps (a_ind q'' k'') L).
      { intros L; unfold ind_mty; rewrite Hk''; unfold im_ty_at, im_ref, im_pre; rewrite Hpm; cbn [fst snd].
        rewrite List.firstn_skipn; reflexivity. }
      assert (ET : T = apps (a_ind q'' k'') Ps).
      { unfold T, ind_mty; rewrite Hi'; unfold im_ty_at, im_ref, im_pre; rewrite Hhi; cbn [fst snd].
        rewrite map_sub_of_wk; reflexivity. }
      rewrite Emty in Hcc, HcV.
      unfold im_ref, im_pre; rewrite Hhi, Hhv; cbn [fst snd]; fold Isw.
      rewrite !List.app_assoc; fold Ps Ps'; rewrite ET.
      split.
      - eapply wf_conv; [ exact HcV | exact Hj1 | apply wf_exp_eq_sym; exact Hj3 ].
      - exact Hcc.
    Qed.

    (** The container's branch: the view's, its context instantiated, of
        the type of the container's branch. *)
    Lemma vb_branch : forall b n B, nth_error Bks v = Some b -> brs_lookup (eb_brs b) c = Some (n, B) ->
        Θ ⍮ Ξ ⍮ Δc ⊢ snd (wrap_br p D Us Bks Mv (eb_brs b) c gs') : elim_bty qc i' Mi' c gs' (eb_motive b) Is'.
    Proof.
      intros * Hb HBl.
      destruct vw_facts as (HD & Hc & HD' & Hc' & HIl & HIs).
      pose proof (brs_lookup_in _ _ _ _ HBl) as HinB.
      pose proof (bt_brs _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ Hmv Hb Hcon HinB) as HB.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB vb_sub) as HBτ.
      rewrite vb_bty_view in HBτ by (apply length_wrap_ihs with (vm := vm); exact Hcorr).
      unfold wrap_br; cbv zeta; rewrite Hcon, HBl; cbn [snd].
      rewrite vb_bty_cont.
      fold nn na nr' n' nvars avars; fold (σ0); fold (δ (wrap_ihs gs' gs (elim_ihs p D (Some p) (List.map (fun U => U[wk_shiftn n']ʷ) Us)
                                                                 (blocks_wk Bks (wk_shiftn n')) σ0 gs avars) 0 nr')).
      destruct (im_head Mi') as [pm | q'' k'' Is'' vm''] eqn:Hhi.
      - (* a declared member of the container: the same constructor *)
        destruct (dt_view_decl _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hhi Hv) as (Mv0 & vm' & Hmv0 & Hhv).
        rewrite Hmv in Hmv0; injection Hmv0 as <-.
        replace (apps (a_con (fst (im_ref qc i' Mi')) (snd (im_ref qc i' Mi')) c)
                   (im_pre Mi' (List.map (fun U => U[wk_shiftn n']ʷ) Is') ++ nvars ++ avars))
          with (apps (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                  (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us) ++ nvars ++ avars)); [ exact HBτ |].
        unfold im_ref, im_pre; rewrite Hhi, Hhv; cbn [fst snd]; do 2 f_equal.
        pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ Hm Hh) as HsIs.
        rewrite <- map_sub_of_wk, (inst_sub_comm Is Us (ind_nu D)) by assumption.
        unfold Is'; rewrite !List.map_map; apply List.map_ext; intros; apply exp_sub_of_wk.
      - (* a view: the constructors equal *)
        pose proof (vb_con_conv _ _ _ _ Hhi) as Hcv; cbv zeta in Hcv; destruct Hcv as [HcV Hcc].
        set (conV := apps (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                       (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us) ++ nvars ++ avars)) in *.
        set (conC := apps (a_con (fst (im_ref qc i' Mi')) (snd (im_ref qc i' Mi')) c)
                       (im_pre Mi' (List.map (fun U => U[wk_shiftn n']ʷ) Is') ++ nvars ++ avars)) in *.
        pose proof (vw_motives_typed _ _ Hi') as HA.
        unfold Bks' in HA; rewrite (vwrap_motive_nth _ _ _ _ _ _ _ _ _ _ Hi' Hv Hb ltac:(eauto)) in HA.
        assert (HM : forall j Mj, ind_member D' j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx qc D' j Mj Is' ++ Γ)
          by (intros j Mj Hj; exact (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl' Hj HΓ HIl HIs)).
        pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl' Hi' HΓ HIl HIs HM vw_motives_typed Hcon') as Hρc.
        rewrite vb_nn in Hρc; fold na nr' n' nvars avars conC in Hρc.
        fold Δc in Hρc.
        assert (HNl : List.length nvars = im_nn Mi') by (unfold nvars; rewrite length_vars_from, vb_nn; reflexivity).
        assert (Hlen : forall x, List.length (nvars ++ x :: nil) = List.length (elim_mctx qc D' i' Mi' Is'))
          by (intros; rewrite List.length_app, length_elim_mctx, HNl; cbn; lia).
        pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_mctx_ass _ _ _ _ Is' Hc' Hi') (Hlen conC) Hρc) as HMs.
        pose proof (fun x => elim_mctx_insts qc D' i' Mi' Is' (ι wk_shiftn n') nvars x Hc' Hi' HIl HNl) as E.
        assert (Hl2 : List.length (tele_insts (im_nparams Mi') (sb_of_list Id Is' ⨟ ι wk_shiftn n') nvars) = im_nn Mi')
          by (rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption); rewrite HNl; unfold im_nn; lia).
        assert (Hσ : Θ ⍮ Ξ ⍮ Δc ⊢ˢ sb_of_list (ι wk_shiftn n') (nvars ++ conC :: nil) ≈ sb_of_list (ι wk_shiftn n') (nvars ++ conV :: nil)
                       : elim_mctx qc D' i' Mi' Is' ++ Γ).
        { eapply wf_sub_eq_of_list_left;
            [ exact (elim_mctx_ass _ _ _ _ _ Hc' Hi') | exact (HM _ _ Hi') | apply wf_sub_eq_refl, vb_wk
            | exact (Hlen conC) | exact (Hlen conV) | exact HMs | |].
          - intros k N T0 HN HT; rewrite E in HT.
            destruct (Nat.lt_ge_cases k (im_nn Mi')) as [Hk | Hk].
            + rewrite List.nth_error_app1 in HN by lia.
              apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite E; exact HT ].
            + rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
              rewrite HNl in HN; rewrite Hl2 in HT.
              destruct (k - im_nn Mi') as [| k0] eqn:Hk0; cbn in HN, HT; [| destruct k0; discriminate ].
              injection HN as <-; injection HT as <-; exact HcV.
          - intros k N N' T0 HN HN' HT; rewrite E in HT.
            destruct (Nat.lt_ge_cases k (im_nn Mi')) as [Hk | Hk].
            + rewrite List.nth_error_app1 in HN, HN' by lia; rewrite HN in HN'; injection HN' as <-.
              apply wf_exp_eq_refl; apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite E; exact HT ].
            + rewrite List.nth_error_app2 in HN, HN' by lia; rewrite List.nth_error_app2 in HT by lia.
              rewrite HNl in HN, HN'; rewrite Hl2 in HT.
              destruct (k - im_nn Mi') as [| k0] eqn:Hk0; cbn in HN, HN', HT; [| destruct k0; discriminate ].
              injection HN as <-; injection HN' as <-; injection HT as <-; exact Hcc. }
        pose proof (sub_eq_preserves_exp _ _ _ _ _ HA _ _ _ Hσ) as Heq; cbn [exp_sub] in Heq.
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hρc) as Hty; cbn [exp_sub] in Hty.
        eapply wf_conv; [ exact HBτ | exact Hty | apply wf_exp_eq_sym; exact Heq ].
    Qed.

  End ViewBranch.

  Lemma cons_lookup_of_nodup : forall cs c gs, List.NoDup (List.map fst cs) -> List.In (c, gs) cs -> cons_lookup cs c = Some gs.
  Proof.
    induction cs as [| [c' gs'] cs IH]; intros * Hnd Hin; [ destruct Hin |]; destruct Hin as [[= <- <-] | Hin]; cbn.
    - rewrite String.eqb_refl; reflexivity.
    - inversion Hnd as [| ? ? Hn Hnd']; subst.
      destruct (String.eqb_spec c c') as [<- |]; [| apply IH; assumption ].
      exfalso; apply Hn, (List.in_map fst _ (c, gs)), Hin.
  Qed.

  Lemma brs_lookup_of_names : forall cs (Bs : list (String.string * nat * exp)) c,
      brs_names cs Bs -> List.In c (List.map fst cs) -> exists n B, brs_lookup Bs c = Some (n, B).
  Proof.
    unfold brs_names; intros * Hn Hc; rewrite Hn in Hc; clear Hn.
    induction Bs as [| [[c' n'] B'] Bs IH]; cbn in Hc |- *; [ destruct Hc |].
    destruct (String.eqb_spec c c') as [-> | Hne]; [ eauto |].
    destruct Hc as [-> | Hc]; [ congruence | exact (IH Hc) ].
  Qed.

  (** The container's blocks are typed at the view's instance. *)
  Lemma vw_blocks_typed : blocks_typed Θ Ξ Γ qc D' Is' Bks' i.
  Proof.
    destruct vw_facts as (HD & Hc & HD' & Hc' & HIl & HIs).
    assert (HM : forall j Mj, ind_member D' j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx qc D' j Mj Is' ++ Γ)
      by (intros j Mj Hj; exact (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl' Hj HΓ HIl HIs)).
    pose proof (wf_sub_uparams _ _ _ HD' Hc' _ _ HΓ HIl HIs) as Hσ.
    (* the block of a member: the view's member's, wrapped *)
    assert (Hblk : forall k Mk b', ind_member D' k = Some Mk -> List.nth_error Bks' k = Some b' ->
               exists v Mv b, List.nth_error vm k = Some v /\ ind_member D v = Some Mv /\ List.nth_error Bks v = Some b /\
                 im_nn Mv = im_nn Mk /\ List.map fst (im_cons Mv) = List.map fst (im_cons Mk) /\
                 (forall c gs' gs, In (c, gs') (im_cons Mk) -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs) /\
                 b' = eb_mk (eb_nm b) None (eb_motive b)
                        (List.map (fun cg => wrap_br p D Us Bks Mv (eb_brs b) (fst cg) (snd cg)) (im_cons Mk))).
    { intros * Hk Hb'.
      destruct (vw_member _ _ Hk) as (v & Mv & b & Hv & Hmv & Hb & Hnn & Hnames & Hcorr).
      unfold Bks' in Hb'; rewrite (nth_error_vwrap _ _ _ _ _ _ _ _ Hk) in Hb'; injection Hb' as <-.
      exists v, Mv, b; repeat split; try assumption.
      exact (vwrap_block_eq _ _ _ _ _ _ _ _ _ _ Hv Hb Hmv). }
    constructor.
    - unfold Bks'; apply length_vwrap.
    - intros k Mk b' Hk Hb'.
      destruct (Hblk _ _ _ Hk Hb') as (v & Mv & b & Hv & Hmv & Hb & Hnn & _ & _ & ->); cbn.
      rewrite (bt_nm _ _ _ _ _ _ _ _ HBt _ _ _ Hmv Hb), Hnn; reflexivity.
    - intros k Mk b' Z Hk Hb' HZ.
      destruct (Hblk _ _ _ Hk Hb') as (v & Mv & b & _ & _ & _ & _ & _ & _ & ->); discriminate.
    - intros k Mk b' Hk Hb'.
      pose proof (vw_motives_typed _ _ Hk) as H; rewrite (blocks_motives_nth _ _ _ Hb') in H; exact H.
    - intros k Mk Hk; apply ctx_ext_refl; [ eapply elim_mctx_ass; eassumption | exact (HM _ _ Hk) ].
    - intros k Mk b' Hk Hb'.
      destruct (Hblk _ _ _ Hk Hb') as (v & Mv & b & _ & _ & _ & _ & _ & _ & ->); cbn [eb_brs].
      unfold brs_names; rewrite List.map_map; apply List.map_ext; intros [c gs']; reflexivity.
    - intros k Mk c gs' Hk Hcon'; apply ctx_ext_refl; [ eapply elim_bctx_ass; eassumption |].
      eapply elim_bctx_wf; [ exact Hg | exact HDs | exact Hl' | exact Hk | exact HΓ | exact HIl | exact Hσ | exact HM
                           | exact vw_motives_typed | exact Hcon' ].
    - intros k Mk b' c gs' n B' Hk Hb' Hcon' Hin.
      destruct (Hblk _ _ _ Hk Hb') as (v & Mv & b & _ & _ & _ & Hnn & _ & _ & ->); cbn [eb_brs] in Hin.
      apply List.in_map_iff in Hin as ([c0 gs0] & Hw & Hin0); cbn [fst snd] in Hw.
      unfold wrap_br in Hw; cbv zeta in Hw; injection Hw as <- <- _.
      unfold ind_con in Hcon'; rewrite (cons_lookup_of_nodup _ _ _ (dt_nodup _ _ _ HD' _ _ Hk) Hin0) in Hcon'; injection Hcon' as <-.
      rewrite Hnn; lia.
    - intros k Mk b' c gs' n B' Hk Hb' Hcon' Hin.
      destruct (Hblk _ _ _ Hk Hb') as (v & Mv & b & Hv & Hmv & Hb & Hnn & Hnames & Hcorr & ->); cbn [eb_brs eb_motive] in Hin |- *.
      apply List.in_map_iff in Hin as ([c0 gs0] & Hw & Hin0); cbn [fst snd] in Hw.
      assert (Ec : c0 = c) by (unfold wrap_br in Hw; cbv zeta in Hw; injection Hw as <- _ _; reflexivity); subst c0.
      pose proof (cons_lookup_of_nodup _ _ _ (dt_nodup _ _ _ HD' _ _ Hk) Hin0) as Hcon0.
      unfold ind_con in Hcon'; rewrite Hcon0 in Hcon'; injection Hcon' as <-.
      assert (HcMv : exists gs, ind_con Mv c = Some gs).
      { assert (Hc0 : List.In c (List.map fst (im_cons Mv))) by (rewrite Hnames; exact (List.in_map fst _ _ Hin0)).
        apply List.in_map_iff in Hc0 as ([c1 gs1] & Hc1 & Hin1); cbn in Hc1; subst c1.
        exact (cons_lookup_of_in _ _ _ Hin1). }
      destruct HcMv as [gs Hcmv].
      destruct (brs_lookup_of_names _ _ c (bt_names _ _ _ _ _ _ _ _ HBt _ _ _ Hmv Hb)
                  ltac:(rewrite Hnames; exact (List.in_map fst _ _ Hin0))) as (n0 & B0 & HBl).
      replace B' with (snd (wrap_br p D Us Bks Mv (eb_brs b) c gs0)) by (rewrite Hw; reflexivity).
      exact (vb_branch _ _ _ _ _ _ _ Hk Hv Hmv Hcon0 Hcmv (Hcorr _ _ _ Hin0 Hcmv) _ _ _ Hb HBl).
  Qed.
End ViewBlocks.

(** ** The Right-Hand Side of [wf_exp_eq_elim_view]

    The container's eliminator at the container's member, its blocks the
    group's wrapped, is of the type of the eliminator at the view: the
    container's blocks are typed at the view's instance, and the block of
    the container's member is the view's block, whose motive the type is
    of.  The lemma takes the rule's premises. *)
Lemma wf_elim_view_rhs : forall Θ Ξ Γ p D oq m Mm qc k' Is vm D' Bks bm Ps M i,
    ind_lookup Θ Ξ p = Some D ->
    elim_grp D oq p m ->
    ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm ->
    ind_lookup Θ Ξ qc = Some D' ->
    vwrap_ok D D' vm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim (Some qc) (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
                  (vwrap p D D' vm (List.firstn (ind_nu D) Ps) Bks) M
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hgr Hm Hh Hl' Hvw Hbm HlB HPl HPs HM Hnm HZ HA HΨ Hn HΨB Hk HB.
  pose proof (presup_exp_ctx HM) as HΓ.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (HDs _ _ Hl') as HD'; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hm HPl HPs) as [HUs HNs].
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  assert (HBt : blocks_typed Θ Ξ Γ p D Us Bks i) by (constructor; assumption).
  pose proof (vw_blocks_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt) as HBt'.
  destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D0 & Mk' & Hl0 & Hk' & Hlt' & HIl & _ & Hself & _).
  rewrite Hl' in Hl0; injection Hl0 as <-.
  set (Is' := List.map (fun I => I[sb_of_list Id Us]) Is) in *.
  assert (HIl' : List.length Is' = ind_nu D') by (unfold Is'; rewrite List.length_map; exact HIl).
  (* the container's parameters at the view's instance *)
  destruct (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ Us Ns Hg Hl HDs HD Hc Hc' Hm Hh Hl' Hk' Hself HIl HΓ HUl HUs HNl HNs)
    as [HNl' HPs'].
  fold Is' in HPs'.
  replace (im_pre Mm Us) with Is' by (unfold im_pre; rewrite Hh; reflexivity).
  assert (HPl' : List.length (Is' ++ Ns) = im_np D' Mk') by (rewrite List.length_app, HIl', HNl'; unfold im_np; lia).
  destruct (params_typed_split _ _ D' Hc' _ _ Γ (Is' ++ Ns) Hk' HPl' HPs') as [HIs' HNs'].
  rewrite firstn_app_len in HIs', HNs' by exact HIl'; rewrite skipn_app_len in HNs' by exact HIl'.
  (* the container's block of its member: the view's *)
  pose proof (nth_error_vwrap p D D' vm Us Bks _ _ Hk') as Hb'.
  pose proof (vwrap_block_eq p D vm Us Bks k' Mk' _ _ _ Hself Hbm Hm) as Eb'.
  (* the scrutinee, of the container's member's type *)
  assert (HM' : Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty qc D' k' Is' Ns).
  { destruct (member_lt_decl _ _ _ _ _ HD' Hk' Hlt') as [pm Hpm].
    replace (ind_mty qc D' k' Is' Ns) with (ind_mty p D m Us Ns); [ exact HM |].
    unfold ind_mty; rewrite Hm, Hk'; unfold im_ty_at, im_ref, im_pre; rewrite Hh, Hpm; reflexivity. }
  pose proof (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl' (or_introl eq_refl) Hk' Hb' HBt'
                HIl' HIs' HNl' HNs' HM') as H.
  rewrite Eb' in H; cbn [eb_motive] in H; exact H.
Qed.
