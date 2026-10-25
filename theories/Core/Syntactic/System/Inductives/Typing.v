(** * The Contexts of the Eliminator Are Well Formed

    What the typing rules of groups of inductive types state as premises
    about the contexts of the motives and of the branches, and about the
    instances of those contexts, follows from the typing of the parameters
    and the validity of the groups in scope: the parameters' variables are
    of the types of the parameters, the motives' instances at the recursive
    arguments are substitutions into the motives' contexts, a constructor
    applies to terms of its arguments' types, and the recursive results are
    eliminations.  These are what presupposition of the eliminator's
    equations and the checker need. *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Lemmas.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Groups in Scope *)

Lemma decls_of_ctx : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> decls_typed Θ Ξ.
Proof. intros * HΓ pq D Hl; exact (gv_decls _ _ _ _ _ _ (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl). Qed.

Lemma decl_of_lookup : forall Θ Ξ Γ p D,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D -> decl_typed Θ Ξ D /\ decl_closed D.
Proof.
  intros * HΓ Hl; split; [ exact (decls_of_ctx _ _ _ HΓ _ _ Hl) |].
  exact (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HΓ) Hl).
Qed.

(** A constructor is typed at its type without the shape premise of
    [wf_con]: that premise follows from the groups in scope. *)
Lemma wf_con_of_lookup : forall Θ Ξ Γ p D k M c gs i,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some M ->
    ind_con M c = Some gs ->
    ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D M gs ++ im_params D M ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D k M gs : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_con p k c : con_ty p D k M gs.
Proof.
  intros * HΓ Hl Hk Hcon HΨ Hty.
  eapply wf_con; try eassumption.
  exact (shape_rest_wf' _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ) Hl Hk Hcon).
Qed.

#[export]
Hint Resolve wf_con_of_lookup : mctt.

(** ** Closed Telescopes Under a Context *)

Lemma wf_ctx_closed_app : forall Θ Ξ Δ Γ,
    tele_ass Δ -> ctx_scoped 0 Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ.
Proof.
  intros * Hass Hs HΔ HΓ.
  assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ Δ ++ ⋅) by (rewrite List.app_nil_r; exact HΔ).
  pose proof (wf_wk_shiftn_app Θ Ξ Γ ⋅) as Hw; rewrite List.app_nil_r in Hw.
  specialize (Hw HΓ ltac:(constructor; eapply ctx_wf_gctx; eassumption)).
  pose proof (wk_preserves_ext _ _ _ _ _ _ _ (ctx_ext_refl _ _ _ _ Hass HΔ0) Hw) as Hx.
  rewrite tele_closed_wk in Hx by exact Hs; eapply ext_eq_ctx_left; exact Hx.
Qed.

Lemma wf_exp_closed_app : forall Θ Ξ Δ Γ M A,
    tele_ass Δ -> ctx_scoped 0 Δ -> exp_scoped (List.length Δ) M -> exp_scoped (List.length Δ) A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A.
Proof.
  intros * Hass Hs HsM HsA HM HΓ.
  assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ Δ ++ ⋅) by (rewrite List.app_nil_r; eapply presup_exp_ctx; exact HM).
  pose proof (wf_wk_shiftn_app Θ Ξ Γ ⋅) as Hw; rewrite List.app_nil_r in Hw.
  specialize (Hw HΓ ltac:(constructor; eapply ctx_wf_gctx; eassumption)).
  assert (HΔΓ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ) by (apply wf_ctx_closed_app; try assumption; rewrite List.app_nil_r in HΔ0; exact HΔ0).
  pose proof (wf_wk_ext _ _ Δ _ _ _ Hw) as Hq.
  rewrite tele_closed_wk in Hq by exact Hs; specialize (Hq HΔΓ HΔ0).
  assert (HM0 : Θ ⍮ Ξ ⍮ Δ ++ ⋅ ⊢ M : A) by (rewrite List.app_nil_r; exact HM).
  pose proof (wk_preserves_exp _ _ _ _ _ _ _ HM0 Hq) as Hw'.
  rewrite !(exp_scoped_wk_id _ (List.length Δ + 0)) in Hw' by (rewrite ?Nat.add_0_r; assumption || (intros; apply wk_qn_fix with (n := 0); lia)).
  exact Hw'.
Qed.

(** ** The Variables of a Telescope *)

(** The variables of [Δ], under [Φ], are of the instances of [Δ]'s types at
    them, at any base [τ] that sends the same terms as [Δ]'s own base [ρ]
    shifted past [Φ] and [Δ]. *)
Lemma wf_vars_tele_gen : forall Θ Ξ Φ Δ ρ τ Γ0 n,
    tele_ass Δ -> ctx_mvc Δ -> ctx_scoped n Δ ->
    ⊢ Θ ⍮ Ξ ⍮ Φ ++ tele_sub Δ ρ ++ Γ0 ->
    (forall y, y < n -> sentry_exp (τ y) = (sentry_exp (ρ y))[wk_shiftn (List.length Φ + List.length Δ)]ʷ) ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ τ (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      Θ ⍮ Ξ ⍮ Φ ++ tele_sub Δ ρ ++ Γ0 ⊢ N : T.
Proof.
  intros * Hass Hmv Hs HΨ Hτ k N T HN HT.
  apply vars_from_nth_error in HN as [Hk ->].
  apply tele_insts_nth in HT as (A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HsA : exp_scoped (k + n) A).
  { rewrite HΔeq in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HsA _].
    rewrite List.length_rev in HsA; congruence. }
  assert (HmA : exp_mvc 0 A).
  { unfold ctx_mvc in Hmv; rewrite HΔeq in Hmv; apply List.Forall_app in Hmv as [_ Hmv].
    apply List.Forall_cons_iff in Hmv as [HmA _]; exact HmA. }
  set (s := List.length Φ + List.length l2 + 1).
  replace (A[sb_of_list τ (List.firstn k (vars_from (List.length Φ) (List.length Δ)))])
    with (A[sb_qn k ρ][wk_shiftn s]ʷ).
  - apply wf_vlookup; [ exact HΨ |].
    replace (List.length Φ + (List.length Δ - 1 - k)) with (0 + List.length (Φ ++ tele_sub (List.rev l2) (sb_qn (S k) ρ)))
      by (rewrite List.length_app, length_tele_sub, List.length_rev; lia).
    replace (A[sb_qn k ρ][wk_shiftn s]ʷ)
      with (A[sb_qn k ρ][↑]ʷ[wk_shiftn (List.length (Φ ++ tele_sub (List.rev l2) (sb_qn (S k) ρ)))]ʷ)
      by (rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app, length_tele_sub, List.length_rev; unfold s; lia).
    rewrite HΔeq, tele_sub_app; cbn [tele_sub centry_sub List.length]; rewrite List.length_rev, Hl1.
    rewrite <- List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
    apply ctx_lookup_app_r; constructor.
  - rewrite <- exp_sub_of_wk, exp_sub_sub; symmetry; eapply exp_scoped_mvc_agree; [ exact HsA | exact HmA |].
    intros x Hx; cbn [sb_compose].
    destruct (Nat.lt_ge_cases x k) as [Hxk | Hxk].
    + rewrite sb_of_list_firstn_vars by lia; rewrite sb_qn_lt by exact Hxk; cbn; f_equal; unfold s; lia.
    + replace x with (List.length (List.firstn k (vars_from (List.length Φ) (List.length Δ))) + (x - k)) at 1
        by (rewrite List.length_firstn, length_vars_from; lia).
      rewrite sb_of_list_ge, Hτ by lia.
      rewrite sb_qn_ge by exact Hxk.
      rewrite <- sentry_exp_sub, <- sentry_exp_wk, exp_sub_of_wk, exp_wk_wk.
      apply exp_wk_wk_eq; intros z; cbn; unfold s; lia.
Qed.

(** The closed telescope, at the identity base. *)
Corollary wf_vars_tele_closed : forall Θ Ξ Φ Δ,
    tele_ass Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> ⊢ Θ ⍮ Ξ ⍮ Φ ++ Δ ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      Θ ⍮ Ξ ⍮ Φ ++ Δ ⊢ N : T.
Proof.
  intros * Hass Hs Hmv HΨ k N T HN HT.
  assert (E : Φ ++ Δ = Φ ++ tele_sub Δ Id ++ ⋅) by (rewrite tele_sub_id, List.app_nil_r; reflexivity).
  rewrite E in HΨ |- *.
  eapply (wf_vars_tele_gen _ _ _ _ Id Id ⋅ 0); try eassumption; intros; lia.
Qed.

(** ** The Parameters *)

Lemma exp_shift_past : forall M Ms Ns σ,
    M[wk_shiftn (List.length Ns)]ʷ[sb_of_list σ (Ms ++ Ns)] = M[sb_of_list σ Ms].
Proof.
  intros; rewrite exp_sub_wk; apply exp_sub_sb_eq; intros x.
  cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]; rewrite sb_of_list_app, Nat.add_comm, sb_of_list_ge; reflexivity.
Qed.

Lemma tele_insts_closed_wk : forall Δ Ms φ,
    tele_ass Δ -> ctx_scoped 0 Δ ->
    List.map (fun T => T[φ]ʷ) (tele_insts Δ Id Ms) = tele_insts Δ Id (List.map (fun M => M[φ]ʷ) Ms).
Proof.
  intros * Hass Hs; rewrite <- !map_sub_of_wk; apply (tele_insts_sub _ 0); [ exact Hass | exact Hs | lia ].
Qed.

Lemma ind_sort_univ_sub : forall S σ, ind_sort_univ S -> ind_sort_univ S[σ] /\ (ind_sort_lvl S)[σ] = ind_sort_lvl S[σ].
Proof. intros * [[i ->] | [t ->]]; cbn; unfold ind_sort_univ; split; eauto. Qed.

Lemma length_im_nparams : forall M, List.length (im_nparams M) = im_nn M.
Proof. reflexivity. Qed.

Section Params.
  Context (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (HD : decl_typed Θ Ξ D) (Hc : decl_closed D).

  Lemma decl_uparams_closed : ctx_scoped 0 (ind_uparams D).
  Proof. exact (decl_closed_uparams _ Hc). Qed.

  Lemma decl_uparams_ass : tele_ass (ind_uparams D).
  Proof. exact (decl_closed_ass _ Hc). Qed.

  Lemma decl_uparams_mvc : ctx_mvc (ind_uparams D).
  Proof. exact (decl_mvc_uparams _ (decl_typed_mvc _ _ _ HD)). Qed.

  Lemma decl_nparams_mvc : forall k M, ind_member D k = Some M -> ctx_mvc (im_nparams M).
  Proof. intros * HM; exact (proj1 (decl_mvc_members _ (decl_typed_mvc _ _ _ HD) _ _ HM)). Qed.

  Lemma decl_params_mvc : forall k M, ind_member D k = Some M -> ctx_mvc (im_params D M).
  Proof.
    intros * HM; unfold ctx_mvc, im_params; apply List.Forall_app; split;
      [ exact (decl_nparams_mvc _ _ HM) | exact decl_uparams_mvc ].
  Qed.

  Lemma wf_params_app : forall k M Γ, ind_member D k = Some M -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ im_params D M ++ Γ.
  Proof.
    intros * HM HΓ; apply wf_ctx_closed_app;
      [ eapply decl_closed_params_ass; eassumption | eapply decl_closed_params; eassumption
      | exact (member_params_wf _ _ _ _ _ HD HM) | exact HΓ ].
  Qed.

  Lemma wf_uparams_app : forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ.
  Proof.
    intros * HΓ; apply wf_ctx_closed_app;
      [ exact decl_uparams_ass | exact decl_uparams_closed | exact (decl_typed_uparams_field _ _ _ HD) | exact HΓ ].
  Qed.

  (** The parameters of a member typed one by one: the uniform ones at the
      uniform parameters' types, the others at theirs at the uniform
      ones, and back. *)
  Lemma params_typed_split : forall k M Γ Ps,
      ind_member D k = Some M -> List.length Ps = im_np D M ->
      (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D M) Id Ps) j = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
      (forall j U T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) /\
      (forall j N T, List.nth_error (List.skipn (ind_nu D) Ps) j = Some N ->
         List.nth_error (tele_insts (im_nparams M) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) j
           = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : T).
  Proof.
    intros * HM Hl HPs.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in Hl; lia).
    assert (Hti : tele_insts (im_params D M) Id Ps
                  = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                    ++ tele_insts (im_nparams M) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
    { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
        [ exact decl_uparams_ass | rewrite HUl; reflexivity ]. }
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
      by (rewrite length_tele_insts by exact decl_uparams_ass; rewrite HUl; unfold ind_nu; lia).
    split; intros j N T HN HT.
    - apply (HPs j); [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HN |].
      rewrite Hti, List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HT.
    - apply (HPs (ind_nu D + j)).
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + j - ind_nu D) with j by lia; exact HN.
      + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + j - ind_nu D) with j by lia; exact HT.
  Qed.

  Lemma params_typed_join : forall k M Γ Us Ns,
      ind_member D k = Some M -> List.length Us = ind_nu D ->
      (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      (forall j N T, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams M) (sb_of_list Id Us) Ns) j = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
      forall j P T, List.nth_error (Us ++ Ns) j = Some P -> List.nth_error (tele_insts (im_params D M) Id (Us ++ Ns)) j = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T.
  Proof.
    intros * HM HUl HUs HNs j P T HP HT; unfold im_params in HT.
    rewrite tele_insts_app in HT by (try exact decl_uparams_ass; exact HUl).
    assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
      by (rewrite length_tele_insts by exact decl_uparams_ass; rewrite HUl; unfold ind_nu; lia).
    destruct (Nat.lt_ge_cases j (ind_nu D)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HP by lia; rewrite List.nth_error_app1 in HT by lia; eauto.
    - rewrite List.nth_error_app2 in HP by lia; rewrite List.nth_error_app2 in HT by lia.
      rewrite HUl in HP; rewrite Hl1 in HT; eauto.
  Qed.

  Lemma wf_sub_uparams : forall Γ Us,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> List.length Us = ind_nu D ->
      (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ.
  Proof.
    intros * HΓ Hl HUs; apply wf_sub_of_list_id;
      [ exact decl_uparams_ass | apply wf_uparams_app, HΓ | exact Hl | exact HUs ].
  Qed.

  Lemma wf_nparams_sub : forall k M Γ Us,
      ind_member D k = Some M -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ tele_sub (im_nparams M) (sb_of_list Id Us) ++ Γ.
  Proof.
    intros * HM HΓ Hσ; eapply ctx_sub_wf; [ exact Hσ | eapply decl_closed_nparams_ass; eassumption |].
    rewrite List.app_assoc; apply (wf_params_app _ _ _ HM HΓ).
  Qed.

  (** The level of the sort, at the uniform parameters. *)
  Lemma sort_lvl_at : forall Γ Us,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      exists n, Θ ⍮ Ξ ⍮ Γ ⊢ ind_sort_lvl (ind_sort D)[sb_of_list Id Us] : Level@n.
  Proof.
    intros * HΓ Hσ; destruct (decl_typed_sort_lvl _ _ _ HD) as [n Hn]; pose proof (decl_typed_sort_univ _ _ _ HD) as HS; exists n.
    pose proof (decl_closed_sort _ Hc) as HsS.
    destruct (ind_sort_univ_sub (ind_sort D) (sb_of_list Id Us) HS) as [_ <-].
    assert (Hn' : Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ ⊢ ind_sort_lvl (ind_sort D) : Level@n).
    { apply wf_exp_closed_app; [ exact decl_uparams_ass | exact decl_uparams_closed | | exact I | exact Hn | exact HΓ ].
      destruct HS as [[i Heq] | [t Heq]]; rewrite Heq in *; cbn in *; auto. }
    exact (sub_preserves_exp _ _ _ _ _ _ _ Hn' Hσ).
  Qed.

  (** The sort at the uniform parameters is a type of a large universe. *)
  Lemma sort_at_large : forall Γ Us A,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : (ind_sort D)[sb_of_list Id Us] -> exists j, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j.
  Proof.
    intros * HΓ Hσ HA; pose proof (decl_typed_sort_univ _ _ _ HD) as HS.
    destruct (sort_lvl_at _ _ HΓ Hσ) as [n Hn].
    destruct (ind_sort_univ_sub (ind_sort D) (sb_of_list Id Us) HS) as [HS' Hl].
    eapply sort_large; eassumption.
  Qed.
End Params.

Lemma sb_of_list_map : forall Ms f σ x,
    x < List.length Ms -> sentry_exp (sb_of_list σ (List.map f Ms) x) = f (sentry_exp (sb_of_list σ Ms x)).
Proof.
  intros * Hx.
  rewrite (sb_of_list_nth _ _ _ (f (a_var 0))) by (rewrite List.length_map; exact Hx).
  rewrite (sb_of_list_nth _ _ _ (a_var 0)) by exact Hx; cbn.
  rewrite List.length_map, List.map_nth; reflexivity.
Qed.

(** ** The Motives' Contexts *)

(** The member at the uniform parameters [Us], shifted past its
    non-uniform ones, at those as variables, at an instance of them: the
    member at [Us] and the instance. *)
Lemma ind_head_inst : forall p D j Mj Us Ns β,
    decl_closed D -> List.length Us = ind_nu D -> List.length Ns = im_nn Mj ->
    (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))[sb_of_list β Ns]
    = ind_mty p D j (List.map (fun U => U[β]) Us) Ns.
Proof.
  intros * Hc HUl HNl.
  rewrite ind_mty_sub by (try exact Hc; rewrite List.length_map; exact HUl).
  rewrite List.map_map, <- HNl, vars_from_sb_of_list; f_equal.
  apply List.map_ext; intros U; exact (exp_shift_past U nil Ns β).
Qed.

Lemma elim_mctx_wf : forall Θ Ξ Γ p D k Mk Us,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D k Mk Us ++ Γ.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl HUs.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  pose proof (wf_nparams_sub _ _ _ HD Hc _ _ _ _ Hk HΓ Hσ) as HΨ0.
  assert (Hw : Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ ⊢ʷ wk_shiftn (im_nn Mk) : Γ).
  { rewrite <- (length_nparams_sub Mk (sb_of_list Id Us)); apply wf_wk_shiftn_app'; exact HΨ0. }
  set (Us' := List.map (fun U => U[wk_shiftn (im_nn Mk)]ʷ) Us).
  assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
  assert (HUs' : forall j U T, List.nth_error Us' j = Some U ->
             List.nth_error (tele_insts (ind_uparams D) Id Us') j = Some T ->
             Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ ⊢ U : T).
  { intros j U' T' HU HT; unfold Us' in *.
    rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
    apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    exact (wk_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hw). }
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΨ0 HUl' HUs') as Hσ'.
  assert (Hhd : Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ
                ⊢ ind_mty p D k Us' (vars_from 0 (im_nn Mk)) : (ind_sort D)[sb_of_list Id Us']).
  { eapply ind_mty_typed; [ exact Hg | exact HDs | exact Hl | exact Hk | exact HΨ0 | exact HUl' | exact HUs'
                          | apply length_vars_from |].
    intros j N T HN HT.
    change (vars_from 0 (im_nn Mk)) with (vars_from (List.length (@nil centry)) (List.length (im_nparams Mk))) in HN, HT.
    change (tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ) with (nil ++ tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ).
    eapply (wf_vars_tele_gen _ _ nil _ _ _ Γ (ind_nu D));
      [ eapply decl_closed_nparams_ass; eassumption | exact (decl_nparams_mvc _ _ _ HD _ _ Hk)
      | eapply decl_closed_nparams_scoped; eassumption | exact HΨ0 | | exact HN | exact HT ].
    intros y Hy; unfold Us'; rewrite sb_of_list_map by lia; reflexivity. }
  destruct (sort_at_large _ _ _ HD Hc _ _ _ HΨ0 Hσ' Hhd) as [j Hj].
  unfold elim_mctx; cbn [List.app]; econstructor; exact Hj.
Qed.

Lemma elim_mctx_head_typed : forall Θ Ξ Γ p D k Mk Us,
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D k Mk Us ++ Γ ->
    exists j, Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ
      ⊢ ind_mty p D k (List.map (fun U => U[wk_shiftn (im_nn Mk)]ʷ) Us) (vars_from 0 (im_nn Mk)) : Typeω@j.
Proof. intros * HM; unfold elim_mctx in HM; cbn [List.app] in HM; destruct (ctx_decomp HM) as [_ [j Hj]]; eauto. Qed.

(** ** The Arguments of a Constructor at the Parameters *)

Lemma cargs_ctx_closed : forall p D k M c gs gs1 gs2,
    decl_closed D -> ind_member D k = Some M -> List.In (c, gs) (im_cons M) -> gs = gs1 ++ gs2 ->
    ctx_scoped 0 (cargs_ctx p D M gs1 ++ im_params D M).
Proof.
  intros * Hc HM Hin Heq; pose proof (decl_closed_members _ Hc _ _ HM) as HMc.
  apply ctx_scoped_app; split; [| exact (decl_closed_params _ _ _ Hc HM) ].
  rewrite Nat.add_0_r, length_im_params; change (im_np D M) with (List.length (@nil bool) + (im_nn M + ind_nu D)).
  apply (cargs_ctx_aux_scoped p D (im_nn M) gs1 nil 0 Hc eq_refl); cbn.
  - intros gs3 A gs4 ->; eapply exp_scoped_mono; [| apply (member_closed_args _ _ HMc c gs gs3 A (gs4 ++ gs2) Hin);
                                                    rewrite Heq, <- List.app_assoc; reflexivity ].
    unfold im_np; lia.
  - intros gs3 t gs4 ->; eapply ptyp_scoped_mono; [| apply (member_closed_recs _ _ HMc c gs gs3 t (gs4 ++ gs2) Hin);
                                                     rewrite Heq, <- List.app_assoc; reflexivity ].
    unfold im_np; lia.
Qed.

Lemma vars_from_sb_qn : forall K Ms σ,
    List.map (fun M => M[sb_qn K (sb_of_list σ Ms)]) (vars_from K (List.length Ms)) = List.map (fun M => M[wk_shiftn K]ʷ) Ms.
Proof.
  intros; apply (List.nth_ext _ _ (a_var 0) (a_var 0)); rewrite !List.length_map, ?length_vars_from; [ reflexivity |].
  intros t Ht.
  rewrite (List.nth_indep _ (a_var 0) ((a_var 0)[sb_qn K (sb_of_list σ Ms)])) by (rewrite List.length_map, length_vars_from; lia).
  rewrite (List.map_nth (fun M : typ => M[sb_qn K (sb_of_list σ Ms)]) (vars_from K (List.length Ms)) (a_var 0) t).
  rewrite (List.nth_indep (List.map (fun M : typ => M[wk_shiftn K]ʷ) Ms) (a_var 0) ((a_var 0)[wk_shiftn K]ʷ)) by (rewrite List.length_map; lia).
  rewrite (List.map_nth (fun M : typ => M[wk_shiftn K]ʷ) Ms (a_var 0) t).
  replace t with (List.length Ms - 1 - (List.length Ms - 1 - t)) at 1 by lia.
  rewrite vars_from_nth by lia; cbn.
  rewrite sb_qn_ge by lia; replace (K + (List.length Ms - 1 - t) - K) with (List.length Ms - 1 - t) by lia.
  rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia; cbn.
  replace (List.length Ms - 1 - (List.length Ms - 1 - t)) with t by lia; reflexivity.
Qed.

Section Cargs.
  Context (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (k : nat) (Mk : imember) (Us : list typ).
  Hypothesis (Hg : ⊢ᵍ Θ ⍮ Ξ) (HDs : decls_typed Θ Ξ) (Hl : ind_lookup Θ Ξ p = Some D) (Hk : ind_member D k = Some Mk)
    (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ).
  Hypothesis (HUl : List.length Us = ind_nu D).
  Hypothesis (Hσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ).

  (** The context of a constructor's arguments [gs1] at the uniform
      arguments [Us], over its non-uniform parameters there and [Γ]. *)
  Definition cinst (gs1 : list carg) : ctx :=
    tele_sub (cargs_ctx p D Mk gs1) (sb_qn (im_nn Mk) (sb_of_list Id Us)) ++ tele_sub (im_nparams Mk) (sb_of_list Id Us) ++ Γ.

  Lemma cinst_eq : forall gs1,
      cinst gs1 = tele_sub (cargs_ctx p D Mk gs1 ++ im_nparams Mk) (sb_of_list Id Us) ++ Γ.
  Proof. intros; unfold cinst; rewrite tele_sub_app, length_im_nparams, List.app_assoc; reflexivity. Qed.

  Lemma wf_sub_cinst : forall c gs gs1 gs2,
      List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ cinst gs1 /\
      Θ ⍮ Ξ ⍮ cinst gs1 ⊢ˢ sb_qn (List.length gs1 + im_nn Mk) (sb_of_list Id Us) : cargs_ctx p D Mk gs1 ++ im_params D Mk ++ Γ.
  Proof.
    intros * Hin Heq.
    pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
    destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs1 gs2 Heq) as (HΨ & _ & _).
    assert (HΨΓ : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D Mk gs1 ++ im_params D Mk) ++ Γ).
    { apply wf_ctx_closed_app; [| eapply cargs_ctx_closed; eassumption | exact HΨ | exact HΓ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_params_ass; eassumption ]. }
    unfold im_params in HΨΓ; rewrite <- !List.app_assoc, (List.app_assoc (cargs_ctx p D Mk gs1)) in HΨΓ.
    assert (Hi : ⊢ Θ ⍮ Ξ ⍮ cinst gs1).
    { rewrite cinst_eq; eapply ctx_sub_wf; [ exact Hσ | | exact HΨΓ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ]. }
    split; [ exact Hi |].
    pose proof (wf_sub_ext _ _ (cargs_ctx p D Mk gs1 ++ im_nparams Mk) _ _ _ Hσ) as Hext; rewrite <- cinst_eq in Hext.
    specialize (Hext Hi HΨΓ).
    rewrite List.length_app, length_cargs_ctx, length_im_nparams in Hext.
    unfold im_params; rewrite <- (List.app_assoc (im_nparams Mk)), List.app_assoc; exact Hext.
  Qed.
End Cargs.

(** ** The Motives' Instances at the Recursive Arguments *)

Lemma cinst_split : forall Γ p D Mk Us gs1 t gs2,
    cinst Γ p D Mk Us (gs1 ++ ca_rec t :: gs2)
    = (tele_sub (cargs_ctx_aux p D (im_nn Mk) (true :: cargs_pat gs1) gs2)
         (sb_qn (S (List.length gs1)) (sb_qn (im_nn Mk) (sb_of_list Id Us)))
       ++ ce_ass (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t)[sb_qn (List.length gs1) (sb_qn (im_nn Mk) (sb_of_list Id Us))] :: nil)
      ++ cinst Γ p D Mk Us gs1.
Proof.
  intros; unfold cinst, cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; cbn [cargs_ctx_aux].
  rewrite !tele_sub_app, length_cargs_ctx_aux, <- !List.app_assoc; cbn [tele_sub List.length List.app centry_sub sb_qn].
  reflexivity.
Qed.

(** A substitution into a context is one into a well-formed prefix. *)
Lemma ctx_lookup_def_app_l : forall Γ Δ x M A, Γ ∋ #x ≔ M : A -> Γ ++ Δ ∋ #x ≔ M : A.
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma ctx_lookup_mod_app_l : forall Γ Δ x U, Γ ∋ #x ≔ₘ U -> Γ ++ Δ ∋ #x ≔ₘ U.
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma wf_sub_prefix : forall Θ Ξ Ψ Δ Γ σ, Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Δ.
Proof.
  intros * Hσ HΔ; destruct Hσ as [Hd _ Ha Had Ham]; constructor; [ exact Hd | exact HΔ | | | ].
  - intros x A Hx; apply Ha, ctx_lookup_app_l; exact Hx.
  - intros x A M Hx; apply Had, ctx_lookup_def_app_l; exact Hx.
  - intros x U Hx; apply Ham, ctx_lookup_mod_app_l; exact Hx.
Qed.

(** *** The Leaf

    At the end of a shape, the motive's context of the member [j] the shape
    ends in is instantiated by the shape's non-uniform parameters, moved by
    [σ] from the closed context [Tc] of the shape's components, and by the
    argument applied to the shape's domains, over the base [β]: the uniform
    parameters [σ] sends are those of the motive's context, moved by [β]. *)

Definition shape_uc (D : ind_decl) (Us : list exp) (Tc : ctx) (σ β : sub) : Prop :=
  forall y, y < ind_nu D -> sentry_exp (σ (y + (List.length Tc - ind_nu D))) = sentry_exp ((sb_of_list Id Us ⨟ β) y).

Lemma ih_leaf_nsub : forall Θ Ξ Γ p D j Mj Us Ψ Tc β σ Ps,
    decl_typed Θ Ξ D -> decl_closed D -> ind_member D j = Some Mj ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Tc ->
    shape_uc D Us Tc σ β ->
    List.length Ps = im_nn Mj ->
    (forall k P T, List.nth_error Ps k = Some P ->
       List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))) Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Tc ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps) : tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ.
Proof.
  intros * HD Hc Hj HUl HM Hβ Hσ Huc HPl HP.
  assert (HPl' : List.length (List.map (fun P => P[σ]) Ps) = im_nn Mj) by (rewrite List.length_map; exact HPl).
  assert (HN : ⊢ Θ ⍮ Ξ ⍮ tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)
    by (unfold elim_mctx in HM; cbn [List.app] in HM; destruct (ctx_decomp HM) as [H0 _]; exact H0).
  apply wf_sub_of_list; [ apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption | exact HN | exact Hβ
                        | rewrite length_tele_sub, HPl'; reflexivity |].
  intros k N T HN' HT.
  apply nth_error_map_inv in HN' as (P & HPk & ->).
  rewrite tele_insts_tele_sub in HT.
  set (σ0 := sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))).
  assert (HT0 : exists T0, List.nth_error (tele_insts (im_nparams Mj) σ0 Ps) k = Some T0).
  { destruct (List.nth_error (tele_insts (im_nparams Mj) σ0 Ps) k) as [T0 |] eqn:E0; [ eauto |].
    apply List.nth_error_None in E0; rewrite length_tele_insts in E0 by (eapply decl_closed_nparams_ass; eassumption).
    rewrite length_im_nparams, HPl in E0.
    assert (Hk : k < List.length Ps) by (apply List.nth_error_Some; congruence); lia. }
  destruct HT0 as [T0 HT0].
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HP _ _ _ HPk HT0) Hσ) as HP1.
  replace T with T0[σ]; [ exact HP1 |].
  rewrite <- (tele_insts_sub_mvc (im_nparams Mj) (ind_nu D) σ0 _ σ Ps) in HT.
  + apply nth_error_map_inv in HT as (T1 & HT1 & ->); rewrite HT0 in HT1; injection HT1 as ->; reflexivity.
  + eapply decl_closed_nparams_ass; eassumption.
  + exact (decl_nparams_mvc _ _ _ HD _ _ Hj).
  + eapply decl_closed_nparams_scoped; eassumption.
  + intros y Hy; unfold σ0; cbn [sb_of_wk sentry_sub wk_shiftn]; exact (Huc y Hy).
Qed.

Lemma ih_leaf_sub : forall Θ Ξ Γ p D j Mj Us Ψ Tc β σ Ps x,
    decl_typed Θ Ξ D -> decl_closed D -> ind_member D j = Some Mj ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Tc ->
    shape_uc D Us Tc σ β ->
    List.length Ps = im_nn Mj ->
    (forall k P T, List.nth_error Ps k = Some P ->
       List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))) Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Tc ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ x : ind_mty p D j (List.map (fun U => U[β]) Us) (List.map (fun P => P[σ]) Ps) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps ++ x :: nil) : elim_mctx p D j Mj Us ++ Γ.
Proof.
  intros * HD Hc Hj HUl HM Hβ Hσ Huc HPl HP Hx.
  pose proof (ih_leaf_nsub _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hj HUl HM Hβ Hσ Huc HPl HP) as Hn.
  destruct (elim_mctx_head_typed _ _ _ _ _ _ _ _ HM) as [i Hi].
  rewrite sb_of_list_app; cbn [sb_of_list]; unfold elim_mctx; cbn [List.app].
  eapply wf_sub_extend; [ exact Hn | exact Hi |].
  rewrite ind_head_inst by (try assumption; rewrite List.length_map; exact HPl); exact Hx.
Qed.

(** *** Along a Shape

    The invariant of a shape's prefix, for a constructor of the member
    [Mk]: the components' context so far is [doms_ctx Bs1 ++ Tb ++
    im_params D Mk], the domains [Bs1] above the context [Tb] of the
    non-recursive arguments; what remains of the shape has its domains and
    its leaf, at the member [Mj] it ends in, typed there. *)

(** The remaining domains of the shape [t] are types, each under the
    domains before it. *)
Definition shape_doms_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (Mk : imember) (Bs1 : list exp) (Tb : ctx) (t : ptyp) : Prop :=
  forall Bs1' B Bs2, ptyp_doms t = Bs1' ++ B :: Bs2 ->
    exists j, Θ ⍮ Ξ ⍮ doms_ctx (Bs1 ++ Bs1') ++ Tb ++ im_params D Mk ⊢ B : Typeω@j.

(** The leaf's parameters of the shape [t] are typed at the non-uniform
    telescope of the member [Mj] it ends in, under all its domains. *)
Definition shape_leaf_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (Mk Mj : imember) (Bs1 : list exp) (Tb : ctx) (t : ptyp) : Prop :=
  forall k P T, List.nth_error (ptyp_ps t) k = Some P ->
    List.nth_error (tele_insts (im_nparams Mj)
                      (sb_of_wk (wk_shiftn (List.length Bs1 + ptyp_depth t + List.length Tb + im_nn Mk))) (ptyp_ps t)) k
      = Some T ->
    Θ ⍮ Ξ ⍮ doms_ctx (Bs1 ++ ptyp_doms t) ++ Tb ++ im_params D Mk ⊢ P : T.

Lemma doms_ctx_app_one : forall Bs B, doms_ctx (Bs ++ B :: nil) = ce_ass B :: doms_ctx Bs.
Proof. intros; unfold doms_ctx; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma length_doms_ctx : forall Bs, List.length (doms_ctx Bs) = List.length Bs.
Proof. intros; unfold doms_ctx; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma shape_doms_typed_pi : forall Θ Ξ D Mk Bs1 Tb B t,
    shape_doms_typed Θ Ξ D Mk Bs1 Tb (pt_pi B t) -> shape_doms_typed Θ Ξ D Mk (Bs1 ++ B :: nil) Tb t.
Proof.
  intros * H Bs1' B' Bs2 E; destruct (H (B :: Bs1') B' Bs2 ltac:(cbn; rewrite E; reflexivity)) as [j Hj].
  exists j; rewrite <- List.app_assoc; exact Hj.
Qed.

Lemma shape_leaf_typed_pi : forall Θ Ξ D Mk Mj Bs1 Tb B t,
    shape_leaf_typed Θ Ξ D Mk Mj Bs1 Tb (pt_pi B t) -> shape_leaf_typed Θ Ξ D Mk Mj (Bs1 ++ B :: nil) Tb t.
Proof.
  intros * H k P T HP HT; specialize (H k P T HP).
  unfold ptyp_depth in H, HT; cbn [ptyp_doms ptyp_ps List.length] in H.
  rewrite <- List.app_assoc; cbn [List.app]; apply H.
  rewrite List.length_app in HT; cbn [List.length] in HT.
  replace (List.length Bs1 + S (List.length (ptyp_doms t)) + List.length Tb + im_nn Mk)
    with (List.length Bs1 + 1 + List.length (ptyp_doms t) + List.length Tb + im_nn Mk) by lia; exact HT.
Qed.

Lemma shape_uc_pi : forall D Us Tc σ β B,
    ind_nu D <= List.length Tc ->
    shape_uc D Us Tc σ β -> shape_uc D Us (Tc ▹ B) (q σ) (β ⨟ ι ↑).
Proof.
  intros * Hle H y Hy; cbn [List.length].
  replace (y + (S (List.length Tc) - ind_nu D)) with (S (y + (List.length Tc - ind_nu D))) by lia.
  rewrite sb_q_succ, <- sentry_exp_wk, H by exact Hy.
  cbn [sb_compose]; rewrite sentry_exp_wk, <- sentry_sub_of_wk, !sentry_sub_sub; reflexivity.
Qed.

Lemma length_shape_ctx : forall D Mk Bs1 Tb,
    List.length (doms_ctx Bs1 ++ Tb ++ im_params D Mk) - ind_nu D = List.length Bs1 + List.length Tb + im_nn Mk /\
    ind_nu D <= List.length (doms_ctx Bs1 ++ Tb ++ im_params D Mk).
Proof.
  intros; rewrite !List.length_app, length_doms_ctx, length_im_params; unfold im_np; lia.
Qed.

(** The leaf's parameters, in the shape's components' context. *)
Lemma shape_leaf_at : forall Θ Ξ D Mk Mj Bs1 Tb t, shape_leaf_typed Θ Ξ D Mk Mj Bs1 Tb t ->
    ptyp_doms t = nil ->
    forall k P T, List.nth_error (ptyp_ps t) k = Some P ->
      List.nth_error (tele_insts (im_nparams Mj)
        (sb_of_wk (wk_shiftn (List.length (doms_ctx Bs1 ++ Tb ++ im_params D Mk) - ind_nu D))) (ptyp_ps t)) k = Some T ->
      Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ Tb ++ im_params D Mk ⊢ P : T.
Proof.
  intros * HP Hd k P T HPk HT; specialize (HP k P T HPk).
  unfold ptyp_depth in HP; rewrite Hd in HP; cbn [List.length] in HP; rewrite List.app_nil_r in HP.
  apply HP; rewrite (proj1 (length_shape_ctx D Mk Bs1 Tb)) in HT; rewrite Nat.add_0_r; exact HT.
Qed.

(** The type of a shape's argument is a type. *)
Lemma ty_at_typed : forall Θ Ξ Γ p D Mk Us t Ψ Bs1 Tb β σ Mj,
    decl_typed Θ Ξ D -> decl_closed D ->
    List.length Us = ind_nu D ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β ->
    ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t) = im_nn Mj ->
    shape_doms_typed Θ Ξ D Mk Bs1 Tb t -> shape_leaf_typed Θ Ξ D Mk Mj Bs1 Tb t ->
    exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ty_at p D (List.map (fun U => U[β]) Us) σ t : Typeω@j.
Proof.
  intros Θ Ξ Γ p D Mk Us t; induction t as [j0 Ps | B t IH];
    intros * HD Hc HUl HM Hβ Hσ Huc Hj HPl HB HP; cbn [ptyp_ty_at].
  - cbn [ptyp_mem ptyp_ps] in Hj, HPl |- *.
    destruct (elim_mctx_head_typed Θ Ξ Γ p D j0 Mj Us (HM _ _ Hj)) as [j Hj']; exists j.
    rewrite <- (ind_head_inst p D j0 Mj Us _ β) by (try assumption; rewrite List.length_map; exact HPl).
    exact (sub_preserves_exp _ _ _ _ _ _ _ Hj' (ih_leaf_nsub _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hj HUl (HM _ _ Hj) Hβ Hσ Huc HPl
             (shape_leaf_at _ _ _ _ _ _ _ _ HP eq_refl))).
  - destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
    assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
    pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
    assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
      by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
    replace ((doms_ctx Bs1 ++ Tb ++ im_params D Mk) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) in Hσ'
      by (rewrite doms_ctx_app_one; reflexivity).
    destruct (IH (Ψ ▹ B[σ]) (Bs1 ++ B :: nil) Tb (β ⨟ ι ↑) (q σ) Mj HD Hc HUl HM Hβ' Hσ') as [j2 Hj2].
    + rewrite doms_ctx_app_one; apply shape_uc_pi; [ exact (proj2 (length_shape_ctx D Mk Bs1 Tb)) | exact Huc ].
    + exact Hj.
    + exact HPl.
    + apply shape_doms_typed_pi; exact HB.
    + apply shape_leaf_typed_pi; exact HP.
    + exists (max j1 j2); eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' |].
      eapply lift_exp_max_right.
      rewrite List.map_map, (List.map_ext (fun U => U[β][↑]ʷ) (fun U => U[β ⨟ ι ↑])) by (intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      exact Hj2.
Qed.

(** The argument of a shape applied to the shape's next domain. *)
Lemma shape_arg_app : forall Θ Ξ Ψ B C x j1 j2,
    Θ ⍮ Ξ ⍮ Ψ ⊢ B : Typeω@j1 -> Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ C : Typeω@j2 -> Θ ⍮ Ξ ⍮ Ψ ⊢ x : Π B C ->
    Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ x[↑]ʷ $ #0 : C.
Proof.
  intros * HB HC Hx.
  pose proof (lift_exp_max_left _ _ _ _ _ j2 HB) as HB2.
  pose proof (lift_exp_max_right _ _ _ _ j1 _ HC) as HC2.
  set (i := max j1 j2) in *.
  assert (⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ʷ ↑ : Ψ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ exp_wk x ↑ : exp_wk (Π B C) ↑) as H' by (eapply wk_preserves_exp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ x[↑]ʷ : Π B[↑]ʷ C[wk_q ↑]ʷ) by exact H'.
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ B[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; eassumption).
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ #0 : B[↑]ʷ) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ▹ B[↑]ʷ ⊢ C[wk_q ↑]ʷ : Typeω@i)
    by (eapply wk_preserves_typ; [ eassumption | eapply wf_wk_q'; eassumption ]).
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ x[↑]ʷ $ #0 : C[wk_q ↑]ʷ[Id,,#0]) by (eapply wf_app; eassumption).
  assert (Θ ⍮ Ξ ⍮ Ψ ▹ B ⊢ C[wk_q ↑]ʷ[Id,,#0] ≈ C : Typeω@i).
  { rewrite <- (exp_wk_q_shift_single C) at 2.
    eapply (sub_eq_preserves_typ _ _ _ _ _ _ _ i); [ eassumption | eapply wf_sub_eq_var_zero; eassumption ]. }
  eapply wf_exp_subtyp'; [ eassumption |].
  eapply wf_subtyp_refl; [ eassumption | eassumption ].
Qed.

(** The motives [As] of the members, typed in their contexts, and equal to
    [As']. *)
Definition motives_typed (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (Us As : list exp) (i : nat) : Prop :=
  forall j Mj, ind_member D j = Some Mj -> Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ ⊢ List.nth j As a_True : Typeω@i.

(** The motives [As] and [As'] are equal, member by member, in their
    contexts. *)
Definition motives_eq (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (Us As As' : list exp) (i : nat) : Prop :=
  forall j Mj, ind_member D j = Some Mj ->
    Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ ⊢ List.nth j As a_True ≈ List.nth j As' a_True : Typeω@i.

(** The type of a recursive result of a shape is a type, and equal ones of
    equal motives. *)
Lemma ihty_typed : forall Θ Ξ Γ p D Mk Us As As' i t Ψ Bs1 Tb β σ x Mj,
    decl_typed Θ Ξ D -> decl_closed D ->
    List.length Us = ind_nu D ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As i -> motives_typed Θ Ξ Γ p D Us As' i -> motives_eq Θ Ξ Γ p D Us As As' i ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β ->
    ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t) = im_nn Mj ->
    shape_doms_typed Θ Ξ D Mk Bs1 Tb t -> shape_leaf_typed Θ Ξ D Mk Mj Bs1 Tb t ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => U[β]) Us) σ t ->
    exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty As β σ x t : Typeω@j /\ Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty As' β σ x t : Typeω@j /\
      Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty As β σ x t ≈ ptyp_ihty As' β σ x t : Typeω@j.
Proof.
  intros Θ Ξ Γ p D Mk Us As As' i t; induction t as [j0 Ps | B t IH];
    intros * HD Hc HUl HM HA HA' HAA Hβ Hσ Huc Hj HPl HB HP Hx; cbn [ptyp_ihty ptyp_ty_at] in *.
  - cbn [ptyp_mem ptyp_ps] in Hj, HPl.
    pose proof (ih_leaf_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hj HUl (HM _ _ Hj) Hβ Hσ Huc HPl
                  (shape_leaf_at _ _ _ _ _ _ _ _ HP eq_refl) Hx) as Hτ; exists i.
    refine (conj (sub_preserves_exp _ _ _ _ _ _ _ (HA _ _ Hj) Hτ) (conj (sub_preserves_exp _ _ _ _ _ _ _ (HA' _ _ Hj) Hτ) _)).
    exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ (HAA _ _ Hj) Hτ).
  - cbn [ptyp_ps ptyp_mem] in HPl, Hj.
    destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
    assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
    pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
    assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
      by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
    replace ((doms_ctx Bs1 ++ Tb ++ im_params D Mk) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) in Hσ'
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
    destruct (IH _ _ _ _ _ _ _ HD Hc HUl HM HA HA' HAA Hβ' Hσ' Huc' Hj HPl HB'' HP'' Hx') as (j3 & H1 & H2 & H3).
    exists (max j1 j3); split; [| split ].
    + eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_max_right; exact H1 ].
    + eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_max_right; exact H2 ].
    + eapply wf_exp_eq_pi_cong_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_eq_max_left, wf_exp_eq_refl; exact Hj1'
                                | eapply lift_exp_eq_max_right; exact H3 ].
Qed.

(** *** A Recursive Argument in a Branch's Context

    In the context of the arguments of a constructor of the member [Mk],
    after [E], the recursive argument's components are moved by [ihs_sub]
    from the closed context of the non-recursive arguments before it and
    the parameters, the eliminator's context [Γ] is that many binders out,
    and the argument is of its shape's type there. *)
Lemma rec_arg_inst : forall Θ Ξ Γ p D k Mk Us c gs gs1 t gs2 E,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ->
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ˢ ι (wk_shiftn (List.length E + List.length gs + im_nn Mk)) : Γ /\
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ˢ ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E)
      : doms_ctx nil ++ cargs_strat gs1 ++ im_params D Mk /\
    shape_uc D Us (doms_ctx nil ++ cargs_strat gs1 ++ im_params D Mk)
      (ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E))
      (ι (wk_shiftn (List.length E + List.length gs + im_nn Mk))) /\
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ #(List.length E + List.length gs - 1 - List.length (cargs_pat gs1))
      : ptyp_ty_at p D (List.map (fun U => U[ι (wk_shiftn (List.length E + List.length gs + im_nn Mk))]) Us)
          (ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E)) t.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl Hσ Hin Heq HΨ.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  set (pat := cargs_pat gs1) in *.
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  set (i := List.length pat) in *.
  set (j := List.length E) in *.
  set (na := List.length gs) in *.
  set (nn := im_nn Mk) in *.
  assert (Hna : na = i + S (List.length gs2)) by (unfold na, i; rewrite Heq, List.length_app; cbn; lia).
  set (m := j + na + nn).
  set (s := na - i + j).
  set (ρ := sb_qn (i + nn) (sb_of_list Id Us)).
  set (θ := ihs_sub nn Us na pat j).
  assert (Hθ : θ = (ι (wk_pat pat) ⨟ ρ) ⨟ ι (wk_shiftn s)) by reflexivity.
  (* the base: a shift past the results, the arguments and the non-uniform parameters *)
  assert (Hb : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ˢ ι (wk_shiftn m) : Γ).
  { apply wf_sub_of_wk.
    unfold cinst in HΨ |- *; rewrite !List.app_assoc in HΨ |- *.
    replace m with (List.length ((E ++ tele_sub (cargs_ctx p D Mk gs) (sb_qn nn (sb_of_list Id Us)))
                                     ++ tele_sub (im_nparams Mk) (sb_of_list Id Us)))
      by (rewrite !List.length_app, !length_tele_sub, length_cargs_ctx; unfold m, nn, im_nn; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  (* the components: past the recursive arguments before, the uniform
     parameters instantiated, past the arguments after *)
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ Hσ c gs gs1 (ca_rec t :: gs2) Hin Heq) as (Hi1 & Hτ2).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs1 (ca_rec t :: gs2) Heq) as (HΨ1 & HSt & Hφ).
  assert (Hw3 : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ʷ wk_shiftn s : cinst Γ p D Mk Us gs1).
  { rewrite Heq in HΨ |- *; rewrite cinst_split in HΨ |- *; rewrite List.app_assoc in HΨ |- *.
    replace s with (List.length (E ++ tele_sub (cargs_ctx_aux p D (im_nn Mk) (true :: cargs_pat gs1) gs2)
                                     (sb_qn (S (List.length gs1)) (sb_qn (im_nn Mk) (sb_of_list Id Us)))
                                     ++ ce_ass (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t)
                                          [sb_qn (List.length gs1) (sb_qn (im_nn Mk) (sb_of_list Id Us))] :: nil))
      by (rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; unfold s, i, j, na; rewrite Heq, List.length_app; cbn; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  rewrite <- Hpat in Hτ2; fold i in Hτ2; fold nn in Hτ2; fold ρ in Hτ2.
  rewrite List.app_assoc in Hτ2; apply wf_sub_prefix in Hτ2; [| exact HΨ1 ].
  assert (Hθt : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ˢ θ : cargs_strat gs1 ++ im_params D Mk).
  { rewrite Hθ; eapply wf_sub_compose; [| apply wf_sub_of_wk; exact Hw3 ].
    eapply wf_sub_compose; [ apply wf_sub_of_wk; exact Hφ | exact Hτ2 ]. }
  refine (conj Hb (conj Hθt (conj _ _))).
  - (* the uniform parameters *)
    intros x Hx; cbn [doms_ctx List.rev List.map List.app] in *.
    replace (x + (List.length (cargs_strat gs1 ++ im_params D Mk) - ind_nu D))
      with (pat_nargs pat + (nn + x))
      by (rewrite List.length_app, length_im_params; unfold pat; rewrite pat_nargs_cargs_pat; unfold nn, im_np; lia).
    rewrite Hθ; cbn [sb_compose sb_of_wk sentry_sub].
    rewrite wk_pat_ge; fold i; unfold ρ; rewrite sb_qn_ge by lia.
    replace (i + (nn + x) - (i + nn)) with x by lia.
    rewrite !sentry_sub_of_wk, sentry_wk_wk; f_equal; apply sentry_wk_wk_eq; intros z; cbn; unfold m, s; lia.
  - (* the recursive argument *)
    apply wf_vlookup; [ exact HΨ |].
    rewrite Heq in HΨ |- *; rewrite cinst_split, List.app_assoc.
    rewrite <- !List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
    set (L := tele_sub (cargs_ctx_aux p D (im_nn Mk) (true :: cargs_pat gs1) gs2)
                (sb_qn (S (List.length gs1)) (sb_qn (im_nn Mk) (sb_of_list Id Us)))).
    assert (HL : List.length L = List.length gs2) by (unfold L; rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity).
    replace (j + na - 1 - i) with (0 + List.length (E ++ L)) by (rewrite List.length_app, HL; unfold j; lia).
    match goal with |- _ ∋ # _ : ?T =>
      replace T with ((ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t)
                        [sb_qn (List.length gs1) (sb_qn (im_nn Mk) (sb_of_list Id Us))][↑]ʷ[wk_shiftn (List.length (E ++ L))]ʷ)
    end.
    { apply ctx_lookup_app_r; constructor. }
    assert (HuvL : List.length (ind_uvars D (im_nn Mk) (List.length pat)) = ind_nu D) by apply length_ind_uvars.
    rewrite ptyp_ty_eq_at; fold pat.
    rewrite ptyp_ty_at_sub by assumption.
    rewrite <- !exp_sub_of_wk.
    rewrite ptyp_ty_at_sub by (try assumption; rewrite List.length_map; exact HuvL).
    rewrite ptyp_ty_at_sub by (try assumption; rewrite !List.length_map; exact HuvL).
    rewrite !List.map_map.
    rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ θ); [ f_equal |].
    + unfold ind_uvars.
      rewrite (List.map_ext _ (fun M => M[sb_qn (List.length gs1 + im_nn Mk) (sb_of_list Id Us)][ι wk_shiftn (S (List.length (E ++ L)))]))
        by (intros; rewrite !exp_sub_sub; apply exp_sub_sb_eq; intros z; cbn [sb_compose];
            rewrite <- !sentry_sub_sub, (sb_qn_add _ _ _ z), !sentry_sub_of_wk, sentry_wk_wk; apply sentry_wk_wk_eq; intros w; cbn; lia).
      rewrite <- (List.map_map (fun M => M[sb_qn (List.length gs1 + im_nn Mk) (sb_of_list Id Us)]) (fun M => M[ι wk_shiftn (S (List.length (E ++ L)))])).
      fold i; rewrite Hpat, <- HUl, vars_from_sb_qn, List.map_map.
      apply List.map_ext; intros U; rewrite !exp_sub_of_wk, !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn.
      rewrite List.length_app, HL; unfold m, j, na, nn; rewrite Heq, List.length_app; cbn; lia.
    + rewrite Hθ; intros y; cbn [sb_compose].
      rewrite !sentry_sub_sub; apply sentry_sub_sb_eq; intros z; cbn [sb_compose].
      unfold ρ; rewrite <- (sb_qn_add _ _ _ z), Hpat.
      apply sentry_sub_sb_eq; intros w; cbn.
      rewrite List.length_app, HL; unfold s, j, na; rewrite Heq, List.length_app; cbn; f_equal; lia.
Qed.

(** What a group says of a shape, in the invariant's terms. *)
Lemma decl_shape_facts : forall Θ Ξ D k Mk c gs gs1 t gs2,
    decl_typed Θ Ξ D -> ind_member D k = Some Mk -> List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 ->
    exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj /\
      shape_doms_typed Θ Ξ D Mk nil (cargs_strat gs1) t /\ shape_leaf_typed Θ Ξ D Mk Mj nil (cargs_strat gs1) t.
Proof.
  intros * HD Hk Hin Heq.
  destruct (decl_typed_plen _ _ _ HD _ _ _ _ Hk Hin _ _ _ Heq) as (Mj & Hj & HPl).
  exists Mj; split; [ exact Hj | split; [ exact HPl | split ] ].
  - intros Bs1' B Bs2 E; cbn [List.app].
    pose proof (decl_typed_doms _ _ _ HD _ _ _ _ _ _ _ _ _ _ Hk Hin Heq E) as HB.
    pose proof (presup_exp_ctx HB) as HE.
    assert (HE' : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx Bs1' ++ cargs_strat gs1 ++ im_nparams Mk) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc; exact HE).
    destruct (sort_under _ _ _ _ HD HE') as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc in Hn; fold (im_params D Mk) in Hn.
    replace (List.length (doms_ctx Bs1' ++ cargs_strat gs1 ++ im_nparams Mk))
      with (List.length Bs1' + List.length (cargs_strat gs1) + im_nn Mk) in Hn, HSu
      by (rewrite !List.length_app, length_doms_ctx; unfold im_nn; lia).
    exact (sort_large _ _ _ _ _ _ HSu Hn HB).
  - intros j P T HPk HT; cbn [List.app List.length] in HT |- *.
    exact (decl_typed_rec_ps _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ Hk Hin Heq Hj HPk HT).
Qed.

(** The type of the recursive result of a recursive argument, in a
    branch's context, is a type, and equal ones of equal motives. *)
Lemma rec_ih_typed : forall Θ Ξ Γ p D k Mk Us As As' i c gs gs1 t gs2 E,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As i -> motives_typed Θ Ξ Γ p D Us As' i -> motives_eq Θ Ξ Γ p D Us As As' i ->
    List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ->
    let T X := ptyp_ihty X (ι (wk_shiftn (List.length E + List.length gs + im_nn Mk)))
                 (ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E))
                 (a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1))) t in
    exists j, Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ T As : Typeω@j /\ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ T As' : Typeω@j /\
      Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ⊢ T As ≈ T As' : Typeω@j.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl Hσ HM HA HA' HAA Hin Heq HΨ T.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hk HΓ HUl Hσ Hin Heq HΨ) as (Hb & Hθ & Huc & Hx).
  destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HD Hk Hin Heq) as (Mj & Hj & HPl & HBt & HPt).
  exact (ihty_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc HUl HM HA HA' HAA Hb Hθ Huc Hj HPl HBt HPt Hx).
Qed.

Lemma cargs_nrec_snoc : forall gs g,
    cargs_nrec (gs ++ g :: nil) = cargs_nrec gs + match g with ca_rec _ => 1 | ca_arg _ => 0 end.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?IH; destruct g; reflexivity. Qed.

(** ** The Branches' Contexts *)

(** The motives' contexts are well formed, and each motive is a type there. *)
Lemma ihs_ctx_wf : forall Θ Ξ Γ p D k Mk Us As i c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As i ->
    List.In (c, gs) (im_cons Mk) ->
    forall rest gs1 E, gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs ->
      ⊢ Θ ⍮ Ξ ⍮ ihs_ctx_aux (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E ++ cinst Γ p D Mk Us gs.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl Hσ HM HA Hin rest.
  assert (HAA : motives_eq Θ Ξ Γ p D Us As As i) by (intros j Mj Hj; apply wf_exp_eq_refl; exact (HA _ _ Hj)).
  induction rest as [| [A' | t] rest IH]; intros gs1 E Heq HE HΨ; cbn [ihs_ctx_aux List.app]; [ exact HΨ | |].
  - replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg A' :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | exact HΨ ].
  - destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hk HΓ HUl Hσ HM HA HA HAA Hin Heq HΨ)
      as (j & HAj & _).
    rewrite <- List.app_assoc; cbn [List.app].
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec t :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    match goal with |- ⊢ _ ⍮ _ ⍮ ?L ++ ?e :: E ++ _ =>
      change (L ++ e :: E ++ cinst Γ p D Mk Us gs) with (L ++ (e :: E) ++ cinst Γ p D Mk Us gs) end.
    match goal with |- ⊢ _ ⍮ _ ⍮ ihs_ctx_aux _ _ _ _ _ ?n _ ++ (?e :: E) ++ _ =>
      replace n with (List.length (e :: E)) by reflexivity end.
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia |].
    cbn [List.app]; econstructor; exact HAj.
Qed.

Lemma elim_bctx_wf : forall Θ Ξ Γ p D k Mk Us As i c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As i ->
    ind_con Mk c = Some gs ->
    ⊢ Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl Hσ HM HA Hcon.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  pose proof (ihs_ctx_wf _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ HUl Hσ HM HA Hin gs nil nil eq_refl eq_refl Hi) as H.
  unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
Qed.

(** ** A Constructor Applied *)

Lemma vars_from_shift : forall k n, List.map (fun M => M[wk_shiftn k]ʷ) (vars_from 0 n) = vars_from k n.
Proof. intros; unfold vars_from; rewrite List.map_map; apply List.map_ext; intros; cbn; f_equal; lia. Qed.

Lemma vars_from_sb_of_list_app : forall Ms Ns σ,
    List.map (fun M => M[sb_of_list σ (Ms ++ Ns)]) (vars_from (List.length Ns) (List.length Ms)) = Ms.
Proof.
  intros; rewrite <- vars_from_shift, List.map_map.
  rewrite (List.map_ext _ (fun M => M[sb_of_list σ Ms])) by (intros; apply exp_shift_past).
  apply vars_from_sb_of_list.
Qed.

Lemma vars_from_sb_of_list_mid : forall Ls Ms Ns σ,
    List.map (fun M => M[sb_of_list σ (Ls ++ Ms ++ Ns)]) (vars_from (List.length Ns) (List.length Ms)) = Ms.
Proof.
  intros; rewrite (List.map_ext _ (fun M => M[sb_of_list (sb_of_list σ Ls) (Ms ++ Ns)]))
    by (intros; rewrite sb_of_list_app; reflexivity).
  apply vars_from_sb_of_list_app.
Qed.

Lemma firstn_app_len : forall {X : Type} (l l' : list X) n, List.length l = n -> List.firstn n (l ++ l') = l.
Proof. intros * <-; rewrite List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r. Qed.

Lemma skipn_app_len : forall {X : Type} (l l' : list X) n, List.length l = n -> List.skipn n (l ++ l') = l'.
Proof. intros * <-; rewrite List.skipn_app, List.skipn_all, Nat.sub_diag; reflexivity. Qed.

Lemma member_decl_lt : forall Θ Ξ D k M pm,
    decl_typed Θ Ξ D -> ind_member D k = Some M -> im_head M = mh_decl pm -> k < ind_ndecl D.
Proof. intros * HD Hk Hh; apply (decl_typed_order _ _ _ HD _ _ Hk); unfold im_is_decl; rewrite Hh; reflexivity. Qed.

Lemma member_lt_decl : forall Θ Ξ D k M,
    decl_typed Θ Ξ D -> ind_member D k = Some M -> k < ind_ndecl D -> exists pm, im_head M = mh_decl pm.
Proof.
  intros * HD Hk Hlt; pose proof (proj2 (decl_typed_order _ _ _ HD _ _ Hk) Hlt) as H; unfold im_is_decl in H.
  destruct (im_head M) as [pm |]; [ eauto | discriminate ].
Qed.

(** The parameters of a member typed one by one, read off a substitution
    into its parameters, and back. *)
Lemma wf_sub_params : forall Θ Ξ Γ D k M Ps,
    decl_typed Θ Ξ D -> decl_closed D -> ind_member D k = Some M -> ⊢ Θ ⍮ Ξ ⍮ Γ -> List.length Ps = im_np D M ->
    (forall j P T, nth_error Ps j = Some P -> nth_error (tele_insts (im_params D M) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ps : im_params D M.
Proof.
  intros * HD Hc Hk HΓ Hl HPs; rewrite <- (List.app_nil_r (im_params D M)).
  eapply wf_sub_of_list; [ eapply decl_closed_params_ass; eassumption
                         | rewrite List.app_nil_r; exact (member_params_wf _ _ _ _ _ HD Hk)
                         | exact (wf_sub_to_nil _ _ _ HΓ) | rewrite length_im_params; exact Hl | exact HPs ].
Qed.

(** Terms typed at the instances of a telescope are typed at those of one
    equal to it. *)
Lemma tele_insts_conv_rev : forall Θ Ξ Γ Δ Δ' Ms,
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> List.length Ms = List.length Δ' ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts Δ' Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T.
Proof.
  intros * HΔ Ha Ha' Hl HMs.
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha' (ext_eq_ctx_right _ _ _ _ _ HΔ) Hl HMs) as Hσ.
  pose proof (wf_sub_compose _ _ _ _ _ _ _ (ctxsub_ext _ _ _ _ _ HΔ Ha) Hσ) as Hσ'.
  rewrite sb_compose_id_left in Hσ'.
  eapply wf_sub_of_list_inv; [ exact Ha | rewrite (ext_eq_length _ _ _ _ _ HΔ); exact Hl | exact Hσ' ].
Qed.

(** A constructor of a declared member applied to its parameters and
    arguments. *)
Lemma wf_con_apps_decl : forall Θ Ξ Γ p D m Mm c gs Ps As,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D m = Some Mm -> m < ind_ndecl D ->
    ind_con Mm c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, nth_error As k = Some N ->
       nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_con p m c) (Ps ++ As) : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps).
Proof.
  intros * Hg HDs Hl Hm Hlt Hcon HΓ HPl HPs HAl HAs.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (con_cod_typed _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hcon) as [j Hj].
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ0 & _ & _).
  destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hcon) as [j0 Hj0].
  assert (HC : Θ ⍮ Ξ ⍮ Γ ⊢ a_con p m c : con_ty p D m Mm gs) by (eapply wf_con_of_lookup; eassumption).
  unfold con_ty in HC; rewrite <- ctx_pi_app in HC.
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ Hj) as (_ & Hscod & _).
  assert (Hass : tele_ass (cargs_ctx p D Mm gs ++ im_params D Mm))
    by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | eapply decl_closed_params_ass; eassumption ]).
  pose proof (wf_apps_closed_pi _ _ _ _ j _ _ (Ps ++ As) Hass
                (cargs_ctx_closed p D m Mm c gs gs nil Hc Hm Hin (eq_sym (List.app_nil_r gs))) Hscod Hj HΓ HC) as HR.
  set (Us := List.firstn (ind_nu D) Ps); set (Ns := List.skipn (ind_nu D) Ps).
  assert (HPs' : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  replace (ind_mty p D m Us Ns)
    with ((ind_mty p D m (ind_uvars D (im_nn Mm) (List.length gs)) (vars_from (List.length gs) (im_nn Mm)))[sb_of_list Id (Ps ++ As)]).
  - apply HR.
    + rewrite !List.length_app, length_cargs_ctx, length_im_params, HPl, HAl; lia.
    + rewrite tele_insts_app by (try (eapply decl_closed_params_ass; eassumption); rewrite length_im_params; exact HPl).
      intros k N T HN HT.
      assert (Hl2 : List.length (tele_insts (im_params D Mm) Id Ps) = List.length Ps)
        by (rewrite length_tele_insts by (eapply decl_closed_params_ass; eassumption); rewrite length_im_params; lia).
      destruct (Nat.lt_ge_cases k (List.length Ps)) as [Hk | Hk].
      * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; eauto.
      * rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl2 in HT; eauto.
  - rewrite ind_mty_sub by (try exact Hc; apply length_ind_uvars).
    rewrite HPs', <- List.app_assoc; f_equal.
    + unfold ind_uvars.
      replace (vars_from (List.length gs + im_nn Mm) (ind_nu D)) with (vars_from (List.length (Ns ++ As)) (List.length Us))
        by (rewrite List.length_app, HNl, HAl, HUl; f_equal; lia).
      apply vars_from_sb_of_list_app.
    + replace (vars_from (List.length gs) (im_nn Mm)) with (vars_from (List.length As) (List.length Ns))
        by (rewrite HNl, HAl; reflexivity).
      apply vars_from_sb_of_list_mid.
Qed.

(** The parameters of a view's container at the view's instance: the
    uniform ones at the view's uniform arguments, the others the view's. *)
Lemma view_params_typed : forall Θ Ξ Γ p D j Mj qc k' Is vm D' Mk' Us Ns,
    ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ p = Some D ->
    decls_typed Θ Ξ -> decl_typed Θ Ξ D -> decl_closed D -> decl_closed D' ->
    ind_member D j = Some Mj -> im_head Mj = mh_view qc k' Is vm ->
    ind_lookup Θ Ξ qc = Some D' -> ind_member D' k' = Some Mk' -> List.nth_error vm k' = Some j ->
    List.length Is = ind_nu D' -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    List.length Ns = im_nn Mj ->
    (forall k N T, nth_error Ns k = Some N -> nth_error (tele_insts (im_nparams Mj) (sb_of_list Id Us) Ns) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    List.length Ns = im_nn Mk' /\
    forall k P T, nth_error (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) k = Some P ->
      nth_error (tele_insts (im_params D' Mk') Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) k = Some T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ P : T.
Proof.
  intros * Hg Hl HDs HD Hc Hc' Hj Hh Hl' Hk' Hself HIl HΓ HUl HUs HNl HNs.
  pose proof (HDs _ _ Hl') as HD'.
  pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
  pose proof (decl_typed_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hj Hh Hl' Hk' Hself Hj) as HNeq.
  set (Is' := List.map (fun I => I[sb_of_list Id Us]) Is).
  assert (HIl' : List.length Is' = ind_nu D') by (unfold Is'; rewrite List.length_map; exact HIl).
  assert (HNl' : List.length Ns = im_nn Mk').
  { rewrite HNl; unfold im_nn; rewrite (ext_eq_length _ _ _ _ _ HNeq), length_tele_sub; reflexivity. }
  split; [ exact HNl' |].
  unfold im_params; intros k N T HN HT.
  rewrite tele_insts_app in HT by (try exact (decl_typed_ass _ _ _ HD'); exact HIl').
  assert (Hl1 : List.length (tele_insts (ind_uparams D') Id Is') = ind_nu D')
    by (rewrite length_tele_insts by exact (decl_typed_ass _ _ _ HD'); rewrite HIl'; unfold ind_nu; lia).
  destruct (Nat.lt_ge_cases k (ind_nu D')) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
    unfold Is' in HN, HT.
    rewrite <- (tele_insts_sub (ind_uparams D') 0 Id Id (sb_of_list Id Us) Is (decl_typed_ass _ _ _ HD') (decl_closed_uparams _ Hc')
                  ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HN as (I & HI & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (decl_typed_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ Hj Hh Hl' HI HT0) Hσ).
  - rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
    rewrite HIl' in HN; rewrite Hl1 in HT.
    revert HN HT; generalize (k - ind_nu D'); intros k0 HN HT.
    rewrite (tele_insts_sb_eq _ (sb_of_list Id Is') (sb_of_list Id Is' ⨟ Id)) in HT
      by (intro; symmetry; apply sb_compose_id_right).
    rewrite <- tele_insts_tele_sub in HT.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as HNeq'.
    rewrite (nparams_sub D' k' Mk' Is (sb_of_list Id Us) Hc' Hk' HIl) in HNeq'; fold Is' in HNeq'.
    eapply (tele_insts_conv _ _ _ _ _ _ HNeq');
      [ apply tele_ass_sub; exact (decl_typed_nparams_ass _ _ _ HD _ _ Hj)
      | apply tele_ass_sub; exact (decl_typed_nparams_ass _ _ _ HD' _ _ Hk')
      | rewrite length_tele_sub; exact HNl | | exact HN | exact HT ].
    intros k1 N1 T1 HN1 HT1; apply (HNs _ _ _ HN1).
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT1 by apply sb_compose_id_right.
    exact HT1.
Qed.

(** The parameters and arguments of a view's constructor, as the
    container's constructor's: the container's parameters at the view's
    instance, and the arguments at the container's arguments' types. *)
#[warnings="-cannot-define-projection"]
Record view_con_inst (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (qc : qname) (k' : nat) (Is : list exp) (c : String.string)
    (Us Ns As : list exp) : Prop := mk_view_con_inst
  { (** The container group *)
    view_con_inst_decl : ind_decl
    (** The container's member viewed *)
  ; view_con_inst_mem : imember
    (** The container constructor's arguments *)
  ; view_con_inst_args : list carg
    (** The container is found at [qc] *)
  ; view_con_inst_lookup : ind_lookup Θ Ξ qc = Some view_con_inst_decl
    (** The viewed member is the container's [k']-th *)
  ; view_con_inst_member : ind_member view_con_inst_decl k' = Some view_con_inst_mem
    (** It is a declared member *)
  ; view_con_inst_lt : k' < ind_ndecl view_con_inst_decl
    (** The constructor [c] is the viewed member's *)
  ; view_con_inst_con : ind_con view_con_inst_mem c = Some view_con_inst_args
    (** The view's instance and the parameters [Ns] are all the viewed
        member's parameters *)
  ; view_con_inst_plen : List.length (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) = im_np view_con_inst_decl view_con_inst_mem
    (** One argument per constructor argument *)
  ; view_con_inst_alen : List.length As = List.length view_con_inst_args
    (** The parameters are typed at the viewed member's telescope *)
  ; view_con_inst_params : forall k P T, nth_error (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) k = Some P ->
      nth_error (tele_insts (im_params view_con_inst_decl view_con_inst_mem) Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) k = Some T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ P : T
    (** The arguments are typed at the container constructor's argument
        telescope, at the parameters *)
  ; view_con_inst_cargs : forall k N T, nth_error As k = Some N ->
      nth_error (tele_insts (cargs_ctx qc view_con_inst_decl view_con_inst_mem view_con_inst_args)
                   (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) k = Some T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : T }.

Lemma view_con_inst_of : forall Θ Ξ Γ p D m Mm qc k' Is vm c gs Us Ns As,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm -> ind_con Mm c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm ->
    (forall k N T, nth_error Ns k = Some N -> nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    List.length As = List.length gs ->
    (forall k N T, nth_error As k = Some N ->
       nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    view_con_inst Θ Ξ Γ qc k' Is c Us Ns As.
Proof.
  intros * Hg HDs Hl Hm Hh Hcon HΓ HUl HUs HNl HNs HAl HAs.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (params_typed_join _ _ _ Hc _ _ _ _ _ Hm HUl HUs HNs) as HPs.
  assert (HPl : List.length (Us ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
  destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & Hlt' & HIl & _ & Hself & Hnames & _).
  pose proof (HDs _ _ Hl') as HD'.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl') as Hc'.
  destruct (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ Us Ns Hg Hl HDs HD Hc Hc' Hm Hh Hl' Hk' Hself HIl HΓ HUl HUs HNl HNs)
    as [HNl' HPs'].
  set (Is' := List.map (fun I => I[sb_of_list Id Us]) Is) in *.
  assert (HIl' : List.length Is' = ind_nu D') by (unfold Is'; rewrite List.length_map; exact HIl).
  assert (Hcon' : exists gs', ind_con Mk' c = Some gs').
  { pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (Hc0 : List.In c (List.map fst (im_cons Mk'))) by (rewrite <- Hnames; apply (List.in_map fst _ _ Hin)).
    apply List.in_map_iff in Hc0 as ([c0 gs0] & Hc0 & Hin0); cbn in Hc0; subst c0.
    exact (cons_lookup_of_in _ _ _ Hin0). }
  destruct Hcon' as [gs' Hcon'].
  (* the arguments: the view's are the container's at the view's instance *)
  pose proof (decl_typed_view_args _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hm Hh Hl' Hk' Hself Hm Hcon' Hcon) as HV.
  pose proof (wf_sub_params _ _ _ _ _ _ _ HD Hc Hm HΓ HPl HPs) as Hσ.
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ HV Hσ) as HV'.
  assert (Eq : tele_sub (tele_sub (cargs_ctx qc D' Mk' gs') (sb_qn (im_nn Mm) (sb_of_list Id Is))) (sb_of_list Id (Us ++ Ns))
               = tele_sub (cargs_ctx qc D' Mk' gs') (sb_of_list Id (Is' ++ Ns))).
  { rewrite tele_sub_sub.
    eapply tele_scoped_sub_agree;
      [ eapply decl_closed_cargs_scoped; [ exact Hc' | exact Hk' | exact (cons_lookup_in _ _ _ Hcon') ] |].
    intros x Hx; unfold im_np in Hx; cbn [sb_compose].
    destruct (Nat.lt_ge_cases x (im_nn Mm)) as [Hx1 | Hx1].
    - rewrite sb_qn_lt by exact Hx1; cbn [sentry_sub].
      rewrite !sb_of_list_app; apply sb_of_list_lt_base; lia.
    - rewrite sb_qn_ge by exact Hx1.
      rewrite !sb_of_list_app.
      replace x with (List.length Ns + (x - im_nn Mm)) at 2 by lia.
      rewrite sb_of_list_ge.
      unfold Is'; rewrite <- sb_of_list_lt_compose by lia.
      rewrite <- sentry_sub_of_wk, sentry_sub_sub; apply sentry_sub_sb_eq; intros z; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      rewrite <- HNl, Nat.add_comm, sb_of_list_ge; reflexivity. }
  rewrite Eq in HV'.
  assert (HAl' : List.length As = List.length gs')
    by (rewrite HAl; pose proof (ext_eq_length _ _ _ _ _ HV) as E; rewrite length_tele_sub, !length_cargs_ctx in E; lia).
  unfold Is' in *.
  econstructor; [ exact Hl' | exact Hk' | exact Hlt' | exact Hcon' | rewrite List.length_app, List.length_map, HIl, HNl'; unfold im_np; lia
                | exact HAl' | exact HPs' |].
  intros k N T HN HT.
  eapply (tele_insts_conv_rev _ _ _ _ _ _ HV');
    [ apply tele_ass_sub, cargs_ctx_aux_ass | apply tele_ass_sub, cargs_ctx_aux_ass
    | rewrite length_tele_sub, length_cargs_ctx; exact HAl | | exact HN | ].
  - intros k1 N1 T1 HN1 HT1; apply (HAs _ _ _ HN1).
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id (Us ++ Ns))) in HT1 by apply sb_compose_id_right.
    exact HT1.
  - rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id (Is' ++ Ns))) by apply sb_compose_id_right.
    exact HT.
Qed.

(** The constructor of a member, the container's at a view, applied to the
    member's uniform arguments at the uniform parameters [Us], the
    non-uniform parameters [Ns] and the arguments [As]: of the member's
    type at them. *)
Lemma wf_con_apps_at : forall Θ Ξ Γ p D m Mm c gs Us Ns As,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D m = Some Mm ->
    ind_con Mm c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm ->
    (forall k N T, nth_error Ns k = Some N -> nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    List.length As = List.length gs ->
    (forall k N T, nth_error As k = Some N ->
       nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As) : ind_mty p D m Us Ns.
Proof.
  intros * Hg HDs Hl Hm Hcon HΓ HUl HUs HNl HNs HAl HAs.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (params_typed_join _ _ _ Hc _ _ _ _ _ Hm HUl HUs HNs) as HPs.
  assert (HPl : List.length (Us ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
  unfold im_ref, im_pre; destruct (im_head Mm) as [pm | qc k' Is vm] eqn:Hh; cbn [fst snd].
  - (* a declared member *)
    pose proof (member_decl_lt _ _ _ _ _ _ HD Hm Hh) as Hlt.
    rewrite List.app_assoc.
    pose proof (wf_con_apps_decl _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hlt Hcon HΓ HPl HPs HAl HAs) as H.
    rewrite firstn_app_len, skipn_app_len in H by exact HUl; exact H.
  - (* a view: the container's constructor *)
    destruct (view_con_inst_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hcon HΓ HUl HUs HNl HNs HAl HAs)
      as [D' Mk' gs' Hl' Hk' Hlt' Hcon' HPl' HAl' HPs' HAs'].
    pose proof (HDs _ _ Hl') as HD'.
    destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D'' & Mk'' & Hl'' & Hk'' & _ & HIl & _).
    rewrite Hl' in Hl''; injection Hl'' as <-; rewrite Hk' in Hk''; injection Hk'' as <-.
    set (Is' := List.map (fun I => I[sb_of_list Id Us]) Is) in *.
    assert (HIl' : List.length Is' = ind_nu D') by (unfold Is'; rewrite List.length_map; exact HIl).
    rewrite List.app_assoc.
    pose proof (wf_con_apps_decl _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl' Hk' Hlt' Hcon' HΓ HPl' HPs' HAl' HAs') as H.
    rewrite firstn_app_len, skipn_app_len in H by exact HIl'.
    destruct (member_lt_decl _ _ _ _ _ HD' Hk' Hlt') as [pm' Hh'].
    unfold ind_mty in H |- *; rewrite Hm; rewrite Hk' in H; unfold im_ty_at, im_ref, im_pre in H |- *.
    rewrite Hh; rewrite Hh' in H; cbn [fst snd] in H |- *.
    fold Is'; exact H.
Qed.

(** ** The Branch's Type *)

Lemma exp_mvc_apps : forall Ns M n, exp_mvc n (apps M Ns) <-> exp_mvc n M /\ List.Forall (exp_mvc n) Ns.
Proof.
  induction Ns as [| N Ns IH]; intros; cbn; [ split; [ auto | tauto ] |].
  rewrite IH, List.Forall_cons_iff; cbn; tauto.
Qed.

Lemma vars_from_mvc : forall n j k, List.Forall (exp_mvc n) (vars_from j k).
Proof. intros; unfold vars_from; apply List.Forall_map, List.Forall_forall; intros; exact I. Qed.

(** A member at the uniform parameters as variables has no free module
    variable. *)
Lemma ind_mty_vars_mvc : forall p D j nn k Ns,
    decl_closed D -> decl_mvc D -> List.Forall (exp_mvc 0) Ns -> exp_mvc 0 (ind_mty p D j (ind_uvars D nn k) Ns).
Proof.
  intros * Hc Hmv HNs; unfold ind_mty.
  destruct (ind_member D j) as [M |] eqn:HM; [| exact I ].
  unfold im_ty_at; apply exp_mvc_apps; split; [ exact I |]; apply List.Forall_app; split; [| exact HNs ].
  unfold im_pre; destruct (im_head M) as [pm | qc k' Is vm] eqn:Hh; [ apply vars_from_mvc |].
  pose proof (proj1 (proj2 (decl_mvc_members _ Hmv _ _ HM))) as HIs; rewrite Hh in HIs; cbn in HIs.
  pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ HM Hh) as HsIs.
  apply List.Forall_map; apply List.Forall_forall; intros I HI.
  unfold ind_uvars; rewrite exp_at_vars;
    [ apply exp_mvc_wk | exact (proj1 (List.Forall_forall _ _) HsIs I HI) | ];
    exact (proj1 (List.Forall_forall _ _) HIs I HI).
Qed.

Lemma ptyp_ty_mvc : forall p D nn t pat,
    decl_closed D -> decl_mvc D ->
    List.Forall (exp_mvc 0) (ptyp_doms t) -> List.Forall (exp_mvc 0) (ptyp_ps t) -> exp_mvc 0 (ptyp_ty p D nn pat t).
Proof.
  intros p D nn t; induction t as [j Ps | B t IH]; intros pat Hc Hmv HB HP; cbn [ptyp_ty ptyp_doms ptyp_ps] in *.
  - apply ind_mty_vars_mvc; [ exact Hc | exact Hmv |].
    apply List.Forall_map; eapply List.Forall_impl; [| exact HP ]; intros; apply exp_mvc_wk; assumption.
  - inversion_clear HB as [| ? ? HB1 HB2]; cbn; split; [ apply exp_mvc_wk; exact HB1 |].
    eapply exp_mvc_mono; [| apply IH; assumption ]; lia.
Qed.

Lemma cargs_ctx_aux_mvc : forall p D nn gs pat,
    decl_closed D -> decl_mvc D -> List.Forall carg_mvc gs -> ctx_mvc (cargs_ctx_aux p D nn pat gs).
Proof.
  induction gs as [| [A | t] gs IH]; intros pat Hc Hmv Hg; cbn; [ constructor | |].
  all: inversion_clear Hg as [| ? ? Hg1 Hg2]; apply List.Forall_app; split;
    [ apply IH; assumption | constructor; [| constructor ] ]; cbn in *.
  - apply exp_mvc_wk; exact Hg1.
  - apply ptyp_ty_mvc; [ exact Hc | exact Hmv | apply Hg1 | apply Hg1 ].
Qed.

Lemma cargs_ctx_mvc : forall Θ Ξ p D k Mk c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_member D k = Some Mk -> List.In (c, gs) (im_cons Mk) ->
    ctx_mvc (cargs_ctx p D Mk gs).
Proof.
  intros * HD Hc Hk Hin; pose proof (decl_mvc_members _ (decl_typed_mvc _ _ _ HD) _ _ Hk) as (_ & _ & Hmvc).
  apply cargs_ctx_aux_mvc; [ exact Hc | exact (decl_typed_mvc _ _ _ HD) | eauto ].
Qed.

(** The instance of the motive's context of the member [k] the type of a
    branch of a constructor of [k] substitutes: the non-uniform parameters
    and the constructor applied, as variables of the branch's context. *)
Lemma wf_bty_sub : forall Θ Ξ Γ p D k Mk Us As i c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As i ->
    ind_con Mk c = Some gs ->
    Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ
      ⊢ˢ sb_of_list (ι (wk_shiftn (im_nn Mk + List.length gs + cargs_nrec gs)))
           (vars_from (cargs_nrec gs + List.length gs) (im_nn Mk) ++
            apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
              (im_pre Mk (List.map (fun U => U[wk_shiftn (im_nn Mk + List.length gs + cargs_nrec gs)]ʷ) Us) ++
               vars_from (cargs_nrec gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec gs) (List.length gs))
            :: nil)
      : elim_mctx p D k Mk Us ++ Γ.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl HUs HM HA Hcon.
  pose proof (HDs _ _ Hl) as HD; pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  pose proof (elim_bctx_wf _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ HUl Hσ HM HA Hcon) as HB.
  set (nn := im_nn Mk) in *.
  set (n := nn + List.length gs + cargs_nrec gs).
  set (IHs := ihs_ctx_aux nn As Us (List.length gs) nil 0 gs).
  set (Cs := tele_sub (cargs_ctx p D Mk gs) (sb_qn nn (sb_of_list Id Us))).
  set (Nc := tele_sub (im_nparams Mk) (sb_of_list Id Us)).
  assert (HBeq : elim_bctx p D Mk gs As Us ++ Γ = (IHs ++ Cs) ++ Nc ++ Γ)
    by (unfold elim_bctx; rewrite <- !List.app_assoc; reflexivity).
  assert (HlI : List.length IHs = cargs_nrec gs) by (unfold IHs; apply length_ihs_ctx_aux).
  assert (HlC : List.length Cs = List.length gs) by (unfold Cs; rewrite length_tele_sub, length_cargs_ctx; reflexivity).
  assert (HlN : List.length Nc = nn) by (unfold Nc; apply length_nparams_sub).
  assert (Hw : Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ ⊢ʷ wk_shiftn n : Γ).
  { rewrite HBeq, List.app_assoc.
    replace n with (List.length ((IHs ++ Cs) ++ Nc)) by (rewrite !List.length_app, HlI, HlC, HlN; unfold n; lia).
    apply wf_wk_shiftn_app'; rewrite <- List.app_assoc, <- HBeq; exact HB. }
  (* the uniform parameters, shifted, and the non-uniform ones, as variables *)
  set (Us' := List.map (fun U => U[wk_shiftn n]ʷ) Us).
  assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
  assert (HUs' : forall k U T, List.nth_error Us' k = Some U ->
             List.nth_error (tele_insts (ind_uparams D) Id Us') k = Some T -> Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ ⊢ U : T).
  { intros k0 U' T' HU HT; unfold Us' in *.
    rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
    apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    exact (wk_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hw). }
  set (nvars := vars_from (cargs_nrec gs + List.length gs) nn).
  set (avars := vars_from (cargs_nrec gs) (List.length gs)).
  assert (Hvars : forall τ, (forall y, y < ind_nu D -> sentry_exp (τ y) = (sentry_exp (sb_of_list Id Us y))[wk_shiftn n]ʷ) ->
             forall k N T, List.nth_error nvars k = Some N ->
               List.nth_error (tele_insts (im_nparams Mk) τ nvars) k = Some T ->
               Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ ⊢ N : T).
  { intros τ Hτ k0 N T HN HT.
    replace nvars with (vars_from (List.length (IHs ++ Cs)) (List.length (im_nparams Mk))) in HN, HT
      by (rewrite List.length_app, HlI, HlC; reflexivity).
    rewrite HBeq.
    eapply (wf_vars_tele_gen _ _ _ _ (sb_of_list Id Us) τ Γ (ind_nu D));
      [ eapply decl_closed_nparams_ass; eassumption | exact (decl_nparams_mvc _ _ _ HD _ _ Hk)
      | eapply decl_closed_nparams_scoped; eassumption
      | fold Nc; rewrite <- HBeq; exact HB | | exact HN | exact HT ].
    intros y Hy; rewrite Hτ by exact Hy; rewrite List.length_app, HlI, HlC; change (List.length (im_nparams Mk)) with nn.
    unfold n; f_equal; f_equal; lia. }
  assert (HNs : forall k N T, List.nth_error nvars k = Some N ->
             List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Us') nvars) k = Some T ->
             Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ ⊢ N : T)
    by (apply Hvars; intros y Hy; unfold Us'; rewrite sb_of_list_map by lia; reflexivity).
  assert (HAs : forall k N T, List.nth_error avars k = Some N ->
             List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ nvars)) avars) k = Some T ->
             Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As Us ++ Γ ⊢ N : T).
  { intros k0 N T HN HT.
    replace avars with (vars_from (List.length IHs) (List.length (cargs_ctx p D Mk gs))) in HN, HT
      by (rewrite HlI, length_cargs_ctx; reflexivity).
    rewrite HBeq, <- List.app_assoc.
    eapply (wf_vars_tele_gen _ _ IHs (cargs_ctx p D Mk gs) (sb_qn nn (sb_of_list Id Us)) _ (Nc ++ Γ) (im_np D Mk));
      [ apply cargs_ctx_aux_ass | eapply cargs_ctx_mvc; eassumption | eapply decl_closed_cargs_scoped; eassumption
      | fold Cs; rewrite List.app_assoc, <- HBeq; exact HB | | exact HN | exact HT ].
    intros y Hy; rewrite length_cargs_ctx, HlI.
    destruct (Nat.lt_ge_cases y nn) as [Hy1 | Hy1].
    - rewrite sb_of_list_app; unfold nvars; rewrite sb_of_list_vars by lia; rewrite sb_qn_lt by exact Hy1; cbn; f_equal; lia.
    - replace y with (List.length nvars + (y - nn)) at 1 by (unfold nvars; rewrite length_vars_from; lia).
      rewrite sb_of_list_app, sb_of_list_ge; unfold Us'; rewrite sb_of_list_map by (rewrite HUl; unfold im_np, nn in *; lia).
      rewrite sb_qn_ge by exact Hy1; rewrite <- sentry_exp_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold n; lia. }
  (* the substitution *)
  apply wf_sub_of_list; [ eapply elim_mctx_ass; eassumption | exact (HM _ _ Hk) | apply wf_sub_of_wk, Hw
                        | unfold nvars; rewrite List.length_app, length_vars_from, length_elim_mctx; cbn; lia |].
  intros k0 N T HN HT.
  unfold elim_mctx in HT.
  change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
  assert (Hrass : tele_ass Nc) by (apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption).
  fold Nc in HT.
  rewrite tele_insts_app in HT by (try exact Hrass; unfold nvars; rewrite length_vars_from; symmetry; exact HlN).
  assert (Hl2 : List.length (tele_insts Nc (ι (wk_shiftn n)) nvars) = nn)
    by (rewrite length_tele_insts by exact Hrass; rewrite HlN; unfold nvars; rewrite length_vars_from; lia).
  destruct (Nat.lt_ge_cases k0 nn) as [Hk0 | Hk0].
  - rewrite List.nth_error_app1 in HN by (unfold nvars; rewrite length_vars_from; lia); rewrite List.nth_error_app1 in HT by lia.
    unfold Nc in HT; rewrite tele_insts_tele_sub in HT.
    apply (Hvars _ ltac:(intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; reflexivity) k0); assumption.
  - rewrite List.nth_error_app2 in HN by (unfold nvars; rewrite length_vars_from; lia).
    rewrite List.nth_error_app2 in HT by (rewrite Hl2; lia).
    unfold nvars in HN; rewrite length_vars_from in HN; rewrite Hl2 in HT.
    destruct (k0 - nn) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
    injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
    rewrite ind_head_inst by (try assumption; apply length_vars_from).
    rewrite map_sub_of_wk; fold Us' nvars.
    exact (wf_con_apps_at _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon (wf_wk_dom _ _ _ _ _ Hw) HUl' HUs'
             ltac:(unfold nvars; apply length_vars_from) HNs ltac:(unfold avars; apply length_vars_from) HAs).
Qed.

(** ** The Motives Varying *)

(** [cinst] without the outer context: the constructor's arguments and the
    member's non-uniform parameters at [Us]. *)
Definition ctel (p : qname) (D : ind_decl) (Mk : imember) (Us : list typ) (gs : list carg) : ctx :=
  tele_sub (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) (sb_of_list Id Us)) ++ tele_sub (im_nparams Mk) (sb_of_list Id Us).

Lemma cinst_ctel : forall Γ p D Mk Us gs, cinst Γ p D Mk Us gs = ctel p D Mk Us gs ++ Γ.
Proof. intros; unfold cinst, ctel; rewrite List.app_assoc; reflexivity. Qed.

Lemma ihs_ctx_eq : forall Θ Ξ Γ p D k Mk Us As As' i c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As i -> motives_typed Θ Ξ Γ p D Us As' i -> motives_eq Θ Ξ Γ p D Us As As' i ->
    List.In (c, gs) (im_cons Mk) ->
    forall rest gs1 E E', gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 -> List.length E' = cargs_nrec gs1 ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ E ++ ctel p D Mk Us gs ≈ E' ++ ctel p D Mk Us gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ ihs_ctx_aux (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E ++ ctel p D Mk Us gs
               ≈ ihs_ctx_aux (im_nn Mk) As' Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E' ++ ctel p D Mk Us gs.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl Hσ HM HA HA' HAA Hin rest.
  induction rest as [| [B | t] rest IH]; intros gs1 E E' Heq HE HE' HEE; cbn [ihs_ctx_aux List.app]; [ exact HEE | |].
  - replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg B :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia
              | rewrite cargs_nrec_snoc, HE'; lia | exact HEE ].
  - assert (HΨ : ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk Us gs)
      by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_left; exact HEE).
    assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ E' ++ cinst Γ p D Mk Us gs)
      by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_right; exact HEE).
    destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hk HΓ HUl Hσ HM HA HA' HAA Hin Heq HΨ)
      as (j & HAj & HA'j & HAAj).
    destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' Hg HDs Hl Hk HΓ HUl Hσ HM HA HA' HAA Hin Heq HΨ')
      as (j' & _ & HA'j' & _).
    rewrite HE', <- HE in HA'j'.
    rewrite cinst_ctel, List.app_assoc in HAj, HA'j, HAAj, HA'j'.
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec t :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    rewrite <- !List.app_assoc.
    eapply (IH (gs1 ++ ca_rec t :: nil) (_ :: E) (_ :: E'));
      [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
      | cbn; rewrite cargs_nrec_snoc, HE'; lia |].
    cbn [List.app]; eapply wf_ext_eq_ass with (i := max j j');
      [ exact HEE | eapply lift_exp_max_left; exact HAj | eapply lift_exp_eq_max_left; exact HAAj
      | eapply lift_exp_max_right; exact HA'j' ].
Qed.

Lemma elim_bctx_eq : forall Θ Ξ Γ p D k Mk Us As As' i c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As i -> motives_typed Θ Ξ Γ p D Us As' i -> motives_eq Θ Ξ Γ p D Us As As' i ->
    ind_con Mk c = Some gs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs As Us ≈ elim_bctx p D Mk gs As' Us.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl Hσ HM HA HA' HAA Hcon.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl) as Hc.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  assert (H0 : Θ ⍮ Ξ ⍮ Γ ⊢ˣ nil ++ ctel p D Mk Us gs ≈ nil ++ ctel p D Mk Us gs).
  { apply ctx_ext_refl; [| cbn [List.app]; rewrite <- cinst_ctel; exact Hi ].
    cbn [List.app]; unfold ctel; apply List.Forall_app; split; apply tele_ass_sub;
      [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ]. }
  exact (ihs_ctx_eq _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ HUl Hσ HM HA HA' HAA Hin gs nil nil nil eq_refl eq_refl eq_refl H0).
Qed.

(** The type of a branch, the motive of its member varying, the others'
    being [As']. *)
Lemma elim_bty_eq : forall Θ Ξ Γ p D k Mk Us As' A A' i c gs,
    ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    (forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ) ->
    motives_typed Θ Ξ Γ p D Us As' i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D k Mk Us ++ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D k Mk Us ++ Γ ⊢ A ≈ A' : Typeω@i ->
    ind_con Mk c = Some gs ->
    Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As' Us ++ Γ ⊢ elim_bty p k Mk c gs A' Us : Typeω@i /\
    Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs As' Us ++ Γ ⊢ elim_bty p k Mk c gs A Us ≈ elim_bty p k Mk c gs A' Us : Typeω@i.
Proof.
  intros * Hg HDs Hl Hk HΓ HUl HUs HM HA HA' HAA Hcon.
  pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ HUl HUs HM HA Hcon) as Hθ.
  split; [ exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hθ) | exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA Hθ) ].
Qed.

(** ** The Blocks of an Eliminator

    The premises of the eliminator's rules about its blocks, at the uniform
    parameters [Us]. *)

(** [blocks_typed Θ Ξ Γ p D Us Bks i]: the blocks [Bks] are typed as the
    eliminator of the group [D] at [p] asks, at the level [i]. *)
Record blocks_typed (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (Us : list exp)
    (Bks : list eblock) (i : nat) : Prop := mk_blocks_typed
  { (** One block per member *)
    blocks_typed_len : List.length Bks = List.length (ind_members D)
    (** Each block binds as many variables as its member's motive *)
  ; blocks_typed_nm : blocks_nm_ok D Bks
    (** An annotation is the member's type at [Us] *)
  ; blocks_typed_ann : forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id Us) ▹ Z ≈ elim_mctx p D k Mk Us
    (** Each motive is a type in its member's motive context *)
  ; blocks_typed_motive : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      Θ ⍮ Ξ ⍮ elim_mctx p D k Mk Us ++ Γ ⊢ eb_motive b : Typeω@i
    (** Each motive context is well formed *)
  ; blocks_typed_mctx : forall k Mk, ind_member D k = Some Mk -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk Us ≈ elim_mctx p D k Mk Us
    (** Each block has one branch per constructor, in order *)
  ; blocks_typed_names : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)
    (** Each branch context is well formed *)
  ; blocks_typed_bctx : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) Us ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us
    (** Each branch binds the non-uniform parameters, the arguments and the
        recursive results *)
  ; blocks_typed_counts : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat
    (** Each branch is of the branch type at its block's motive *)
  ; blocks_typed_brs : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
      Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ⊢ B : elim_bty p k Mk c gs (eb_motive b) Us }.

Lemma ind_member_lt : forall D k M, ind_member D k = Some M -> k < List.length (ind_members D).
Proof. intros * H; apply List.nth_error_Some; unfold ind_member in H; rewrite H; discriminate. Qed.

(** Every member has its block. *)
Lemma blocks_nth : forall D (Bks : list eblock) k Mk,
    List.length Bks = List.length (ind_members D) -> ind_member D k = Some Mk -> exists b, List.nth_error Bks k = Some b.
Proof.
  intros * Hl Hk; destruct (List.nth_error Bks k) as [b |] eqn:E; [ eauto |].
  apply List.nth_error_None in E; pose proof (ind_member_lt _ _ _ Hk); lia.
Qed.

Lemma blocks_motives_nth : forall Bks k b, List.nth_error Bks k = Some b -> List.nth k (blocks_motives Bks) a_True = eb_motive b.
Proof. intros * Hb; apply List.nth_error_nth; unfold blocks_motives; rewrite List.nth_error_map, Hb; reflexivity. Qed.

Lemma blocks_motives_typed : forall Θ Ξ Γ p D Us Bks i,
    blocks_typed Θ Ξ Γ p D Us Bks i -> motives_typed Θ Ξ Γ p D Us (blocks_motives Bks) i.
Proof.
  intros * HB j Mj Hj; destruct (blocks_nth _ _ _ _ (blocks_typed_len _ _ _ _ _ _ _ _ HB) Hj) as [b Hb].
  rewrite (blocks_motives_nth _ _ _ Hb); exact (blocks_typed_motive _ _ _ _ _ _ _ _ HB _ _ _ Hj Hb).
Qed.

Lemma blocks_mctx_wf : forall Θ Ξ Γ p D Us Bks i,
    blocks_typed Θ Ξ Γ p D Us Bks i -> forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ.
Proof. intros * HB j Mj Hj; exact (ext_eq_ctx_left _ _ _ _ _ (blocks_typed_mctx _ _ _ _ _ _ _ _ HB _ _ Hj)). Qed.

Lemma blocks_sub_sub : forall Bks σ τ, blocks_sub (blocks_sub Bks σ) τ = blocks_sub Bks (σ ⨟ τ).
Proof.
  intros; unfold blocks_sub; rewrite List.map_map; apply List.map_ext; intros [nm oZ A Bs]; cbn.
  f_equal; [ destruct oZ; cbn; [ f_equal | reflexivity ] | | ].
  - rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_qn_compose_ext; reflexivity.
  - rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_qn_compose_ext; reflexivity.
  - unfold brs_sub; rewrite List.map_map; apply List.map_ext; intros [[c n] B]; cbn [fst snd]; f_equal.
    rewrite exp_sub_sub; apply exp_sub_sb_eq, sb_qn_compose_ext; reflexivity.
Qed.

Lemma blocks_sub_id : forall Bks, blocks_sub Bks Id = Bks.
Proof.
  intros; unfold blocks_sub; rewrite <- List.map_id; apply List.map_ext; intros [nm oZ A Bs]; cbn.
  f_equal; [ destruct oZ; cbn; [ f_equal | reflexivity ] | | ].
  - apply exp_sub_id_ext, sb_qn_id_ext; reflexivity.
  - apply exp_sub_id_ext, sb_qn_id_ext; reflexivity.
  - unfold brs_sub; rewrite <- List.map_id; apply List.map_ext; intros [[c n] B]; cbn [fst snd]; f_equal.
    apply exp_sub_id_ext, sb_qn_id_ext; reflexivity.
Qed.

(** The blocks moved by a substitution. *)
Lemma blocks_typed_sub : forall Θ Ξ Γ Δ σ p D Us Bks i,
    ind_lookup Θ Ξ p = Some D -> List.length Us = ind_nu D ->
    blocks_typed Θ Ξ Γ p D Us Bks i -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    blocks_typed Θ Ξ Δ p D (List.map (fun U => U[σ]) Us) (blocks_sub Bks σ) i.
Proof.
  intros * Hl HUl [HlB Hnm HZ HA HΨ Hn HΨB Hk HB] Hσ.
  pose proof (sub_as_sub_dom Θ Ξ) as Rd; pose proof (sub_as_sub_ext Θ Ξ) as Re.
  assert (HD : decl_closed D) by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hσ) | exact Hl ]).
  assert (IHZ : forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 Γ ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id Us) ▹ Z) σ0 ≈ tele_sub (elim_mctx p D k Mk Us) σ0)
    by (intros; eapply sub_preserves_ext; eauto).
  assert (IHA : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 (elim_mctx p D k Mk Us ++ Γ) -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] : Typeω@i[σ0])
    by (intros; eapply sub_preserves_exp; eauto).
  assert (IHΨ : forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 Γ ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk Us) σ0 ≈ tele_sub (elim_mctx p D k Mk Us) σ0)
    by (intros; eapply sub_preserves_ext; eauto).
  assert (IHΨB : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 Γ ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0
                          ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0)
    by (intros; eapply sub_preserves_ext; eauto).
  assert (IHB : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
             ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ) ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] : (elim_bty p k Mk c gs (eb_motive b) Us)[σ0])
    by (intros; eapply sub_preserves_exp; eauto).
  constructor.
  - rewrite length_blocks_sub; exact HlB.
  - apply blocks_nm_ok_sub; exact Hnm.
  - eapply mv_blocks_ann with (R := sub_as_sub Θ Ξ); eassumption.
  - eapply mv_blocks_motive with (R := sub_as_sub Θ Ξ); eassumption.
  - intros k Mk HMk; erewrite <- elim_mctx_sub by eassumption; exact (IHΨ _ _ HMk _ _ Hσ).
  - apply mv_blocks_names; exact Hn.
  - eapply mv_blocks_bctx with (R := sub_as_sub Θ Ξ); eassumption.
  - apply mv_blocks_counts; exact Hk.
  - eapply mv_blocks_brs with (R := sub_as_sub Θ Ξ); eassumption.
Qed.

(** In a group without views every member is declared. *)
(** The eliminator at uniform parameters [Us] and non-uniform ones [Ns]. *)
Lemma wf_elim_blocks : forall Θ Ξ Γ p D oq m Mm Bks bm Us Ns M i,
    ind_lookup Θ Ξ p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    blocks_typed Θ Ξ Γ p D Us Bks i ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm ->
    (forall k N T, nth_error Ns k = Some N -> nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m Us Ns ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq Us m Bks M : (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)].
Proof.
  intros * Hl Hg Hm Hbm [HlB Hnm HZ HA HΨ Hn HΨB Hk HB] HUl HUs HNl HNs HM.
  assert (Hc : decl_closed D)
    by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (presup_exp_ctx HM) | exact Hl ]).
  pose proof (params_typed_join _ _ _ Hc _ _ _ _ _ Hm HUl HUs HNs) as HPs.
  rewrite <- (skipn_app_len Us Ns (ind_nu D) HUl).
  rewrite <- (firstn_app_len Us Ns (ind_nu D) HUl) in HZ, HA, HΨ, HΨB, HB.
  eapply wf_elim; try eassumption.
  - rewrite List.length_app, HUl, HNl; unfold im_np; lia.
  - rewrite firstn_app_len, skipn_app_len by exact HUl; exact HM.
  - rewrite firstn_app_len by exact HUl; reflexivity.
Qed.

(** The eliminator at the parameters and the scrutinee a substitution into
    the motive's context sends, the blocks moved by its base [β]. *)
Lemma wf_elim_at_inst : forall Θ Ξ Γ Ψ β p D oq m Mm Bks bm Us Ns M i,
    ind_lookup Θ Ξ p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    blocks_typed Θ Ξ Γ p D Us Bks i ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (Ns ++ M :: nil) : elim_mctx p D m Mm Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ a_elim oq (List.map (fun U => U[β]) Us) m (blocks_sub Bks β) M
      : (eb_motive bm)[sb_of_list β (Ns ++ M :: nil)].
Proof.
  intros * Hl Hg Hm Hbm HBt HUl HUs HNl Hβ Hδ.
  pose proof (wf_sub_dom _ _ _ _ _ Hβ) as HΨ.
  destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
  pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hβ) as HBt'.
  set (Us' := List.map (fun U => U[β]) Us) in *.
  assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
  assert (Hrass : tele_ass (tele_sub (im_nparams Mm) (sb_of_list Id Us'))) by (apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption).
  (* the instances read back *)
  assert (Hlen : List.length (Ns ++ M :: nil) = List.length (elim_mctx p D m Mm Us))
    by (rewrite List.length_app, length_elim_mctx, HNl; cbn; lia).
  pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_mctx_ass p D m Mm Us Hc Hm) Hlen Hδ) as Hinv.
  assert (Hti : tele_insts (elim_mctx p D m Mm Us) β (Ns ++ M :: nil)
                = tele_insts (im_nparams Mm) (sb_of_list Id Us') Ns ++ ind_mty p D m Us' Ns :: nil).
  { rewrite (tele_insts_sb_eq _ _ (β ⨟ Id)) by (intros x; symmetry; apply sb_compose_id_right).
    rewrite <- tele_insts_tele_sub; erewrite elim_mctx_sub by eassumption; fold Us'.
    unfold elim_mctx; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R).
    rewrite tele_insts_app by (try exact Hrass; rewrite length_tele_sub; exact HNl).
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id Us')) by apply sb_compose_id_right.
    f_equal; unfold tele_insts; cbn; f_equal.
    rewrite ind_head_inst by (try assumption; exact HNl).
    unfold Us'; rewrite List.map_map; f_equal; apply List.map_ext; intros; apply exp_sub_id. }
  rewrite Hti in Hinv.
  assert (Hl2 : List.length (tele_insts (im_nparams Mm) (sb_of_list Id Us') Ns) = im_nn Mm)
    by (rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption); rewrite HNl; unfold im_nn; lia).
  assert (HNs : forall k N T, List.nth_error Ns k = Some N ->
             List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us') Ns) k = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T).
  { intros k N T HN HT; apply (Hinv k); [ rewrite List.nth_error_app1; [ exact HN | apply List.nth_error_Some; congruence ]
                                    | rewrite List.nth_error_app1; [ exact HT | apply List.nth_error_Some; congruence ] ]. }
  assert (HM : Θ ⍮ Ξ ⍮ Ψ ⊢ M : ind_mty p D m Us' Ns).
  { specialize (Hinv (im_nn Mm) M).
    rewrite List.nth_error_app2 in Hinv by lia; rewrite List.nth_error_app2 in Hinv by lia.
    rewrite HNl, Hl2, Nat.sub_diag in Hinv; exact (Hinv _ eq_refl eq_refl). }
  (* the uniform parameters *)
  assert (HUs' : forall k U T, nth_error Us' k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us') k = Some T ->
             Θ ⍮ Ξ ⍮ Ψ ⊢ U : T).
  { intros k U' T' HU HT; unfold Us' in HU, HT.
    rewrite <- (tele_insts_sub (ind_uparams D) 0 Id Id β Us (decl_typed_ass _ _ _ HD) (decl_closed_uparams _ Hc) ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hβ). }
  pose proof (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hg Hm ltac:(rewrite nth_error_blocks_sub, Hbm; reflexivity)
                HBt' HUl' HUs' HNl HNs HM) as H.
  pose proof (blocks_typed_nm _ _ _ _ _ _ _ _ HBt _ _ _ Hm Hbm) as Enm.
  destruct bm as [nm oZ A Bs]; cbn in Enm, H |- *; subst nm.
  replace (S (im_nn Mm)) with (List.length (Ns ++ M :: nil)) in H by (rewrite List.length_app, HNl; cbn; lia).
  rewrite exp_sub_qn_of_list in H; exact H.
Qed.

(** ** The Recursive Results

    The eliminator a recursive result at the member [j] is ([elim_at]), at
    a substitution into [j]'s motive's context: the group's eliminator, its
    blocks moved by the substitution's base, at a declared member as
    written, at a view with the group named and its first block
    annotated. *)
Lemma wf_elim_at_typed : forall Θ Ξ Γ Ψ β p D oq Us Bks i j Mj Ns M,
    ind_lookup Θ Ξ p = Some D -> oq = Some p \/ oq = None ->
    blocks_typed Θ Ξ Γ p D Us Bks i ->
    List.length Us = ind_nu D ->
    (forall k U T, nth_error Us k = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    ind_member D j = Some Mj -> List.length Ns = im_nn Mj ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (Ns ++ M :: nil) : elim_mctx p D j Mj Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ elim_at p D oq (List.map (fun U => U[β]) Us) (blocks_sub Bks β) j M
      : (List.nth j (blocks_motives Bks) a_True)[sb_of_list β (Ns ++ M :: nil)].
Proof.
  intros * Hl Hoq HBt HUl HUs Hj HNl Hβ Hδ.
  pose proof (wf_sub_dom _ _ _ _ _ Hβ) as HΨ.
  destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
  destruct (blocks_nth _ _ _ _ (blocks_typed_len _ _ _ _ _ _ _ _ HBt) Hj) as [b Hb].
  rewrite (blocks_motives_nth _ _ _ Hb).
  unfold elim_at; destruct (ind_has_views D) eqn:Hv.
  - eapply wf_elim_at_inst; try eassumption; left; reflexivity.
  - eapply wf_elim_at_inst; try eassumption.
    destruct Hoq as [-> | ->]; [ left; reflexivity | right; split; [ reflexivity |] ].
    apply (decl_typed_order _ _ _ HD _ _ Hj); exact (no_views_decl _ _ _ Hv Hj).
Qed.

Lemma shape_uc_sb_eq : forall D Us Tc σ β β', sb_eq β β' -> shape_uc D Us Tc σ β -> shape_uc D Us Tc σ β'.
Proof. intros * Hβ H y Hy; rewrite H by exact Hy; cbn [sb_compose]; rewrite (sentry_sub_sb_eq _ _ _ Hβ); reflexivity. Qed.

Section IhTm.
  Context (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (oq : option qname) (Us : list exp)
    (Bks : list eblock) (i : nat).
  Hypothesis (Hl : ind_lookup Θ Ξ p = Some D) (Hoq : oq = Some p \/ oq = None)
    (HBt : blocks_typed Θ Ξ Γ p D Us Bks i)
    (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T).

  (** The recursive result of a shape, at an argument of its type: the
      eliminator's blocks, in [Γ], moved by [β] into the current context. *)
  Lemma ih_tm_typed : forall Mk t Ψ β Bs1 Tb σ M Mj,
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
      shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β ->
      ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t) = im_nn Mj ->
      shape_doms_typed Θ Ξ D Mk Bs1 Tb t -> shape_leaf_typed Θ Ξ D Mk Mj Bs1 Tb t ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ M : ptyp_ty_at p D (List.map (fun U => U[β]) Us) σ t ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ih p D oq (List.map (fun U => U[β]) Us) (blocks_sub Bks β) σ M t
        : ptyp_ihty (blocks_motives Bks) β σ M t.
  Proof.
    intros Mk t; induction t as [j0 Ps | B t IH]; intros * Hβ Hσ Huc Hj HPl HBt' HPt HM;
      cbn [ptyp_ih ptyp_ihty ptyp_ty_at ptyp_mem ptyp_ps] in *.
    - pose proof (wf_sub_dom _ _ _ _ _ Hβ) as HΨ.
      destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
      pose proof (ih_leaf_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hj HUl (blocks_mctx_wf _ _ _ _ _ _ _ _ HBt _ _ Hj) Hβ Hσ Huc HPl
                    (shape_leaf_at _ _ _ _ _ _ _ _ HPt eq_refl) HM) as Hτ.
      eapply wf_elim_at_typed; try eassumption; rewrite List.length_map; exact HPl.
    - pose proof (wf_sub_dom _ _ _ _ _ Hβ) as HΨ.
      destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
      destruct (HBt' nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
      assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
      pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
      replace ((doms_ctx Bs1 ++ Tb ++ im_params D Mk) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) in Hσ'
        by (rewrite doms_ctx_app_one; reflexivity).
      assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
        by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
      assert (Huc' : shape_uc D Us (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) (q σ) (β ⨟ ι ↑))
        by (rewrite doms_ctx_app_one; apply shape_uc_pi; [ exact (proj2 (length_shape_ctx D Mk Bs1 Tb)) | exact Huc ]).
      pose proof (shape_doms_typed_pi _ _ _ _ _ _ _ _ HBt') as HBt''.
      pose proof (shape_leaf_typed_pi _ _ _ _ _ _ _ _ _ HPt) as HPt'.
      assert (Hus : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[β]) Us) = List.map (fun U => U[β ⨟ ι ↑]) Us)
        by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      rewrite Hus in HM |- *.
      rewrite <- blocks_sub_of_wk, blocks_sub_sub.
      destruct (ty_at_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc HUl (blocks_mctx_wf _ _ _ _ _ _ _ _ HBt) Hβ' Hσ' Huc' Hj HPl
                  HBt'' HPt') as [j2 Hj2].
      pose proof (shape_arg_app _ _ _ _ _ _ _ _ Hj1' Hj2 HM) as HM'.
      pose proof (IH _ _ _ _ _ _ _ Hβ' Hσ' Huc' Hj HPl HBt'' HPt' HM') as Hbody.
      eapply wf_fn; [ exact Hj1' | exact Hbody ].
  Qed.
End IhTm.

(** ** The Instance of a Branch's Context at a Constructor

    [ι] substitutes the non-uniform parameters, the constructor's arguments
    and the recursive eliminations into a branch. *)

Lemma wf_sub_nparams_inst : forall Θ Ξ Γ p D k Mk Ps,
    ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ⊢ Θ ⍮ Ξ ⍮ Γ -> List.length Ps = im_np D Mk ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps)
      : tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ++ Γ.
Proof.
  intros * Hl Hk HΓ HPl HPs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hk HPl HPs) as [HUs HNs].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  apply wf_sub_of_list;
    [ apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption | exact (wf_nparams_sub _ _ _ HD Hc _ _ _ _ Hk HΓ Hσ)
    | exact (wf_sub_id _ _ _ HΓ) | rewrite length_tele_sub, List.length_skipn; unfold im_np, im_nn in *; lia |].
  intros j N T HN HT; rewrite tele_insts_tele_sub in HT.
  rewrite (tele_insts_sb_eq _ _ (sb_of_list Id (List.firstn (ind_nu D) Ps))) in HT by apply sb_compose_id_right.
  exact (HNs _ _ _ HN HT).
Qed.

Lemma wf_sub_args_inst : forall Θ Ξ Γ p D k Mk c gs Ps As,
    ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = im_np D Mk ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall j N T, List.nth_error As j = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Ps) As) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As) : cinst Γ p D Mk (List.firstn (ind_nu D) Ps) gs.
Proof.
  intros * Hl Hk Hcon HΓ HPl HPs HAl HAs.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hk HPl HPs) as [HUs _].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mk) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  rewrite sb_of_list_app; unfold cinst in Hi |- *.
  apply wf_sub_of_list;
    [ apply tele_ass_sub, cargs_ctx_aux_ass | exact Hi | exact (wf_sub_nparams_inst _ _ _ _ _ _ _ _ Hl Hk HΓ HPl HPs)
    | rewrite length_tele_sub, length_cargs_ctx; exact HAl |].
  intros j N T HN HT; rewrite tele_insts_tele_sub in HT.
  rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Ps)) in HT; [ exact (HAs _ _ _ HN HT) |].
  rewrite <- HNl; etransitivity; [ apply sb_qn_of_list |].
  etransitivity; [ apply sb_of_list_cong; intros x; cbn; apply sentry_sub_id |].
  rewrite <- sb_of_list_app, List.firstn_skipn; reflexivity.
Qed.

(** A shift past [N] followed by a list ending in [N] is the list before. *)
Lemma sb_shift_of_list_app : forall M N σ,
    sb_eq (ι (wk_shiftn (List.length N)) ⨟ sb_of_list σ (M ++ N)) (sb_of_list σ M).
Proof.
  intros M N σ x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite sb_of_list_app, Nat.add_comm, sb_of_list_ge; reflexivity.
Qed.

Lemma sb_of_list_shift_compose : forall Ms L,
    sb_eq (sb_of_list (ι (wk_shiftn (List.length L))) Ms ⨟ sb_of_list Id L)
          (sb_of_list Id (List.map (fun M => M[sb_of_list Id L]) Ms)).
Proof.
  intros; etransitivity; [ apply (sb_of_list_compose Ms _ _ Id Id) |].
  - intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
    rewrite Nat.add_comm, sb_of_list_ge, sentry_sub_id; reflexivity.
  - rewrite <- (List.length_map (fun M => M[sb_of_list Id L]) Ms) at 1.
    etransitivity; [ apply sb_qn_of_list |]; apply sb_of_list_cong; intros x; reflexivity.
Qed.

Lemma firstn_S_nth : forall {X : Type} (l : list X) n a,
    List.nth_error l n = Some a -> List.firstn (S n) l = List.firstn n l ++ a :: nil.
Proof.
  induction l as [| x l IH]; intros [| n] a H; cbn in *; try discriminate.
  - injection H as ->; reflexivity.
  - f_equal; apply IH; exact H.
Qed.

Lemma skipn_nth_cons : forall {X : Type} (l : list X) n a,
    List.nth_error l n = Some a -> List.skipn n l = a :: List.skipn (S n) l.
Proof.
  induction l as [| b l IH]; intros [| n] a H; cbn in *; try discriminate; [ injection H as ->; reflexivity | apply IH; exact H ].
Qed.

Lemma nth_error_lt_some : forall {X : Type} (l : list X) n, n < List.length l -> exists a, List.nth_error l n = Some a.
Proof.
  intros * H; destruct (List.nth_error l n) as [a |] eqn:E; [ eauto |].
  apply List.nth_error_None in E; lia.
Qed.

(** [ι]'s substitution into a branch, after a shape's move: the shape's
    components instantiated by the parameters and the non-recursive
    arguments before. *)
Lemma ihs_sub_iota : forall D Mk Ps As L (gs1 gs : list carg),
    List.length Ps = im_np D Mk -> List.length As = List.length gs ->
    List.length gs1 <= List.length gs ->
    sb_eq (ihs_sub (im_nn Mk) (List.firstn (ind_nu D) Ps) (List.length gs) (cargs_pat gs1) (List.length L)
             ⨟ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L))
          (cargs_sub (sb_of_list Id Ps) gs1 As).
Proof.
  intros * HPl HAl Hg.
  set (i := List.length gs1).
  assert (Hpi : List.length (cargs_pat gs1) = i) by apply length_cargs_pat.
  unfold ihs_sub; rewrite Hpi, !sb_compose_assoc.
  rewrite <- (List.firstn_skipn i As), <- !List.app_assoc, List.app_assoc.
  replace (List.length gs - i + List.length L) with (List.length (List.skipn i As ++ L))
    by (rewrite List.length_app, List.length_skipn; lia).
  rewrite sb_shift_of_list_app, List.firstn_skipn.
  replace (i + im_nn Mk) with (List.length (List.skipn (ind_nu D) Ps ++ List.firstn i As))
    by (rewrite List.length_app, List.length_skipn, List.length_firstn; unfold im_np in *; lia).
  rewrite sb_qn_of_list, (sb_of_list_cong _ _ _ (sb_compose_id_right _)), <- sb_of_list_app, List.app_assoc, List.firstn_skipn.
  rewrite sb_of_list_app, cargs_sub_pat by (rewrite List.length_firstn; lia).
  unfold i; rewrite cargs_sub_firstn; reflexivity.
Qed.

Lemma wf_iota_ihs : forall Θ Ξ Γ p D oq k Mk c gs Ps As Bks i,
    ind_lookup Θ Ξ p = Some D -> oq = Some p \/ oq = None -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = im_np D Mk ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    blocks_typed Θ Ξ Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
    forall rest gs1 E L, gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 -> List.length L = List.length E ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Mk (List.firstn (ind_nu D) Ps) gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L) : E ++ cinst Γ p D Mk (List.firstn (ind_nu D) Ps) gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L ++
                     elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (cargs_sub (sb_of_list Id Ps) gs1 As) rest
                       (List.skipn (List.length gs1) As))
        : ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) (List.firstn (ind_nu D) Ps) (List.length gs) (cargs_pat gs1)
            (List.length E) rest ++ E ++ cinst Γ p D Mk (List.firstn (ind_nu D) Ps) gs.
Proof.
  intros * Hl Hoq Hk Hcon HΓ HPl HPs HAl HBt rest.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hk HPl HPs) as [HUs _].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mk) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  pose proof (blocks_mctx_wf _ _ _ _ _ _ _ _ HBt) as HM.
  pose proof (blocks_motives_typed _ _ _ _ _ _ _ _ HBt) as HA.
  assert (HAA : motives_eq Θ Ξ Γ p D (List.firstn (ind_nu D) Ps) (blocks_motives Bks) (blocks_motives Bks) i)
    by (intros j Mj Hj; apply wf_exp_eq_refl; exact (HA _ _ Hj)).
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  induction rest as [| [B0 | t] rest IH]; intros gs1 E L Heq HE HL HΨ Hδ; cbn [ihs_ctx_aux List.app].
  - cbn [elim_ihs]; rewrite List.app_nil_r; exact Hδ.
  - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
    destruct (nth_error_lt_some As _ Hlt) as [a Ha].
    rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
    assert (Hcs : cargs_sub (sb_of_list Id Ps) (gs1 ++ ca_arg B0 :: nil) As = (cargs_sub (sb_of_list Id Ps) gs1 As ,, a)).
    { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
      apply cargs_sub_snoc_arg; rewrite List.length_firstn; lia. }
    replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg B0 :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    replace (S (List.length gs1)) with (List.length (gs1 ++ ca_arg B0 :: nil)) by (rewrite List.length_app; cbn; lia).
    rewrite <- Hcs.
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | exact HL | exact HΨ | exact Hδ ].
  - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
    destruct (nth_error_lt_some As _ Hlt) as [a Ha].
    rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
    set (σg := cargs_sub (sb_of_list Id Ps) gs1 As).
    assert (Hcs : cargs_sub (sb_of_list Id Ps) (gs1 ++ ca_rec t :: nil) As = σg).
    { unfold σg; rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
      apply cargs_sub_snoc_rec; rewrite List.length_firstn; lia. }
    destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hk HΓ HUl Hσ HM HA HA HAA Hin Heq HΨ)
      as (j & HAj & _).
    destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ _ _ E Hg HDs Hl Hk HΓ HUl Hσ Hin Heq HΨ) as (Hb & Hθ & Huc & Hx).
    destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HD Hk Hin Heq) as (Mj & Hj & HPlt & HBt' & HPt).
    set (θ := ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E)) in *.
    set (δ := sb_of_list Id (Ns ++ As ++ L)) in *.
    set (b := List.length E + List.length gs + im_nn Mk) in *.
    set (x := List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) in *.
    assert (Hθδ : sb_eq (θ ⨟ δ) σg)
      by (unfold θ, δ, σg, Us, Ns; rewrite <- HL; apply ihs_sub_iota; [ exact HPl | exact HAl | rewrite Heq, List.length_app; lia ]).
    assert (Hbδ : sb_eq (ι (wk_shiftn b) ⨟ δ) Id).
    { intros z; unfold b, δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      replace (z + (List.length E + List.length gs + im_nn Mk)) with (List.length (Ns ++ As ++ L) + z)
        by (rewrite !List.length_app, HNl, HAl, HL; lia).
      rewrite sb_of_list_ge; reflexivity. }
    assert (Hidx : (a_var x)[δ] = a).
    { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ, x.
      rewrite (sb_of_list_nth _ _ _ a) by (rewrite !List.length_app, HNl, HAl, HL, Heq, List.length_app, length_cargs_pat; cbn; lia).
      rewrite !List.length_app, HNl, HAl, HL, length_cargs_pat.
      replace (im_nn Mk + (List.length gs + List.length E) - 1 - (List.length E + List.length gs - 1 - List.length gs1))
        with (im_nn Mk + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
      cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl; replace (im_nn Mk + List.length gs1 - im_nn Mk) with (List.length gs1) by lia.
      rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact Ha. }
    (* the recursive result is of the instance of its type *)
    assert (Hσg : Θ ⍮ Ξ ⍮ Γ ⊢ˢ σg : doms_ctx nil ++ cargs_strat gs1 ++ im_params D Mk)
      by (rewrite <- Hθδ; eapply wf_sub_compose; [ exact Hθ | exact Hδ ]).
    assert (Hucg : shape_uc D Us (doms_ctx nil ++ cargs_strat gs1 ++ im_params D Mk) σg Id).
    { intros y Hy; rewrite <- (Hθδ (y + _)); cbn [sb_compose].
      rewrite <- sentry_exp_sub, (Huc y Hy), sentry_exp_sub; cbn [sb_compose].
      rewrite sentry_sub_sub; f_equal; apply sentry_sub_sb_eq; exact Hbδ. }
    assert (Ha' : Θ ⍮ Ξ ⍮ Γ ⊢ a : ptyp_ty_at p D (List.map (fun U => U[Id]) Us) σg t).
    { rewrite <- Hidx; pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hx Hδ) as H.
      rewrite ptyp_ty_at_sub, List.map_map in H by (try exact Hc; rewrite List.length_map; exact HUl).
      rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ _ Hθδ) in H.
      replace (List.map (fun U => U[Id]) Us) with (List.map (fun U => U[ι wk_shiftn b][δ]) Us); [ exact H |].
      apply List.map_ext; intros U; rewrite !exp_sub_sub; apply exp_sub_sb_eq; rewrite Hbδ; intros z; reflexivity. }
    pose proof (ih_tm_typed _ _ _ _ _ _ _ _ _ Hl Hoq HBt HUl HUs Mk t Γ Id nil (cargs_strat gs1) σg a Mj
                  (wf_sub_id _ _ _ HΓ) Hσg Hucg Hj HPlt HBt' HPt Ha') as Hih.
    rewrite blocks_sub_id, (List.map_ext _ (fun U => U) exp_sub_id), List.map_id in Hih.
    rewrite <- !List.app_assoc; cbn [List.app].
    replace (Ns ++ As ++ L ++ ptyp_ih p D oq Us Bks σg a t :: elim_ihs p D oq Us Bks σg rest (List.skipn (S (List.length gs1)) As))
      with (Ns ++ As ++ (L ++ ptyp_ih p D oq Us Bks σg a t :: nil) ++ elim_ihs p D oq Us Bks σg rest (List.skipn (S (List.length gs1)) As))
      by (rewrite <- !List.app_assoc; reflexivity).
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec t :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec t :: nil)) by (rewrite List.length_app; cbn; lia).
    rewrite <- Hcs.
    apply (IH (gs1 ++ ca_rec t :: nil) (_ :: E));
      [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
      | rewrite List.length_app; cbn; lia | cbn [List.app]; econstructor; exact HAj |].
    rewrite Hcs.
    replace (Ns ++ As ++ L ++ ptyp_ih p D oq Us Bks σg a t :: nil) with ((Ns ++ As ++ L) ++ ptyp_ih p D oq Us Bks σg a t :: nil)
      by (rewrite <- !List.app_assoc; reflexivity).
    rewrite (sb_of_list_app (Ns ++ As ++ L) (ptyp_ih p D oq Us Bks σg a t :: nil) Id).
    change (sb_of_list (sb_of_list Id (Ns ++ As ++ L)) (ptyp_ih p D oq Us Bks σg a t :: nil))
      with (sb_of_list Id (Ns ++ As ++ L) ,, ptyp_ih p D oq Us Bks σg a t).
    eapply wf_sub_extend; [ exact Hδ | exact HAj |].
    fold δ; rewrite ptyp_ihty_sub, Hidx.
    rewrite (ptyp_ihty_sb_eq t _ (ι wk_shiftn b ⨟ δ) Id (θ ⨟ δ) σg a); [ exact Hih | exact Hbδ | exact Hθδ ].
Qed.

Lemma wf_iota_sub : forall Θ Ξ Γ p D oq k Mk c gs Ps As Bks i,
    ind_lookup Θ Ξ p = Some D -> oq = Some p \/ oq = None -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = im_np D Mk ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall j N T, List.nth_error As j = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Ps) As) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    blocks_typed Θ Ξ Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As)
      : elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ.
Proof.
  intros * Hl Hoq Hk Hcon HΓ HPl HPs HAl HAs HBt.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hk HPl HPs) as [HUs _].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl Hk HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  pose proof (wf_sub_args_inst _ _ _ _ _ _ _ _ _ _ _ Hl Hk Hcon HΓ HPl HPs HAl HAs) as Hδ.
  rewrite <- (List.app_nil_r As) in Hδ at 1.
  pose proof (wf_iota_ihs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hoq Hk Hcon HΓ HPl HPs HAl HBt gs nil nil nil
                eq_refl eq_refl eq_refl Hi Hδ) as H.
  cbn [List.app List.skipn List.length cargs_pat] in H.
  unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
Qed.

(** The type of a branch at the instance [ι] substitutes is the motive at
    the constructor applied. *)
Lemma elim_bty_iota : forall p D k Mk c gs A Us Ns As ihs,
    decl_closed D -> ind_member D k = Some Mk -> List.length Us = ind_nu D ->
    List.length Ns = im_nn Mk -> List.length As = List.length gs -> List.length ihs = cargs_nrec gs ->
    (elim_bty p k Mk c gs A Us)[sb_of_list Id (Ns ++ As ++ ihs)]
    = A[sb_of_list Id (Ns ++ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Us ++ Ns ++ As) :: nil)].
Proof.
  intros * Hc Hk HUl HNl HAl Hil.
  unfold elim_bty; rewrite exp_sub_sub; apply exp_sub_sb_eq.
  replace (im_nn Mk + List.length gs + cargs_nrec gs) with (List.length (Ns ++ As ++ ihs))
    by (rewrite !List.length_app; lia).
  etransitivity; [ apply sb_of_list_shift_compose |].
  rewrite List.map_app; cbn [List.map]; rewrite apps_exp_sub, !List.map_app; cbn [exp_sub].
  rewrite (im_pre_sub D k Mk) by (try assumption; rewrite List.length_map; exact HUl).
  rewrite List.map_map, map_shift_sb_of_list, (List.map_ext (fun U => U[Id]) (fun U => U)), List.map_id by apply exp_sub_id.
  replace (cargs_nrec gs + List.length gs) with (List.length (As ++ ihs)) by (rewrite List.length_app; lia).
  rewrite <- HNl, vars_from_sb_of_list_app.
  rewrite <- HAl, <- Hil, (sb_of_list_app Ns (As ++ ihs) Id), vars_from_sb_of_list_app.
  reflexivity.
Qed.

(** ** The Sides of the Eliminator's Equations

    What presupposition needs of [wf_exp_eq_elim_cong],
    [wf_exp_eq_elim_iota] and [wf_exp_eq_elim_view]: both sides are of the
    type of the equation.  The lemmas take the rules' premises. *)

Lemma elim_grp_oq : forall D oq p m, elim_grp D oq p m -> oq = Some p \/ oq = None.
Proof. intros * [-> | [-> _]]; auto. Qed.

Lemma wf_iota_lhs : forall Θ Ξ Γ p D oq Us m Mm Bks bm c gs Ps As i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_lookup Θ Ξ p = Some D ->
    elim_grp D oq p m ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    ind_con Mm c = Some gs ->
    List.length Bks = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, nth_error As k = Some N -> nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Us = List.firstn (ind_nu D) Ps ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq Us m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                   (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As))
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                         apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                           (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)].
Proof.
  intros * HΓ Hl Hgr Hm Hbm Hcon HlB HPl HPs HAl HAs Hann Hnm HZ HA HΨ Hn HΨB Hk HB.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hm HPl HPs) as [HUs HNs].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mm) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  eapply wf_elim; try eassumption.
  eapply wf_con_apps_at; try eassumption.
  rewrite List.firstn_skipn; exact HAs.
Qed.

Lemma wf_iota_rhs : forall Θ Ξ Γ p D oq Us m Mm Bks bm c gs Ps As i n B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_lookup Θ Ξ p = Some D ->
    elim_grp D oq p m ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    ind_con Mm c = Some gs ->
    List.length Bks = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, nth_error As k = Some N -> nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Us = List.firstn (ind_nu D) Ps ->
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
    brs_lookup (eb_brs bm) c = Some (n, B) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++
                                  elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As)]
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                         apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                           (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)].
Proof.
  intros * HΓ Hl Hgr Hm Hbm Hcon HlB HPl HPs HAl HAs Hann Hnm HZ HA HΨ Hn HΨB Hk HB HBl.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mm) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  assert (HBt : blocks_typed Θ Ξ Γ p D (List.firstn (ind_nu D) Ps) Bks i) by (constructor; assumption).
  pose proof (brs_lookup_in _ _ _ _ HBl) as Hin.
  pose proof (wf_iota_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl (elim_grp_oq _ _ _ _ Hgr) Hm Hcon HΓ HPl HPs HAl HAs HBt) as Hσ.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HB _ _ _ _ _ _ _ Hm Hbm Hcon Hin) Hσ) as H.
  rewrite (elim_bty_iota p D m Mm) in H by (try eassumption; apply length_elim_ihs; exact HAl).
  exact H.
Qed.

(** The scrutinee varying moves the instance of the motive's context. *)
Lemma wf_elim_inst_sub_eq : forall Θ Ξ Γ p D m Mm Ps M M',
    ind_lookup Θ Ξ p = Some D -> ind_member D m = Some Mm -> ⊢ Θ ⍮ Ξ ⍮ Γ -> List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) ≈ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M' :: nil)
      : elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ.
Proof.
  intros * Hl Hm HΓ HPl HPs HM HM' HMM HΨ.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mm) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  pose proof (wf_sub_nparams_inst _ _ _ _ _ _ _ _ Hl Hm HΓ HPl HPs) as Hδ.
  rewrite !sb_of_list_app; cbn [sb_of_list].
  unfold elim_mctx in HΨ |- *; cbn [List.app] in HΨ |- *.
  destruct (ctx_decomp HΨ) as [_ [j Hj]].
  eapply wf_sub_eq_extend; [ apply wf_sub_eq_refl; exact Hδ | exact Hj | | | ];
    rewrite ind_head_inst, (List.map_ext _ (fun U => U) exp_sub_id), List.map_id by assumption; assumption.
Qed.

Lemma brs_names_fst : forall cs (Bs Bs' : list (String.string * nat * exp)),
    brs_names cs Bs -> List.map fst Bs = List.map fst Bs' -> brs_names cs Bs'.
Proof.
  unfold brs_names; intros * Hn Hm; rewrite Hn.
  rewrite <- (List.map_map fst fst Bs), Hm, List.map_map; reflexivity.
Qed.

Lemma brs_in_fst : forall (Bs Bs' : list (String.string * nat * exp)) c n B',
    List.map fst Bs = List.map fst Bs' -> In (c, n, B') Bs' ->
    exists k B, List.nth_error Bs k = Some (c, n, B) /\ List.nth_error Bs' k = Some (c, n, B') /\ In (c, n, B) Bs.
Proof.
  intros * Hm Hin; destruct (List.In_nth_error _ _ Hin) as [k Hk].
  destruct (brs_nth_same _ _ _ _ _ _ (eq_sym Hm) Hk) as [B HB].
  exists k, B; split; [ exact HB | split; [ exact Hk | eapply List.nth_error_In; exact HB ] ].
Qed.

Lemma brs_in_fst' : forall (Bs Bs' : list (String.string * nat * exp)) c n B,
    List.map fst Bs = List.map fst Bs' -> In (c, n, B) Bs ->
    exists k B', List.nth_error Bs k = Some (c, n, B) /\ List.nth_error Bs' k = Some (c, n, B').
Proof.
  intros * Hm Hin; destruct (List.In_nth_error _ _ Hin) as [k Hk].
  destruct (brs_nth_same _ _ _ _ _ _ Hm Hk) as [B' HB']; eauto.
Qed.

Lemma wf_elim_cong_lhs : forall Θ Ξ Γ p D oq Us m Mm (Bks Bks' : list eblock) bm Ps M i,
    ind_lookup Θ Ξ p = Some D ->
    elim_grp D oq p m ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = List.length (ind_members D) ->
    List.length Bks' = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Us = List.firstn (ind_nu D) Ps ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' ->
       nth_error (eb_brs b) i = Some (c, n, B) -> nth_error (eb_brs b') i = Some (c, n, B') ->
       ind_con Mk c = Some gs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq Us m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hgr Hm Hbm HlB HlB' HPl HPs HM Hann Hnm HZ HA HΨ Hn Hf HΨB Hk HB.
  eapply wf_elim; try eassumption.
  intros k Mk b c gs n B HMk Hb Hcon Hin.
  destruct (blocks_nth _ _ _ _ HlB' HMk) as [b' Hb'].
  destruct (brs_in_fst' _ _ _ _ _ (Hf _ _ _ Hb Hb') Hin) as (i0 & B' & Hi & Hi').
  exact (HB _ _ _ _ _ _ _ _ _ _ HMk Hb Hb' Hi Hi' Hcon).
Qed.

(** The right blocks of the congruence are typed at the left uniform
    parameters: the motives varying ([elim_bctx_eq], [elim_bty_eq]). *)
Lemma wf_elim_cong_rhs_blocks : forall Θ Ξ Γ p D m Mm (Bks Bks' : list eblock) Ps i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_lookup Θ Ξ p = Some D ->
    ind_member D m = Some Mm ->
    List.length Bks = List.length (ind_members D) ->
    List.length Bks' = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
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
    blocks_typed Θ Ξ Γ p D (List.firstn (ind_nu D) Ps) Bks' i.
Proof.
  intros * HΓ Hl Hm HlB HlB' HPl HPs Hnm Hnm' HZ' HA HA'' HAA HΨ Hn Hf Hk HB.
  assert (HA' : forall k Mk b', ind_member D k = Some Mk -> List.nth_error Bks' k = Some b' ->
             Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b' : Typeω@i)
    by (intros k Mk b' Hk' Hb'; destruct (blocks_nth _ _ _ _ HlB Hk') as [b Hb]; eauto).
  clear HA''.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hm HPl HPs) as [HUs HNs].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mm) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  set (Us := List.firstn (ind_nu D) Ps) in *.
  pose proof (fun j Mj Hj => ext_eq_ctx_left _ _ _ _ _ (HΨ j Mj Hj)) as HMx.
  (* the motives, on both sides *)
  assert (HAs : motives_typed Θ Ξ Γ p D Us (blocks_motives Bks) i).
  { intros j Mj Hj; destruct (blocks_nth _ _ _ _ HlB Hj) as [b Hb]; rewrite (blocks_motives_nth _ _ _ Hb); eauto. }
  assert (HAs' : motives_typed Θ Ξ Γ p D Us (blocks_motives Bks') i).
  { intros j Mj Hj; destruct (blocks_nth _ _ _ _ HlB' Hj) as [b Hb]; rewrite (blocks_motives_nth _ _ _ Hb); eauto. }
  assert (HAAs : motives_eq Θ Ξ Γ p D Us (blocks_motives Bks) (blocks_motives Bks') i).
  { intros j Mj Hj; destruct (blocks_nth _ _ _ _ HlB Hj) as [b Hb]; destruct (blocks_nth _ _ _ _ HlB' Hj) as [b' Hb'].
    rewrite (blocks_motives_nth _ _ _ Hb), (blocks_motives_nth _ _ _ Hb'); eauto. }
  (* the right blocks are typed *)
  { constructor; try assumption.
    - intros k Mk b' HMk Hb'; destruct (blocks_nth _ _ _ _ HlB HMk) as [b Hb].
      exact (brs_names_fst _ _ _ (Hn _ _ _ HMk Hb) (Hf _ _ _ Hb Hb')).
    - intros k Mk c gs HMk Hcon; apply ctx_ext_refl; [ eapply elim_bctx_ass; eassumption |].
      eapply elim_bctx_wf; eassumption.
    - intros k Mk b' c gs n B' HMk Hb' Hcon Hin; destruct (blocks_nth _ _ _ _ HlB HMk) as [b Hb].
      destruct (brs_in_fst _ _ _ _ _ (Hf _ _ _ Hb Hb') Hin) as (i0 & B & _ & _ & HinB).
      exact (Hk _ _ _ _ _ _ _ HMk Hb Hcon HinB).
    - intros k Mk b' c gs n B' HMk Hb' Hcon Hin; destruct (blocks_nth _ _ _ _ HlB HMk) as [b Hb].
      destruct (brs_in_fst _ _ _ _ _ (Hf _ _ _ Hb Hb') Hin) as (i0 & B & Hi & Hi' & _).
      pose proof (HB _ _ _ _ _ _ _ _ _ _ HMk Hb Hb' Hi Hi' Hcon) as HB'.
      pose proof (elim_bctx_eq _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl HMk HΓ HUl Hσ HMx HAs HAs' HAAs Hcon) as Hx.
      pose proof (ctxsub_ext _ _ _ _ _ Hx (elim_bctx_ass _ _ _ _ _ _ _ Hc HMk)) as Hs.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB' Hs) as HB''; rewrite !exp_sub_id in HB''.
      destruct (elim_bty_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl HMk HΓ HUl HUs HMx HAs' (HA' _ _ _ HMk Hb')
                  (HAA _ _ _ _ HMk Hb Hb') Hcon) as [Hty Heq].
      eapply wf_conv; [ exact HB'' | exact Hty | exact Heq ]. }
Qed.
