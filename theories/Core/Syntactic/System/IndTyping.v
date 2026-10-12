(** * The Contexts of the Eliminator Are Well Formed

    What the typing rules of inductive types state as premises about the
    contexts of the motive and of the branches, and about the instances of
    those contexts, follows from the typing of the parameters and the
    validity of the declaration: the parameters' variables are of the types
    of the parameters, the motive's instances at the recursive arguments are
    substitutions into the motive's context, and a constructor applies to
    terms of its arguments' types.  These are what presupposition of the
    eliminator's equations and the checker need. *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Lemmas.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Declaration of a Type in Scope *)

Lemma decl_of_lookup : forall Θ Ξ Γ p D,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D -> decl_typed Θ Ξ D /\ decl_closed D.
Proof.
  intros * HΓ Hl; destruct (ind_lookup_resolve _ _ _ _ Hl) as [pv Hres]; split.
  - exact (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ) _ _ Hres).
  - exact (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HΓ) Hl).
Qed.

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

Section Params.
  Context (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (HD : decl_typed Θ Ξ D) (Hc : decl_closed D).

  Lemma decl_uparams_closed : ctx_scoped 0 (ind_uparams D).
  Proof. pose proof Hc as (_ & _ & Hs & _); rewrite params_split in Hs; apply ctx_scoped_app in Hs as [_ Hs]; exact Hs. Qed.

  Lemma decl_uparams_ass : tele_ass (ind_uparams D).
  Proof. apply Forall_skipn', decl_closed_params, Hc. Qed.

  Lemma decl_uparams_mvc : ctx_mvc (ind_uparams D).
  Proof. pose proof HD as (_ & (Hmv & _) & _); apply Forall_skipn'; exact Hmv. Qed.

  Lemma decl_nparams_mvc : ctx_mvc (ind_nparams D).
  Proof. pose proof HD as (_ & (Hmv & _) & _); apply Forall_firstn'; exact Hmv. Qed.

  Lemma wf_params_app : forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_params D ++ Γ.
  Proof.
    intros * HΓ; pose proof HD as (Hass & _ & _ & HΔ & _); pose proof Hc as (_ & _ & Hs & _).
    apply wf_ctx_closed_app; assumption.
  Qed.

  Lemma wf_uparams_app : forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ.
  Proof.
    intros * HΓ; pose proof HD as (_ & _ & _ & HΔ & _); rewrite params_split in HΔ.
    apply wf_ctx_closed_app; [ apply decl_uparams_ass | apply decl_uparams_closed | eapply ctx_app_wf_tail; exact HΔ | exact HΓ ].
  Qed.

  (** The parameters typed one by one: the uniform ones at the uniform
      parameters' types, the others at theirs at the uniform ones. *)
  Lemma params_typed_split : forall Γ Ps,
      List.length Ps = ind_np D ->
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
      (forall k U T, List.nth_error (List.firstn (ind_nu D) Ps) k = Some U ->
         List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ U : T) /\
      (forall k N T, List.nth_error (List.skipn (ind_nu D) Ps) k = Some N ->
         List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : T).
  Proof.
    intros * Hl HPs.
    pose proof (decl_closed_nu D Hc) as Hle.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
    assert (Hti : tele_insts (ind_params D) Id Ps
                  = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                    ++ tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
    { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite params_split; apply tele_insts_app;
        [ apply decl_uparams_ass | rewrite HUl, length_ind_uparams by exact Hle; reflexivity ]. }
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
      by (rewrite length_tele_insts by apply decl_uparams_ass; rewrite HUl, length_ind_uparams by exact Hle; lia).
    split; intros k N T HN HT.
    - apply (HPs k); [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HN |].
      rewrite Hti, List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HT.
    - apply (HPs (ind_nu D + k)).
      + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
        rewrite HUl; replace (ind_nu D + k - ind_nu D) with k by lia; exact HN.
      + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + k - ind_nu D) with k by lia; exact HT.
  Qed.

  Lemma wf_sub_uparams : forall Γ Us,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> List.length Us = ind_nu D ->
      (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ.
  Proof.
    intros * HΓ Hl HUs; apply wf_sub_of_list_id;
      [ apply decl_uparams_ass | apply wf_uparams_app, HΓ | rewrite length_ind_uparams by apply (decl_closed_nu D Hc); exact Hl | exact HUs ].
  Qed.

  Lemma wf_nparams_sub : forall Γ Us,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ.
  Proof.
    intros * HΓ Hσ; eapply ctx_sub_wf; [ exact Hσ | apply decl_closed_nparams_ass, Hc |].
    rewrite List.app_assoc, <- params_split; apply wf_params_app, HΓ.
  Qed.

  (** The level of the sort, at the uniform parameters. *)
  Lemma sort_lvl_at : forall Γ Us,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
      exists n, Θ ⍮ Ξ ⍮ Γ ⊢ ind_sort_lvl (ind_sort D)[sb_of_list Id Us] : Level@n.
  Proof.
    intros * HΓ Hσ; pose proof HD as (_ & _ & Hle & _ & HS & _ & [n Hn] & _); exists n.
    pose proof Hc as (_ & _ & _ & HsS & _).
    destruct (ind_sort_univ_sub (ind_sort D) (sb_of_list Id Us) HS) as [_ <-].
    assert (Hn' : Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ ⊢ ind_sort_lvl (ind_sort D) : Level@n).
    { apply wf_exp_closed_app; [ apply decl_uparams_ass | apply decl_uparams_closed | | exact I | exact Hn | exact HΓ ].
      rewrite length_ind_uparams by exact Hle; destruct HS as [[i Heq] | [t Heq]]; rewrite Heq in *; cbn in *; auto. }
    exact (sub_preserves_exp _ _ _ _ _ _ _ Hn' Hσ).
  Qed.

  (** The sort at the uniform parameters is a type of a large universe. *)
  Lemma sort_at_large : forall Γ Us A,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : (ind_sort D)[sb_of_list Id Us] -> exists j, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j.
  Proof.
    intros * HΓ Hσ HA; pose proof HD as (_ & _ & _ & _ & HS & _).
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

(** ** The Motive's Context *)

Lemma elim_mctx_wf : forall Θ Ξ Γ p D Us,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ.
Proof.
  intros * HD Hc Hl HΓ HUl HUs.
  pose proof (decl_closed_nu D Hc) as Hle.
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  pose proof (wf_nparams_sub _ _ _ HD Hc _ _ HΓ Hσ) as HΨ0.
  assert (Hw : Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ ⊢w wk_shiftn (ind_nn D) : Γ).
  { rewrite <- (length_ind_nparams_sub D (sb_of_list Id Us)); apply wf_wk_shiftn_app'; exact HΨ0. }
  assert (HUs' : forall k U T, List.nth_error (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us) k = Some U ->
             List.nth_error (tele_insts (ind_uparams D) Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us)) k = Some T ->
             Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ ⊢ U : T).
  { intros k U' T' HU HT.
    rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
    apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    exact (wk_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hw). }
  assert (Hσ' : Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ
                  ⊢s sb_of_list Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us)
                  : ind_uparams D ++ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ)
    by (apply (wf_sub_uparams _ _ _ HD Hc); [ exact HΨ0 | rewrite List.length_map; exact HUl | exact HUs' ]).
  pose proof (wf_ind_apps _ _ _ p D (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)) HD Hc Hl HΨ0) as HR.
  assert (Hty : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D))]
                = (ind_sort D)[sb_of_list Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us)])
    by (rewrite <- (length_vars_from 0 (ind_nn D)) at 1; apply exp_shift_past).
  rewrite Hty in HR.
  assert (Hhd : Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ
                ⊢ apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D))
                : (ind_sort D)[sb_of_list Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us)]).
  { apply HR.
  - rewrite List.length_app, List.length_map, HUl, length_vars_from; unfold ind_nn; lia.
  - rewrite params_split; intros k N T HN HT.
    rewrite tele_insts_app in HT;
      [| apply (decl_uparams_ass D Hc) | rewrite List.length_map, HUl, length_ind_uparams by exact Hle; reflexivity ].
    assert (Hl1 : List.length (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
    assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us)) = ind_nu D)
      by (rewrite length_tele_insts by apply (decl_uparams_ass D Hc); rewrite Hl1, length_ind_uparams by exact Hle; lia).
    destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; exact (HUs' _ _ _ HN HT).
    + rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl1 in HN; rewrite Hl2 in HT.
      replace (vars_from 0 (ind_nn D)) with (vars_from (List.length (@nil centry)) (List.length (ind_nparams D))) in HN, HT
        by (rewrite length_nparams; reflexivity).
      change (tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ) with (nil ++ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ).
      eapply (wf_vars_tele_gen _ _ nil _ _ _ Γ (ind_nu D));
        [ apply decl_closed_nparams_ass, Hc | apply (decl_nparams_mvc _ _ _ HD) | apply decl_closed_nparams_scoped, Hc
        | exact HΨ0 | | exact HN | exact HT ].
      intros y Hy; rewrite sb_of_list_map by lia; cbn [List.length]; rewrite length_nparams; reflexivity. }
  destruct (sort_at_large _ _ _ HD Hc _ _ _ HΨ0 Hσ' Hhd) as [j Hj].
  unfold elim_mctx; cbn [List.app]; econstructor; exact Hj.
Qed.

(** ** The Arguments of a Constructor at the Parameters *)

Lemma cargs_ctx_closed : forall p D c gs gs1 gs2,
    decl_closed D -> List.In (c, gs) (ind_cons D) -> gs = gs1 ++ gs2 ->
    ctx_scoped 0 (cargs_ctx p D gs1 ++ ind_params D).
Proof.
  intros * Hc Hin Heq; pose proof Hc as (_ & Hle & Hs & _ & HA & HPs & _).
  apply ctx_scoped_app; split; [| exact Hs ].
  rewrite Nat.add_0_r; change (List.length (ind_params D)) with (List.length (@nil bool) + ind_np D).
  apply (cargs_ctx_aux_scoped p D gs1 nil 0 Hle eq_refl); cbn.
  - intros gs3 A gs4 ->; apply (HA c gs gs3 A (gs4 ++ gs2) Hin); rewrite Heq, <- List.app_assoc; reflexivity.
  - intros gs3 Ps gs4 ->; apply (HPs c gs gs3 Ps (gs4 ++ gs2) Hin); rewrite Heq, <- List.app_assoc; reflexivity.
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
  Context (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (Us : list typ).
  Hypothesis (HD : decl_typed Θ Ξ D) (Hc : decl_closed D) (Hl : ind_lookup Θ Ξ p = Some D) (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ).
  Hypothesis (HUl : List.length Us = ind_nu D).
  Hypothesis (Hσ : Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ).

  Definition cinst (gs1 : list carg) : ctx :=
    tele_sub (cargs_ctx p D gs1) (sb_qn (ind_nn D) (sb_of_list Id Us)) ++ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ.

  Lemma cinst_eq : forall gs1,
      cinst gs1 = tele_sub (cargs_ctx p D gs1 ++ ind_nparams D) (sb_of_list Id Us) ++ Γ.
  Proof. intros; unfold cinst; rewrite tele_sub_app, length_nparams, List.app_assoc; reflexivity. Qed.

  Lemma wf_sub_cinst : forall c gs gs1 gs2,
      List.In (c, gs) (ind_cons D) -> gs = gs1 ++ gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ cinst gs1 /\
      Θ ⍮ Ξ ⍮ cinst gs1 ⊢s sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us) : cargs_ctx p D gs1 ++ ind_params D ++ Γ.
  Proof.
    intros * Hin Heq.
    destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs1 gs2 Heq) as (HΨ & _ & _).
    assert (HΨΓ : ⊢ Θ ⍮ Ξ ⍮ (cargs_ctx p D gs1 ++ ind_params D) ++ Γ).
    { apply wf_ctx_closed_app; [| eapply cargs_ctx_closed; eassumption | exact HΨ | exact HΓ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]. }
    rewrite params_split, <- !List.app_assoc, (List.app_assoc (cargs_ctx p D gs1)) in HΨΓ.
    assert (Hi : ⊢ Θ ⍮ Ξ ⍮ cinst gs1).
    { rewrite cinst_eq; eapply ctx_sub_wf; [ exact Hσ | | exact HΨΓ ].
      apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ]. }
    split; [ exact Hi |].
    pose proof (wf_sub_ext _ _ (cargs_ctx p D gs1 ++ ind_nparams D) _ _ _ Hσ) as Hext; rewrite <- cinst_eq in Hext.
    specialize (Hext Hi HΨΓ).
    rewrite List.length_app, length_cargs_ctx, length_nparams in Hext.
    rewrite params_split, <- (List.app_assoc (ind_nparams D)), List.app_assoc; exact Hext.
  Qed.
End Cargs.

(** ** The Motive's Instances at the Recursive Arguments *)

Lemma exp_wk_sub_wk : forall M φ ρ ψ, M[φ]ʷ[ρ][ψ]ʷ = M[(ι φ ⨟ ρ) ⨟ ι ψ].
Proof. intros; rewrite <- !exp_sub_of_wk, !exp_sub_sub; reflexivity. Qed.

Lemma cinst_split : forall Γ p D Us gs1 Ps gs2,
    cinst Γ p D Us (gs1 ++ ca_rec Ps :: gs2)
    = (tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2) (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))
       ++ ce_ass (apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) (ptyp_ps Ps)))
            [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))] :: nil)
      ++ cinst Γ p D Us gs1.
Proof.
  intros; unfold cinst, cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; cbn [cargs_ctx_aux].
  rewrite !tele_sub_app, length_cargs_ctx_aux, <- !List.app_assoc; cbn [tele_sub List.length List.app centry_sub sb_qn].
  reflexivity.
Qed.

Lemma wf_ih_sub : forall Θ Ξ Γ p D Us c gs gs1 Ps gs2 E,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ->
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs
      ⊢s sb_of_list (ι (wk_shiftn (List.length E + List.length gs + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                 [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)
            ++ a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)
      : elim_mctx p D Us ++ Γ.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ HM Hin Heq HΨ.
  pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _ & _ & HA & HPl & HP & _).
  specialize (HPl _ _ _ _ _ Hin Heq).
  rename Ps into tP; set (Ps := ptyp_ps tP) in *.
  set (pat := cargs_pat gs1) in *.
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  set (i := List.length pat) in *.
  set (j := List.length E) in *.
  set (na := List.length gs) in *.
  assert (Hna : na = i + S (List.length gs2)) by (unfold na, i; rewrite Heq, List.length_app; cbn; lia).
  set (m := j + na + ind_nn D).
  set (s := na - i + j).
  set (ρ := sb_qn (i + ind_nn D) (sb_of_list Id Us)).
  set (θ := (ι (wk_pat pat) ⨟ ρ) ⨟ ι (wk_shiftn s)).
  assert (HPs' : List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps = List.map (fun P => P[θ]) Ps)
    by (apply List.map_ext; intros; apply exp_wk_sub_wk).
  (* the base: a shift past the IHs, the arguments and the non-uniform parameters *)
  assert (Hb : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢s ι (wk_shiftn m) : Γ).
  { apply wf_sub_of_wk.
    unfold cinst in HΨ |- *; rewrite !List.app_assoc in HΨ |- *.
    replace m with (List.length ((E ++ tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                                     ++ tele_sub (ind_nparams D) (sb_of_list Id Us)))
      by (rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_nparams; unfold m; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  (* the context of the arguments before the recursive one *)
  destruct (wf_sub_cinst _ _ _ _ _ _ HD Hc Hl HΓ Hσ c gs gs1 (ca_rec tP :: gs2) Hin Heq) as (Hi1 & Hτ2).
  destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs1 (ca_rec tP :: gs2) Heq) as (HΨ1 & _ & Hφ).
  assert (Hw3 : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢w wk_shiftn s : cinst Γ p D Us gs1).
  { rewrite Heq in HΨ |- *; rewrite cinst_split in HΨ |- *; rewrite List.app_assoc in HΨ |- *.
    replace s with (List.length (E ++ tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                                     (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                                     ++ ce_ass (apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1))
                                                 ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps))
                                          [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))] :: nil))
      by (rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; unfold s, i, j; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  rewrite <- Hpat in Hτ2; fold i in Hτ2; fold ρ in Hτ2.
  apply wf_sub_of_list; [ apply elim_mctx_ass, Hc | exact HM | exact Hb | rewrite List.length_app, List.length_map, length_elim_mctx, HPl; cbn; lia |].
  intros k N T HN HT.
  unfold elim_mctx in HT.
  change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
  assert (Hrass : tele_ass (tele_sub (ind_nparams D) (sb_of_list Id Us))) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
  rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub, length_nparams, List.length_map; exact HPl).
  assert (Hl1 : List.length (List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps) = ind_nn D) by (rewrite List.length_map; exact HPl).
  assert (Hl2 : List.length (tele_insts (tele_sub (ind_nparams D) (sb_of_list Id Us)) (ι (wk_shiftn m))
                               (List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps)) = ind_nn D)
    by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_nparams, Hl1; lia).
  destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
  - (* a non-uniform parameter *)
    rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
    apply nth_error_map_inv in HN as (P & HPk & ->).
    rewrite tele_insts_tele_sub in HT.
    set (σ0 := ι (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))).
    assert (HT0 : exists T0, List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k = Some T0).
    { destruct (List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k) as [T0 |] eqn:E0; [ eauto |].
      apply List.nth_error_None in E0; rewrite length_tele_insts in E0 by (apply decl_closed_nparams_ass, Hc).
      rewrite length_nparams, HPl in E0; lia. }
    destruct HT0 as [T0 HT0].
    pose proof (HP _ _ _ _ _ _ _ _ Hin Heq HPk HT0) as HP0.
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ HP0 Hφ) as HP1.
    destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ HP1) as (_ & HsP & HsT).
    pose proof (wf_exp_closed_app _ _ _ Γ _ _
                  ltac:(apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ])
                  ltac:(eapply cargs_ctx_closed; eassumption) HsP HsT HP1 HΓ) as HP2.
    rewrite <- List.app_assoc in HP2.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HP2 Hτ2) as HP3.
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ HP3 Hw3) as HP4.
    replace T with (T0[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ); [ exact HP4 |].
    rewrite HPs' in HT; rewrite exp_wk_sub_wk; fold θ.
    rewrite <- (tele_insts_sub_mvc (ind_nparams D) (ind_nu D) σ0 _ θ Ps) in HT.
    + apply nth_error_map_inv in HT as (T1 & HT1 & ->); rewrite HT0 in HT1; injection HT1 as ->; reflexivity.
    + apply decl_closed_nparams_ass, Hc.
    + apply Forall_firstn'; exact Hmv.
    + apply decl_closed_nparams_scoped, Hc.
    + intros x Hx; unfold σ0, θ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      rewrite <- pat_nargs_cargs_pat; fold pat.
      replace (x + (pat_nargs pat + ind_nn D)) with (pat_nargs pat + (ind_nn D + x)) by lia.
      rewrite wk_pat_ge; fold i; unfold ρ; rewrite sb_qn_ge by lia.
      replace (i + (ind_nn D + x) - (i + ind_nn D)) with x by lia.
      rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia; cbn.
      rewrite !exp_sub_of_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold m, s; lia.
  - (* the recursive argument *)
    rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl1 in HN; rewrite Hl2 in HT.
    destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
    injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
    rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
    rewrite <- Hl1, map_shift_sb_of_list, vars_from_sb_of_list.
    apply wf_vlookup; [ exact HΨ |].
    rewrite Heq in HΨ |- *; rewrite cinst_split, List.app_assoc.
    rewrite <- !List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
    set (L := tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))).
    assert (HL : List.length L = List.length gs2) by (unfold L; rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity).
    replace (j + na - 1 - i) with (0 + List.length (E ++ L)) by (rewrite List.length_app, HL; unfold j; lia).
    match goal with |- _ ∋ # _ : ?T =>
      replace T with ((apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1))
                         ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps))
                        [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))][↑]ʷ[wk_shiftn (List.length (E ++ L))]ʷ)
    end.
    { apply ctx_lookup_app_r; constructor. }
    rewrite apps_exp_sub, !apps_exp_wk; cbn [exp_sub exp_wk]; f_equal.
    rewrite !List.map_app, !List.map_map; f_equal.
    + unfold ind_uvars.
      rewrite <- (List.map_map (fun M => M[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))])
                    (fun M => M[↑]ʷ[wk_shiftn (List.length (E ++ L))]ʷ)).
      rewrite (List.map_ext (fun M => M[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))])
                 (fun M => M[sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us)]))
        by (intros; apply exp_sub_sb_eq, sb_qn_add).
      change (vars_from (List.length (cargs_pat gs1) + ind_nn D) (ind_nu D)) with (vars_from (i + ind_nn D) (ind_nu D)).
      rewrite Hpat, <- HUl, vars_from_sb_qn, List.map_map.
      apply List.map_ext; intros U; rewrite exp_sub_of_wk, !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn.
      rewrite List.length_app, HL; unfold m, j; lia.
    + apply List.map_ext; intros P.
      rewrite (exp_sub_sb_eq _ _ ρ) by (unfold ρ; rewrite Hpat; apply sb_qn_add).
      rewrite !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; rewrite List.length_app, HL; unfold s, j; lia.
Qed.

Lemma cargs_nrec_snoc : forall gs g,
    cargs_nrec (gs ++ g :: nil) = cargs_nrec gs + match g with ca_rec _ => 1 | ca_arg _ => 0 end.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?IH; destruct g; reflexivity. Qed.

(** ** The Branches' Contexts *)

Lemma ihs_ctx_wf : forall Θ Ξ Γ p D Us A i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    List.In (c, gs) (ind_cons D) ->
    forall rest gs1 E, gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ->
      ⊢ Θ ⍮ Ξ ⍮ ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E ++ cinst Γ p D Us gs.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ HM HA Hin rest.
  induction rest as [| [A' | Ps] rest IH]; intros gs1 E Heq HE HΨ; cbn [ihs_ctx_aux List.app]; [ exact HΨ | |].
  - replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg A' :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | exact HΨ ].
  - pose proof (wf_ih_sub _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM Hin Heq HΨ) as Hj.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hj) as HAj.
    rewrite <- List.app_assoc; cbn [List.app].
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    match goal with |- ⊢ _ ⍮ _ ⍮ ?L ++ ?e :: E ++ _ => change (L ++ e :: E ++ cinst Γ p D Us gs) with (L ++ (e :: E) ++ cinst Γ p D Us gs) end.
    replace (S (List.length E)) with (List.length (ce_ass A[sb_of_list (ι (wk_shiftn (List.length E + List.length gs + ind_nn D)))
              (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                    [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) Ps
               ++ a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)] :: E)) by reflexivity.
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia |].
    cbn [List.app]; econstructor; exact HAj.
Qed.

Lemma elim_bctx_wf : forall Θ Ξ Γ p D Us A i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    ind_con D c = Some gs ->
    ⊢ Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ HM HA Hcon.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (wf_sub_cinst _ _ _ _ _ _ HD Hc Hl HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  pose proof (ihs_ctx_wf _ _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl Hσ HM HA Hin gs nil nil eq_refl eq_refl Hi) as H.
  unfold elim_bctx; rewrite <- !List.app_assoc; exact H.
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

Lemma wf_con_apps : forall Θ Ξ Γ p D c gs Ps As,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_con p c) (Ps ++ As) : apps (a_ind p) Ps.
Proof.
  intros * Hl Hcon HΓ HPl HPs HAl HAs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (con_cod_typed _ _ _ _ _ _ HD Hc Hl Hcon) as [j Hj].
  destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ0 & _ & _).
  destruct (con_ty_typed0 _ _ _ _ _ _ HD Hc Hl Hcon) as [j0 Hj0].
  assert (HC : Θ ⍮ Ξ ⍮ Γ ⊢ a_con p c : con_ty p D gs) by (eapply wf_con; eassumption).
  unfold con_ty in HC; rewrite <- ctx_pi_app in HC.
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ Hj) as (_ & Hscod & _).
  assert (Hass : tele_ass (cargs_ctx p D gs ++ ind_params D))
    by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
  pose proof (wf_apps_closed_pi _ _ _ _ j _ _ (Ps ++ As) Hass
                (cargs_ctx_closed p D c gs gs nil Hc Hin (eq_sym (List.app_nil_r gs))) Hscod Hj HΓ HC) as HR.
  replace (apps (a_ind p) Ps) with ((apps (a_ind p) (ind_pvars D (List.length gs)))[sb_of_list Id (Ps ++ As)]).
  - apply HR.
    + rewrite !List.length_app, length_cargs_ctx, HPl, HAl; unfold ind_np; lia.
    + rewrite tele_insts_app by (try apply decl_closed_params, Hc; exact HPl).
      intros k N T HN HT.
      assert (Hl2 : List.length (tele_insts (ind_params D) Id Ps) = List.length Ps)
        by (rewrite length_tele_insts by apply decl_closed_params, Hc; unfold ind_np in *; lia).
      destruct (Nat.lt_ge_cases k (List.length Ps)) as [Hk | Hk].
      * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; eauto.
      * rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl2 in HT; eauto.
  - rewrite apps_exp_sub; cbn [exp_sub]; f_equal.
    unfold ind_pvars; rewrite <- HAl, <- HPl; apply vars_from_sb_of_list_app.
Qed.

(** ** The Branch's Type *)

Lemma exp_mvc_apps : forall Ns M n, exp_mvc n (apps M Ns) <-> exp_mvc n M /\ List.Forall (exp_mvc n) Ns.
Proof.
  induction Ns as [| N Ns IH]; intros; cbn; [ split; [ auto | tauto ] |].
  rewrite IH, List.Forall_cons_iff; cbn; tauto.
Qed.

Lemma cargs_ctx_aux_mvc : forall p D gs pat, List.Forall carg_mvc gs -> ctx_mvc (cargs_ctx_aux p D pat gs).
Proof.
  induction gs as [| [A | Ps] gs IH]; intros pat Hg; cbn; [ constructor | |].
  all: inversion_clear Hg as [| ? ? Hg1 Hg2]; apply List.Forall_app; split; [ apply IH; exact Hg2 | constructor; [| constructor ] ]; cbn in *.
  - apply exp_mvc_wk; exact Hg1.
  - apply exp_mvc_apps; split; [ exact I |]; apply List.Forall_app; split.
    + unfold ind_uvars, vars_from; apply List.Forall_map, List.Forall_forall; intros; exact I.
    + apply List.Forall_map; eapply List.Forall_impl; [| exact Hg1 ]; intros; apply exp_mvc_wk; assumption.
Qed.

Lemma cargs_ctx_mvc : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> List.In (c, gs) (ind_cons D) -> ctx_mvc (cargs_ctx p D gs).
Proof. intros * (_ & (_ & _ & Hmvc) & _) Hin; apply cargs_ctx_aux_mvc; eauto. Qed.

Lemma wf_bty_sub : forall Θ Ξ Γ p D Us A i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    ind_con D c = Some gs ->
    Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ
      ⊢s sb_of_list (ι (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)))
           (vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++
            apps (a_con p c) (List.map (fun U => U[wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)]ʷ) Us ++
                              vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++ vars_from (cargs_nrec gs) (List.length gs))
            :: nil)
      : elim_mctx p D Us ++ Γ.
Proof.
  intros * HD Hc Hl HΓ HUl HUs HM HA Hcon.
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
  assert (Hw : Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢w wk_shiftn n : Γ).
  { rewrite HBeq, List.app_assoc.
    replace n with (List.length ((IHs ++ Cs) ++ Ns)) by (rewrite !List.length_app, HlI, HlC, HlN; unfold n; lia).
    apply wf_wk_shiftn_app'; rewrite <- List.app_assoc, <- HBeq; exact HB. }
  (* the uniform parameters, shifted, and the non-uniform ones, as variables *)
  set (Us' := List.map (fun U => U[wk_shiftn n]ʷ) Us).
  assert (HUs' : forall k U T, List.nth_error Us' k = Some U ->
             List.nth_error (tele_insts (ind_uparams D) Id Us') k = Some T -> Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ U : T).
  { intros k U' T' HU HT; unfold Us' in *.
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
  apply wf_sub_of_list; [ apply elim_mctx_ass, Hc | exact HM | apply wf_sub_of_wk, Hw
                        | rewrite List.length_app, length_vars_from, length_elim_mctx; cbn; lia |].
  intros k N T HN HT.
  unfold elim_mctx in HT.
  change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
  assert (Hrass : tele_ass Ns) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
  rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_vars_from; symmetry; exact HlN).
  fold Ns in HT.
  assert (Hl2 : List.length (tele_insts Ns (ι (wk_shiftn n)) (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) = ind_nn D)
    by (rewrite length_tele_insts by exact Hrass; rewrite HlN, length_vars_from; lia).
  destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HN by (rewrite length_vars_from; lia); rewrite List.nth_error_app1 in HT by lia.
    unfold Ns in HT; rewrite tele_insts_tele_sub in HT.
    apply (Hvars _ ltac:(intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; reflexivity) k); assumption.
  - rewrite List.nth_error_app2 in HN, HT by (rewrite ?length_vars_from; lia); rewrite length_vars_from in HN; rewrite Hl2 in HT.
    destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
    injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
    rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
    rewrite (List.map_ext _ (fun U => U[ι (wk_shiftn n)]))
      by (intros a; replace (ind_nn D) with (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) at 1
            by apply length_vars_from; exact (exp_shift_past a nil _ _)).
    replace (vars_from 0 (ind_nn D)) with (vars_from 0 (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))))
      by (rewrite length_vars_from; reflexivity).
    rewrite vars_from_sb_of_list.
    rewrite (List.map_ext (fun U => U[ι (wk_shiftn n)]) (fun U => U[wk_shiftn n]ʷ)) by (intros; apply exp_sub_of_wk); fold Us'.
    clear Hk' Hk Hl2 k.
    rewrite (List.app_assoc Us'); apply (wf_con_apps _ _ _ p D c gs); [ exact Hl | exact Hcon | exact HB | | | | ].
    + rewrite List.length_app, length_vars_from; unfold Us'; rewrite List.length_map, HUl; unfold ind_nn; lia.
    + rewrite params_split; intros k N T HN HT.
      rewrite tele_insts_app in HT;
        [| exact (decl_uparams_ass D Hc) | unfold Us'; rewrite List.length_map, HUl, length_ind_uparams by exact Hle; reflexivity ].
      assert (Hl1 : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
      assert (Hl3 : List.length (tele_insts (ind_uparams D) Id Us') = ind_nu D)
        by (rewrite length_tele_insts by exact (decl_uparams_ass D Hc); rewrite Hl1, length_ind_uparams by exact Hle; lia).
      destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk2 | Hk2].
      * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; exact (HUs' _ _ _ HN HT).
      * rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl1 in HN; rewrite Hl3 in HT.
        apply (Hvars (sb_of_list Id Us') ltac:(intros y Hy; unfold Us'; rewrite sb_of_list_map by lia; reflexivity) (k - ind_nu D)); [ exact HN | exact HT ].
    + rewrite length_vars_from; reflexivity.
    + intros k N T HN HT.
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
        rewrite sb_of_list_app, sb_of_list_ge; unfold Us'; rewrite sb_of_list_map by (rewrite HUl; unfold ind_nn in *; lia).
        rewrite sb_qn_ge by exact Hy1; rewrite <- sentry_exp_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold n; lia.
Qed.

(** ** Telescope Conversion *)

Lemma ctxsub_ext : forall Θ Ξ Γ Ψ Ψ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> tele_ass Ψ -> Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢s Id : Ψ ++ Γ.
Proof.
  induction 1 as [| | |]; intros Hass.
  - cbn; apply wf_sub_id; assumption.
  - inversion_clear Hass as [| ? ? _ Hass'].
    cbn [List.app]; eapply wf_sub_id_extend; [ apply IHwf_ext_eq; exact Hass' | eassumption | eassumption |].
    eapply wf_subtyp_refl; [ eapply ctxsub_exp; [ apply IHwf_ext_eq; exact Hass' | eassumption ] |].
    eapply wf_exp_eq_sym, ctxsub_exp_eq; [ apply IHwf_ext_eq; exact Hass' | eassumption ].
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
Qed.

(** ** The Motive Varying *)

Definition ctel (p : qname) (D : ind_decl) (Us : list typ) (gs : list carg) : ctx :=
  tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)) ++ tele_sub (ind_nparams D) (sb_of_list Id Us).

Lemma cinst_ctel : forall Γ p D Us gs, cinst Γ p D Us gs = ctel p D Us gs ++ Γ.
Proof. intros; unfold cinst, ctel; rewrite List.app_assoc; reflexivity. Qed.

Lemma ihs_ctx_eq : forall Θ Ξ Γ p D Us A A' i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A ≈ A' : Typeω@i ->
    List.In (c, gs) (ind_cons D) ->
    forall rest gs1 E E', gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 -> List.length E' = cargs_nrec gs1 ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ E ++ ctel p D Us gs ≈ E' ++ ctel p D Us gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E ++ ctel p D Us gs
               ≈ ihs_ctx_aux D A' Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E' ++ ctel p D Us gs.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ HM HA HA' HAA Hin rest.
  induction rest as [| [B | Ps] rest IH]; intros gs1 E E' Heq HE HE' HEE; cbn [ihs_ctx_aux List.app]; [ exact HEE | |].
  - replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg B :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | rewrite cargs_nrec_snoc, HE'; lia | exact HEE ].
  - assert (HΨ : ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs)
      by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_left; exact HEE).
    assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ E' ++ cinst Γ p D Us gs)
      by (rewrite cinst_ctel, List.app_assoc; eapply ext_eq_ctx_right; exact HEE).
    pose proof (wf_ih_sub _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM Hin Heq HΨ) as Hj.
    pose proof (wf_ih_sub _ _ _ _ _ _ _ _ _ _ _ E' HD Hc Hl HΓ HUl Hσ HM Hin Heq HΨ') as Hj'.
    rewrite HE' , <- HE in Hj'.
    rewrite cinst_ctel, List.app_assoc in Hj, Hj'.
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    rewrite <- !List.app_assoc.
    eapply (IH (gs1 ++ ca_rec Ps :: nil) (_ :: E) (_ :: E'));
      [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
      | cbn; rewrite cargs_nrec_snoc, HE'; lia |].
    cbn [List.app]; eapply wf_ext_eq_ass;
      [ exact HEE | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hj)
      | exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA Hj) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hj') ].
Qed.

Lemma elim_bctx_eq : forall Θ Ξ Γ p D Us A A' i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A ≈ A' : Typeω@i ->
    ind_con D c = Some gs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A' Us.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ HM HA HA' HAA Hcon.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (wf_sub_cinst _ _ _ _ _ _ HD Hc Hl HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  assert (H0 : Θ ⍮ Ξ ⍮ Γ ⊢ˣ nil ++ ctel p D Us gs ≈ nil ++ ctel p D Us gs).
  { apply ctx_ext_refl; [| cbn [List.app]; rewrite <- cinst_ctel; exact Hi ].
    cbn [List.app]; unfold ctel; apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ]. }
  pose proof (ihs_ctx_eq _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl Hσ HM HA HA' HAA Hin gs nil nil nil eq_refl eq_refl eq_refl H0) as H.
  exact H.
Qed.


(** ** Instances of Telescopes Read Back

    A substitution of a list of terms into a telescope sends each of the
    telescope's variables to its term, at the instance of its type. *)

Lemma wf_sub_of_list_inv : forall Θ Ξ Γ Δ Γ0 σ Ms,
    tele_ass Δ -> List.length Ms = List.length Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list σ Ms : Δ ++ Γ0 ->
    forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : T.
Proof.
  intros * Hass Hl Hσ k N T HN HT.
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
  pose proof (wf_sub_apply _ _ _ _ _ Hσ _ _ Hlk) as H.
  change (exp_sub (a_var ?x) ?s) with (sentry_exp (s x)) in H.
  rewrite (sb_of_list_nth _ _ _ N) in H by lia.
  replace (List.length Ms - 1 - List.length l2) with k in H by lia.
  rewrite (List.nth_error_nth _ _ _ HN) in H; cbn in H.
  replace (A[sb_of_list σ (List.firstn k Ms)]) with (A[wk_shiftn (List.length l2 + 1)]ʷ[sb_of_list σ Ms]); [ exact H |].
  rewrite exp_sub_wk; apply exp_sub_sb_eq; intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite <- (List.firstn_skipn k Ms) at 1; rewrite sb_of_list_app.
  replace (x + (List.length l2 + 1)) with (List.length (List.skipn k Ms) + x) by (rewrite List.length_skipn; lia).
  rewrite sb_of_list_ge; reflexivity.
Qed.

(** A list substitution under a shift past [L], followed by [L]. *)
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

Lemma firstn_app_len : forall {X : Type} (l l' : list X) n, List.length l = n -> List.firstn n (l ++ l') = l.
Proof. intros * <-; rewrite List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r. Qed.

Lemma skipn_app_len : forall {X : Type} (l l' : list X) n, List.length l = n -> List.skipn n (l ++ l') = l'.
Proof. intros * <-; rewrite List.skipn_app, List.skipn_all, Nat.sub_diag; reflexivity. Qed.

(** ** The Eliminator at a Substitution into the Motive's Context

    The parameters and the scrutinee of an elimination are read back from a
    substitution into the motive's context. *)

Lemma wf_elim_at_sub : forall Θ Ξ Γ p D Us Ns M nm A i Bs,
    ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    List.length Ns = ind_nn D ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (Ns ++ M :: nil) : elim_mctx p D Us ++ Γ ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ B : elim_bty p D c gs A Us) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim p nm A Bs M : A[sb_of_list Id (Ns ++ M :: nil)].
Proof.
  intros * Hl HΓ HUl HUs HNl Hδ Hnm HA HMx Hn HBx Hk HB.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (decl_closed_nu D Hc) as Hle.
  assert (Hrass : tele_ass (tele_sub (ind_nparams D) (sb_of_list Id Us))) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
  assert (Hti : tele_insts (elim_mctx p D Us) Id (Ns ++ M :: nil)
                = tele_insts (ind_nparams D) (sb_of_list Id Us) Ns
                  ++ (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))[sb_of_list Id Ns] :: nil).
  { unfold elim_mctx; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R).
    rewrite tele_insts_app by (try exact Hrass; rewrite length_tele_sub, length_nparams; exact HNl).
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id Us)) by (intros x; cbn; apply sentry_sub_id).
    reflexivity. }
  assert (Hlen : List.length (Ns ++ M :: nil) = List.length (elim_mctx p D Us))
    by (rewrite List.length_app, length_elim_mctx, HNl; cbn; lia).
  pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_mctx_ass p D Us Hc) Hlen Hδ) as Hinv.
  rewrite Hti in Hinv.
  assert (Hl2 : List.length (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) = ind_nn D)
    by (rewrite length_tele_insts by apply decl_closed_nparams_ass, Hc; rewrite length_nparams, HNl; lia).
  assert (HNs : forall k N T, List.nth_error Ns k = Some N ->
             List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T).
  { intros k N T HN HT; apply (Hinv k); [ rewrite List.nth_error_app1; [ exact HN | apply List.nth_error_Some; congruence ]
                                    | rewrite List.nth_error_app1; [ exact HT | apply List.nth_error_Some; congruence ] ]. }
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) (Us ++ Ns)).
  { specialize (Hinv (ind_nn D) M).
    rewrite List.nth_error_app2 in Hinv by lia; rewrite List.nth_error_app2 in Hinv by lia.
    rewrite HNl, Hl2, Nat.sub_diag in Hinv; cbn in Hinv.
    specialize (Hinv _ eq_refl eq_refl).
    rewrite apps_exp_sub, List.map_app, List.map_map in Hinv; cbn [exp_sub] in Hinv.
    rewrite <- HNl in Hinv; rewrite map_shift_sb_of_list, vars_from_sb_of_list in Hinv.
    rewrite (List.map_ext _ (fun U => U)), List.map_id in Hinv by apply exp_sub_id; exact Hinv. }
  rewrite <- (skipn_app_len Us Ns (ind_nu D) HUl).
  rewrite <- (firstn_app_len Us Ns (ind_nu D) HUl) in HA, HMx, HBx, HB.
  eapply wf_elim; [ exact Hl | | | exact HM | exact Hnm | exact HA | exact HMx | exact Hn
                  | exact HBx | exact Hk | exact HB ].
  - rewrite List.length_app, HUl, HNl; unfold ind_nn; lia.
  - assert (Hti' : tele_insts (ind_params D) Id (Us ++ Ns)
                   = tele_insts (ind_uparams D) Id Us ++ tele_insts (ind_nparams D) (sb_of_list Id Us) Ns).
    { rewrite params_split; apply tele_insts_app;
        [ apply (decl_uparams_ass D Hc) | rewrite HUl, length_ind_uparams by exact Hle; reflexivity ]. }
    assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
      by (rewrite length_tele_insts by apply (decl_uparams_ass D Hc); rewrite HUl, length_ind_uparams by exact Hle; lia).
    intros k P T HP HT; rewrite Hti' in HT.
    destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk' | Hk'].
    + rewrite List.nth_error_app1 in HP, HT by lia; exact (HUs _ _ _ HP HT).
    + rewrite List.nth_error_app2 in HP, HT by lia; rewrite HUl in HP; rewrite Hl1 in HT; exact (HNs _ _ _ HP HT).
Qed.

(** ** The Instance of a Branch's Context at a Constructor

    [ι] substitutes the non-uniform parameters, the constructor's arguments
    and the recursive eliminations into a branch. *)

Lemma wf_sub_nparams_inst : forall Θ Ξ Γ p D Ps,
    ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps)
      : tele_sub (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ++ Γ.
Proof.
  intros * Hl HΓ HPl HPs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (decl_closed_nu D Hc) as Hle.
  destruct (params_typed_split _ _ D Hc Γ Ps HPl HPs) as [HUs HNs].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  apply wf_sub_of_list;
    [ apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact (wf_nparams_sub _ _ _ HD Hc _ _ HΓ Hσ) | exact (wf_sub_id _ _ _ HΓ)
    | rewrite length_tele_sub, length_nparams, List.length_skipn; unfold ind_nn; lia |].
  intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
  rewrite (tele_insts_sb_eq _ _ (sb_of_list Id (List.firstn (ind_nu D) Ps))) in HT by (intros x; cbn; apply sentry_sub_id).
  exact (HNs _ _ _ HN HT).
Qed.

Lemma wf_sub_args_inst : forall Θ Ξ Γ p D c gs Ps As,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps ++ As) : cinst Γ p D (List.firstn (ind_nu D) Ps) gs.
Proof.
  intros * Hl Hcon HΓ HPl HPs HAl HAs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  pose proof (decl_closed_nu D Hc) as Hle.
  destruct (params_typed_split _ _ D Hc Γ Ps HPl HPs) as [HUs _].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  destruct (wf_sub_cinst _ _ _ _ _ _ HD Hc Hl HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  rewrite sb_of_list_app; unfold cinst in Hi |- *.
  apply wf_sub_of_list;
    [ apply tele_ass_sub, cargs_ctx_aux_ass | exact Hi | exact (wf_sub_nparams_inst _ _ _ _ _ _ Hl HΓ HPl HPs)
    | rewrite length_tele_sub, length_cargs_ctx; exact HAl |].
  intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
  rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Ps)) in HT; [ exact (HAs _ _ _ HN HT) |].
  rewrite <- HNl; etransitivity; [ apply sb_qn_of_list |].
  etransitivity; [ apply sb_of_list_cong; intros x; cbn; apply sentry_sub_id |].
  rewrite <- sb_of_list_app, List.firstn_skipn; reflexivity.
Qed.

Lemma wf_iota_ihs : forall Θ Ξ Γ p D c gs Ps As nm A i Bs,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    forall rest gs1 E L, gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 -> List.length L = List.length E ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D (List.firstn (ind_nu D) Ps) gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L) : E ++ cinst Γ p D (List.firstn (ind_nu D) Ps) gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L ++ elim_ihs p nm A Bs rest (List.skipn (List.length gs1) As))
        : ihs_ctx_aux D A (List.firstn (ind_nu D) Ps) (List.length gs) (cargs_pat gs1) (List.length E) rest
            ++ E ++ cinst Γ p D (List.firstn (ind_nu D) Ps) gs.
Proof.
  intros * Hl Hcon HΓ HPl HPs HAl Hnm HA HMx Hn HBx Hk HB rest.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  pose proof (decl_closed_nu D Hc) as Hle.
  destruct (params_typed_split _ _ D Hc Γ Ps HPl HPs) as [HUs _].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  assert (HM : ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) by (eapply presup_exp_ctx; exact HA).
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  induction rest as [| [B0 | Ps0] rest IH]; intros gs1 E L Heq HE HL HΨ Hδ; cbn [ihs_ctx_aux List.app].
  - cbn [elim_ihs]; rewrite List.app_nil_r; exact Hδ.
  - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
    destruct (nth_error_lt_some As _ Hlt) as [a Ha].
    rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
    replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg B0 :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    replace (S (List.length gs1)) with (List.length (gs1 ++ ca_arg B0 :: nil)) by (rewrite List.length_app; cbn; lia).
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | exact HL | exact HΨ | exact Hδ ].
  - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
    destruct (nth_error_lt_some As _ Hlt) as [a Ha].
    rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
    pose proof (wf_ih_sub _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM Hin Heq HΨ) as Hj.
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & HPl0 & _).
    specialize (HPl0 _ _ _ _ _ Hin Heq).
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hj) as HAj.
    rewrite <- List.app_assoc; cbn [List.app].
    replace (Ns ++ As ++ L ++ a_elim p nm A Bs a :: elim_ihs p nm A Bs rest (List.skipn (S (List.length gs1)) As))
      with (Ns ++ As ++ (L ++ a_elim p nm A Bs a :: nil) ++ elim_ihs p nm A Bs rest (List.skipn (S (List.length gs1)) As))
      by (rewrite <- !List.app_assoc; reflexivity).
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps0 :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec Ps0 :: nil)) by (rewrite List.length_app; cbn; lia).
    apply (IH (gs1 ++ ca_rec Ps0 :: nil) (_ :: E));
      [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
      | rewrite List.length_app; cbn; lia | cbn [List.app]; econstructor; exact HAj |].
    replace (Ns ++ As ++ L ++ a_elim p nm A Bs a :: nil) with ((Ns ++ As ++ L) ++ a_elim p nm A Bs a :: nil)
      by (rewrite <- !List.app_assoc; reflexivity).
    rewrite (sb_of_list_app (Ns ++ As ++ L) (a_elim p nm A Bs a :: nil) Id).
    change (sb_of_list (sb_of_list Id (Ns ++ As ++ L)) (a_elim p nm A Bs a :: nil))
      with (sb_of_list Id (Ns ++ As ++ L) ,, a_elim p nm A Bs a).
    eapply wf_sub_extend; [ exact Hδ | exact HAj |].
    rewrite exp_sub_sub.
    match type of Hj with wf_sub _ _ _ _ (sb_of_list (ι (wk_shiftn ?m)) (?Q ++ ?v :: nil)) =>
      assert (Hm : m = List.length (Ns ++ As ++ L)) by (rewrite !List.length_app, HNl, HAl, HL; lia);
      assert (Hidx : v[sb_of_list Id (Ns ++ As ++ L)] = a);
      [| assert (Hcomp : sb_eq (sb_of_list (ι (wk_shiftn m)) (Q ++ v :: nil) ⨟ sb_of_list Id (Ns ++ As ++ L))
                               (sb_of_list Id (List.map (fun P => P[sb_of_list Id (Ns ++ As ++ L)]) Q ++ a :: nil)));
         [ rewrite Hm; etransitivity; [ apply sb_of_list_shift_compose |]; rewrite List.map_app; cbn [List.map]; rewrite Hidx; reflexivity
         | rewrite (exp_sub_sb_eq _ _ _ Hcomp); eapply wf_elim_at_sub;
             [ exact Hl | exact HΓ | exact HUl | exact HUs | rewrite !List.length_map; exact HPl0
             | rewrite <- Hcomp; exact (wf_sub_compose _ _ _ _ _ _ _ Hj Hδ)
             | exact Hnm | exact HA | exact HMx | exact Hn | exact HBx | exact Hk | exact HB ] ] ]
    end.
    change (exp_sub (a_var ?x) ?s) with (sentry_exp (s x)).
    rewrite (sb_of_list_nth _ _ _ a) by (rewrite !List.length_app, HNl, HAl, HL, Heq, List.length_app, length_cargs_pat; cbn; lia).
    rewrite !List.length_app, HNl, HAl, HL, length_cargs_pat.
    replace (ind_nn D + (List.length gs + List.length E) - 1 - (List.length E + List.length gs - 1 - List.length gs1))
      with (ind_nn D + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
    cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl; replace (ind_nn D + List.length gs1 - ind_nn D) with (List.length gs1) by lia.
    rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact Ha.
Qed.

Lemma wf_iota_sub : forall Θ Ξ Γ p D c gs Ps As nm A i Bs,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs p nm A Bs gs As)
      : elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ.
Proof.
  intros * Hl Hcon HΓ HPl HPs HAl HAs Hnm HA HMx Hn HBx Hk HB.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  pose proof (decl_closed_nu D Hc) as Hle.
  destruct (params_typed_split _ _ D Hc Γ Ps HPl HPs) as [HUs _].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  destruct (wf_sub_cinst _ _ _ _ _ _ HD Hc Hl HΓ Hσ c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
  pose proof (wf_sub_args_inst _ _ _ _ _ _ _ _ _ Hl Hcon HΓ HPl HPs HAl HAs) as Hδ.
  rewrite <- (List.app_nil_r As) in Hδ at 1.
  pose proof (wf_iota_ihs _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hcon HΓ HPl HPs HAl Hnm HA HMx Hn HBx Hk HB gs nil nil nil
                eq_refl eq_refl eq_refl Hi Hδ) as H.
  cbn [List.app List.skipn List.length cargs_pat] in H.
  unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
Qed.

(** The type of a branch at the instance [ι] substitutes is the motive at
    the constructor applied. *)
Lemma elim_bty_iota : forall p D c gs A Us Ns As ihs,
    List.length Ns = ind_nn D -> List.length As = List.length gs -> List.length ihs = cargs_nrec gs ->
    (elim_bty p D c gs A Us)[sb_of_list Id (Ns ++ As ++ ihs)]
    = A[sb_of_list Id (Ns ++ apps (a_con p c) (Us ++ Ns ++ As) :: nil)].
Proof.
  intros * HNl HAl Hil.
  unfold elim_bty; rewrite exp_sub_sub; apply exp_sub_sb_eq.
  replace (ind_nn D + List.length gs + cargs_nrec gs) with (List.length (Ns ++ As ++ ihs))
    by (rewrite !List.length_app; lia).
  etransitivity; [ apply sb_of_list_shift_compose |].
  rewrite List.map_app; cbn [List.map]; rewrite apps_exp_sub, !List.map_app; cbn [exp_sub].
  rewrite List.map_map, map_shift_sb_of_list, (List.map_ext (fun U => U[Id]) (fun U => U)), List.map_id by apply exp_sub_id.
  replace (cargs_nrec gs + List.length gs) with (List.length (As ++ ihs)) by (rewrite List.length_app; lia).
  rewrite <- HNl, vars_from_sb_of_list_app.
  rewrite <- HAl, <- Hil, (sb_of_list_app Ns (As ++ ihs) Id), vars_from_sb_of_list_app.
  reflexivity.
Qed.

(** ** The Sides of the Eliminator's Equations

    What presupposition needs of [wf_exp_eq_elim_cong] and
    [wf_exp_eq_elim_iota]: both sides are of the type of the equation. *)

Lemma elim_mctx_head_inst : forall p D Us Ns,
    List.length Ns = ind_nn D ->
    (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))[sb_of_list Id Ns]
    = apps (a_ind p) (Us ++ Ns).
Proof.
  intros * HNl.
  rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
  rewrite <- HNl, map_shift_sb_of_list, vars_from_sb_of_list.
  rewrite (List.map_ext (fun U => U[Id]) (fun U => U)), List.map_id by apply exp_sub_id; reflexivity.
Qed.

(** The scrutinee varying moves the instance of the motive's context. *)
Lemma wf_elim_inst_sub_eq : forall Θ Ξ Γ p D Ps M M',
    ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps -> Θ ⍮ Ξ ⍮ Γ ⊢ M' : apps (a_ind p) Ps ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps (a_ind p) Ps ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) ≈ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M' :: nil)
      : elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ.
Proof.
  intros * Hl HΓ HPl HPs HM HM' HMM HΨ.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
  pose proof (wf_sub_nparams_inst _ _ _ _ _ _ Hl HΓ HPl HPs) as Hδ.
  rewrite !sb_of_list_app; cbn [sb_of_list].
  unfold elim_mctx in HΨ |- *; cbn [List.app] in HΨ |- *.
  destruct (ctx_decomp HΨ) as [_ [j Hj]].
  assert (Hty : (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) (List.firstn (ind_nu D) Ps) ++ vars_from 0 (ind_nn D)))
                  [sb_of_list Id (List.skipn (ind_nu D) Ps)] = apps (a_ind p) Ps)
    by (rewrite elim_mctx_head_inst by exact HNl; rewrite List.firstn_skipn; reflexivity).
  eapply wf_sub_eq_extend; [ apply wf_sub_eq_refl; exact Hδ | exact Hj | rewrite Hty; exact HM | rewrite Hty; exact HM'
                           | rewrite Hty; exact HMM ].
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

(** The type of a branch, the motive varying. *)
Lemma elim_bty_eq : forall Θ Ξ Γ p D Us A A' i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A ≈ A' : Typeω@i ->
    ind_con D c = Some gs ->
    Θ ⍮ Ξ ⍮ elim_bctx p D gs A' Us ++ Γ ⊢ elim_bty p D c gs A' Us : Typeω@i /\
    Θ ⍮ Ξ ⍮ elim_bctx p D gs A' Us ++ Γ ⊢ elim_bty p D c gs A Us ≈ elim_bty p D c gs A' Us : Typeω@i.
Proof.
  intros * HD Hc Hl HΓ HUl HUs HM HA' HAA Hcon.
  pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl HUs HM HA' Hcon) as Hθ.
  split; [ exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hθ) | exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA Hθ) ].
Qed.

Lemma wf_elim_cong_lhs : forall Θ Ξ Γ p D Ps M nm A i Bs (Bs' : list (String.string * nat * exp)),
    ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', List.nth_error Bs k = Some (c, n, B) -> List.nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim p nm A Bs M : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl HPl HPs HM Hnm HA HMx Hn HBx Hm Hk HB.
  eapply wf_elim; try eassumption.
  intros c gs n B Hcon Hin.
  destruct (brs_in_fst' _ _ _ _ _ Hm Hin) as (k & B' & Hk1 & Hk2).
  exact (HB _ _ _ _ _ _ Hk1 Hk2 Hcon).
Qed.

Lemma wf_elim_cong_rhs : forall Θ Ξ Γ p D Ps M M' nm A A' i Bs (Bs' : list (String.string * nat * exp)),
    ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : apps (a_ind p) Ps ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps (a_ind p) Ps ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A ≈ A' : Typeω@i ->
    brs_names (ind_cons D) Bs ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', List.nth_error Bs k = Some (c, n, B) -> List.nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B' : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim p nm A' Bs' M' : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl HPl HPs HM HM' HMM Hnm HA HMx HA' HAA Hn Hm Hk HB.
  pose proof (presup_exp_ctx HM) as HΓ.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (decl_closed_nu D Hc) as Hle.
  destruct (params_typed_split _ _ D Hc Γ Ps HPl HPs) as [HUs _].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUs) as Hσ.
  pose proof (presup_exp_ctx HA) as HΨ.
  set (Us := List.firstn (ind_nu D) Ps) in *.
  assert (Hδ : Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) : elim_mctx p D Us ++ Γ)
    by (apply wf_elim_inst_sub; assumption).
  assert (HE : Θ ⍮ Ξ ⍮ Γ ⊢ a_elim p nm A' Bs' M' : A'[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M' :: nil)]).
  { eapply wf_elim; [ exact Hl | exact HPl | exact HPs | exact HM' | exact Hnm | exact HA' | exact HMx
                    | exact (brs_names_fst _ _ _ Hn Hm) | | |].
    - intros c gs Hcon; apply ctx_ext_refl; [ apply elim_bctx_ass, Hc |].
      eapply elim_bctx_wf; eassumption.
    - intros c gs n B' Hcon Hin.
      destruct (brs_in_fst _ _ _ _ _ Hm Hin) as (k & B & _ & _ & HinB).
      exact (Hk _ _ _ _ Hcon HinB).
    - intros c gs n B' Hcon Hin.
      destruct (brs_in_fst _ _ _ _ _ Hm Hin) as (k & B & Hk1 & Hk2 & _).
      pose proof (HB _ _ _ _ _ _ Hk1 Hk2 Hcon) as HB'.
      pose proof (elim_bctx_eq _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl Hσ HΨ HA HA' HAA Hcon) as Hx.
      pose proof (ctxsub_ext _ _ _ _ _ Hx (elim_bctx_ass _ _ _ _ _ Hc)) as Hs.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB' Hs) as HB''; rewrite !exp_sub_id in HB''.
      destruct (elim_bty_eq _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HΓ HUl HUs HΨ HA' HAA Hcon) as [Hty Heq].
      eapply wf_conv; [ exact HB'' | exact Hty | exact Heq ]. }
  pose proof (wf_elim_inst_sub_eq _ _ _ _ _ _ _ _ Hl HΓ HPl HPs HM HM' HMM HΨ) as Hδδ.
  pose proof (sub_eq_preserves_exp _ _ _ _ _ HA' _ _ _ Hδδ) as H1.
  pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA Hδ) as H2.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hδ) as H3.
  eapply wf_conv; [ exact HE | exact H3 |].
  eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact H1 | apply wf_exp_eq_sym; exact H2 ].
Qed.

Lemma wf_iota_lhs : forall Θ Ξ Γ p D c gs Ps As nm A i Bs,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim p nm A Bs (apps (a_con p c) (Ps ++ As))
      : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ apps (a_con p c) (Ps ++ As) :: nil)].
Proof.
  intros * Hl Hcon HΓ HPl HPs HAl HAs Hnm HA HMx Hn HBx Hk HB.
  eapply wf_elim; try eassumption.
  eapply wf_con_apps; eassumption.
Qed.

Lemma wf_iota_rhs : forall Θ Ξ Γ p D c gs Ps As nm A i Bs n B,
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    brs_lookup Bs c = Some (n, B) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs p nm A Bs gs As)]
      : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ apps (a_con p c) (Ps ++ As) :: nil)].
Proof.
  intros * Hl Hcon HΓ HPl HPs HAl HAs Hnm HA HMx Hn HBx Hk HB HBl.
  pose proof (brs_lookup_in _ _ _ _ HBl) as Hin.
  pose proof (wf_iota_sub _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hcon HΓ HPl HPs HAl HAs Hnm HA HMx Hn HBx Hk HB) as Hσ.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HB _ _ _ _ Hcon Hin) Hσ) as H.
  rewrite elim_bty_iota in H;
    [| rewrite List.length_skipn; unfold ind_nn; lia | exact HAl | apply length_elim_ihs; exact HAl ].
  replace (List.firstn (ind_nu D) Ps ++ List.skipn (ind_nu D) Ps ++ As) with (Ps ++ As) in H
    by (rewrite List.app_assoc, List.firstn_skipn; reflexivity).
  exact H.
Qed.
