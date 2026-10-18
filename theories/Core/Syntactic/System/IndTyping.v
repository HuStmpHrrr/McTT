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
  intros * HΓ Hl; split.
  - exact (gv_decls _ _ _ _ _ _ (gctx_rwf _ _ (ctx_wf_gctx _ _ _ HΓ)) _ _ Hl).
  - exact (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HΓ) Hl).
Qed.

(** A constructor is typed at its type without the shape premise of
    [wf_con]: that premise follows from the declaration. *)
Lemma wf_con_of_lookup : forall Θ Ξ Γ p D c gs i,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_con p c : con_ty p D gs.
Proof.
  intros * HΓ Hl Hcon HΨ Hty.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  eapply wf_con; try eassumption.
  exact (shape_rest_wf' _ _ _ _ _ _ HD Hc Hl Hcon).
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

Section Params.
  Context (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (HD : decl_typed Θ Ξ D) (Hc : decl_closed D).

  Lemma decl_uparams_closed : ctx_scoped 0 (ind_uparams D).
  Proof. pose proof (dc_params _ Hc) as Hs; rewrite params_split in Hs; apply ctx_scoped_app in Hs as [_ Hs]; exact Hs. Qed.

  Lemma decl_uparams_ass : tele_ass (ind_uparams D).
  Proof. apply Forall_skipn', decl_closed_params, Hc. Qed.

  Lemma decl_uparams_mvc : ctx_mvc (ind_uparams D).
  Proof. pose proof (dmv_params _ (dt_mvc _ _ _ HD)) as Hmv; apply Forall_skipn'; exact Hmv. Qed.

  Lemma decl_nparams_mvc : ctx_mvc (ind_nparams D).
  Proof. pose proof (dmv_params _ (dt_mvc _ _ _ HD)) as Hmv; apply Forall_firstn'; exact Hmv. Qed.

  Lemma wf_params_app : forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_params D ++ Γ.
  Proof.
    intros * HΓ; pose proof (dt_ass _ _ _ HD) as Hass; pose proof (dt_params _ _ _ HD) as HΔ; pose proof (dc_params _ Hc) as Hs.
    apply wf_ctx_closed_app; assumption.
  Qed.

  Lemma wf_uparams_app : forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ.
  Proof.
    intros * HΓ; pose proof (dt_params _ _ _ HD) as HΔ; rewrite params_split in HΔ.
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
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ.
  Proof.
    intros * HΓ Hl HUs; apply wf_sub_of_list_id;
      [ apply decl_uparams_ass | apply wf_uparams_app, HΓ | rewrite length_ind_uparams by apply (decl_closed_nu D Hc); exact Hl | exact HUs ].
  Qed.

  Lemma wf_nparams_sub : forall Γ Us,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ.
  Proof.
    intros * HΓ Hσ; eapply ctx_sub_wf; [ exact Hσ | apply decl_closed_nparams_ass, Hc |].
    rewrite List.app_assoc, <- params_split; apply wf_params_app, HΓ.
  Qed.

  (** The level of the sort, at the uniform parameters. *)
  Lemma sort_lvl_at : forall Γ Us,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      exists n, Θ ⍮ Ξ ⍮ Γ ⊢ ind_sort_lvl (ind_sort D)[sb_of_list Id Us] : Level@n.
  Proof.
    intros * HΓ Hσ; pose proof HD as [_ _ Hle _ HS _ [n Hn] _ _ _ _ _ _]; exists n.
    pose proof (dc_sort _ Hc) as HsS.
    destruct (ind_sort_univ_sub (ind_sort D) (sb_of_list Id Us) HS) as [_ <-].
    assert (Hn' : Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ ⊢ ind_sort_lvl (ind_sort D) : Level@n).
    { apply wf_exp_closed_app; [ apply decl_uparams_ass | apply decl_uparams_closed | | exact I | exact Hn | exact HΓ ].
      rewrite length_ind_uparams by exact Hle; destruct HS as [[i Heq] | [t Heq]]; rewrite Heq in *; cbn in *; auto. }
    exact (sub_preserves_exp _ _ _ _ _ _ _ Hn' Hσ).
  Qed.

  (** The sort at the uniform parameters is a type of a large universe. *)
  Lemma sort_at_large : forall Γ Us A,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : (ind_sort D)[sb_of_list Id Us] -> exists j, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j.
  Proof.
    intros * HΓ Hσ HA; pose proof (dt_sort_univ _ _ _ HD) as HS.
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
  assert (Hw : Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ ⊢ʷ wk_shiftn (ind_nn D) : Γ).
  { rewrite <- (length_ind_nparams_sub D (sb_of_list Id Us)); apply wf_wk_shiftn_app'; exact HΨ0. }
  assert (HUs' : forall k U T, List.nth_error (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us) k = Some U ->
             List.nth_error (tele_insts (ind_uparams D) Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us)) k = Some T ->
             Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ ⊢ U : T).
  { intros k U' T' HU HT.
    rewrite <- tele_insts_closed_wk in HT by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
    apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    exact (wk_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hw). }
  assert (Hσ' : Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ
                  ⊢ˢ sb_of_list Id (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us)
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
  intros * Hc Hin Heq; pose proof Hc as [_ Hle Hs _ HA HPs _].
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
  Hypothesis (Hσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ).

  Definition cinst (gs1 : list carg) : ctx :=
    tele_sub (cargs_ctx p D gs1) (sb_qn (ind_nn D) (sb_of_list Id Us)) ++ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ.

  Lemma cinst_eq : forall gs1,
      cinst gs1 = tele_sub (cargs_ctx p D gs1 ++ ind_nparams D) (sb_of_list Id Us) ++ Γ.
  Proof. intros; unfold cinst; rewrite tele_sub_app, length_nparams, List.app_assoc; reflexivity. Qed.

  Lemma wf_sub_cinst : forall c gs gs1 gs2,
      List.In (c, gs) (ind_cons D) -> gs = gs1 ++ gs2 ->
      ⊢ Θ ⍮ Ξ ⍮ cinst gs1 /\
      Θ ⍮ Ξ ⍮ cinst gs1 ⊢ˢ sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us) : cargs_ctx p D gs1 ++ ind_params D ++ Γ.
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

Lemma cinst_split : forall Γ p D Us gs1 Ps gs2,
    cinst Γ p D Us (gs1 ++ ca_rec Ps :: gs2)
    = (tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2) (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))
       ++ ce_ass (ptyp_ty p D (cargs_pat gs1) Ps)[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))] :: nil)
      ++ cinst Γ p D Us gs1.
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

    At the end of a shape, the motive's context is instantiated by the
    shape's non-uniform parameters, moved by [σ] from the closed context
    [Tc] of the shape's components, and by the argument applied to the
    shape's domains, over the base [β]: the uniform parameters [σ] sends
    are those of the motive's context, moved by [β]. *)

Definition shape_uc (D : ind_decl) (Us : list exp) (Tc : ctx) (σ β : sub) : Prop :=
  forall y, y < ind_nu D -> sentry_exp (σ (y + (List.length Tc - ind_nu D))) = sentry_exp ((sb_of_list Id Us ⨟ β) y).

Lemma ind_head_inst : forall p D Us Ns β,
    List.length Ns = ind_nn D ->
    (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))[sb_of_list β Ns]
    = apps (a_ind p) (List.map (fun U => U[β]) Us ++ Ns).
Proof.
  intros * HNl.
  rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
  rewrite <- HNl, vars_from_sb_of_list; f_equal; f_equal.
  apply List.map_ext; intros U; exact (exp_shift_past U nil Ns β).
Qed.

Lemma ih_leaf_nsub : forall Θ Ξ Γ p D Us Ψ Tc β σ Ps,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Tc ->
    shape_uc D Us Tc σ β ->
    List.length Ps = ind_nn D ->
    (forall k P T, List.nth_error Ps k = Some P ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))) Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Tc ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps) : tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ.
Proof.
  intros * HD Hc Hl HUl HM Hβ Hσ Huc HPl HP.
  assert (HPl' : List.length (List.map (fun P => P[σ]) Ps) = ind_nn D) by (rewrite List.length_map; exact HPl).
  assert (HN : ⊢ Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ)
    by (unfold elim_mctx in HM; cbn [List.app] in HM; destruct (ctx_decomp HM) as [H0 _]; exact H0).
  apply wf_sub_of_list; [ apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact HN | exact Hβ
                        | rewrite length_tele_sub, HPl', length_nparams; reflexivity |].
  intros k N T HN' HT.
  apply nth_error_map_inv in HN' as (P & HPk & ->).
  rewrite tele_insts_tele_sub in HT.
  set (σ0 := sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))).
  assert (HT0 : exists T0, List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k = Some T0).
  { destruct (List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k) as [T0 |] eqn:E0; [ eauto |].
    apply List.nth_error_None in E0; rewrite length_tele_insts in E0 by (apply decl_closed_nparams_ass, Hc).
    rewrite length_nparams, HPl in E0.
    assert (Hk : k < List.length Ps) by (apply List.nth_error_Some; congruence); lia. }
  destruct HT0 as [T0 HT0].
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HP _ _ _ HPk HT0) Hσ) as HP1.
  replace T with T0[σ]; [ exact HP1 |].
  rewrite <- (tele_insts_sub_mvc (ind_nparams D) (ind_nu D) σ0 _ σ Ps) in HT.
  + apply nth_error_map_inv in HT as (T1 & HT1 & ->); rewrite HT0 in HT1; injection HT1 as ->; reflexivity.
  + apply decl_closed_nparams_ass, Hc.
  + apply (decl_nparams_mvc _ _ _ HD).
  + apply decl_closed_nparams_scoped, Hc.
  + intros y Hy; unfold σ0; cbn [sb_of_wk sentry_sub wk_shiftn]; exact (Huc y Hy).
Qed.

Lemma elim_mctx_head_typed : forall Θ Ξ Γ p D Us,
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    exists j, Θ ⍮ Ξ ⍮ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ
      ⊢ apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)) : Typeω@j.
Proof. intros * HM; unfold elim_mctx in HM; cbn [List.app] in HM; destruct (ctx_decomp HM) as [_ [j Hj]]; eauto. Qed.

Lemma ih_leaf_sub : forall Θ Ξ Γ p D Us Ψ Tc β σ Ps x,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Tc ->
    shape_uc D Us Tc σ β ->
    List.length Ps = ind_nn D ->
    (forall k P T, List.nth_error Ps k = Some P ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length Tc - ind_nu D))) Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Tc ⊢ P : T) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ x : apps (a_ind p) (List.map (fun U => U[β]) Us ++ List.map (fun P => P[σ]) Ps) ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => P[σ]) Ps ++ x :: nil) : elim_mctx p D Us ++ Γ.
Proof.
  intros * HD Hc Hl HUl HM Hβ Hσ Huc HPl HP Hx.
  pose proof (ih_leaf_nsub _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HM Hβ Hσ Huc HPl HP) as Hn.
  destruct (elim_mctx_head_typed _ _ _ _ _ _ HM) as [j Hj].
  rewrite sb_of_list_app; cbn [sb_of_list]; unfold elim_mctx; cbn [List.app].
  eapply wf_sub_extend; [ exact Hn | exact Hj |].
  rewrite ind_head_inst by (rewrite List.length_map; exact HPl); exact Hx.
Qed.

(** *** Along a Shape

    The invariant of a shape's prefix: the components' context so far is
    [doms_ctx Bs1 ++ Tb ++ ind_params D], the domains [Bs1] above the
    context [Tb] of the non-recursive arguments; what remains of the shape
    has its domains and its leaf typed there. *)

Definition shape_doms_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (Bs1 : list exp) (Tb : ctx) (t : ptyp) : Prop :=
  forall Bs1' B Bs2, ptyp_doms t = Bs1' ++ B :: Bs2 ->
    exists j, Θ ⍮ Ξ ⍮ doms_ctx (Bs1 ++ Bs1') ++ Tb ++ ind_params D ⊢ B : Typeω@j.

Definition shape_leaf_typed (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (Bs1 : list exp) (Tb : ctx) (t : ptyp) : Prop :=
  forall k P T, List.nth_error (ptyp_ps t) k = Some P ->
    List.nth_error (tele_insts (ind_nparams D)
                      (sb_of_wk (wk_shiftn (List.length Bs1 + ptyp_depth t + List.length Tb + ind_nn D))) (ptyp_ps t)) k
      = Some T ->
    Θ ⍮ Ξ ⍮ doms_ctx (Bs1 ++ ptyp_doms t) ++ Tb ++ ind_params D ⊢ P : T.

Lemma doms_ctx_app_one : forall Bs B, doms_ctx (Bs ++ B :: nil) = ce_ass B :: doms_ctx Bs.
Proof. intros; unfold doms_ctx; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma length_doms_ctx : forall Bs, List.length (doms_ctx Bs) = List.length Bs.
Proof. intros; unfold doms_ctx; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma shape_doms_typed_pi : forall Θ Ξ D Bs1 Tb B t,
    shape_doms_typed Θ Ξ D Bs1 Tb (pt_pi B t) -> shape_doms_typed Θ Ξ D (Bs1 ++ B :: nil) Tb t.
Proof.
  intros * H Bs1' B' Bs2 E; destruct (H (B :: Bs1') B' Bs2 ltac:(cbn; rewrite E; reflexivity)) as [j Hj].
  exists j; rewrite <- List.app_assoc; exact Hj.
Qed.

Lemma shape_leaf_typed_pi : forall Θ Ξ D Bs1 Tb B t,
    shape_leaf_typed Θ Ξ D Bs1 Tb (pt_pi B t) -> shape_leaf_typed Θ Ξ D (Bs1 ++ B :: nil) Tb t.
Proof.
  intros * H k P T HP HT; specialize (H k P T HP).
  unfold ptyp_depth in H, HT; cbn [ptyp_doms ptyp_ps List.length] in H.
  rewrite <- List.app_assoc; cbn [List.app]; apply H.
  rewrite List.length_app in HT; cbn [List.length] in HT.
  replace (List.length Bs1 + S (List.length (ptyp_doms t)) + List.length Tb + ind_nn D)
    with (List.length Bs1 + 1 + List.length (ptyp_doms t) + List.length Tb + ind_nn D) by lia; exact HT.
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
Lemma length_shape_ctx : forall D Bs1 Tb, decl_closed D ->
    List.length (doms_ctx Bs1 ++ Tb ++ ind_params D) - ind_nu D = List.length Bs1 + List.length Tb + ind_nn D /\
    ind_nu D <= List.length (doms_ctx Bs1 ++ Tb ++ ind_params D).
Proof.
  intros * Hc; rewrite !List.length_app, length_doms_ctx; pose proof (decl_closed_nu D Hc) as Hnu.
  unfold ind_nn, ind_np in *; lia.
Qed.

(** The leaf's parameters, in the shape's components' context. *)
Lemma shape_leaf_at : forall Θ Ξ D Bs1 Tb t, decl_closed D -> shape_leaf_typed Θ Ξ D Bs1 Tb t ->
    ptyp_doms t = nil ->
    forall k P T, List.nth_error (ptyp_ps t) k = Some P ->
      List.nth_error (tele_insts (ind_nparams D)
        (sb_of_wk (wk_shiftn (List.length (doms_ctx Bs1 ++ Tb ++ ind_params D) - ind_nu D))) (ptyp_ps t)) k = Some T ->
      Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ Tb ++ ind_params D ⊢ P : T.
Proof.
  intros * Hc HP Hd k P T HPk HT; specialize (HP k P T HPk).
  unfold ptyp_depth in HP; rewrite Hd in HP; cbn [List.length] in HP; rewrite List.app_nil_r in HP.
  apply HP; rewrite (proj1 (length_shape_ctx D Bs1 Tb Hc)) in HT; rewrite Nat.add_0_r; exact HT.
Qed.

(** The type of a shape's argument is a type. *)
Lemma ty_at_typed : forall Θ Ξ Γ p D Us t Ψ Bs1 Tb β σ,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ ind_params D ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ ind_params D) σ β ->
    List.length (ptyp_ps t) = ind_nn D ->
    shape_doms_typed Θ Ξ D Bs1 Tb t -> shape_leaf_typed Θ Ξ D Bs1 Tb t ->
    exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ty_at p (List.map (fun U => U[β]) Us) σ t : Typeω@j.
Proof.
  intros Θ Ξ Γ p D Us t; induction t as [k0 Ps | k0 Ps | B t IH];
    intros * HD Hc Hl HUl HM Hβ Hσ Huc HPl HB HP; cbn [ptyp_ty_at].
  1, 2: destruct (elim_mctx_head_typed Θ Ξ Γ p D Us HM) as [j Hj]; exists j; cbn [ptyp_ps] in HPl |- *;
    rewrite <- (ind_head_inst p D Us _ β) by (rewrite List.length_map; exact HPl);
    exact (sub_preserves_exp _ _ _ _ _ _ _ Hj (ih_leaf_nsub _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HM Hβ Hσ Huc HPl
             (shape_leaf_at _ _ _ _ _ _ Hc HP eq_refl))).
  destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
  assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
  pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
  assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
    by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
  replace ((doms_ctx Bs1 ++ Tb ++ ind_params D) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ ind_params D) in Hσ'
    by (rewrite doms_ctx_app_one; reflexivity).
  destruct (IH (Ψ ▹ B[σ]) (Bs1 ++ B :: nil) Tb (β ⨟ ι ↑) (q σ) HD Hc Hl HUl HM Hβ' Hσ') as [j2 Hj2].
  - rewrite doms_ctx_app_one; apply shape_uc_pi; [ exact (proj2 (length_shape_ctx D Bs1 Tb Hc)) | exact Huc ].
  - exact HPl.
  - apply shape_doms_typed_pi; exact HB.
  - apply shape_leaf_typed_pi; exact HP.
  - exists (max j1 j2); eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' |].
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

(** The type of a recursive result of a shape is a type, and equal ones of
    equal motives. *)
Lemma ihty_typed : forall Θ Ξ Γ p D Us A A' i t Ψ Bs1 Tb β σ x,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D ->
    List.length Us = ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ β : Γ -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ ind_params D ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ ind_params D) σ β ->
    List.length (ptyp_ps t) = ind_nn D ->
    shape_doms_typed Θ Ξ D Bs1 Tb t -> shape_leaf_typed Θ Ξ D Bs1 Tb t ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ x : ptyp_ty_at p (List.map (fun U => U[β]) Us) σ t ->
    exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty A β σ x t : Typeω@j /\ Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty A' β σ x t : Typeω@j /\
      Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ihty A β σ x t ≈ ptyp_ihty A' β σ x t : Typeω@j.
Proof.
  intros Θ Ξ Γ p D Us A A' i t; induction t as [k0 Ps | k0 Ps | B t IH];
    intros * HD Hc Hl HUl HM HA HA' HAA Hβ Hσ Huc HPl HB HP Hx; cbn [ptyp_ihty ptyp_ty_at] in *.
  1, 2: pose proof (ih_leaf_sub _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HM Hβ Hσ Huc HPl (shape_leaf_at _ _ _ _ _ _ Hc HP eq_refl) Hx)
          as Hτ; exists i;
    refine (conj (sub_preserves_exp _ _ _ _ _ _ _ HA Hτ) (conj (sub_preserves_exp _ _ _ _ _ _ _ HA' Hτ) _));
    exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA Hτ).
  cbn [ptyp_ps] in HPl.
  destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
  assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
  pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
  assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ β ⨟ ι ↑ : Γ)
    by (eapply wf_sub_compose; [ exact Hβ | apply wf_sub_of_wk, wf_wk_shift; exact HΨ' ]).
  replace ((doms_ctx Bs1 ++ Tb ++ ind_params D) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ ind_params D) in Hσ'
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
  destruct (IH _ _ _ _ _ _ HD Hc Hl HUl HM HA HA' HAA Hβ' Hσ' Huc' HPl HB'' HP'' Hx') as (j3 & H1 & H2 & H3).
  exists (max j1 j3); split; [| split ].
  - eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_max_right; exact H1 ].
  - eapply wf_pi_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_max_right; exact H2 ].
  - eapply wf_exp_eq_pi_cong_large; [ eapply lift_exp_max_left; exact Hj1' | eapply lift_exp_eq_max_left, wf_exp_eq_refl; exact Hj1'
                              | eapply lift_exp_eq_max_right; exact H3 ].
Qed.

(** *** A Recursive Argument in a Branch's Context

    In the context of the arguments, after [E], the recursive argument's
    components are moved by [ihs_sub] from the closed context of the
    non-recursive arguments before it and the parameters, the eliminator's
    context [Γ] is [b] binders out, and the argument is of its shape's type
    there. *)
Lemma rec_arg_inst : forall Θ Ξ Γ p D Us c gs gs1 t gs2 E,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ->
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ˢ ι (wk_shiftn (List.length E + List.length gs + ind_nn D)) : Γ /\
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ˢ ihs_sub D Us (List.length gs) (cargs_pat gs1) (List.length E)
      : doms_ctx nil ++ cargs_strat gs1 ++ ind_params D /\
    shape_uc D Us (doms_ctx nil ++ cargs_strat gs1 ++ ind_params D)
      (ihs_sub D Us (List.length gs) (cargs_pat gs1) (List.length E)) (ι (wk_shiftn (List.length E + List.length gs + ind_nn D))) /\
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ #(List.length E + List.length gs - 1 - List.length (cargs_pat gs1))
      : ptyp_ty_at p (List.map (fun U => U[ι (wk_shiftn (List.length E + List.length gs + ind_nn D))]) Us)
          (ihs_sub D Us (List.length gs) (cargs_pat gs1) (List.length E)) t.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ Hin Heq HΨ.
  pose proof HD as [Hass [Hmv Hmvs Hmvc] Hle HΔ HS _ _ _ _ _ _ _ _].
  set (pat := cargs_pat gs1) in *.
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  set (i := List.length pat) in *.
  set (j := List.length E) in *.
  set (na := List.length gs) in *.
  assert (Hna : na = i + S (List.length gs2)) by (unfold na, i; rewrite Heq, List.length_app; cbn; lia).
  set (m := j + na + ind_nn D).
  set (s := na - i + j).
  set (ρ := sb_qn (i + ind_nn D) (sb_of_list Id Us)).
  set (θ := ihs_sub D Us na pat j).
  assert (Hθ : θ = (ι (wk_pat pat) ⨟ ρ) ⨟ ι (wk_shiftn s)) by reflexivity.
  (* the base: a shift past the IHs, the arguments and the non-uniform parameters *)
  assert (Hb : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ˢ ι (wk_shiftn m) : Γ).
  { apply wf_sub_of_wk.
    unfold cinst in HΨ |- *; rewrite !List.app_assoc in HΨ |- *.
    replace m with (List.length ((E ++ tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                                     ++ tele_sub (ind_nparams D) (sb_of_list Id Us)))
      by (rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_nparams; unfold m; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  (* the components: past the recursive arguments before, the uniform
     parameters instantiated, past the arguments after *)
  destruct (wf_sub_cinst _ _ _ _ _ _ HD Hc Hl HΓ Hσ c gs gs1 (ca_rec t :: gs2) Hin Heq) as (Hi1 & Hτ2).
  destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs1 (ca_rec t :: gs2) Heq) as (HΨ1 & HSt & Hφ).
  assert (Hw3 : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ʷ wk_shiftn s : cinst Γ p D Us gs1).
  { rewrite Heq in HΨ |- *; rewrite cinst_split in HΨ |- *; rewrite List.app_assoc in HΨ |- *.
    replace s with (List.length (E ++ tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                                     (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                                     ++ ce_ass (ptyp_ty p D (cargs_pat gs1) t)
                                          [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))] :: nil))
      by (rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; unfold s, i, j; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  rewrite <- Hpat in Hτ2; fold i in Hτ2; fold ρ in Hτ2.
  rewrite List.app_assoc in Hτ2; apply wf_sub_prefix in Hτ2; [| exact HΨ1 ].
  assert (Hθt : Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ˢ θ : cargs_strat gs1 ++ ind_params D).
  { rewrite Hθ; eapply wf_sub_compose; [| apply wf_sub_of_wk; exact Hw3 ].
    eapply wf_sub_compose; [ apply wf_sub_of_wk; exact Hφ | exact Hτ2 ]. }
  refine (conj Hb (conj Hθt (conj _ _))).
  - (* the uniform parameters *)
    intros x Hx; cbn [doms_ctx List.rev List.map List.app] in *.
    replace (x + (List.length (cargs_strat gs1 ++ ind_params D) - ind_nu D))
      with (pat_nargs pat + (ind_nn D + x))
      by (rewrite List.length_app; unfold pat; rewrite pat_nargs_cargs_pat; unfold ind_nn, ind_np in *; lia).
    rewrite Hθ; cbn [sb_compose sb_of_wk sentry_sub].
    rewrite wk_pat_ge; fold i; unfold ρ; rewrite sb_qn_ge by lia.
    replace (i + (ind_nn D + x) - (i + ind_nn D)) with x by lia.
    rewrite !sentry_sub_of_wk, sentry_wk_wk; f_equal; apply sentry_wk_wk_eq; intros z; cbn; unfold m, s; lia.
  - (* the recursive argument *)
    apply wf_vlookup; [ exact HΨ |].
    rewrite Heq in HΨ |- *; rewrite cinst_split, List.app_assoc.
    rewrite <- !List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
    set (L := tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))).
    assert (HL : List.length L = List.length gs2) by (unfold L; rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity).
    replace (j + na - 1 - i) with (0 + List.length (E ++ L)) by (rewrite List.length_app, HL; unfold j; lia).
    match goal with |- _ ∋ # _ : ?T =>
      replace T with ((ptyp_ty p D (cargs_pat gs1) t)
                        [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))][↑]ʷ[wk_shiftn (List.length (E ++ L))]ʷ)
    end.
    { apply ctx_lookup_app_r; constructor. }
    rewrite ptyp_ty_eq_at, ptyp_ty_at_sub, <- !exp_sub_of_wk, !ptyp_ty_at_sub, !List.map_map.
    fold pat.
    rewrite (ptyp_ty_at_sb_eq _ _ _ _ θ); [ f_equal |].
    + unfold ind_uvars.
      rewrite (List.map_ext _ (fun M => M[sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us)][ι wk_shiftn (S (List.length (E ++ L)))]))
        by (intros; rewrite !exp_sub_sub; apply exp_sub_sb_eq; intros z; cbn [sb_compose];
            rewrite <- !sentry_sub_sub, (sb_qn_add _ _ _ z), !sentry_sub_of_wk, sentry_wk_wk; apply sentry_wk_wk_eq; intros w; cbn; lia).
      rewrite <- (List.map_map (fun M => M[sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us)]) (fun M => M[ι wk_shiftn (S (List.length (E ++ L)))])).
      fold i; rewrite Hpat, <- HUl, vars_from_sb_qn, List.map_map.
      apply List.map_ext; intros U; rewrite !exp_sub_of_wk, !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn.
      rewrite List.length_app, HL; unfold m, j; lia.
    + rewrite Hθ; intros y; cbn [sb_compose].
      rewrite !sentry_sub_sub; apply sentry_sub_sb_eq; intros z; cbn [sb_compose].
      unfold ρ; rewrite <- (sb_qn_add _ _ _ z), Hpat.
      apply sentry_sub_sb_eq; intros w; cbn.
      rewrite List.length_app, HL; unfold s, j; f_equal; lia.
Qed.

(** What a declaration says of a shape, in the invariant's terms. *)
Lemma decl_shape_facts : forall Θ Ξ D c gs gs1 t gs2,
    decl_typed Θ Ξ D -> decl_closed D -> List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
    List.length (ptyp_ps t) = ind_nn D /\ shape_doms_typed Θ Ξ D nil (cargs_strat gs1) t /\
    shape_leaf_typed Θ Ξ D nil (cargs_strat gs1) t.
Proof.
  intros * HD Hc Hin Heq.
  pose proof HD as [_ _ _ _ _ _ _ _ HPl HP _ _ Hsh].
  split; [ exact (HPl _ _ _ _ _ Hin Heq) | split ].
  - intros Bs1' B Bs2 E; cbn [List.app].
    pose proof (proj2 (Hsh _ _ _ _ _ Hin Heq) _ _ _ E) as HB.
    pose proof (presup_exp_ctx HB) as HE.
    assert (HE' : ⊢ Θ ⍮ Ξ ⍮ (doms_ctx Bs1' ++ cargs_strat gs1 ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- !List.app_assoc, <- params_split; exact HE).
    destruct (sort_under _ _ _ _ HD HE') as (_ & [n Hn] & HSu).
    rewrite <- !List.app_assoc, <- params_split, !List.length_app, length_nparams, length_doms_ctx in Hn;
      rewrite !List.length_app, length_nparams, length_doms_ctx in HSu.
    rewrite Nat.add_assoc in Hn, HSu.
    exact (sort_large _ _ _ _ _ _ HSu Hn HB).
  - intros k P T HPk HT; exact (HP _ _ _ _ _ _ _ _ Hin Heq HPk HT).
Qed.

(** The type of the recursive result of a recursive argument, in a
    branch's context, is a type, and equal ones of equal motives. *)
Lemma rec_ih_typed : forall Θ Ξ Γ p D Us A A' i c gs gs1 t gs2 E,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A ≈ A' : Typeω@i ->
    List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ->
    let T X := ptyp_ihty X (ι (wk_shiftn (List.length E + List.length gs + ind_nn D)))
                 (ihs_sub D Us (List.length gs) (cargs_pat gs1) (List.length E))
                 (a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1))) t in
    exists j, Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ T A : Typeω@j /\ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ T A' : Typeω@j /\
      Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ⊢ T A ≈ T A' : Typeω@j.
Proof.
  intros * HD Hc Hl HΓ HUl Hσ HM HA HA' HAA Hin Heq HΨ T.
  destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ Hin Heq HΨ) as (Hb & Hθ & Huc & Hx).
  destruct (decl_shape_facts _ _ _ _ _ _ _ _ HD Hc Hin Heq) as (HPl & HBt & HPt).
  exact (ihty_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HM HA HA' HAA Hb Hθ Huc HPl HBt HPt Hx).
Qed.

Lemma cargs_nrec_snoc : forall gs g,
    cargs_nrec (gs ++ g :: nil) = cargs_nrec gs + match g with ca_rec _ => 1 | ca_arg _ => 0 end.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?IH; destruct g; reflexivity. Qed.

(** ** The Branches' Contexts *)

Lemma ihs_ctx_wf : forall Θ Ξ Γ p D Us A i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
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
  - destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM HA HA (wf_exp_eq_refl HA) Hin Heq HΨ)
      as (j & HAj & _).
    rewrite <- List.app_assoc; cbn [List.app].
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    match goal with |- ⊢ _ ⍮ _ ⍮ ?L ++ ?e :: E ++ _ => change (L ++ e :: E ++ cinst Γ p D Us gs) with (L ++ (e :: E) ++ cinst Γ p D Us gs) end.
    match goal with |- ⊢ _ ⍮ _ ⍮ ihs_ctx_aux _ _ _ _ _ ?n _ ++ (?e :: E) ++ _ =>
      replace n with (List.length (e :: E)) by reflexivity end.
    apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia |].
    cbn [List.app]; econstructor; exact HAj.
Qed.

Lemma elim_bctx_wf : forall Θ Ξ Γ p D Us A i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
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
  pose proof (shape_rest_wf' _ _ _ _ _ _ HD Hc Hl Hcon) as Hsh0.
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

Lemma ptyp_ty_mvc : forall p D t pat,
    List.Forall (exp_mvc 0) (ptyp_doms t) -> List.Forall (exp_mvc 0) (ptyp_ps t) -> exp_mvc 0 (ptyp_ty p D pat t).
Proof.
  intros p D t; induction t as [k Ps | k Ps | B t IH]; intros pat HB HP; cbn [ptyp_ty ptyp_doms ptyp_ps] in *.
  1, 2: apply exp_mvc_apps; split; [ exact I |]; apply List.Forall_app; split;
    [ unfold ind_uvars, vars_from; apply List.Forall_map, List.Forall_forall; intros; exact I
    | apply List.Forall_map; eapply List.Forall_impl; [| exact HP ]; intros; apply exp_mvc_wk; assumption ].
  inversion_clear HB as [| ? ? HB1 HB2]; cbn; split; [ apply exp_mvc_wk; exact HB1 |].
  eapply exp_mvc_mono; [| apply IH; assumption ]; lia.
Qed.

Lemma cargs_ctx_aux_mvc : forall p D gs pat, List.Forall carg_mvc gs -> ctx_mvc (cargs_ctx_aux p D pat gs).
Proof.
  induction gs as [| [A | Ps] gs IH]; intros pat Hg; cbn; [ constructor | |].
  all: inversion_clear Hg as [| ? ? Hg1 Hg2]; apply List.Forall_app; split; [ apply IH; exact Hg2 | constructor; [| constructor ] ]; cbn in *.
  - apply exp_mvc_wk; exact Hg1.
  - apply ptyp_ty_mvc; apply Hg1.
Qed.

Lemma cargs_ctx_mvc : forall Θ Ξ p D c gs,
    decl_typed Θ Ξ D -> List.In (c, gs) (ind_cons D) -> ctx_mvc (cargs_ctx p D gs).
Proof. intros * HD Hin; pose proof (dmv_cons _ (dt_mvc _ _ _ HD)) as Hmvc; apply cargs_ctx_aux_mvc; eauto. Qed.

Lemma wf_bty_sub : forall Θ Ξ Γ p D Us A i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T) ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    ind_con D c = Some gs ->
    Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ
      ⊢ˢ sb_of_list (ι (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)))
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
  assert (Hw : Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ʷ wk_shiftn n : Γ).
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> tele_ass Ψ -> Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ˢ Id : Ψ ++ Γ.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
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
    destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM HA HA' HAA Hin Heq HΨ)
      as (j & HAj & HA'j & HAAj).
    destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' HD Hc Hl HΓ HUl Hσ HM HA HA' HAA Hin Heq HΨ')
      as (j' & _ & HA'j' & _).
    rewrite HE', <- HE in HA'j'.
    rewrite cinst_ctel, List.app_assoc in HAj, HA'j, HAAj, HA'j'.
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    rewrite <- !List.app_assoc.
    eapply (IH (gs1 ++ ca_rec Ps :: nil) (_ :: E) (_ :: E'));
      [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
      | cbn; rewrite cargs_nrec_snoc, HE'; lia |].
    cbn [List.app]; eapply wf_ext_eq_ass with (i := max j j');
      [ exact HEE | eapply lift_exp_max_left; exact HAj | eapply lift_exp_eq_max_left; exact HAAj
      | eapply lift_exp_max_right; exact HA'j' ].
Qed.

Lemma elim_bctx_eq : forall Θ Ξ Γ p D Us A A' i c gs,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us : ind_uparams D ++ Γ ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list σ Ms : Δ ++ Γ0 ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (Ns ++ M :: nil) : elim_mctx p D Us ++ Γ ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ B : elim_bty p D c gs A Us) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim nm A Bs M : A[sb_of_list Id (Ns ++ M :: nil)].
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps)
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As) : cinst Γ p D (List.firstn (ind_nu D) Ps) gs.
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

(** ** The Recursive Results of [ι]

    An eliminator's premises move along a weakening. *)
Lemma elim_premises_wk : forall Θ Ξ Γ Ψ φ p D Us A i Bs,
    decl_closed D -> List.length Us = ind_nu D ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us ->
    (forall c gs, ind_con D c = Some gs -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ B : elim_bty p D c gs A Us) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.map (fun U => U[φ]ʷ) Us) ++ Ψ ⊢ A[wk_qn (S (ind_nn D)) φ]ʷ : Typeω@i /\
    Θ ⍮ Ξ ⍮ Ψ ⊢ˣ elim_mctx p D (List.map (fun U => U[φ]ʷ) Us) ≈ elim_mctx p D (List.map (fun U => U[φ]ʷ) Us) /\
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Ψ ⊢ˣ elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us)
                ≈ elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us)) /\
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_wk Bs φ) -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) /\
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_wk Bs φ) ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us) ++ Ψ
         ⊢ B : elim_bty p D c gs A[wk_qn (S (ind_nn D)) φ]ʷ (List.map (fun U => U[φ]ʷ) Us)).
Proof.
  intros * HD HUl Hφ HA HΨ HΨB Hk HB.
  pose proof (wk_preserves_ext _ _ _ _ _ _ _ HΨ Hφ) as HΨφ.
  split; [| split; [| split; [| split ] ] ].
  - exact (wk_preserves_exp _ _ _ _ _ _ _ HA (wk_elim_motive_ctx _ _ _ _ _ _ _ _ HD HUl Hφ HΨ HΨφ)).
  - rewrite <- elim_mctx_wk by assumption; exact HΨφ.
  - intros c gs Hc; rewrite <- (elim_bctx_wk p D c gs A _ φ HD (cons_lookup_in _ _ _ Hc) HUl).
    exact (wk_preserves_ext _ _ _ _ _ _ _ (HΨB c gs Hc) Hφ).
  - intros c gs n B' Hc Hin; unfold brs_wk in Hin; apply brs_in_map in Hin as (B & Hin & ->); eapply Hk; eassumption.
  - intros c gs n B' Hc Hin; unfold brs_wk in Hin; apply brs_in_map in Hin as (B & Hin & ->); cbn [fst snd].
    rewrite <- elim_bty_wk, (Hk _ _ _ _ Hc Hin).
    apply (wk_preserves_exp _ _ _ _ _ _ _ (HB c gs n B Hc Hin)).
    apply (wk_elim_branch_ctx _ _ _ _ _ _ _ c); eauto using cons_lookup_in, wk_preserves_ext.
Qed.

Lemma brs_wk_wk : forall Bs φ ψ, brs_wk (brs_wk Bs φ) ψ = brs_wk Bs (φ ⊙ ψ).
Proof.
  intros; unfold brs_wk; rewrite List.map_map; apply List.map_ext; intros [[c n] B]; cbn; f_equal.
  rewrite exp_wk_wk; apply exp_wk_wk_eq, wk_qn_compose.
Qed.

Lemma shape_uc_sb_eq : forall D Us Tc σ β β', sb_eq β β' -> shape_uc D Us Tc σ β -> shape_uc D Us Tc σ β'.
Proof. intros * Hβ H y Hy; rewrite H by exact Hy; cbn [sb_compose]; rewrite (sentry_sub_sb_eq _ _ _ Hβ); reflexivity. Qed.

Section IhTm.
  Context (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (D : ind_decl) (Us : list exp) (nm : nat) (A : exp) (i : nat)
    (Bs : list (String.string * nat * exp)).
  Hypothesis (HD : decl_typed Θ Ξ D) (Hc : decl_closed D) (Hl : ind_lookup Θ Ξ p = Some D) (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ)
    (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ U : T)
    (Hnm : nm = S (ind_nn D))
    (HA : Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ⊢ A : Typeω@i)
    (HΨ : Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us)
    (Hn : brs_names (ind_cons D) Bs)
    (HΨB : forall c gs, ind_con D c = Some gs -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us)
    (Hk : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat)
    (HB : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢ B : elim_bty p D c gs A Us).

  (** At the leaf: the eliminator, moved by [φ], at the argument. *)
  Lemma ih_tm_leaf : forall t Ψ φ Bs1 Tb σ M,
      ptyp_doms t = nil ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ ind_params D ->
      shape_uc D Us (doms_ctx Bs1 ++ Tb ++ ind_params D) σ (ι φ) ->
      List.length (ptyp_ps t) = ind_nn D -> shape_leaf_typed Θ Ξ D Bs1 Tb t ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ M : apps (a_ind p) (List.map (fun U => U[ι φ]) Us ++ List.map (fun P => P[σ]) (ptyp_ps t)) ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ a_elim nm A[wk_qn nm φ]ʷ (brs_wk Bs φ) M
        : A[sb_of_list (ι φ) (List.map (fun P => P[σ]) (ptyp_ps t) ++ M :: nil)].
  Proof.
    intros * Hd Hφ Hσ Huc HPl HPt HM; subst nm.
    pose proof (wf_wk_dom _ _ _ _ _ Hφ) as HΨ0.
    destruct (elim_premises_wk _ _ _ _ _ _ _ _ _ _ Bs Hc HUl Hφ HA HΨ HΨB Hk HB) as (HA' & HM' & HB' & Hk' & HBs').
    assert (HUl' : List.length (List.map (fun U => U[φ]ʷ) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
    assert (HMx : ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (List.map (fun U => U[φ]ʷ) Us) ++ Ψ) by (eapply presup_exp_ctx; exact HA').
    assert (Huc' : shape_uc D (List.map (fun U => U[φ]ʷ) Us) (doms_ctx Bs1 ++ Tb ++ ind_params D) σ Id).
    { intros y Hy; rewrite Huc by exact Hy; cbn [sb_compose].
      rewrite (sb_of_list_nth _ _ _ (a_var 0)), (sb_of_list_nth _ _ _ ((a_var 0)[φ]ʷ)) by (rewrite ?List.length_map; lia).
      cbn [sentry_sub sentry_exp]; rewrite List.length_map.
      change ((a_var 0)[φ]ʷ) with ((fun U => U[φ]ʷ) (a_var 0)); rewrite List.map_nth, exp_sub_id, exp_sub_of_wk; reflexivity. }
    assert (HUs' : forall k U T, List.nth_error (List.map (fun U => U[φ]ʷ) Us) k = Some U ->
                      List.nth_error (tele_insts (ind_uparams D) Id (List.map (fun U => U[φ]ʷ) Us)) k = Some T ->
                      Θ ⍮ Ξ ⍮ Ψ ⊢ U : T).
    { intros k U' T' HU' HT'.
      rewrite <- tele_insts_closed_wk in HT' by (first [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) ]).
      apply nth_error_map_inv in HU' as (U & HU & ->); apply nth_error_map_inv in HT' as (T & HT & ->).
      exact (wk_preserves_exp _ _ _ _ _ _ _ (HUs _ _ _ HU HT) Hφ). }
    rewrite (List.map_ext (fun U => U[ι φ]) (fun U => U[φ]ʷ[Id])) in HM by (intros; rewrite exp_sub_id, exp_sub_of_wk; reflexivity).
    rewrite <- (List.map_map (fun U => U[φ]ʷ) (fun U => U[Id])) in HM.
    pose proof (ih_leaf_sub _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl' HMx (wf_sub_id _ _ _ HΨ0) Hσ Huc' HPl
                  (shape_leaf_at _ _ _ _ _ _ Hc HPt Hd) HM) as Hτ.
    replace (A[sb_of_list (ι φ) (List.map (fun P => P[σ]) (ptyp_ps t) ++ M :: nil)])
      with (A[wk_qn (S (ind_nn D)) φ]ʷ[sb_of_list Id (List.map (fun P => P[σ]) (ptyp_ps t) ++ M :: nil)]).
    2:{ rewrite <- exp_sub_qn_of_wk.
        replace (S (ind_nn D)) with (List.length (List.map (fun P => P[σ]) (ptyp_ps t) ++ M :: nil))
          by (rewrite List.length_app, List.length_map; cbn; lia).
        apply exp_sub_qn_of_list. }
    eapply wf_elim_at_sub; [ exact Hl | exact HΨ0 | exact HUl' | exact HUs' | rewrite List.length_map; exact HPl | exact Hτ
                           | reflexivity | exact HA' | exact HM' | apply brs_names_map; exact Hn | exact HB' | exact Hk' | exact HBs' ].
  Qed.

  (** The recursive result of a shape, at an argument of its type: the
      eliminator's data, in [Γ], moved by [φ] into the current context. *)
  Lemma ih_tm_typed : forall t Ψ φ Bs1 Tb σ M,
      Θ ⍮ Ξ ⍮ Ψ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ ind_params D ->
      shape_uc D Us (doms_ctx Bs1 ++ Tb ++ ind_params D) σ (ι φ) ->
      List.length (ptyp_ps t) = ind_nn D ->
      shape_doms_typed Θ Ξ D Bs1 Tb t -> shape_leaf_typed Θ Ξ D Bs1 Tb t ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ M : ptyp_ty_at p (List.map (fun U => U[ι φ]) Us) σ t ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ ptyp_ih nm A[wk_qn nm φ]ʷ (brs_wk Bs φ) σ M t : ptyp_ihty A (ι φ) σ M t.
  Proof.
    induction t as [k0 Ps | k0 Ps | B t IH]; intros * Hφ Hσ Huc HPl HBt HPt HM; cbn [ptyp_ih ptyp_ihty ptyp_ty_at] in *.
    1, 2: eapply ih_tm_leaf; [ reflexivity | eassumption .. ].
    cbn [ptyp_ps] in HPl.
    destruct (HBt nil B (ptyp_doms t) eq_refl) as [j1 Hj1]; rewrite List.app_nil_r in Hj1.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσ) as Hj1'; cbn [exp_sub] in Hj1'.
    assert (HΨ' : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹ B[σ]) by (econstructor; exact Hj1').
    pose proof (wf_sub_q _ _ _ _ _ _ _ Hσ Hj1 Hj1') as Hσ'.
    replace ((doms_ctx Bs1 ++ Tb ++ ind_params D) ▹ B) with (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ ind_params D) in Hσ'
      by (rewrite doms_ctx_app_one; reflexivity).
    assert (Hφ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ʷ φ ⊙ ↑ : Γ) by (eapply wf_wk_compose; [ apply wf_wk_shift; exact HΨ' | exact Hφ ]).
    assert (Huc' : shape_uc D Us (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ ind_params D) (q σ) (ι (φ ⊙ ↑))).
    { rewrite doms_ctx_app_one; eapply shape_uc_sb_eq; [ symmetry; apply sb_of_wk_compose |].
      apply shape_uc_pi; [ exact (proj2 (length_shape_ctx D Bs1 Tb Hc)) | exact Huc ]. }
    pose proof (shape_doms_typed_pi _ _ _ _ _ _ _ HBt) as HBt'.
    pose proof (shape_leaf_typed_pi _ _ _ _ _ _ _ HPt) as HPt'.
    assert (HMx : ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ) by (eapply presup_exp_ctx; exact HA).
    assert (Hβ' : Θ ⍮ Ξ ⍮ Ψ ▹ B[σ] ⊢ˢ ι (φ ⊙ ↑) : Γ) by (apply wf_sub_of_wk; exact Hφ').
    destruct (ty_at_typed _ _ _ _ _ _ _ _ _ _ _ _ HD Hc Hl HUl HMx Hβ' Hσ' Huc' HPl HBt' HPt') as [j2 Hj2].
    assert (Hus : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[ι φ]) Us) = List.map (fun U => U[ι (φ ⊙ ↑)]) Us)
      by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- !exp_sub_of_wk, exp_sub_sub;
          apply exp_sub_sb_eq; symmetry; apply sb_of_wk_compose).
    rewrite Hus in HM.
    pose proof (shape_arg_app _ _ _ _ _ _ _ _ Hj1' Hj2 HM) as HM'.
    pose proof (IH _ _ _ _ _ _ Hφ' Hσ' Huc' HPl HBt' HPt' HM') as Hbody.
    rewrite <- brs_wk_wk in Hbody.
    rewrite <- (exp_wk_wk_eq A _ _ (wk_qn_compose nm φ ↑)), <- exp_wk_wk in Hbody.
    rewrite (ptyp_ihty_sb_eq _ _ (ι φ ⨟ ι ↑) (ι (φ ⊙ ↑)) _ _ _ (fun z => eq_refl) (fun z => eq_refl)).
    eapply wf_fn; [ exact Hj1' |].
    exact Hbody.
  Qed.
End IhTm.

(** A shift past [N] followed by a list ending in [N] is the list before. *)
Lemma sb_shift_of_list_app : forall M N σ,
    sb_eq (ι (wk_shiftn (List.length N)) ⨟ sb_of_list σ (M ++ N)) (sb_of_list σ M).
Proof.
  intros M N σ x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite sb_of_list_app, Nat.add_comm, sb_of_list_ge; reflexivity.
Qed.

(** [ι]'s substitution into a branch, after a shape's move: the shape's
    components instantiated by the parameters and the non-recursive
    arguments before. *)
Lemma ihs_sub_iota : forall D Ps As L (gs1 gs : list carg),
    decl_closed D -> List.length Ps = ind_np D -> List.length As = List.length gs ->
    List.length gs1 <= List.length gs ->
    sb_eq (ihs_sub D (List.firstn (ind_nu D) Ps) (List.length gs) (cargs_pat gs1) (List.length L)
             ⨟ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L))
          (cargs_sub (sb_of_list Id Ps) gs1 As).
Proof.
  intros * Hc HPl HAl Hg.
  pose proof (decl_closed_nu D Hc) as Hle.
  set (i := List.length gs1).
  assert (Hpi : List.length (cargs_pat gs1) = i) by apply length_cargs_pat.
  unfold ihs_sub; rewrite Hpi, !sb_compose_assoc.
  rewrite <- (List.firstn_skipn i As), <- !List.app_assoc, List.app_assoc.
  replace (List.length gs - i + List.length L) with (List.length (List.skipn i As ++ L))
    by (rewrite List.length_app, List.length_skipn; lia).
  rewrite sb_shift_of_list_app, List.firstn_skipn.
  replace (i + ind_nn D) with (List.length (List.skipn (ind_nu D) Ps ++ List.firstn i As))
    by (rewrite List.length_app, List.length_skipn, List.length_firstn; unfold ind_nn, ind_np in *; lia).
  rewrite sb_qn_of_list, (sb_of_list_cong _ _ _ (sb_compose_id_right _)), <- sb_of_list_app, List.app_assoc, List.firstn_skipn.
  rewrite sb_of_list_app, cargs_sub_pat by (rewrite List.length_firstn; lia).
  unfold i; rewrite cargs_sub_firstn; reflexivity.
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
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L) : E ++ cinst Γ p D (List.firstn (ind_nu D) Ps) gs ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ L ++
                     elim_ihs nm A Bs (cargs_sub (sb_of_list Id Ps) gs1 As) rest (List.skipn (List.length gs1) As))
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
    destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM HA HA (wf_exp_eq_refl HA) Hin Heq HΨ)
      as (j & HAj & _).
    destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ Hin Heq HΨ) as (Hb & Hθ & Huc & Hx).
    destruct (decl_shape_facts _ _ _ _ _ _ _ _ HD Hc Hin Heq) as (HPlt & HBt & HPt).
    set (θ := ihs_sub D Us (List.length gs) (cargs_pat gs1) (List.length E)) in *.
    set (δ := sb_of_list Id (Ns ++ As ++ L)) in *.
    set (b := List.length E + List.length gs + ind_nn D) in *.
    set (x := List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) in *.
    assert (Hθδ : sb_eq (θ ⨟ δ) σg)
      by (unfold θ, δ, σg; rewrite <- HL; apply ihs_sub_iota; [ exact Hc | exact HPl | exact HAl | rewrite Heq, List.length_app; lia ]).
    assert (Hbδ : sb_eq (ι (wk_shiftn b) ⨟ δ) Id).
    { intros z; unfold b, δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      replace (z + (List.length E + List.length gs + ind_nn D)) with (List.length (Ns ++ As ++ L) + z)
        by (rewrite !List.length_app, HNl, HAl, HL; lia).
      rewrite sb_of_list_ge; reflexivity. }
    assert (Hidx : (a_var x)[δ] = a).
    { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ, x.
      rewrite (sb_of_list_nth _ _ _ a) by (rewrite !List.length_app, HNl, HAl, HL, Heq, List.length_app, length_cargs_pat; cbn; lia).
      rewrite !List.length_app, HNl, HAl, HL, length_cargs_pat.
      replace (ind_nn D + (List.length gs + List.length E) - 1 - (List.length E + List.length gs - 1 - List.length gs1))
        with (ind_nn D + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
      cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl; replace (ind_nn D + List.length gs1 - ind_nn D) with (List.length gs1) by lia.
      rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact Ha. }
    (* the recursive result is of the instance of its type *)
    assert (Hσg : Θ ⍮ Ξ ⍮ Γ ⊢ˢ σg : doms_ctx nil ++ cargs_strat gs1 ++ ind_params D)
      by (rewrite <- Hθδ; eapply wf_sub_compose; [ exact Hθ | exact Hδ ]).
    assert (Hucg : shape_uc D Us (doms_ctx nil ++ cargs_strat gs1 ++ ind_params D) σg (ι wk_id)).
    { intros y Hy; rewrite <- (Hθδ (y + _)); cbn [sb_compose].
      rewrite <- sentry_exp_sub, (Huc y Hy), sentry_exp_sub; cbn [sb_compose].
      rewrite sentry_sub_sub; f_equal; apply sentry_sub_sb_eq.
      rewrite Hbδ; intros z; reflexivity. }
    assert (Ha' : Θ ⍮ Ξ ⍮ Γ ⊢ a : ptyp_ty_at p (List.map (fun U => U[ι wk_id]) Us) σg t).
    { rewrite <- Hidx; pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hx Hδ) as H.
      rewrite ptyp_ty_at_sub, List.map_map in H.
      rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ Hθδ) in H.
      replace (List.map (fun U => U[ι wk_id]) Us) with (List.map (fun U => U[ι wk_shiftn b][δ]) Us); [ exact H |].
      apply List.map_ext; intros U; rewrite !exp_sub_sub; apply exp_sub_sb_eq; rewrite Hbδ; intros z; reflexivity. }
    assert (Hih : Θ ⍮ Ξ ⍮ Γ ⊢ ptyp_ih nm A[wk_qn nm wk_id]ʷ (brs_wk Bs wk_id) σg a t : ptyp_ihty A (ι wk_id) σg a t)
      by (eapply ih_tm_typed; try eassumption; apply wf_wk_id; exact HΓ).
    rewrite (exp_wk_id_ext _ _ (wk_qn_id_ext _ _ (fun z => eq_refl))) in Hih.
    replace (brs_wk Bs wk_id) with Bs in Hih
      by (unfold brs_wk; symmetry; rewrite <- List.map_id; apply List.map_ext; intros [[c' n'] B']; cbn;
          f_equal; apply exp_wk_id_ext, wk_qn_id_ext; intros z; reflexivity).
    rewrite <- !List.app_assoc; cbn [List.app].
    replace (Ns ++ As ++ L ++ ptyp_ih nm A Bs σg a t :: elim_ihs nm A Bs σg rest (List.skipn (S (List.length gs1)) As))
      with (Ns ++ As ++ (L ++ ptyp_ih nm A Bs σg a t :: nil) ++ elim_ihs nm A Bs σg rest (List.skipn (S (List.length gs1)) As))
      by (rewrite <- !List.app_assoc; reflexivity).
    replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec t :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
    replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec t :: nil)) by (rewrite List.length_app; cbn; lia).
    rewrite <- Hcs.
    apply (IH (gs1 ++ ca_rec t :: nil) (_ :: E));
      [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
      | rewrite List.length_app; cbn; lia | cbn [List.app]; econstructor; exact HAj |].
    rewrite Hcs.
    replace (Ns ++ As ++ L ++ ptyp_ih nm A Bs σg a t :: nil) with ((Ns ++ As ++ L) ++ ptyp_ih nm A Bs σg a t :: nil)
      by (rewrite <- !List.app_assoc; reflexivity).
    rewrite (sb_of_list_app (Ns ++ As ++ L) (ptyp_ih nm A Bs σg a t :: nil) Id).
    change (sb_of_list (sb_of_list Id (Ns ++ As ++ L)) (ptyp_ih nm A Bs σg a t :: nil))
      with (sb_of_list Id (Ns ++ As ++ L) ,, ptyp_ih nm A Bs σg a t).
    eapply wf_sub_extend; [ exact Hδ | exact HAj |].
    fold δ; rewrite ptyp_ihty_sub, Hidx.
    rewrite (ptyp_ihty_sb_eq t A (ι wk_shiftn b ⨟ δ) (ι wk_id) (θ ⨟ δ) σg a); [ exact Hih | | exact Hθδ ].
    etransitivity; [ exact Hbδ | intros z; reflexivity ].
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs nm A Bs (sb_of_list Id Ps) gs As)
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) ≈ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M' :: nil)
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
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim nm A Bs M : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
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
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim nm A' Bs' M' : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
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
  assert (Hδ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil) : elim_mctx p D Us ++ Γ)
    by (apply wf_elim_inst_sub; assumption).
  assert (HE : Θ ⍮ Ξ ⍮ Γ ⊢ a_elim nm A' Bs' M' : A'[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M' :: nil)]).
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
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim nm A Bs (apps (a_con p c) (Ps ++ As))
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
    Θ ⍮ Ξ ⍮ Γ ⊢ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs nm A Bs (sb_of_list Id Ps) gs As)]
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
