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

  Lemma wf_ext_eq_sym_ass : forall Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> tele_ass Ψ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ' ≈ Ψ.
  Proof.
    induction 1 as [| | |]; intros Hass.
    - constructor; assumption.
    - inversion_clear Hass as [| ? ? _ Hass'].
      pose proof (ctxsub_ext _ _ _ _ _ H Hass') as HId.
      eapply wf_ext_eq_ass; [ exact (IHwf_ext_eq Hass') | eassumption | | eassumption ].
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H1 HId) as H'.
      rewrite !exp_sub_id in H'; cbn in H'; symmetry; exact H'.
    - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
    - inversion_clear Hass as [| ? ? [? Heq] _]; discriminate.
  Qed.

  Lemma sb_qn_eq_ext : forall Ψ Δ Γ σ σ', tele_ass Ψ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Δ -> Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
      Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ ⊢s sb_qn (List.length Ψ) σ ≈ sb_qn (List.length Ψ) σ' : Ψ ++ Δ.
  Proof.
    intros * Hass HΨ Hσ.
    exact (proj1 (proj2 (proj2 (proj2 sub_eq_preserves_mut))) _ _ _ _ _ (ctx_ext_refl _ _ _ _ Hass HΨ) Hass _ _ _ Hσ).
  Qed.

  Lemma tele_sub_eq_ext : forall Ψ Δ Γ σ σ', tele_ass Ψ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Δ -> Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ σ'.
  Proof.
    induction Ψ as [| e Ψ IH]; intros * Hass HΨ Hσ.
    - cbn; constructor; gen_presups; assumption.
    - inversion Hass as [| ? ? [A ->] Hass']; subst.
      cbn [List.app] in HΨ; destruct (ctx_decomp HΨ) as [HΨ' [j HA]].
      assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ : Δ) by (gen_presups; mauto 2).
      assert (Hσσ' : Θ ⍮ Ξ ⍮ Γ ⊢s σ' ≈ σ' : Δ) by (gen_presups; mauto 2).
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσ) as Hq.
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσσ) as Hq1.
      pose proof (sb_qn_eq_ext _ _ _ _ _ Hass' HΨ' Hσσ') as Hq2.
      assert (Hs1 : Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ ⊢s sb_qn (List.length Ψ) σ : Ψ ++ Δ) by (gen_presups; assumption).
      assert (Hs2 : Θ ⍮ Ξ ⍮ tele_sub Ψ σ' ++ Γ ⊢s sb_qn (List.length Ψ) σ' : Ψ ++ Δ) by (gen_presups; assumption).
      cbn [tele_sub centry_sub].
      eapply wf_ext_eq_ass; [ exact (IH _ _ _ _ Hass' HΨ' Hσ) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hs1)
                            | exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HA Hq) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hs2) ].
  Qed.

  (** ** The Motive's Context *)

  Lemma uparams_ctx_wf : forall Γ D, decl_typed Θ Ξ D -> decl_closed D -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ.
  Proof.
    intros * HD Hc HΓ.
    pose proof HD as (_ & _ & _ & HΔ & _); rewrite params_split in HΔ.
    apply wf_ctx_closed_app; [ exact (decl_uparams_ass D Hc) | exact (decl_uparams_closed D Hc) | eapply ctx_app_wf_tail; exact HΔ | exact HΓ ].
  Qed.

  Lemma uvars_typed : forall Γ D, decl_typed Θ Ξ D -> decl_closed D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      forall k U T, List.nth_error (vars_from 0 (ind_nu D)) k = Some U ->
        List.nth_error (tele_insts (ind_uparams D) Id (vars_from 0 (ind_nu D))) k = Some T ->
        Θ ⍮ Ξ ⍮ ind_uparams D ++ Γ ⊢ U : T.
  Proof.
    intros * HD Hc HΓ k U T HU HT.
    pose proof HD as (_ & (Hmv & _) & _).
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
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us'.
  Proof.
    intros * HD Hc Hl HΓ HUl HUl' Hσ.
    rewrite (elim_mctx_canon p D Us Hc HUl), (elim_mctx_canon p D Us' Hc HUl').
    eapply tele_sub_eq_ext; [ apply elim_mctx_ass, Hc | exact (elim_mctx_canon_wf _ _ _ HD Hc Hl HΓ) | exact Hσ ].
  Qed.

  (** ** The Recursive Results' Instances *)

Lemma wf_ih_sub_eq : forall Γ p D Us Us' c gs gs1 Ps gs2 E,
    decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D Us ++ Γ ->
    List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
    ⊢ Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs ->
    Θ ⍮ Ξ ⍮ E ++ cinst Γ p D Us gs
      ⊢s sb_of_list (ι (wk_shiftn (List.length E + List.length gs + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                 [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)
            ++ a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)
      ≈ sb_of_list (ι (wk_shiftn (List.length E + List.length gs + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us')]
                                 [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)
            ++ a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)
      : elim_mctx p D Us ++ Γ.
Proof.
  intros * HD Hc Hl HΓ HUl HUl' Hσ Hσσ HM Hin Heq HΨ.
  pose proof HD as (Hass & (Hmv & Hmvs & Hmvc) & Hle & HΔ & HS & _ & _ & HA & HPl & HP & _).
  specialize (HPl _ _ _ _ _ Hin Heq).
  set (pat := cargs_pat gs1) in *.
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  set (i := List.length pat) in *.
  set (j := List.length E) in *.
  set (na := List.length gs) in *.
  assert (Hna : na = i + S (List.length gs2)) by (unfold na, i; rewrite Heq, List.length_app; cbn; lia).
  set (m := j + na + ind_nn D).
  set (s := na - i + j).
  set (ρ := sb_qn (i + ind_nn D) (sb_of_list Id Us)).
  set (ρ' := sb_qn (i + ind_nn D) (sb_of_list Id Us')).
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
  destruct (wf_sub_cinst _ _ _ _ _ _ HD Hc Hl HΓ Hσ c gs gs1 (ca_rec Ps :: gs2) Hin Heq) as (Hi1 & Hτ2).
  destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs1 (ca_rec Ps :: gs2) Heq) as (HΨ1 & _ & Hφ).
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
  assert (Hτ2e : Θ ⍮ Ξ ⍮ cinst Γ p D Us gs1 ⊢s ρ ≈ ρ' : cargs_ctx p D gs1 ++ ind_params D ++ Γ).
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
  apply wf_sub_eq_of_list; [ apply elim_mctx_ass, Hc | exact HM | apply wf_sub_eq_refl; exact Hb
                           | rewrite List.length_app, List.length_map, length_elim_mctx, HPl; cbn; lia
                           | rewrite List.length_app, List.length_map, length_elim_mctx, HPl; cbn; lia |].
  intros k N N' T HN HN' HT.
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
    rewrite List.nth_error_app1 in HN' by (rewrite List.length_map; lia).
    apply nth_error_map_inv in HN as (P & HPk & ->).
    apply nth_error_map_inv in HN' as (P1 & HPk1 & ->); rewrite HPk in HPk1; injection HPk1 as <-.
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
    pose proof (proj1 sub_eq_preserves_mut _ _ _ _ _ HP2 _ _ _ Hτ2e) as HP3.
    pose proof (wk_preserves_exp_eq _ _ _ _ _ _ _ _ HP3 Hw3) as HP4.
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
    rewrite List.nth_error_app2 in HN' by (rewrite List.length_map; lia); rewrite List.length_map, HPl in HN'.
    destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HN', HT; [| destruct k'; discriminate ].
    injection HN as <-; injection HN' as <-; apply wf_exp_eq_refl; unfold tele_insts in HT; cbn in HT; injection HT as <-.
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


  Lemma ihs_ctx_us_eq : forall Γ p D Us Us' A i c gs,
      decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
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
      pose proof (wf_ih_sub _ _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl Hσ HM Hin Heq HΨ) as Hj.
      pose proof (wf_ih_sub _ _ _ _ _ _ _ _ _ _ _ E' HD Hc Hl HΓ HUl' Hσ' HM' Hin Heq HΨ') as Hj'.
      pose proof (wf_ih_sub_eq _ _ _ _ _ _ _ _ _ _ E HD Hc Hl HΓ HUl HUl' Hσ Hσσ HM Hin Heq HΨ) as Hjj.
      rewrite HE', <- HE in Hj'.
      rewrite cinst_ctel, List.app_assoc in Hj, Hj', Hjj.
      replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
      rewrite <- !List.app_assoc.
      eapply (IH (gs1 ++ ca_rec Ps :: nil) (_ :: E) (_ :: E'));
        [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
        | cbn; rewrite cargs_nrec_snoc, HE'; lia |].
      cbn [List.app]; eapply wf_ext_eq_ass;
        [ exact HEE | exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hj)
        | exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HA Hjj) | exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hj') ].
  Qed.

  (** ** The Branches' Contexts *)

  Lemma elim_bctx_us_eq : forall Γ p D Us Us' A i c gs,
      decl_typed Θ Ξ D -> decl_closed D -> ind_lookup Θ Ξ p = Some D -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Us = ind_nu D -> List.length Us' = ind_nu D ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us' : ind_uparams D ++ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ ->
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
      ⊢s sb_of_list (ι (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)))
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
  assert (Hw : Θ ⍮ Ξ ⍮ elim_bctx p D gs A Us ++ Γ ⊢w wk_shiftn n : Γ).
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
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [(_ & _ & _ & _ & Hsu & _) _].
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
    assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ).
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
      assert (Hδδ : Θ ⍮ Ξ ⍮ Γ ⊢s sb_of_list Id (List.skipn (ind_nu D) Ps) ≈ sb_of_list Id (List.skipn (ind_nu D) Ps')
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
