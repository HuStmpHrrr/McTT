(** * The Filed Constructor Types of a Declaration

    A run of a declaration files constructor types that are equal to the
    ones the user wrote, with [Self] the type former at the frames'
    parameters ([rc_ind_con_types]).  An argument classified as written is
    filed as its own weakening ([cls_con_ty]); one classified as its normal
    form is equal to it by soundness, and the equality moves through the
    substitution of [Self] and the [Π]s over the arguments before it. *)

From Stdlib Require Import Lia List String PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import SystemOpt CtxSub IndCong.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System Require Import GlobalPresup IndTyping IndSyntax MemberLemmas Command.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Syntax *)

Lemma tele_wk_shift_sub_extend : forall Δ M, tele_sub (tele_wk Δ wk_shift) (Id ,, M) = Δ.
Proof.
  induction Δ as [| e Δ IH]; intros; cbn [tele_wk tele_sub]; [ reflexivity |].
  rewrite IH, length_tele_wk; f_equal.
  rewrite (centry_sub_wk_ext _ _ _ Id); [ apply centry_sub_id |].
  intros y; destruct (Nat.lt_ge_cases y (List.length Δ)) as [Hy | Hy].
  - rewrite wk_qn_lt, sb_qn_lt by exact Hy; reflexivity.
  - rewrite wk_qn_ge by exact Hy; rewrite sb_qn_ge by (cbn; lia).
    unfold wk_shift; replace (S (y - List.length Δ) + List.length Δ - List.length Δ) with (S (y - List.length Δ)) by lia.
    cbn; f_equal; lia.
Qed.

Lemma rtele_cons : forall y T args, rtele ((y, T) :: args) = rtele args ++ ce_ass T :: nil.
Proof. reflexivity. Qed.

Lemma length_rtele : forall args, List.length (rtele args) = List.length args.
Proof. intros; unfold rtele; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma rtele_app : forall args1 args2, rtele (args1 ++ args2) = rtele args2 ++ rtele args1.
Proof. intros; unfold rtele; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma cargs_ctx_aux_cons : forall p D pat g gs,
    cargs_ctx_aux p D pat (g :: gs) =
      cargs_ctx_aux p D (match g with ca_rec _ => true | ca_arg _ => false end :: pat) gs ++ cargs_ctx_aux p D pat (g :: nil).
Proof. intros; destruct g; reflexivity. Qed.

(** ** Typing *)

(** A [Π] over assumptions of equal bodies. *)
Lemma ctx_pi_ass_eq : forall Θ Ξ Δ Γ A A' i,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A ≈ A' : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A ≈ ctx_pi Δ A' : Typeω@j.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΔ HA; cbn in *; [ eauto |].
  inversion Hass as [| ? ? [B ->] Hass']; subst.
  destruct (ctx_decomp HΔ) as [HΔ' [k HB]].
  eapply IH with (i := max k i); [ exact Hass' | exact HΔ' |].
  eapply wf_exp_eq_pi_cong_large; [ eapply lift_exp_max_left; exact HB | apply wf_exp_eq_refl; eapply lift_exp_max_left; exact HB
                            | eapply lift_exp_eq_ge; [| exact HA ]; lia ].
Qed.

Section ConTypes.
  Variables (Θ : gdeps) (Ξ : gstack) (x : string) (pv : bool) (R : raw_decl) (cs : list (string * list carg)).

  #[local] Abbreviation D := (gs_ind Ξ (rd_filed R cs)).
  #[local] Abbreviation p := (ind_qname Ξ x).
  #[local] Abbreviation Ξf := (gs_add x (ge_ind pv (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) (gen_body (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)))) Ξ).
  #[local] Abbreviation np := (List.length (rd_params R)).
  #[local] Abbreviation t := (List.length (gs_tele Ξ)).
  #[local] Abbreviation σ0 := (Id ,, self_inst (ind_qname Ξ x) (List.length (gs_tele Ξ))).
  #[local] Abbreviation base := (tele_wk (rd_params R) wk_shift ++ ce_ass (rd_self_ty R) :: gs_tele Ξ).

  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis HΞf : ⊢ᵍ Θ ⍮ Ξf.
  Hypothesis Hemb : Emb Θ Ξ Θ Ξf.
  Hypothesis Hl : ind_lookup Θ Ξf p = Some D.
  Hypothesis HD : decl_typed Θ Ξf D.
  Hypothesis Hdc : decl_closed D.

  Lemma D_params : ind_params D = rd_params R ++ gs_tele Ξ.
  Proof. reflexivity. Qed.

  Lemma D_nu : ind_nu D = rd_nu R + t.
  Proof. reflexivity. Qed.

  Lemma D_np : ind_np D = np + t.
  Proof. unfold ind_np; cbn; apply List.length_app. Qed.

  Lemma D_le : rd_nu R <= np.
  Proof. pose proof (dt_nu _ _ _ HD) as Hle; rewrite D_nu, D_np in Hle; lia. Qed.

  Lemma D_nn : ind_nn D = np - rd_nu R.
  Proof. unfold ind_nn; rewrite D_nu, D_np; lia. Qed.

  (** The type former at the frames' parameters is of [Self]'s type. *)
  Lemma self_typed : Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ self_inst p t : rd_self_ty R.
  Proof.
    pose proof HD as [Hass [Hmv _ _] _ HP _ _ _ _ _ _ _ _ _].
    pose proof Hdc as [_ _ Hs HsS _ _ _].
    rewrite D_params in Hass, Hmv, HP, Hs.
    assert (HT : ⊢ Θ ⍮ Ξf ⍮ gs_tele Ξ) by exact (ctx_app_wf_tail _ _ _ _ HP).
    assert (Hassi : tele_ass (gs_tele Ξ)) by (unfold tele_ass in *; apply Forall_app in Hass as [_ H]; exact H).
    assert (Hsi : ctx_scoped 0 (gs_tele Ξ)) by (apply ctx_scoped_app in Hs as [_ H]; exact H).
    assert (Hmvi : ctx_mvc (gs_tele Ξ)) by (unfold ctx_mvc in *; apply Forall_app in Hmv as [_ H]; exact H).
    assert (Hind : Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ a_ind p : ctx_pi (gs_tele Ξ) (rd_self_ty R)).
    { replace (ctx_pi (gs_tele Ξ) (rd_self_ty R)) with (ind_ty D).
      - eapply wf_ind; eassumption.
      - unfold ind_ty, rd_self_ty; rewrite D_params, ctx_pi_app, D_nn; reflexivity. }
    destruct (ind_sort_shift_typed _ _ _ HD) as [i Hi].
    assert (Hsty : exists j, Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ rd_self_ty R : Typeω@j).
    { unfold rd_self_ty; rewrite D_nn in Hi; eapply ctx_pi_wf; [ exact HP | exact Hi ]. }
    destruct Hsty as [j Hj].
    assert (HsT : exp_scoped t (rd_self_ty R)).
    { apply ctx_scoped_app in Hs as [Hsp _].
      unfold rd_self_ty; apply ctx_pi_scoped; [ rewrite Nat.add_0_r in Hsp; exact Hsp |].
      eapply exp_scoped_wk; [ exact HsS |]; intros y Hy.
      rewrite D_nu in Hy; unfold wk_shiftn; pose proof D_le; lia. }
    assert (HmT : exp_mvc 0 (rd_self_ty R)).
    { pose proof (dmv_sort _ (dt_mvc _ _ _ HD)) as HmS.
      unfold ctx_mvc in Hmv; apply Forall_app in Hmv as [Hmp _].
      unfold rd_self_ty; apply ctx_pi_mvc; [ unfold tele_ass in Hass; apply Forall_app in Hass as [H _]; exact H | exact Hmp |].
      eapply exp_mvc_mono; [| apply exp_mvc_wk; exact HmS ]; lia. }
    assert (Heq : Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ apps (a_ind p) (vars_from 0 t) ≈ apps (a_ind p) (vars_from 0 t)
                    : (rd_self_ty R)[sb_of_list Id (vars_from 0 t)]).
    { eapply wf_exp_eq_apps_closed_pi; [ exact Hassi | exact Hsi | exact HsT | exact Hj | exact HT
                                       | apply wf_exp_eq_refl; exact Hind | apply length_vars_from | apply length_vars_from |].
      intros k N N' T HN HN' HTk; rewrite HN in HN'; injection HN' as <-.
      apply wf_exp_eq_refl.
      eapply (wf_vars_tele_closed _ _ nil); [ exact Hassi | exact Hsi | exact Hmvi | exact HT | exact HN | exact HTk ]. }
    assert (Hid : (rd_self_ty R)[sb_of_list Id (vars_from 0 t)] = rd_self_ty R).
    { rewrite <- (exp_sub_id (rd_self_ty R)) at 2.
      eapply exp_scoped_mvc_agree; [ exact HsT | exact HmT |].
      intros y Hy; rewrite sb_of_list_vars by exact Hy; reflexivity. }
    rewrite Hid in Heq.
    unfold self_inst; gen_presups; assumption.
  Qed.

  (** [Self] substituted, from the filed parameters into the parameters and
      [Self] of the context an argument is written in. *)
  Lemma base_sub : ⊢ Θ ⍮ Ξf ⍮ base -> Θ ⍮ Ξf ⍮ ind_params D ⊢ˢ sb_qn np σ0 : base.
  Proof.
    intros Hb.
    pose proof (dt_params _ _ _ HD) as HP.
    assert (HT : ⊢ Θ ⍮ Ξf ⍮ gs_tele Ξ) by (rewrite D_params in HP; exact (ctx_app_wf_tail _ _ _ _ HP)).
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ Hb)) as [_ [j Hj]].
    assert (Hσ0 : Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ˢ σ0 : ce_ass (rd_self_ty R) :: gs_tele Ξ).
    { eapply wf_sub_extend; [ apply wf_sub_id; exact HT | exact Hj | rewrite exp_sub_id; exact self_typed ]. }
    pose proof (wf_sub_ext _ _ (tele_wk (rd_params R) wk_shift) _ _ _ Hσ0) as H.
    rewrite tele_wk_shift_sub_extend, length_tele_wk in H.
    apply H; [ rewrite D_params in HP; exact HP | exact Hb ].
  Qed.

  (** The context of the arguments before, as written with [Self]
      substituted, and as filed. *)
  #[local] Abbreviation L args1 := (tele_sub (rtele args1) (sb_qn np σ0) ++ ind_params D).
  #[local] Abbreviation Rc gs1 := (cargs_ctx (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) gs1 ++ ind_params D).
  #[local] Abbreviation Res n := (apps (a_ind (ind_qname Ξ x)) (ind_pvars (gs_ind Ξ (rd_filed R cs)) n)).

  Lemma cls_args_in_length : forall args1 gs1 args gs, cls_args_in Θ Ξ R args1 gs1 args gs -> List.length gs = List.length args.
  Proof. induction 1; cbn; auto. Qed.

  Lemma conv_tail : forall args1 gs1 args gs2,
      cls_args_in Θ Ξ R args1 gs1 args gs2 ->
      List.length args1 = List.length gs1 ->
      forall c, In (c, gs1 ++ gs2) (ind_cons D) ->
      Θ ⍮ Ξf ⊢ L args1 ⊆ Rc gs1 ->
      exists j, Θ ⍮ Ξf ⍮ L args1
        ⊢ ctx_pi (tele_sub (rtele args) (sb_qn (List.length args1 + np) σ0)) (Res (List.length gs1 + List.length gs2))
        ≈ ctx_pi (cargs_ctx_aux p D (cargs_pat gs1) gs2) (Res (List.length gs1 + List.length gs2)) : Typeω@j.
  Proof.
    induction 1 as [args1 gs1 | args1 gs1 y T args g gs Hg Hgs IH]; intros Hlen c Hin Hsub.
    - (* no argument left: the result type *)
      rewrite List.app_nil_r in Hin.
      destruct (con_cod_typed _ _ _ _ _ _ HD Hdc Hl (cons_lookup_nodup _ _ _ (dt_nodup _ _ _ HD) Hin))
        as [j Hj].
      exists j; cbn [rtele tele_sub ctx_pi List.length cargs_ctx_aux List.rev List.map]; rewrite Nat.add_0_r.
      apply wf_exp_eq_refl.
      pose proof (ctx_sub_escape _ _ _ _ Hsub) as Hid.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj Hid) as H; rewrite !exp_sub_id in H; exact H.
    - (* an argument: equal at its type as written and as filed, then the
         rest *)
      assert (Hin' : In (c, (gs1 ++ g :: nil) ++ gs) (ind_cons D)) by (rewrite <- List.app_assoc; exact Hin).
      pose proof (dt_nodup _ _ _ HD) as Hnd.
      set (τ := sb_qn (List.length gs1 + np) σ0).
      (* the argument as classified, and its filed entry *)
      assert (HT' : exists T', cls_arg (rd_nu R) np gs1 T' g /\
                (T' = T \/ exists i, Θ ⍮ Ξ ⍮ rarg_ctx Ξ R args1 ⊢ T ≈ T' : Typeω@i)).
      { destruct Hg as [g Hc | i W g _ HTt HW Hc]; [ exists T; split; [ exact Hc | left; reflexivity ] |].
        exists (nf_to_exp W); split; [ exact Hc | right; exists i ].
        exact (@soundness_ty' (gc_mk Θ Ξ) _ _ _ _ HTt HW). }
      destruct HT' as (T' & Hc & HTT).
      assert (Hent : cargs_ctx_aux p D (cargs_pat gs1) (g :: nil) = ce_ass T'[τ] :: nil).
      { pose proof (cls_args_cargs_ctx p D t (rd_nu R) np gs1 ((y, T') :: nil) (g :: nil)
                      (cls_args_cons _ _ _ _ _ _ _ _ Hc (cls_args_nil _ _ _)) D_nu D_np D_le) as E.
        rewrite E; reflexivity. }
      destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hdc Hl Hin' (gs1 ++ g :: nil) gs eq_refl) as (HRk & _ & _).
      unfold cargs_ctx in HRk; rewrite cargs_ctx_aux_app, List.app_nil_r in HRk; fold (cargs_ctx p D gs1) in HRk.
      rewrite Hent in HRk; cbn [List.app] in HRk.
      destruct (ctx_decomp HRk) as [HRk0 [i1 HT'i]].
      pose proof (ctx_sub_escape _ _ _ _ Hsub) as Hid.
      assert (HT'L : Θ ⍮ Ξf ⍮ L args1 ⊢ T'[τ] : Typeω@i1)
        by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ HT'i Hid) as H; rewrite !exp_sub_id in H; exact H).
      (* the argument as written and as classified are equal, under [Self] substituted *)
      assert (HTe : exists i2, Θ ⍮ Ξf ⍮ L args1 ⊢ T[τ] ≈ T'[τ] : Typeω@i2).
      { destruct HTT as [-> | [i2 HTe]]; [ exists i1; apply wf_exp_eq_refl; exact HT'L |].
        exists i2.
        pose proof (proj1 (proj2 (proj2 (emb_preserves_wf _ _ _ _ Hemb))) _ _ _ _ HTe) as HTe'.
        pose proof (presup_exp_eq_ctx HTe') as Hraw.
        assert (Hb : ⊢ Θ ⍮ Ξf ⍮ base) by (exact (ctx_app_wf_tail _ _ _ _ Hraw)).
        pose proof (wf_sub_ext _ _ (rtele args1) _ _ _ (base_sub Hb) (ctx_sub_dom _ _ _ _ Hsub) Hraw) as Hτ.
        rewrite length_rtele, <- sb_qn_plus, Hlen in Hτ.
        exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HTe' Hτ). }
      destruct HTe as [i2 HTe].
      assert (HTL : Θ ⍮ Ξf ⍮ L args1 ⊢ T[τ] : Typeω@i2) by (gen_presups; assumption).
      set (m := max i1 i2).
      (* the context after it *)
      assert (Hsub' : Θ ⍮ Ξf ⊢ L (args1 ++ (y, T) :: nil) ⊆ Rc (gs1 ++ g :: nil)).
      { rewrite rtele_app, tele_sub_app; cbn [rtele List.map List.rev List.app tele_sub centry_sub List.length].
        rewrite length_rtele, <- sb_qn_plus, Hlen; fold τ.
        unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; fold (cargs_ctx p D gs1); rewrite Hent; cbn [List.app].
        cbn [snd Nat.add]; rewrite <- sb_qn_plus; fold τ.
        eapply ctx_sub_extend with (i := m);
          [ exact Hsub | eapply lift_exp_ge; [| exact HT'i ]; lia | eapply lift_exp_ge; [| exact HTL ]; lia
          | apply wf_subtyp_refl' with (i := i2); exact HTe ]. }
      destruct (IH ltac:(rewrite !List.length_app; cbn; lia) c Hin' Hsub') as [j Hj].
      exists (max m j).
      (* the sides as [Π]s *)
      rewrite rtele_cons, tele_sub_app; cbn [tele_sub centry_sub List.length]; rewrite ctx_pi_snoc.
      rewrite cargs_ctx_aux_cons, Hent, ctx_pi_app; cbn [ctx_pi].
      rewrite cargs_pat_snoc in Hj.
      replace (List.length args1 + np) with (List.length gs1 + np) by lia; fold τ.
      replace (List.length gs1 + List.length (g :: gs)) with (List.length (gs1 ++ g :: nil) + List.length gs)
        by (rewrite List.length_app; cbn; lia).
      cbn [sb_qn].
      replace (List.length (args1 ++ (y, T) :: nil) + np) with (1 + (List.length gs1 + np)) in Hj
        by (rewrite List.length_app, Hlen; cbn; lia).
      rewrite sb_qn_plus in Hj; fold τ in Hj.
      replace (List.length (gs1 ++ g :: nil) + List.length gs) with (List.length gs1 + S (List.length gs)) in Hj
        by (rewrite List.length_app; cbn; lia).
      eapply wf_exp_eq_pi_cong_large; [ eapply lift_exp_ge; [| exact HTL ]; lia | eapply lift_exp_eq_ge; [| exact HTe ]; lia |].
      rewrite rtele_app, tele_sub_app in Hj; cbn [rtele List.map List.rev List.app tele_sub centry_sub List.length snd Nat.add] in Hj.
      rewrite length_rtele, <- sb_qn_plus, Hlen in Hj; fold τ in Hj.
      cbn [Nat.add] in Hj; rewrite <- sb_qn_plus in Hj; fold τ in Hj.
      eapply lift_exp_eq_ge; [| exact Hj ]; lia.
  Qed.

End ConTypes.

(** A run of a declaration files constructor types equal to the ones as
    written, with [Self] the type former at the frames' parameters, in the
    global context the run makes: the declaration filed in its module. *)
Theorem rc_ind_con_types : forall load_path read to_core ch B Rb Θ Ξ x pv R B' Rb' Θ' Ξ',
    Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind x pv R ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> ⊢ᵍ Θ ⍮ Ξ ->
    forall c args, In (c, args) (rd_cons R) ->
    exists cs gs, cls_cons_in Θ Ξ R cs /\
      ind_con (gs_ind Ξ (rd_filed R cs)) c = Some gs /\
      Ξ' = gs_add x (ge_ind pv (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) (gen_body (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)))) Ξ /\
      exists i, Θ ⍮ Ξ' ⍮ ⋅
        ⊢ con_ty (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) gs
        ≈ user_con_ty (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) (List.length (rd_params R)) args
        : Typeω@i.
Proof.
  intros * Hr HΞ c args Hin; inversion Hr as [| | | | | | | ? ? ? ? ? ? ? ? cs Hcls Hfr HE | | | |]; subst.
  destruct (Forall2_in_left _ _ _ _ Hcls Hin) as ([c' gs] & Hin' & Heq & Hc); cbn [fst snd] in Heq, Hc; subst c'.
  set (D := gs_ind Ξ (rd_filed R cs)) in *; set (p := ind_qname Ξ x) in *.
  pose proof (add_ind_wf _ _ _ _ _ _ HΞ HE Hfr) as HΞf.
  assert (HΞn : Ξ <> nil) by (intros ->; exact Hfr).
  pose proof (ind_lookup_added Θ' Ξ x pv D (gen_body p D) HΞn) as Hl.
  change (qname_in (gs_path Ξ) x) with p in Hl.
  destruct (decl_of_lookup _ _ ⋅ _ _ ltac:(constructor; exact HΞf) Hl) as [HD Hdc].
  pose proof (dt_params _ _ _ HD) as HP; pose proof (dt_nodup _ _ _ HD) as Hnd.
  assert (Hcon : ind_con D c = Some gs) by (apply cons_lookup_nodup; [ exact Hnd | exact Hin' ]).
  assert (Hemb : Emb Θ' Ξ Θ' (gs_add x (ge_ind pv p D (gen_body p D)) Ξ)).
  { constructor; [ exact HΞf |].
    destruct Ξ as [| [mq [P [[] Φ | E0]]] Ξ0]; [ contradiction | | |].
    - exfalso; destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [Δ' Φ' [=] _] & _).
    - cbn [gs_fresh gu_mod] in Hfr; cbn [gs_add gu_params gu_mod]; apply gc_sub_grow; exact Hfr.
    - exfalso; destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [Δ' Φ' [=] _] & _). }
  exists cs, gs; split; [ exact Hcls | split; [ exact Hcon | split; [ reflexivity |] ] ].
  unfold con_ty, cargs_ctx, user_con_ty; rewrite ctx_pi_sub.
  assert (Ht : ind_np D - List.length (rd_params R) = List.length (gs_tele Ξ))
    by (unfold D, ind_np; cbn; rewrite List.length_app; lia).
  fold D; rewrite Ht.
  assert (Hlen : List.length gs = List.length args) by (eapply cls_args_in_length; exact Hc).
  assert (Eres : (apps_exp (a_var (List.length args + List.length (rd_params R)))
                    (vars_from (List.length args) (List.length (rd_params R))))
                   [sb_qn (List.length (rtele args)) (sb_qn (List.length (rd_params R)) (Id,,self_inst p (List.length (gs_tele Ξ))))]
                 = apps_exp (a_ind p) (ind_pvars D (List.length gs))).
  { rewrite length_rtele, <- sb_qn_plus, apps_exp_sub, var_self_sub, self_inst_wk, vars_from_sub_below by lia.
    rewrite <- apps_exp_app; unfold ind_pvars; rewrite Hlen.
    rewrite vars_from_app; unfold ind_np, D; cbn; rewrite List.length_app; do 2 f_equal; lia. }
  rewrite Eres.
  destruct (conv_tail Θ' Ξ x pv R cs Hemb Hl HD Hdc nil nil args gs Hc eq_refl c Hin'
              ltac:(cbn; apply ctx_sub_refl; exact HP)) as [j Hj].
  cbn [rtele tele_sub List.rev List.map List.app List.length cargs_pat] in Hj.
  rewrite Nat.add_0_l in Hj.
  assert (HP0 : ⊢ Θ' ⍮ gs_add x (ge_ind pv p D (gen_body p D)) Ξ ⍮ ind_params D ++ ⋅)
    by (rewrite List.app_nil_r; exact HP).
  pose proof (dt_ass _ _ _ HD) as Hass.
  destruct (ctx_pi_ass_eq _ _ _ ⋅ _ _ _ Hass HP0 ltac:(rewrite List.app_nil_r; exact Hj)) as [i Hi].
  exists i; apply wf_exp_eq_sym; exact Hi.
Qed.
