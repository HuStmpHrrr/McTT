From Stdlib Require Import Nat PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Semantic Require Import RecordPER.
From Mctt.Core.Syntactic.System Require Import Records.Typing.
From Mctt.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations Wk_Notations Fixed_Notations.

Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A Kripke weakening is [⇑^n] on the nose ([kripke_shiftn]), so it acts on
    a variable by index arithmetic alone. *)
Lemma wk_var_kripke : forall Γ Δ φ x,
    Δ ⊢ᵏ φ : Γ ->
    φ x = x + (length Δ - length Γ).
Proof.
  intros * H%kripke_shiftn; destruct H as [_ Hφ].
  now rewrite (Hφ x).
Qed.

(** The instance the gluing model needs: the canonical variable of an extended
    context reads back as the de Bruijn index counting down from the length of
    the context the weakening lands in. *)
Corollary wk_var0_kripke : forall Γ A Δ φ,
    Δ ⊢ᵏ φ : Γ ▹ A ->
    φ 0 = length Δ - length Γ - 1.
Proof. intros * H; pose proof (wk_var_kripke _ _ _ 0 H); simpl in *; lia. Qed.

Lemma var_glu_elem_bot : forall a i P El Γ A,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A[↑]ʷ ® #ᵈ (length Γ) ∈ glu_elem_bot i a.
Proof.
  intros. saturate_glu_info.
  (** The ambient universe of the index is the large universe [Typeω@(ulvl i)],
      at which the syntactic rules apply directly. *)
  econstructor; mauto 4.
  - eapply glu_univ_elem_typ_monotone; eauto.
    mauto 4.
  - intros. progressive_inversion.
    assert (φ 0 = length Δ - length Γ - 1) as <- by (eapply wk_var0_kripke; eassumption).
    change #(φ 0) with #0[φ]ʷ.
    mauto 5.
Qed.



(** The arguments of a constructor read back position by position. *)
Lemma read_cargs_nth : forall s p ups ρ gs vs Vs, Rcargs vs at gs of p ups in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Vs ->
    List.length (List.map nf_to_exp Vs) = List.length gs /\
    (forall gs1 A gs2 v, gs = gs1 ++ ca_arg A :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
       exists a (V : nf), ⟦ A ⟧ env_args ρ (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
         Rnf ⇓ a v in s ↘ V /\ List.nth_error (List.map nf_to_exp Vs) (List.length gs1) = Some (V : exp)) /\
    (forall gs1 Pr gs2 v, gs = gs1 ++ ca_rec Pr :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
       exists (V : nf), Rsh v at Pr of p ups in gc_deps ⍮ gc_stack ⍮
                          env_args ρ (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ⍮ s ↘ V /\
         List.nth_error (List.map nf_to_exp Vs) (List.length gs1) = Some (V : exp)).
Proof.
  induction 1.
  - split; [ reflexivity | split; intros [] *; discriminate ].
  - destruct IHread_cargs as (IHl & IHa & IHr).
    split; [ cbn; congruence | split ].
    + intros [| g gs1] A0 gs2 v0 Heq Hv; cbn in Heq, Hv.
      * injection Heq as <- <-; injection Hv as <-; exists a, V; repeat split; assumption.
      * injection Heq as <- Heq; destruct (IHa _ _ _ _ Heq Hv) as (a0 & V0 & E0 & R0 & N0).
        exists a0, V0; repeat split; assumption.
    + intros [| g gs1] Pr gs2 v0 Heq Hv; cbn in Heq, Hv; [ discriminate |].
      injection Heq as <- Heq; destruct (IHr _ _ _ _ Heq Hv) as (V0 & R0 & N0).
      exists V0; split; assumption.
  - destruct IHread_cargs as (IHl & IHa & IHr).
    split; [ cbn; congruence | split ].
    + intros [| g gs1] A0 gs2 v0 Heq Hv; cbn in Heq, Hv; [ discriminate |].
      injection Heq as <- Heq; destruct (IHa _ _ _ _ Heq Hv) as (a0 & V0 & E0 & R0 & N0).
      exists a0, V0; repeat split; assumption.
    + intros [| g gs1] Pr gs2 v0 Heq Hv; cbn in Heq, Hv.
      * injection Heq as <- <-; injection Hv as <-; exists V; split; [ cbn; assumption | reflexivity ].
      * injection Heq as <- Heq; destruct (IHr _ _ _ _ Heq Hv) as (V0 & R0 & N0).
        exists V0; split; assumption.
Qed.

(** A constructor of a member of a group, at the type of the member: read
    at the member's own telescopes, at a declared member and at a view
    alike ([read_nf_con], [read_nf_con_view]). *)
Lemma read_nf_con_member_inv : forall s p D k Mk hd k' c gs bs vs as' w,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_ref p k Mk = (hd, k') ->
    ind_con Mk c = Some gs -> List.length bs = (im_unu D Mk + im_nn Mk)%nat -> List.length vs = List.length gs ->
    Rnf ⇓ (d_ind p k as') (d_con hd k' c (bs ++ vs)) in gc_deps ⍮ gc_stack ⍮ s ↘ w ->
    forall (Q : nf -> Prop),
      (forall PN Args, Rps as' at List.rev (im_params D Mk) in gc_deps ⍮ gc_stack ⍮ nil ⍮ s ↘ PN ->
         Rcargs vs at gs of p (List.firstn (ind_nu D) as') in gc_deps ⍮ gc_stack ⍮ env_args nil as' ⍮ s ↘ Args ->
         Q (nf_con p k c (PN ++ Args))) ->
      Q w.
Proof.
  intros * Hl HM Href Hc Hbl Hvl Hw Q HQ.
  unfold im_ref in Href.
  inversion Hw; subst;
    match goal with H : ind_lookup _ _ ?qn = Some ?D1, H' : ind_lookup _ _ ?qn = Some ?D2 |- _ =>
      assert_fails (unify D1 D2); rewrite H in H'; injection H' as <- end;
    match goal with H : ind_member ?D0 ?k0 = Some ?M1, H' : ind_member ?D0 ?k0 = Some ?M2 |- _ =>
      assert_fails (unify M1 M2); rewrite H in H'; injection H' as <- end;
    match goal with H : ind_con ?M0 ?c0 = Some ?g1, H' : ind_con ?M0 ?c0 = Some ?g2 |- _ =>
      assert_fails (unify g1 g2); rewrite H in H'; injection H' as <- end.
  - (** A declared member: its stored uniform parameters are the group's. *)
    match goal with H : im_head _ = mh_decl _ |- _ => rename H into Hh end.
    apply HQ; [ assumption |].
    assert (Hu0 : im_unu D Mk = ind_nu D) by (unfold im_unu; rewrite Hh; reflexivity).
    match goal with H : Rcargs List.skipn _ _ at _ of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      rewrite skipn_app_exact in H by (unfold im_np; lia); exact H end.
  - (** A view: the container's, at the view's own telescopes. *)
    apply HQ; [ assumption |].
    match goal with
    | H : List.length (bs ++ vs) = (?n + List.length gs)%nat,
      H' : Rcargs List.skipn ?n _ at _ of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
        rewrite List.length_app in H; rewrite skipn_app_exact in H' by lia; exact H'
    end.
Qed.

(** A constructor of any member of a group applied to equal parameters and
    arguments: [wf_exp_eq_con_apps], at a view too. *)
Lemma wf_exp_eq_con_apps_member : forall Γ p D k Mk c gs Ps Ps' As As',
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs -> ⊢ Γ ->
    List.length Ps = im_np D Mk -> List.length Ps' = im_np D Mk ->
    (forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error Ps' j = Some P' ->
       List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T -> Γ ⊢ P ≈ P' : T) ->
    List.length As = List.length gs -> List.length As' = List.length gs ->
    (forall j N N' T, List.nth_error As j = Some N -> List.nth_error As' j = Some N' ->
       List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Ps) As) j = Some T -> Γ ⊢ N ≈ N' : T) ->
    Γ ⊢ apps (a_con p k c) (Ps ++ As) ≈ apps (a_con p k c) (Ps' ++ As')
      : ind_mty p D k (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps).
Proof.
  intros * Hl Hk Hcon HΓ HPl HPl' HPs HAl HAl' HAs.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (con_cod_typed _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j Hj].
  destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j0 Hj0].
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ0 & _ & _).
  assert (HC : Γ ⊢ a_con p k c : con_ty p D k Mk gs) by (eapply wf_con_of_lookup; eassumption).
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


(** ** Inductive Types *)

(** The codomain of the type of an argument of a function shape, at an
    argument, is the type of the rest of the shape. *)
Lemma eval_fam_cod_shfam_inv : forall p ups ρ t x a,
    ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ t ↦ x ↘ a -> ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ↘ a.
Proof.
  intros * H; unfold fam_cod in H; inversion H; subst.
  match goal with H1 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
  match goal with H0 : ⟦ #0 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H0; subst end.
  match goal with Ha : $| _ & _ | _ ⍮ _ ↘ _ |- _ => cbn in Ha; inversion Ha; subst; assumption end.
Qed.

Lemma glu_params_top_refl : forall Dh Mh Δ Ps as', glu_params_top Dh Mh Δ Ps as' -> exps_eq_at Δ (im_params Dh Mh) Ps Ps.
Proof.
  intros * [_ Ht _]; split; [ reflexivity |].
  intros k X Y A HX HY HA; rewrite HX in HY; injection HY as <-.
  apply wf_exp_eq_refl; eapply Ht; eassumption.
Qed.

Lemma map_wk_id_exp : forall Ps, List.map (fun P => P[wk_id]ʷ) Ps = Ps.
Proof. intros; rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; reflexivity. Qed.

Section IndRealize.
  Variables (i : uidx) (p : qname) (D : ind_decl) (k : nat) (Mk : imember) (pm : qname) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
    (elem_rel : relation domain) (P : glu_typ_pred) (El : glu_exp_pred).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hu : List.length ups = ind_nu D)
    (Hass : grp_tele_ass D) (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_decl pm)
    (Hper : DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel)
    (HP : P <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@(ulvl i))
    (HEl : El <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk elem_rel Typeω@(ulvl i)).

  Lemma ind_realize_typ : forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® glu_typ_top i (d_ind p k (ups ++ ns)).
  Proof.
    intros Γ A HA; apply HP in HA; destruct HA as (Ps & HAPs & Hk).
    econstructor; [ gen_presups; assumption | exact (per_univ_then_per_top_typ Hper) |].
    intros Δ φ A' Hφ Hr.
    inversion Hr; subst.
    match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
    match goal with H : ind_member D k = Some ?M1 |- _ => assert (M1 = Mk) as -> by congruence end.
    destruct (Hk Δ φ Hφ) as ([HPl HPt HPr] & Hs & _).
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ms |- _ => pose proof (HPr Δ wk_id Ms Hid H) as HMs end.
    rewrite map_wk_id_exp in HMs.
    destruct HMs as [HMl HMs].
    cbn [nf_to_exp]; transitivity (apps (a_ind p k) (List.map (fun P => P[φ]ʷ) Ps)); [ rewrite <- wk_apps_ind; mauto 3 |].
    eapply wf_exp_eq_subtyp'; [| exact Hs ].
    eapply wf_exp_eq_ind_apps; [ exact Hl | exact HMk | exact (decl_member_lt _ _ _ _ _ _ HΔ Hl HMk Hh) | exact HΔ
                               | exact HPl | lia | exact HMs ].
  Qed.

  Lemma ind_realize_bot : forall Γ M A m,
      DG d_ind p k (ups ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
      Γ ⊢ M : A ® m ∈ glu_elem_bot i (d_ind p k (ups ++ ns)) ->
      Γ ⊢ M : A ® ⇑ (d_ind p k (ups ++ ns)) m ∈ El.
  Proof.
    intros * Hglu [P' El' HM Hglu' HAP' Hm Hrb].
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
    assert (HA : Γ ⊢ A ® P) by (apply HPP; exact HAP').
    apply HEl; pose proof HA as HA'; apply HP in HA'; destruct HA' as (Ps & HPs).
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Ps HPs _); [ eapply per_bot_then_per_elem; eassumption |].
    intros Δ φ Ps' Hφ HPs'.
    pose proof (ind_typ_at_params_conv p D ups ns NP NEl AP AEl DP DEl k Mk pm _ Γ A Ps Δ φ Ps' Hl HMk Hh HPs Hφ HPs') as HPeq.
    destruct HPs as [HAPs _].
    eapply ind_glu_elem_neut; [ exact HMk | unfold im_ref; rewrite Hh; reflexivity | exact Hm |].
    intros Θ ψ M' Hψ Hr.
    pose proof (kripke_compose _ _ _ _ _ Hψ Hφ) as Hc.
    rewrite exp_wk_wk, (im_ty_at_decl _ _ _ _ _ _ Hh), List.firstn_skipn.
    eapply wf_exp_eq_conv'; [ exact (Hrb _ _ _ Hc Hr) |].
    transitivity ((apps (a_ind p k) (List.map (fun P => P[φ]ʷ) Ps))[ψ]ʷ); [| mauto 3 ].
    rewrite wk_apps_ind, map_wk_wk, <- wk_apps_ind; mauto 3.
  Qed.

  Hypothesis
    (HeA : forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b)
    (HgA : forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem i ↘ AP m ms c j vs ↘ AEl m ms c j vs)
    (HtA : forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       forall Γ M A' n R, DG b ∈ glu_univ_elem i ↘ AP m ms c j vs ↘ AEl m ms c j vs ->
         Γ ⊢ M : A' ® n ∈ AEl m ms c j vs -> DF b ≈ b ∈ per_univ_elem i ↘ R -> Dom n ≈ n ∈ R ->
         Γ ⊢ M : A' ® n ∈ glu_elem_top i b)
    (HeD : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
       exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b)
    (HgD : forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
       ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
       DG b ∈ glu_univ_elem i ↘ DP m (ms ++ ws ++ ys) B ↘ DEl m (ms ++ ws ++ ys) B)
    (HrD : forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
       ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
       (forall Γ A R, DF b ≈ b ∈ per_univ_elem i ↘ R -> Γ ⊢ A ® DP m (ms ++ ws ++ ys) B -> Γ ⊢ A ® glu_typ_top i b) /\
       (forall Γ M A n, Γ ⊢ M : A ® n ∈ glu_elem_bot i b -> Γ ⊢ M : A ® ⇑ b n ∈ DEl m (ms ++ ws ++ ys) B)).

  (** The readback of an element of any member of the group, a view too,
      at the type's parameters [ns'] (the element is related at its own):
      a constructor at the member's own telescopes, a recursive argument
      by its shape, read at the type's prefix [xs], the element's own
      prefix [ms] related to it. *)
  Lemma ind_glu_elem_readback :
      forall k' Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k' Γ Us Ns M m -> ⊢ Γ ->
      forall Mk' ns', ind_member D k' = Some Mk' -> glu_params_top D Mk' Γ (Us ++ Ns) (ups ++ ns') ->
      ind_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups)
        (canon_doms_rel ups) k' ups ups ns' ns' m m ->
      forall (w : nf), Rnf ⇓ (d_ind p k' (ups ++ ns')) m in length Γ ↘ w -> Γ ⊢ M ≈ w : im_ty_at p k' Mk' Us Ns.
  Proof.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as [_ _ Hcp _ _ Hcd _ _].
    destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as (HevN & HevAr & HevD).
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    set (nr := canon_nparams_rel D ups) in *; set (ar := canon_args_rel D ups) in *; set (dr := canon_doms_rel ups) in *.
    pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
    pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
    pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Hidx.
    apply (ind_glu_elem_mut_ind p D ups NEl AEl DP DEl
             (fun k' Γ Us Ns M m _ => ⊢ Γ -> forall Mk' ns', ind_member D k' = Some Mk' ->
                glu_params_top D Mk' Γ (Us ++ Ns) (ups ++ ns') ->
                ind_rel p D (okr_at D ups nr) nr ar dr k' ups ups ns' ns' m m ->
                forall (w : nf), Rnf ⇓ (d_ind p k' (ups ++ ns')) m in length Γ ↘ w -> Γ ⊢ M ≈ w : im_ty_at p k' Mk' Us Ns)
             (fun k' Γ Us pre t A N v _ => ⊢ Γ -> Γ ⊢ N : A -> (exists σ', A = ptyp_ty_at p D Us σ' t) ->
                forall Mk' xs ms c0 gs1 t0 gs2 ws kk ys, ind_member D k' = Some Mk' -> pre = ms ++ ws ++ ys ->
                tele_rel (nr k') (List.rev (im_nparams Mk')) xs ms ->
                ind_con Mk' c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_prefix_rel (ar k' ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
                ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
                tele_prefix_rel (shape_doms_rel (dr k') ms ws (ptyp_doms t0)) kk ys ys ->
                rec_arg_rel p D (okr_at D ups nr) nr ar dr k' ups ups pre pre t v v ->
                List.length Us = ind_nu D ->
                forall (V : nf), Rsh v at t of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ ws ++ ys) ⍮ length Γ ↘ V ->
                Γ ⊢ N ≈ V : A)).
    2:{ (** A neutral reads back by its gluing. *)
        intros k' Mk0 hd k'' m Γ Us Ns M as' HMk0 Href Hm Hr HΓ Mk' ns' HMk' Hpt Hrel w Hw.
        rewrite HMk0 in HMk'; injection HMk' as <-.
        clear - Hr Hw HΓ. inversion Hw; subst.
        assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
        match goal with H : Rne m in _ ↘ ?M0 |- _ => pose proof (Hr _ _ _ Hid H) as Heq end.
        rewrite !exp_wk_id in Heq; exact Heq. }
    - (** A constructor: its parameters and arguments read back as the
          constructor's, at the type's parameters. *)
      intros k' Mk0 hd k'' c gs Us Ns bs vs As Γ M HMk0 Href Hc HUl HNl Hbl Hvl HAl Heq Hnr Har Hnp Htyp Harg Hrec IHrec
        HΓ Mk' ns' HMk' Hpt Hrel w Hw.
      rewrite HMk0 in HMk'; injection HMk' as <-.
      destruct (ind_rel_con_inv p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel HMk0 Hbl)
        as (gs0 & bs' & vs' & Heqd & _ & Hns & Hc0 & Hbl' & Ho & _ & Ha & Hia).
      rewrite Hc in Hc0; injection Hc0 as <-.
      injection Heqd as Heqd.
      destruct (app_split_eq _ _ _ _ Heqd ltac:(congruence)) as [<- <-].
      clear Hrel.
      destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hdc].
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      apply (read_nf_con_member_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HMk0 Href Hc Hbl Hvl Hw); intros PN Args HRps HRc.
      rewrite firstn_app_exact in HRc by exact Hu.
      destruct Hpt as [HPsl HPst HPsr].
      pose proof (HPsr Γ wk_id PN Hid HRps) as HPsN; rewrite map_wk_id_exp in HPsN.
      destruct HPsN as [HlN HPcN].
      clear HPsr HPst.
      cbn [nf_to_exp]; rewrite List.map_app.
      etransitivity; [ exact Heq |].
      replace (im_ty_at p k' Mk0 Us Ns) with (ind_mty p D k' (List.firstn (ind_nu D) (Us ++ Ns)) (List.skipn (ind_nu D) (Us ++ Ns)))
        by (unfold ind_mty; rewrite HMk0, firstn_app_exact, skipn_app_exact by exact HUl; reflexivity).
      rewrite List.app_assoc.
      destruct (read_cargs_nth _ _ _ _ _ _ _ HRc) as (HArl & HArg & HArec).
      eapply wf_exp_eq_con_apps_member; [ exact Hl | exact HMk0 | exact Hc | exact HΓ | rewrite List.length_app; unfold im_np; lia
                                        | rewrite <- HlN, List.length_app; unfold im_np; lia | exact HPcN | exact HAl | exact HArl |].
      intros j N V T HN HV HT.
      assert (Hj : j < length gs) by (rewrite <- HAl; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' gs j Hj) as [g Hg].
      destruct (List.nth_error_split gs j Hg) as (gs1 & gs2 & Heq0 & Hlg).
      subst j.
      destruct (nth_error_lt_some' vs (length gs1) ltac:(lia)) as [v Hv0].
      set (ms := List.skipn (im_unu D Mk0) bs) in *.
      set (pv := nonrec_arg_vals gs1 (List.firstn (length gs1) vs)) in *.
      pose proof (tsym _ _ HMk0 _ _ Ho) as Hsm.
      destruct g as [A0 | Pr].
      + (** A non-recursive argument reads back by its gluing, at the type at
            the constructor's non-uniform parameters, related to the one at
            the type's. *)
        assert (HK : length (cargs_nonrec gs1) < length (cargs_nonrec gs))
          by (rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia).
        assert (HA0' : List.nth_error (cargs_nonrec gs) (length (cargs_nonrec gs1)) = Some A0)
          by (rewrite Heq0, cargs_nonrec_app, List.nth_error_app2 by lia;
              replace (length (cargs_nonrec gs1) - length (cargs_nonrec gs1)) with 0 by lia; reflexivity).
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        destruct (HeA _ _ _ _ _ _ _ _ HMk0 Hnr Hc HA0' Hpre) as [b Eb].
        pose proof (HgA _ _ _ _ _ _ _ _ _ HMk0 Hnr Hc HA0' Hpre Eb) as Hgb.
        destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
        pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq0 Hvl Hv0) as Hn1.
        pose proof Har as Hv'; rewrite tele_rel_iff in Hv'; destruct Hv' as (_ & _ & Hvr).
        pose proof (Hvr _ _ _ Hn1 Hn1) as Hvv0.
        rewrite (nonrec_firstn _ _ _ _ _ Heq0 Hvl) in Hvv0.
        pose proof Hvv0 as Hvv.
        unfold ar, canon_args_rel in Hvv; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMk0 Hc HA0') in Hvv.
        pose proof (per_head_iff Eb Eb HRb) as HRh.
        assert (Hvv' : Rb v v) by (apply HRh; exact Hvv).
        pose proof (HtA _ _ _ _ _ _ _ _ _ HMk0 Hnr Hc HA0' Hpre Eb _ _ _ _ _ Hgb (Harg _ _ _ _ _ _ Heq0 HN HT Hv0) HRb Hvv')
          as Htop.
        destruct Htop as [P' El' _ _ _ _ Hrbt].
        destruct (HArg _ _ _ _ Heq0 Hv0) as (a & V' & Ea & HRa & HnV).
        rewrite HV in HnV; injection HnV as ->.
        rewrite <- env_args_app, <- List.app_assoc in Ea.
        destruct (HevAr _ _ _ _ _ _ _ _ _ _ HMk0 Hsm Hc HA0' Hpre) as [a0 a1 Ea0 Ea1 Ha01].
        assert (a0 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (per_elem_then_per_top Ha01 Hvv0) as Htp.
        destruct (Htp (length Γ)) as (W & HW1 & HW2).
        pose proof (functional_read_nf _ _ _ _ HW2 HRa) as ->.
        pose proof (Hrbt Γ wk_id V' Hid HW1) as Heqn.
        rewrite !exp_wk_id in Heqn.
        exact Heqn.
      + (** A recursive argument, by induction on its shape. *)
        destruct (HArec _ _ _ _ Heq0 Hv0) as (V' & HRV & HnV).
        rewrite HV in HnV; injection HnV as ->.
        rewrite <- env_args_app, <- List.app_assoc in HRV.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        pose proof (con_args_rel_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia _ _ _ _ _ Heq0 Hv0 Hv0) as Hsh0.
        assert (HTf : exists σ', T = ptyp_ty_at p D Us σ' Pr).
        { eexists; rewrite (cargs_rec_type_at p D Mk0 gs gs1 Pr gs2 (Us ++ Ns) As T Heq0 Hdc
                              ltac:(rewrite List.length_app; unfold im_np; lia) HT).
          rewrite firstn_app_exact by exact HUl; reflexivity. }
        eapply (IHrec _ _ _ _ _ _ Heq0 HN HT Hv0 HΓ (Htyp _ _ _ HN HT) HTf Mk0 ns' ms c gs1 Pr gs2 pv 0 nil);
          [ exact HMk0 | rewrite List.app_nil_r; reflexivity | exact Ho | rewrite <- Heq0; exact Hc | exact Hpre | reflexivity
          | lia | apply tele_prefix_rel_nil | exact Hsh0 | exact HUl | rewrite List.app_nil_r; exact HRV ].
    - (** The end of a shape: the element read back at the parameters the
          shape evaluates to at the type's prefix, related to those at the
          element's own by the admissibility of [ups] beside itself. *)
      intros j Mj Ps pre A Us Γ N x k' HMj Hc1 Hc2 IH2 HΓ HN HAf Mk' xs ms c0 gs1 t0 gs2 ws k1 ys HMk' Hpre Hx Hc Hw Hsk Hk Hy
        Hsh HUl V HV.
      inversion HV; subst.
      match goal with Hbs : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs0 |- _ => rename Hbs into Ebt; rename bs0 into bT end.
      match goal with HR0 : Rnf ⇓ (d_ind p j (ups ++ bT)) x in _ ⍮ _ ⍮ _ ↘ V |- _ => rename HR0 into HRV end.
      destruct (ptyp_skip_self _ _ _ _ Hsk) as (HkL & Hj & HPs).
      assert (Hk1 : k1 = List.length (ptyp_doms t0)) by lia.
      assert (Hys : tele_rel (shape_doms_rel (dr k') ms ws (ptyp_doms t0)) (ptyp_doms t0) ys ys)
        by (apply tele_rel_of_pre; rewrite <- Hk1; exact Hy).
      destruct HAf as (σ' & HA); cbn [ptyp_ty_at] in HA; unfold ind_mty in HA; rewrite HMj in HA.
      destruct (adm_rec_params _ _ _ _ _ _ Hcd k' Mk' ms xs c0 _ gs1 t0 gs2 ws ws ys ys HMk' (tsym _ _ HMk' _ _ Hx) Hc eq_refl Hw Hys)
        as [b0 bT' E0 ET R0T].
      rewrite HPs in E0, ET; rewrite Hj in R0T.
      pose proof (functional_eval_exps' _ _ _ _ ET Ebt) as ->.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs' & Ebs & Ebs' & _ & _ & Hvv).
      pose proof (functional_eval_exps' _ _ _ _ Ebs E0) as ->; pose proof (functional_eval_exps' _ _ _ _ Ebs' E0) as ->.
      unfold ntele_rel in R0T; rewrite HMj in R0T.
      destruct (Hc1 _ _ E0 HA) as (HQl & _ & Hgn).
      destruct (Hgn _ R0T) as [_ HQt].
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      pose proof (HQt Γ wk_id Hid) as Hpt0; rewrite map_wk_id_exp in Hpt0.
      pose proof (IH2 _ _ E0 HA Γ wk_id Us _ Hid HUl ltac:(rewrite map_wk_id_exp; exact (glu_params_top_refl _ _ _ _ _ Hpt0))
                    HΓ Mj bT HMj Hpt0 (Hidx _ _ _ _ _ _ _ _ _ _ _ HMj Hvv R0T R0T) V HRV) as Heqn.
      rewrite exp_wk_id in Heqn; rewrite HA; exact Heqn.
    - (** A domain of a shape: the function η-expanded, its body read back
          at a fresh variable of the domain. *)
      intros A Γ k' pre B x Us t N Hd He Hg IH HΓ HN HAf Mk' xs ms c0 gs1 t0 gs2 ws k1 ys HMk' Hpre Hx Hc Hw Hsk Hk Hy
        Hsh HUl V HRV.
      subst pre.
      inversion HRV; subst.
      match goal with Eb : ⟦ B ⟧ env_args nil (ups ++ xs ++ ws ++ ys) ↘ ?b0 |- _ => rename Eb into Ebt; rename b0 into bt end.
      match goal with HRT0 : Rtyp bt in _ ↘ ?A0 |- _ => rename HRT0 into HRT; rename A0 into A' end.
      match goal with Hvapp0 : $| x & ⇑! bt _ | _ ⍮ _ ↘ ?m1 |- _ => rename Hvapp0 into Hvapp; rename m1 into r0 end.
      match goal with HRM0 : Rsh r0 at t of p ups in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?M1 |- _ => rename HRM0 into HRM; rename M1 into V0 end.
      destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hdc].
      destruct HAf as (σ' & HA); cbn [ptyp_ty_at] in HA.
      pose proof (trefl_r _ _ HMk' _ _ Hx) as Hmm.
      destruct (shape_pi_step p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k' Mk' ms c0 gs1 t0 gs2 ws ws k1 ys ys B t
                  HMk' Hmm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & HPd & Hstep).
      destruct (HeD _ _ _ _ _ _ _ _ _ _ _ _ HMk' Hmm Hc eq_refl Hw HB Hy) as [bg Ebg].
      pose proof (HgD _ _ _ _ _ _ _ _ _ _ _ _ _ HMk' Hmm Hc eq_refl Hw HB Hy Ebg) as Hgbg.
      destruct (HrD _ _ _ _ _ _ _ _ _ _ _ _ _ HMk' Hmm Hc eq_refl Hw HB Hy Ebg) as [HrT HrB].
      destruct (HevD k' Mk' ms xs c0 _ gs1 t0 gs2 ws ws k1 B ys ys HMk' (tsym _ _ HMk' _ _ Hx) Hc eq_refl Hw HB Hy)
        as [a0 a1 Ea0 Ea1 Ha01].
      pose proof (functional_eval_exp _ _ _ _ Ea0 Ebg) as ->; pose proof (functional_eval_exp _ _ _ _ Ea1 Ebt) as ->.
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      match type of HA with _ = a_pi ?IT0 ?OT0 => set (IT := IT0) in *; set (OT := OT0) in * end.
      (** The domain reads back as the type of the fresh variable. *)
      pose proof (Hd _ _ HA Γ wk_id Hid) as HITg; rewrite exp_wk_id in HITg.
      destruct (glu_univ_elem_per_univ _ _ _ _ Hgbg) as [Rg HRg].
      destruct (HrT Γ IT Rg HRg HITg) as [HITt _ HITrb].
      assert (HRT' : Rtyp bg in length Γ ↘ A')
        by (eapply per_top_typ_read_left; [ eapply per_univ_then_per_top_typ; exact Ha01 | exact HRT ]).
      pose proof (HITrb Γ wk_id A' Hid HRT') as HITeq; rewrite exp_wk_id in HITeq.
      (** The fresh variable, glued at the domain. *)
      set (c := ⇑! bt (length Γ)).
      assert (HΓIT : ⊢ Γ ▹ IT) by mauto 3.
      assert (Hwk : Γ ▹ IT ⊢ᵏ ↑ : Γ) by mauto 3.
      pose proof (HrB _ _ _ _ (var_glu_elem_bot _ _ _ _ _ _ Hgbg HITg)) as Hvg.
      pose proof (var_per_elem (length Γ) Ha01) as Hcc0.
      assert (ERg : dr k' (ms ++ ws ++ ys) B <~> Rg) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (Hvc : Γ ▹ IT ⊢ #0 : IT[↑]ʷ ® c ∈ DEl k' (ms ++ ws ++ ys) B)
        by (eapply glu_univ_elem_trm_resp_per_elem; [ exact Hgbg | exact HRg | exact Hvg | apply ERg; exact Hcc0 ]).
      assert (Hcc : dr k' (ms ++ ws ++ ys) B c c) by (etransitivity; [ symmetry |]; exact Hcc0).
      (** The rest of the shape, at the variable. *)
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hcc) as (r & r' & Er & Er' & Hsh').
      pose proof (functional_eval_app _ _ _ _ Er Hvapp) as ->.
      pose proof (functional_eval_app _ _ _ _ Er' Hvapp) as ->.
      assert (HNw : Γ ▹ IT ⊢ N[↑]ʷ : Π IT[↑]ʷ OT[wk_q ↑]ʷ) by (rewrite <- exp_wk_pi; rewrite HA in HN; mauto 3).
      assert (HNapp : Γ ▹ IT ⊢ N[↑]ʷ $ #0 : OT[(ι ↑),,#0])
        by (rewrite <- exp_sub_wk_q_extend; eapply wf_app'; [ exact HNw | mauto 3 ]).
      assert (HOTf : exists σ'', OT[(ι ↑),,#0] = ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us) σ'' t).
      { eexists; unfold OT; rewrite ptyp_ty_at_sub by (try exact Hdc; rewrite List.length_map; exact HUl).
        f_equal; rewrite List.map_map; apply List.map_ext; intros U; apply exp_shift_extend_wk. }
      assert (Ecod'' : Rsh r0 at t of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ ws ++ ys ++ c :: nil)
                         ⍮ length (Γ ▹ IT) ↘ V0)
        by (rewrite env_args_snoc3; exact HRM).
      pose proof (IH _ _ HA (Γ ▹ IT) ↑ #0 c r0 Hwk Hcc Hvc Hvapp HΓIT HNapp HOTf Mk' xs ms c0 gs1 t0 gs2 ws (S k1) (ys ++ c :: nil)
                    HMk' ltac:(rewrite <- !List.app_assoc; reflexivity) Hx Hc Hw Hs' Hk' (Hstep _ _ Hcc)
                    Hsh' ltac:(rewrite List.length_map; exact HUl) V0 Ecod'')
        as Hbody.
      assert (HNpi : Γ ⊢ N : Π IT OT) by (rewrite <- HA; exact HN).
      assert (HPI : exists j, Γ ⊢ Π IT OT : Typeω@j) by (gen_presups; eauto).
      destruct HPI as [j HPI].
      destruct (wf_pi_inversion' HPI) as [HITj HOTj].
      assert (HOT : Γ ▹ IT ⊢ OT[(ι ↑),,#0] ≈ OT : Typeω@j).
      { pose proof (kripke_q_var_eq Γ Γ IT (Typeω@j) OT wk_id j HOTj HITj Hid) as H.
        rewrite exp_wk_id in H; rewrite (exp_wk_id_ext OT _ wk_q_id) in H; cbn in H; exact H. }
      rewrite HA; cbn [nf_to_exp].
      etransitivity; [ eapply wf_exp_eq_fn_eta'; exact HNpi |].
      eapply wf_exp_eq_fn_cong'; [ exact HITeq | eapply wf_exp_eq_conv'; [ exact Hbody | exact HOT ] ].
  Qed.

  Lemma ind_realize_top : forall Γ M A m R,
      DG d_ind p k (ups ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
      Γ ⊢ M : A ® m ∈ El ->
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m ∈ R ->
      Γ ⊢ M : A ® m ∈ glu_elem_top i (d_ind p k (ups ++ ns)).
  Proof.
    intros * Hglu HM HR Hm.
    pose proof HM as HM'; apply HEl in HM'; destruct HM' as [HMt Hme Qs HQs Hk].
    assert (HPt : Γ ⊢ A ® P) by (apply HP; exists Qs; exact HQs).
    destruct HQs as [HQ HQk].
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as [_ _ _ _ _ _ _ Herel].
    assert (ER : R <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
    econstructor; [ exact HMt | exact Hglu | exact HPt | eapply per_elem_then_per_top; eassumption |].
    intros Δ φ w Hφ Hw.
    destruct (HQk Δ φ Hφ) as (Hpt & _ & _).
    pose proof (Hk Δ φ _ Hφ (glu_params_top_refl _ _ _ _ _ Hpt)) as Hg.
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    rewrite <- (List.firstn_skipn (ind_nu D) (List.map (fun P => P[φ]ʷ) Qs)) in Hpt.
    pose proof (ind_glu_elem_readback _ _ _ _ _ _ Hg HΔ Mk ns HMk Hpt (proj1 (Herel _ _) (proj1 (ER _ _) Hm)) w Hw) as Hrb.
    rewrite (im_ty_at_decl _ _ _ _ _ _ Hh), List.firstn_skipn in Hrb.
    eapply wf_exp_eq_conv'; [ exact Hrb |].
    rewrite <- wk_apps_ind; symmetry; mauto 3.
  Qed.
End IndRealize.

(** ** Record Types

    A type of a record type reads back as the type former at the readback
    of its parameters.  A neutral is glued by its neutral projections, each
    a neutral of its field's type, field by field.  An element reads back
    as the tuple of the readbacks of its projections, equal to it by η, at
    the readback of its parameters. *)
Section RecordRealize.
  Variables (i : uidx) (p : qname) (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
    (elem_rel : relation domain) (P : glu_typ_pred) (El : glu_exp_pred).
  Hypothesis (Hl : record_lookup gc_deps gc_stack p = Some R)
    (Hper : DF d_record p ns ≈ d_record p ns ∈ per_univ_elem i ↘ elem_rel)
    (HgF : forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ env_args nil (ns ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs)
    (HrF : forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ env_args nil (ns ++ vs) ↘ b ->
       (forall Γ A R0, DF b ≈ b ∈ per_univ_elem i ↘ R0 -> Γ ⊢ A ® FP k vs -> Γ ⊢ A ® glu_typ_top i b) /\
       (forall Γ M A m, DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs ->
          Γ ⊢ M : A ® m ∈ glu_elem_bot i b -> Γ ⊢ M : A ® ⇑ b m ∈ FEl k vs) /\
       (forall Γ M A m R0, DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs ->
          Γ ⊢ M : A ® m ∈ FEl k vs -> DF b ≈ b ∈ per_univ_elem i ↘ R0 -> Dom m ≈ m ∈ R0 ->
          Γ ⊢ M : A ® m ∈ glu_elem_top i b))
    (HP : P <∙> record_glu_typ_pred p R ns FP FEl (Typeω@(ulvl i)))
    (HEl : El <∙> record_glu_exp_pred p R ns FP FEl elem_rel (Typeω@(ulvl i))).

  (** A type at syntactic parameters, at a weakening: equal to the type
      former at them, which are typed at its telescope, its sort in the
      ambient universe. *)
  Lemma record_typ_at_facts : forall Γ A Ns Δ φ, record_typ_at p R ns FP FEl (Typeω@(ulvl i)) Γ A Ns -> Δ ⊢ᵏ φ : Γ ->
      Δ ⊢ A[φ]ʷ ≈ apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns) : Typeω@(ulvl i) /\
      Δ ⊢ a_record p : record_ty R /\
      List.length (List.map (fun N => N[φ]ʷ) Ns) = List.length (record_params R) /\
      (forall j N A0, List.nth_error (List.map (fun N => N[φ]ʷ) Ns) j = Some N ->
         List.nth_error (tele_insts (record_params R) Id (List.map (fun N => N[φ]ʷ) Ns)) j = Some A0 -> Δ ⊢ N : A0) /\
      Δ ⊢ (record_sort R)[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns)] ⊆ Typeω@(ulvl i).
  Proof.
    intros * HNs Hφ.
    destruct (record_typ_at_wk _ _ _ _ _ _ _ _ _ _ _ HNs Hφ) as [HAφ _].
    destruct HNs as [_ Hwk]; destruct (Hwk Δ φ Hφ) as [[HNl HNt _] HS _].
    assert (Hrt : Δ ⊢ a_record p : record_ty R) by (gen_presups; eapply wf_record_own_apps; eassumption).
    repeat split; assumption.
  Qed.

  Lemma record_realize_typ : forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® glu_typ_top i (d_record p ns).
  Proof.
    intros Γ A HA; apply HP in HA; destruct HA as (Ns & HNs).
    econstructor; [ destruct HNs as [HA _]; gen_presups; assumption | exact (per_univ_then_per_top_typ Hper) |].
    intros Δ φ A' Hφ Hr.
    inversion Hr; subst.
    match goal with H : record_lookup _ _ p = Some ?R1 |- _ => assert (R1 = R) as -> by congruence end.
    destruct (record_typ_at_facts _ _ _ _ _ HNs Hφ) as (HAφ & Hrt & HNl & HNt & HS).
    pose proof HNs as [_ Hwk]; destruct (Hwk Δ φ Hφ) as [[_ _ HPr] _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ms |- _ => pose proof (HPr Δ wk_id Ms Hid H) as HMs end.
    rewrite map_wk_id_exp in HMs; destruct HMs as [HMl HMs].
    cbn [nf_to_exp]; etransitivity; [ exact HAφ |].
    eapply wf_exp_eq_subtyp'; [| exact HS ].
    eapply wf_exp_eq_record_apps; [ exact Hrt | exact Hl | exact HNl | rewrite <- HMl; exact HNl | exact HMs ].
  Qed.

  (** A neutral: its projections are neutral projections, each glued at
      its field's type, by induction on the position, the projections
      before it glued, by the realisability of the field's type. *)
  Lemma record_realize_bot : forall Γ M A m,
      DG d_record p ns ∈ glu_univ_elem i ↘ P ↘ El ->
      Γ ⊢ M : A ® m ∈ glu_elem_bot i (d_record p ns) ->
      Γ ⊢ M : A ® ⇑ (d_record p ns) m ∈ El.
  Proof.
    intros * Hglu [P' El' HM Hglu' HAP' Hm Hrb].
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
    assert (HA : Γ ⊢ A ® P) by (apply HPP; exact HAP').
    apply HEl; apply HP in HA; destruct HA as (Ns & HNs).
    destruct (realize_per_univ_elem_gen Hper) as (_ & Hbot & _).
    pose proof (Hbot _ _ Hm) as Hrel.
    pose proof (record_rel_canon _ _ _ _ _ _ Hl Hper) as ER.
    pose proof (proj1 (ER _ _) Hrel) as Hrr; pose proof Hrr as [vs vs' Hvs _ _].
    refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hrel Ns HNs vs Hvs _); [ exact HM |].
    intros Δ φ Ns' Hφ HNs'.
    destruct (record_typ_at_facts _ _ _ _ _ HNs Hφ) as (HAφ & Hrt & HNl & HNt & HS).
    pose proof HNs as [_ Hwk]; destruct (Hwk Δ φ Hφ) as [_ _ Hfg].
    pose proof (Hfg Ns' HNs') as HFg.
    destruct HNs' as [HNl' HNN].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HSu HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    pose proof (wf_record_closed _ _ _ _ _ HΔ Hl) as Hc.
    assert (HNl'' : List.length Ns' = List.length (record_params R)) by lia.
    assert (HNt' : forall j Y T0, List.nth_error Ns' j = Some Y -> List.nth_error (tele_insts (record_params R) Id Ns') j = Some T0 ->
               Δ ⊢ Y : T0)
      by (eapply (record_params_eq_right _ _ _ R (List.map (fun N => N[φ]ʷ) Ns) Ns'); eassumption).
    assert (Happs : Δ ⊢ apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns) ≈ apps_exp (a_record p) Ns' : Typeω@(ulvl i))
      by (eapply wf_exp_eq_subtyp'; [ exact (wf_exp_eq_record_apps _ _ _ _ _ _ _ Hrt Hl HNl HNl'' HNN) | exact HS ]).
    assert (HMφ : Δ ⊢ M[φ]ʷ : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)) by (eapply wf_conv'; [ mauto 3 | exact HAφ ]).
    assert (HMb : Δ ⊢ M[φ]ʷ : apps_exp (a_record p) Ns') by (eapply wf_conv'; [ exact HMφ | exact Happs ]).
    assert (Hlv : List.length vs = List.length (record_fields R)) by (symmetry; exact (List.Forall2_length Hvs)).
    enough (Hall : forall k, k <= List.length (record_fields R) -> forall j f T r, j < k ->
              List.nth_error (record_fields R) j = Some (f, T) -> List.nth_error vs j = Some r ->
              Δ ⊢ a_proj f M[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R j M[φ]ʷ)] ® r ∈ FEl j (List.firstn j vs)).
    { intros k f T r Hk Hr.
      eapply (Hall (List.length (record_fields R))); [ lia | exact (nth_error_lt_length _ _ _ Hk) | exact Hk | exact Hr ]. }
    induction k as [| k IH]; intros Hk j f T r Hj Hjf Hjr; [ lia |].
    destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [ exact (IH ltac:(lia) j f T r Hjk Hjf Hjr) |].
    assert (j = k) as -> by lia.
    destruct (record_projs_neut_nth _ _ _ _ _ Hl Hnd Hvs _ _ _ _ Hjf Hjr) as (a & -> & Ea).
    pose proof (record_projs_prefix_diag _ _ _ _ k Hrr Hvs ltac:(lia)) as Hpre.
    pose proof (HgF _ _ _ _ _ Hjf Hpre Ea) as Hga.
    destruct (HrF _ _ _ _ _ Hjf Hpre Ea) as (_ & HrB & _).
    apply HrB; [ exact Hga |].
    (** The field's type is glued: the projections before it are. *)
    assert (HTP : Δ ⊢ T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)] ® FP k (List.firstn k vs)).
    { apply (HFg k f T (record_pre R k M[φ]ʷ) (List.firstn k vs) Hjf);
        [ apply length_record_pre; lia | rewrite List.length_firstn; lia | | exact Hpre ].
      intros j' g T' N v Hj' HN Hv.
      assert (Hj'k : j' < k)
        by (pose proof (nth_error_lt_length _ _ _ HN) as Hx; rewrite length_record_pre in Hx by lia; exact Hx).
      rewrite List.nth_error_firstn in Hv; destruct (Nat.ltb_spec j' k); [| lia ].
      unfold record_pre in HN; rewrite List.nth_error_map, List.nth_error_firstn in HN.
      destruct (Nat.ltb_spec j' k); [| lia ]; rewrite Hj' in HN; cbn in HN; injection HN as <-.
      rewrite List.firstn_firstn, Nat.min_l by lia.
      replace (List.firstn j' (record_pre R k M[φ]ʷ)) with (record_pre R j' M[φ]ʷ)
        by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
      exact (IH ltac:(lia) j' g T' v Hj'k Hj' Hv). }
    pose proof (glu_univ_elem_univ_lvl _ _ _ _ _ eq_refl Hga _ _ HTP) as HTw.
    assert (Hp : Δ ⊢ a_proj f M[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)])
      by (eapply wf_proj; [ exact HMb | exact Hrt | exact Hl | exact HNl'' | exact HNt' | exact Hjf | exact HTw ]).
    econstructor; [ exact Hp | exact Hga | exact HTP | |].
    - intros s; destruct (Hm s) as (W & H1 & H2); exists (ne_proj f W); split; constructor; assumption.
    - (** The readback: the projection of the readback of the neutral, at
          the field's type at the parameters of the weakening. *)
      intros Δ' φ' W Hφ' HW.
      inversion HW; subst.
      match goal with H : Rne m in _ ↘ ?W0 |- _ => rename H into HW0; rename W0 into W1 end.
      pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hc'.
      pose proof (Hrb _ _ _ Hc' HW0) as HMW.
      destruct (record_typ_at_facts _ _ _ _ _ HNs Hc') as (HAd & Hrt' & HNld & HNtd & HSd).
      assert (HMW' : Δ' ⊢ M[φ ⊙ φ']ʷ ≈ W1 : apps_exp (a_record p) (List.map (fun N => N[φ ⊙ φ']ʷ) Ns))
        by (eapply wf_exp_eq_conv'; [ exact HMW | exact HAd ]).
      destruct (record_proj_cong_at _ _ _ _ _ p R _ (ulvl i) k f T HMW' Hrt' Hl HNld HNtd HSd Hjf) as [_ Hpp].
      assert (HTeq : Δ ⊢ T[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns ++ record_pre R k M[φ]ʷ)]
                       ≈ T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)] : Typeω@(ulvl i))
        by (eapply record_field_params_cong; [ exact HMφ | exact Hrt | exact Hl | exact HNl | exact HNl'' | exact HNt
                                              | exact HNN | exact HS | exact Hjf ]).
      assert (HTeq' : Δ' ⊢ T[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns ++ record_pre R k M[φ]ʷ)][φ']ʷ
                        ≈ T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)][φ']ʷ : Typeω@(ulvl i)) by mauto 3.
      assert (HLk : List.length (record_pre R k M[φ]ʷ) = k) by (apply length_record_pre; lia).
      rewrite (record_field_wk R k f T (List.map (fun N => N[φ]ʷ) Ns) (record_pre R k M[φ]ʷ) φ' Hc Hjf HNl HLk) in HTeq'.
      rewrite (record_field_wk R k f T Ns' (record_pre R k M[φ]ʷ) φ' Hc Hjf HNl'' HLk) in HTeq'.
      rewrite (record_field_wk R k f T Ns' (record_pre R k M[φ]ʷ) φ' Hc Hjf HNl'' HLk).
      rewrite !record_pre_wk, map_wk_wk, exp_wk_wk in HTeq'.
      rewrite record_pre_wk, exp_wk_wk.
      replace ((a_proj f M[φ]ʷ)[φ']ʷ) with (a_proj f M[φ ⊙ φ']ʷ) by (cbn [exp_wk]; rewrite exp_wk_wk; reflexivity).
      eapply wf_exp_eq_conv'; [ exact Hpp | exact HTeq' ].
  Qed.

  (** An element: η, then the tuple of the readbacks of its projections,
      each by the realisability of its field's type, at the readback of
      the parameters. *)
  Lemma record_realize_top : forall Γ M A m R0,
      DG d_record p ns ∈ glu_univ_elem i ↘ P ↘ El ->
      Γ ⊢ M : A ® m ∈ El ->
      DF d_record p ns ≈ d_record p ns ∈ per_univ_elem i ↘ R0 ->
      Dom m ≈ m ∈ R0 ->
      Γ ⊢ M : A ® m ∈ glu_elem_top i (d_record p ns).
  Proof.
    intros * Hglu HM HR Hm.
    pose proof HM as HM'; apply HEl in HM'; destruct HM' as [HMt Hme Ns HNs vs Hvs Hk].
    assert (HPt : Γ ⊢ A ® P) by (apply HP; exists Ns; exact HNs).
    pose proof (record_rel_canon _ _ _ _ _ _ Hl Hper) as ER.
    pose proof (proj1 (ER _ _) Hme) as Hrr.
    econstructor; [ exact HMt | exact Hglu | exact HPt | eapply per_elem_then_per_top; eassumption |].
    intros Δ φ w Hφ Hw.
    inversion Hw; subst.
    match goal with H : record_lookup _ _ p = Some ?R1 |- _ => assert (R1 = R) as -> by congruence end.
    match goal with H1 : Rps ns at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ps0, H2 : Rflds m at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Fs0 |- _ =>
      rename H1 into HRps; rename H2 into HRf; rename Ps0 into Ps; rename Fs0 into Fs end.
    destruct (record_typ_at_facts _ _ _ _ _ HNs Hφ) as (HAφ & Hrt & HNl & HNt & HS).
    pose proof HNs as [_ Hwk]; destruct (Hwk Δ φ Hφ) as [[_ _ HPr] _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    pose proof (HPr Δ wk_id Ps Hid HRps) as HPs; rewrite map_wk_id_exp in HPs; destruct HPs as [HPl HPs].
    assert (HMφ : Δ ⊢ M[φ]ʷ : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)) by (eapply wf_conv'; [ mauto 3 | exact HAφ ]).
    assert (HT : Δ ⊢ apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns) : Typeω@(ulvl i)) by (gen_presups; eassumption).
    pose proof (wf_record_eta_tuple _ _ _ _ _ _ _ _ HMφ Hrt Hl HNl HNt HS HT) as Hetat.
    assert (Heta : Δ ⊢ M[φ]ʷ ≈ a_tuple (apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)) (record_eta_fields R M[φ]ʷ)
                     : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns))
      by (eapply wf_exp_eq_record_eta; [ exact HMφ | exact Hl | exact HNl | exact Hetat ]).
    destruct (read_fields_nth _ _ _ _ _ HRf ns nil vs ltac:(rewrite List.app_nil_r; reflexivity) Hvs) as [HFl HFn].
    assert (Hlv : List.length vs = List.length (record_fields R)) by (symmetry; exact (List.Forall2_length Hvs)).
    assert (HNdrefl : exps_eq_at Δ (record_params R) (List.map (fun N => N[φ]ʷ) Ns) (List.map (fun N => N[φ]ʷ) Ns)).
    { split; [ reflexivity |].
      intros k X Y A0 HX HY HA0; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; exact (HNt _ _ _ HX HA0). }
    assert (Htc : Δ ⊢ a_tuple (apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)) (record_eta_fields R M[φ]ʷ)
                    ≈ a_tuple (apps_exp (a_record p) (List.map nf_to_exp Ps)) (List.combine (List.map fst (record_fields R)) (List.map nf_to_exp Fs))
                    : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)).
    { eapply wf_exp_eq_tuple_fields;
        [ exact Hetat | exact Hrt | exact Hl | exact HNl | rewrite <- HPl; exact HNl | exact HPs | exact HS
        | apply record_eta_fields_names
        | rewrite record_eta_fields_names; apply map_fst_combine; rewrite List.length_map; symmetry; exact HFl |].
      intros k f M1 M1' U Hk1 Hk1' Hfk.
      rewrite (record_eta_fields_nth _ _ _ _ _ Hfk) in Hk1; injection Hk1 as <-.
      rewrite record_eta_fields_pre.
      assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [r Hr].
      destruct (HFn _ _ _ _ Hfk Hr) as (t & F & Et & HF & HnF).
      assert (M1' = nf_to_exp F) as ->.
      { pose proof (nth_error_combine_both (List.map fst (record_fields R)) (List.map nf_to_exp Fs) k f (nf_to_exp F)
                      ltac:(rewrite List.nth_error_map, Hfk; reflexivity) HnF) as E.
        rewrite E in Hk1'; injection Hk1' as <-; reflexivity. }
      cbn [List.app] in Et.
      pose proof (record_projs_prefix_diag _ _ _ _ k Hrr Hvs ltac:(lia)) as Hpre.
      pose proof (HgF _ _ _ _ _ Hfk Hpre Et) as Hgt.
      destruct (HrF _ _ _ _ _ Hfk Hpre Et) as (_ & _ & HrT).
      destruct (glu_univ_elem_per_univ _ _ _ _ Hgt) as [Rt HRt].
      assert (Hrr' : Dom r ≈ r ∈ Rt).
      { destruct Hrr as [vs1 vs2 Hv1 Hv2 Hrel].
        pose proof (record_projs_functional _ _ _ _ Hv1 Hvs) as ->; pose proof (record_projs_functional _ _ _ _ Hv2 Hvs) as ->.
        rewrite tele_rel_iff in Hrel; destruct Hrel as (_ & _ & Hrel).
        pose proof (Hrel _ _ _ Hr Hr) as Hrk; unfold canon_fields_rel in Hrk; rewrite (nth_ftyp_eq _ _ _ _ Hfk) in Hrk.
        exact (proj2 (per_head_iff Et Et HRt _ _) Hrk). }
      pose proof (Hk Δ φ (List.map (fun N => N[φ]ʷ) Ns) Hφ HNdrefl k f U r Hfk Hr) as Hgl.
      destruct (HrT _ _ _ _ _ Hgt Hgl HRt Hrr') as [_ _ _ _ _ _ Hrbt].
      pose proof (Hrbt Δ wk_id F Hid HF) as Heq; rewrite !exp_wk_id in Heq; exact Heq. }
    cbn [nf_to_exp].
    eapply wf_exp_eq_conv'; [ etransitivity; [ exact Heta | exact Htc ] | symmetry; exact HAφ ].
  Qed.
End RecordRealize.

Theorem realize_glu_univ_elem_gen : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    (forall Γ A R,
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        Γ ⊢ A ® P ->
        Γ ⊢ A ® glu_typ_top i a) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          DG a ∈ glu_univ_elem i ↘ P ↘ El ->
          Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
          Γ ⊢ M : A ® ⇑ a m ∈ El) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          DG a ∈ glu_univ_elem i ↘ P ↘ El ->
          Γ ⊢ M : A ® m ∈ El ->
          DF a ≈ a ∈ per_univ_elem i ↘ R ->
          Dom m ≈ m ∈ R ->
          Γ ⊢ M : A ® m ∈ glu_elem_top i a).
Proof.
  simpl. glu_univ_elem_induction1.
  9:{ (** A record type. *)
      split; [| split]; intros.
      - eapply record_realize_typ; eassumption.
      - eapply record_realize_bot; eassumption.
      - match goal with H : _ <∙> record_glu_exp_pred _ _ _ _ _ ?er _ |- _ =>
          eapply record_realize_top with (elem_rel := er); eassumption end. }
  8:{ (** An inductive type. *)
      split; [| split]; intros.
      - eapply ind_realize_typ; eassumption.
      - eapply ind_realize_bot; eassumption.
      - eapply ind_realize_top with (elem_rel := elem_rel); try eassumption.
        + intros * HM Hm Hc HA Hp Eb; exact (proj2 (proj2 (H10 _ _ _ _ _ _ _ _ _ HM Hm Hc HA Hp Eb))).
        + intros * HM Hm Hc Heq Hw HB Hy Eb.
          destruct (H13 _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy Eb) as (Ht & Hbt & _).
          split; [ exact Ht | intros; eapply Hbt; [ eapply H12; eassumption | eassumption ] ]. }
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 per_univ_elem ltac:(fun H => pose proof (per_univ_then_per_top_typ H));
    match_by_head glu_elem_bot ltac:(fun H => destruct_anon H);
    destruct_all; destruct_glu_records.
  (** The two universe clauses, large then small.  The large one's equations
      are at the ambient [Typeω@(ulvl i)].  The small one's element predicate
      carries its own readback clause, at the element's type, so its top case
      is that clause, and its bottom case lifts the neutral's equations to the
      ambient [Typeω@0] by cumulativity. *)
  1:{ econstructor; eauto; intros.
      progressive_inversion.
      mauto 3. }
  1:{ handle_functional_glu_univ_elem.
      match_by_head glu_univ_elem invert_glu_univ_elem.
      clear_dups.
      apply_equiv_left.
      repeat split; eauto.
      repeat eexists.
      + glu_univ_elem_econstructor; eauto; reflexivity.
      + simpl. repeat split.
        * eapply wf_conv'; eassumption.
        * intros. saturate_kripke_escape.
          eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ]. }
  1:{ deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
      firstorder.
      specialize (H _ _ _ gta_elem) as [Htop _].
      econstructor; mauto 3.
      + apply_equiv_left. trivial.
      + intros.
        saturate_kripke_escape.
        match goal with Hx : per_univ_elem _ _ m m |- _ => pose proof (Htop _ _ _ Hx gta_glu) as Ht end.
        progressive_invert Ht.
        match goal with Hn : Rnf ⇓ 𝕌ω@_ m in _ ↘ _ |- _ => progressive_invert Hn end.
        match goal with Hr : forall _ _ _, _ ⊢ᵏ _ : Γ -> Rtyp m in _ ↘ _ -> _ |- _ =>
          deepexec Hr ltac:(fun H => pose proof H) end.
        functional_read_rewrite_clear.
        eapply wf_exp_eq_conv'; [ eassumption | mauto 3 ]. }
  (** The small universe as a type: it reads back as the universe at the
      canonical form of its level, which its glued level term is equal to. *)
  1:{ econstructor; [ gen_presups; eassumption | eassumption |].
      intros Δ φ W Hφ Hr.
      assert (⊢ Δ) by (eapply kripke_dom; eassumption).
      inversion Hr; subst.
      match goal with Hg : glu_lvl ?n _ ?t _ |- _ =>
        assert (Δ ⊢ t[φ]ʷ ≈ nf_lvl_of L : Level@n) by (eapply glu_lvl_readback; eassumption);
        assert (Δ ⊢ A[φ]ʷ ≈ Type⟨t[φ]ʷ⟩ : Typeω@(ulvl i)) by mauto 3 end.
      etransitivity; [ eassumption |].
      eapply wf_exp_eq_univ_cong_large_tm; [ assumption | gen_presups; eassumption | eassumption ]. }
  (** A neutral of a small universe: its type-level gluing is a neutral type's
      at the ambient [Typeω@0], which cumulativity reaches from the small
      universe, and its readback clause is the neutral's. *)
  1:{ handle_functional_glu_univ_elem.
      match_by_head glu_univ_elem invert_glu_univ_elem.
      clear_dups.
      apply_equiv_left.
      destruct_glu_records.
      econstructor; [ assumption | econstructor; eassumption | |].
      + glu_witness2; [ glu_univ_elem_econstructor; eauto; reflexivity |].
        cbn; split; [ eapply suniv_elem_large; eassumption |].
        intros Δ φ M' Hφ Hr.
        eapply suniv_elem_eq_large; [ eauto | mauto 3 ].
      + intros Δ φ W Hφ Hr.
        inversion Hr; subst; eauto. }
  (** An element of a small universe reads back by its own readback clause,
      which is at its type. *)
  1:{ deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
      match goal with Hx : per_univ _ m m |- _ => destruct Hx as [? Hx] end.
      match goal with
      | Hx : per_univ_elem (us _) ?x m m, Ht : glu_lvl ?nt _ ?t l |- _ =>
          econstructor; [ assumption | eassumption | apply_equiv_left; cbn; econstructor; eassumption | |];
          [ intros s; destruct (per_univ_then_per_top_typ Hx s) as [W [HW _]];
            exists W; split; constructor; assumption
          | intros Δ φ w Hφ Hr; inversion Hr; subst; eauto ]
      end. }
  (* Level *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    assert (HA : Γ ⊢ A ≈ Level@n : Typeω@(ulvl i)) by eauto.
    econstructor; [ exact HA | apply per_bot_then_per_lvl_at; assumption |].
    (** A neutral level reads back as the atom of its sort, a level of that
        sort by its readback equation. *)
    intros Δ φ L Hφ Hr.
    progressive_inversion.
    assert (HMeq : Δ ⊢ M[φ]ʷ ≈ M0 : Level@n) by (eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ]).
    split; [ exact HMeq |].
    cbn; split; [ lia | split; [ split; [ lia | gen_presups; eassumption ] | exact I ] ].
  - econstructor; mauto 3.
    + match goal with H : per_lvl_at _ ?m ?m |- _ => pose proof (per_lvl_at_lvl _ _ _ H) end.
      bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      eapply wf_exp_eq_conv';
        [ eapply glu_lvl_readback;
          [ eassumption | eassumption | eapply read_nf_level_sort; eassumption ]
        | mauto 3 ].
  (* True *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    mauto 3.
  - econstructor; mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      progressive_inversion.
      eapply wf_exp_eq_conv'; [ apply wf_exp_eq_true_eta; mauto 3 | mauto 3 ].
  (* False *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    intros.
    eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ].
  - econstructor; mauto 3.
    + bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      eapply wf_exp_eq_conv'; [ eapply False_glu_elem_readback; eassumption | mauto 3 ].
  (* pi *)
  - match_by_head pi_glu_typ_pred progressive_invert.
    handle_per_univ_elem_irrel.
    invert_per_univ_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + saturate_kripke_escape.
      pose proof (H13 Γ wk_id ltac:(mauto 3)) as HIT.
      rewrite exp_wk_id in HIT.
      dir_inversion_clear_by_head read_typ.
      assert (Γ ⊢ IT ® glu_typ_top i a) as Hgtt by mauto 3; destruct_anon Hgtt.
      assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HA' by (rewrite <- exp_wk_pi; mauto 3).
      rewrite HA'.
      simpl. apply wf_exp_eq_pi_cong_large'; [ firstorder | ].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? Hgt]; destruct_anon Hgt.
      pose proof (H13 _ _ H16) as HIPφ.
      assert (IEl (Δ ▹ IT[φ]ʷ) IT[φ]ʷ[↑]ʷ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      assert (⊢ Δ ▹ IT[φ]ʷ) by mauto 3.
      assert (Δ ▹ IT[φ]ʷ ⊢ᵏ φ ⊙ ↑ : Γ) as Hk by mauto 3.
      pose proof (H14 _ _ _ _ Hk HEl H24) as HOP.
      assert (HOT : Δ ▹ IT[φ]ʷ ⊢ OT[ι (φ ⊙ ↑),,#0] ≈ OT[wk_q φ]ʷ : Typeω@(ulvl i))
        by (assert (Hqv := kripke_q_var_eq _ _ _ (Typeω@(ulvl i)) _ _ (ulvl i) H12 H17 H16);
            cbn in Hqv; exact Hqv).
      specialize (H8 _ _ _ H27 HOP) as [].
      eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact HOT |].
      rewrite <- (exp_wk_id OT[ι (φ ⊙ ↑),,#0]).
      mauto 3.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    invert_glu_rel1.
    econstructor; try eapply per_bot_then_per_elem; eauto.
    intros.
    saturate_kripke_escape.
    saturate_glu_info.
    match_by_head1 per_univ_elem invert_per_univ_elem.
    destruct_rel_mod_eval.
    simplify_evals.
    eexists; repeat split; mauto 3.
    eapply H2; eauto.
    assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
    assert (Δ ⊢ M[φ]ʷ : Π IT[φ]ʷ OT[wk_q φ]ʷ) as HM by mauto 3.
    assert (Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N]) as HMN
      by (rewrite <- exp_sub_wk_q_extend; eapply wf_app'; eassumption).
    pose proof (H11 _ _ _ _ H17 H18 equiv_n) as HOP.
    pose proof (H1 _ equiv_n _ H22) as HG.
    pose proof (H15 _ _ _ _ _ H H18 H0 equiv_n) as HNtop.
    destruct HNtop as [? ? ? ? ? HNtoprel HNrb].
    eapply glu_elem_bot_make with (P := OP n equiv_n) (El := OEl n equiv_n); try eassumption.
    + mauto 3 using domain_app_per.
    + intros Δ0 φ0 M' Hk Hrb.
      progressive_invert Hrb.
      assert (Δ0 ⊢ᵏ φ ⊙ φ0 : Γ) as Hkc by (eapply kripke_compose; eassumption).
      assert (Δ0 ⊢ A[φ ⊙ φ0]ʷ ≈ Π IT[φ ⊙ φ0]ʷ OT[wk_q (φ ⊙ φ0)]ʷ : Typeω@(ulvl i)) as HAeq'
        by (rewrite <- exp_wk_pi; mauto 3).
      rewrite exp_wk_sub_of_wk_extend, <- exp_sub_wk_q_extend, exp_wk_app, exp_wk_wk.
      eapply wf_exp_eq_app_cong'.
      * eapply wf_exp_eq_conv'; [ eapply H16; eassumption | eassumption ].
      * rewrite <- exp_wk_wk. eapply HNrb; eassumption.
  - handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    pose proof H8.
    invert_per_univ_elem H8.
    econstructor; mauto 3.
    + invert_glu_rel1. trivial.
    + eapply glu_univ_elem_trm_typ; eauto.
    + intros Δ φ w Hk Hrb.
      saturate_kripke_escape.
      invert_glu_rel1. clear_dups.
      progressive_invert Hrb.
      assert (⊢ Γ) by mauto 2.
      pose proof (H10 _ _ Hk) as HIPφ.
      pose proof (H10 Γ wk_id ltac:(mauto 3)) as HITId.
      rewrite exp_wk_id in HITId.
      assert (Γ ⊢ IT ® glu_typ_top i a) as [? ? HITrb] by mauto 3.
      assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
      assert (Δ ⊢ M[φ]ʷ : Π IT[φ]ʷ OT[wk_q φ]ʷ) as HM by mauto 3.
      eapply wf_exp_eq_conv'; [ | symmetry; eapply HAeq ].
      (** Read back a function by η-expanding it and recursing into the body. *)
      etransitivity; [ eapply wf_exp_eq_fn_eta'; eassumption | ].
      cbn [nf_to_exp].
      eapply wf_exp_eq_fn_cong'; [ eapply HITrb; eassumption | ].
      assert (⊢ Δ ▹ IT[φ]ʷ) by mauto 3.
      assert (Δ ▹ IT[φ]ʷ ⊢ᵏ φ ⊙ ↑ : Γ) as Hk' by mauto 3.
      pose proof (var_per_elem (length Δ) H0) as Hvar.
      assert (IEl (Δ ▹ IT[φ]ʷ) IT[φ]ʷ[↑]ʷ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      destruct (H14 _ _ _ _ Hk' HEl Hvar) as [mn [Happ HOEl]].
      rewrite exp_wk_wk.
      functional_eval_rewrite_clear.
      pose proof (H1 _ Hvar _ H20) as HG.
      destruct (H2 _ Hvar _ H20) as [? [? Htop]].
      apply_equiv_left.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      specialize (Htop _ _ _ _ _ HG HOEl ltac:(eassumption) ltac:(eassumption)) as [? ? ? ? ? ? Hrbtop].
      specialize (Hrbtop (Δ ▹ IT[φ]ʷ) wk_id M0 ltac:(mauto 3) Hrb).
      repeat rewrite exp_wk_id in Hrbtop.
      assert (HOT : Δ ▹ IT[φ]ʷ ⊢ OT[ι (φ ⊙ ↑),,#0] ≈ OT[wk_q φ]ʷ : Typeω@(ulvl i))
        by (assert (Hqv := kripke_q_var_eq Δ Γ IT (Typeω@(ulvl i)) OT φ (ulvl i) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption));
            cbn in Hqv; exact Hqv).
      eapply wf_exp_eq_conv'; [ exact Hrbtop | exact HOT ].
  (* neut *)
  - econstructor; eauto.
    intros.
    progressive_inversion.
    firstorder.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    econstructor; eauto.
  - handle_functional_glu_univ_elem.
    invert_glu_rel1.
    econstructor; eauto.
    + intros s. destruct (H3 s) as [? []].
      mauto.
    + intros.
      progressive_inversion.
      specialize (H11 (length Δ)) as [? []].
      firstorder.
Qed.

Corollary realize_glu_typ_top : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A ® glu_typ_top i a.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_bot : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m,
      Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
      Γ ⊢ M : A ® ⇑ a m ∈ El.
Proof.
  intros.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M : A ® m ∈ glu_elem_top i a.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
  eapply glu_univ_elem_per_elem; eauto.
Qed.

Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.

Corollary var0_glu_elem : forall {i : uidx} {a P El Γ A},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A[↑]ʷ ® ⇑! a (length Γ) ∈ El.
Proof.
  intros.
  eapply realize_glu_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.
