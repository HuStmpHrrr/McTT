From Stdlib Require Import Nat PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Semantic Require Import RecordPER.
From Mctt.Core.Syntactic.System Require Import Records.Typing.
From Mctt.Core.Completeness.Consequences Require Import AnnotatedUpto.
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
Corollary wk_var0_kripke : forall Γ κ A Δ φ,
    Δ ⊢ᵏ φ : Γ ▹{κ} A ->
    φ 0 = length Δ - length Γ - 1.
Proof. intros * H; pose proof (wk_var_kripke _ _ _ 0 H); simpl in *; lia. Qed.

(** The variable of a glued type other than [LevelSort], at the kind of
    its value. *)
Lemma var_glu_elem_bot : forall a i P El Γ A,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ▹{domain_kind a} A ⊢ #0 : A[↑]ʷ ® #ᵈ (length Γ) ∈ glu_elem_bot i a.
Proof.
  intros * Hu Hn HA. saturate_glu_info.
  (** The type is of the sort of its value's kind next to the large
      universe of the index, at which the syntactic rules apply directly. *)
  assert (HΓA : ⊢ Γ ▹{domain_kind a} A) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
  econstructor; [ mauto 4 | exact Hu | | | ].
  - eapply glu_univ_elem_typ_monotone; [ eassumption | eassumption | ]. mauto 4.
  - apply var_neutral_at; exact Hn.
  - intros Δ φ M' Hφ Hr. progressive_inversion.
    assert (φ 0 = length Δ - length Γ - 1) as <- by (eapply wk_var0_kripke; eassumption).
    (** The variable reads back as itself, which holds no proof *)
    unfold glu_ne_eq; cbn [ne_annotate_proofs ne_to_exp].
    change #(φ 0) with #0[φ]ʷ.
    mauto 5.
Qed.



(** The arguments of a constructor read back position by position. *)
Lemma read_cargs_nth : forall s p ups ρ gs vs Vs, Rcargs vs at gs of p ups in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Vs ->
    List.length Vs = List.length gs /\
    (forall gs1 r A gs2 v, gs = gs1 ++ ca_arg r A :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
       exists a (V : nf), ⟦ A ⟧ env_tele ρ (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
         Rnf ⇓ a v in s ↘ V /\ List.nth_error Vs (List.length gs1) = Some V) /\
    (forall gs1 Pr gs2 v, gs = gs1 ++ ca_rec Pr :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
       exists (V : nf), Rsh v at Pr of p ups in gc_deps ⍮ gc_stack ⍮
                          env_tele ρ (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ⍮ s ↘ V /\
         List.nth_error Vs (List.length gs1) = Some V).
Proof.
  induction 1.
  - split; [ reflexivity | split; intros [] *; discriminate ].
  - destruct IHread_cargs as (IHl & IHa & IHr).
    split; [ cbn; congruence | split ].
    + intros [| g gs1] r0 A0 gs2 v0 Heq Hv; cbn in Heq, Hv.
      * injection Heq as <- <- <-; injection Hv as <-; exists a, V; repeat split; assumption.
      * injection Heq as <- Heq; destruct (IHa _ _ _ _ _ Heq Hv) as (a0 & V0 & E0 & R0 & N0).
        exists a0, V0; repeat split; assumption.
    + intros [| g gs1] Pr gs2 v0 Heq Hv; cbn in Heq, Hv; [ discriminate |].
      injection Heq as <- Heq; destruct (IHr _ _ _ _ Heq Hv) as (V0 & R0 & N0).
      exists V0; split; assumption.
  - destruct IHread_cargs as (IHl & IHa & IHr).
    split; [ cbn; congruence | split ].
    + intros [| g gs1] r0 A0 gs2 v0 Heq Hv; cbn in Heq, Hv; [ discriminate |].
      injection Heq as <- Heq; destruct (IHa _ _ _ _ _ Heq Hv) as (a0 & V0 & E0 & R0 & N0).
      exists a0, V0; repeat split; assumption.
    + intros [| g gs1] Pr gs2 v0 Heq Hv; cbn in Heq, Hv.
      * injection Heq as <- <-; injection Hv as <-; exists V; split; [ cbn; assumption | reflexivity ].      * injection Heq as <- Heq; destruct (IHr _ _ _ _ Heq Hv) as (V0 & R0 & N0).
        exists V0; split; assumption.
Qed.

(** A constructor of a member of a group, at the type of the member: read
    at the member's own telescopes, at a declared member and at a view
    alike ([read_nf_con], [read_nf_con_view]). *)
Lemma read_nf_con_member_inv : forall s p D k Mk hd k' c gs bs vs as' w,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_is_rview Mk = false -> im_ref p k Mk = (hd, k') ->
    ind_con Mk c = Some gs -> List.length bs = (im_unu D Mk + im_nn Mk)%nat -> List.length vs = List.length gs ->
    Rnf ⇓ (d_ind p k as') (d_con hd k' c (bs ++ vs)) in gc_deps ⍮ gc_stack ⍮ s ↘ w ->
    forall (Q : nf -> Prop),
      (forall PN Args, Rps as' at List.rev (im_params D Mk) in gc_deps ⍮ gc_stack ⍮ nil ⍮ s ↘ PN ->
         Rcargs vs at gs of p (List.firstn (ind_nu D) as') in gc_deps ⍮ gc_stack ⍮ env_tele nil (List.rev (im_params D Mk)) as' ⍮ s ↘ Args ->
         Q (nf_con p k c (PN ++ Args))) ->
      Q w.
Proof.
  intros * Hl HM Hrv Href Hc Hbl Hvl Hw Q HQ.
  unfold im_ref in Href.
  inversion Hw; subst;
    (** a proof: no inductive type is a proposition *)
    try (match goal with H : domain_kind (d_ind _ _ _) = _ |- _ => cbn in H; discriminate H end);
    match goal with H : ind_lookup _ _ ?qn = Some ?D1, H' : ind_lookup _ _ ?qn = Some ?D2 |- _ =>
      assert_fails (unify D1 D2); rewrite H in H'; injection H' as <- end;
    match goal with H : ind_member ?D0 ?k0 = Some ?M1, H' : ind_member ?D0 ?k0 = Some ?M2 |- _ =>
      assert_fails (unify M1 M2); rewrite H in H'; injection H' as <- end;
    try (exfalso; eapply not_rview_record; eassumption);
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

(** Any value at a record view of a group, at the type of the view: read
    as the view's constructor at the group's uniform parameters, its
    arguments the value's projections ([read_nf_rview]). *)
Lemma read_nf_rview_member_inv : forall s p D k Mk qr Is fl c gs as' v w,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
    im_cons Mk = (c, gs) :: nil ->
    Rnf ⇓ (d_ind p k as') v in gc_deps ⍮ gc_stack ⍮ s ↘ w ->
    forall (Q : nf -> Prop),
      (forall ws PN Args, ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws ->
         Rps as' at List.rev (ind_uparams D) in gc_deps ⍮ gc_stack ⍮ nil ⍮ s ↘ PN ->
         Rcargs ws at gs of p as' in gc_deps ⍮ gc_stack ⍮ decl_env D as' ⍮ s ↘ Args ->
         Q (nf_con p k c (PN ++ Args))) ->
      Q w.
Proof.
  intros * Hl HM Hh Hcs Hw Q HQ.
  inversion Hw; subst;
    (** a proof: no inductive type is a proposition *)
    try (match goal with H : domain_kind (d_ind _ _ _) = _ |- _ => cbn in H; discriminate H end);
    match goal with H : ind_lookup _ _ ?qn = Some ?D1, H' : ind_lookup _ _ ?qn = Some ?D2 |- _ =>
      assert_fails (unify D1 D2); rewrite H in H'; injection H' as <- end;
    match goal with H : ind_member ?D0 ?k0 = Some ?M1, H' : ind_member ?D0 ?k0 = Some ?M2 |- _ =>
      assert_fails (unify M1 M2); rewrite H in H'; injection H' as <- end;
    try match goal with H : im_head Mk = _ |- _ => rewrite Hh in H; discriminate H end;
    try (exfalso; eapply not_rview_record; eassumption).
  match goal with H : im_head Mk = mh_record _ _ _ |- _ => rewrite Hh in H; injection H as <- <- <- end.
  match goal with H : im_cons Mk = _ |- _ => rewrite Hcs in H; injection H as <- <- end.
  eapply HQ; eassumption.
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
  assert (Hass : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk))
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
Lemma eval_fam_cod_shfam_inv : forall p ups ρ B t T x a,
    ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ B t ⦂ entry_type_none ↦ x ⦂ T ↘ a ->
    ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ⦂ entry_type_closure B ρ ↘ a.
Proof.
  intros * H; unfold fam_cod in H; inversion H; subst.
  match goal with H1 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
  match goal with H0 : ⟦ #0 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H0; subst end.
  - match goal with Ha : $| _ & _ | _ ⍮ _ ↘ _ |- _ => cbn in Ha; inversion Ha; subst; assumption end.
  (** The family takes relevant arguments *)
  - match goal with H2 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _, H3 : arg_kind _ _ _ = ak_propositional |- _ =>
      inversion H2; subst; cbn in H3; discriminate end.
Qed.

Lemma glu_params_top_refl : forall Dh Mh Δ Ps as', glu_params_top Dh Mh Δ Ps as' -> exps_eq_at Δ (im_params Dh Mh) Ps Ps.
Proof.
  intros * [_ Ht _]; split; [ reflexivity |].
  intros k X Y A HX HY HA; rewrite HX in HY; injection HY as <-.
  apply wf_exp_eq_refl; eapply Ht; eassumption.
Qed.

(** A choice of a witness at each position of a list. *)
Lemma list_choice_nth : forall {X Y : Type} (R : nat -> X -> Y -> Prop) (xs : list X),
    (forall j x, List.nth_error xs j = Some x -> exists y, R j x y) ->
    exists ys, List.length ys = List.length xs /\
      forall j x y, List.nth_error xs j = Some x -> List.nth_error ys j = Some y -> R j x y.
Proof.
  intros X Y R xs; revert R; induction xs as [| x xs IH]; intros R H.
  - exists nil; split; [ reflexivity | intros [] *; discriminate ].
  - destruct (H 0 x eq_refl) as [y Hy].
    destruct (IH (fun j => R (S j)) (fun j x' Hx' => H (S j) x' Hx')) as (ys & Hl & Hys).
    exists (y :: ys); split; [ cbn; congruence |].
    intros [| j] x' y' Hx' Hy'; cbn in Hx', Hy'; [ injection Hx' as <-; injection Hy' as <-; exact Hy | exact (Hys _ _ _ Hx' Hy') ].
Qed.

(** Lists of normal forms related position by position are related. *)
Lemma nfs_eq_upto_proofs_of_nth : forall Ms Ms', List.length Ms = List.length Ms' ->
    (forall j M M', List.nth_error Ms j = Some M -> List.nth_error Ms' j = Some M' -> nf_eq_upto_proofs M M') ->
    nfs_eq_upto_proofs Ms Ms'.
Proof.
  induction Ms as [| M Ms IH]; intros [| M' Ms'] Hl H; cbn in Hl; try discriminate; [ reflexivity |].
  apply nfs_eq_upto_proofs_cons; split; [ exact (H 0 _ _ eq_refl eq_refl) |].
  apply IH; [ congruence | intros j N N' HN HN'; exact (H (S j) _ _ HN HN') ].
Qed.

Lemma nf_con_upto_proofs : forall p k c Ms Ms', nfs_eq_upto_proofs Ms Ms' -> nf_eq_upto_proofs (nf_con p k c Ms) (nf_con p k c Ms').
Proof. intros * H; unfold nf_eq_upto_proofs, nfs_eq_upto_proofs in *; cbn; rewrite !dec_eqb_refl, PeanoNat.Nat.eqb_refl; exact H. Qed.

(** The environment of a constructor's components, as the arguments'
    telescope over that of the non-uniform parameters. *)
Lemma components_env_nparams_args : forall D u (Mm : imember) gs ms vs,
    List.length ms = List.length (im_nparams Mm) ->
    components_env D u (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs)
    = env_tele (components_env D u (List.rev (im_nparams Mm)) ms) (cargs_nonrec_tele gs) vs.
Proof. intros * Hl; unfold components_env; rewrite env_tele_app by (rewrite List.length_rev; exact Hl); reflexivity. Qed.

(** A neutral's readback equation, as one of the normal form of a neutral
    of any kind. *)
Lemma glu_nf_eq_neut : forall Γ M W A κ, glu_ne_eq Γ M W A -> glu_nf_eq Γ M (nf_neut κ W) A.
Proof.
  unfold glu_nf_eq, glu_ne_eq; intros * H; exact H.
Qed.

(** A normal form free of proofs is its own annotation. *)
Lemma nf_ne_annotate_proofs_proof_free :
  (forall W, nf_proof_free W -> nf_annotate_proofs W = W) /\
  (forall M, ne_proof_free M -> ne_annotate_proofs M = M).
Proof.
  apply nf_ne_ind; intros; cbn [nf_proof_free ne_proof_free] in *; destruct_all;
    try contradiction; cbn [nf_annotate_proofs ne_annotate_proofs]; f_equal; eauto.
  (** The lists, element by element *)
  all: lazymatch goal with Hl : list_all _ _ ?l, Ha : all_list _ ?l |- ListDef.map _ ?l = ?l =>
         clear - Hl Ha; induction Hl as [| x Hx l' Hl' IH]; cbn in *; [ reflexivity |]; destruct Ha as [Ha1 Ha2];
           f_equal; [| exact (IH Ha2) ] end.
  all: try (exact (Hx Ha1)).
  (** The atoms of a level *)
  1-2: (destruct Hx as [o s M HM]; cbn in *; rewrite (HM Ha1); reflexivity).
  (** A block of a stuck eliminator: its scrutinee type, its motive, its
      branches *)
  destruct Hx as [n Z HZ A HA brs Hbrs]; destruct Ha1 as (HZ' & HA' & Hbrs'); cbn in *.
  rewrite (HZ HZ'), (HA HA'); f_equal.
  clear - Hbrs Hbrs'; induction Hbrs as [| br Hbr brs' Hbrs IH]; cbn in *; [ reflexivity |]; destruct Hbrs' as [Hb1 Hb2].
  f_equal; [| exact (IH Hb2) ]; destruct Hbr as [c k Bd HB]; cbn in *; rewrite (HB Hb1); reflexivity.
Qed.

(** A readback free of proofs is glued by its equation alone. *)
Lemma glu_nf_eq_proof_free : forall Γ M W A, nf_proof_free W -> Γ ⊢ M ≈ W : A -> glu_nf_eq Γ M W A.
Proof.
  intros * Hf HM; unfold glu_nf_eq.
  rewrite (proj1 nf_ne_annotate_proofs_proof_free W Hf); exact HM.
Qed.

Lemma map_wk_id_exp :forall Ps, List.map (fun P => P[wk_id]ʷ) Ps = Ps.
Proof. intros; rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; reflexivity. Qed.

Section IndRealize.
  Variables (i : universe_index) (p : qname) (D : ind_decl) (k : nat) (Mk : imember) (pm : qname) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (elem_rel : relation domain) (P : glu_typ_pred) (El : glu_exp_pred).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hu : List.length ups = ind_nu D)
    (Hass : group_structure D) (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_decl pm)
    (Hper : DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel)
    (HP : P <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@(large_level i))
    (HEl : El <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk elem_rel Typeω@(large_level i)).

  Lemma ind_realize_typ : forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® glu_typ_top i (d_ind p k (ups ++ ns)).
  Proof.
    intros Γ A HA; apply HP in HA; destruct HA as (Ps & HAPs & Hk).
    econstructor; [ cbn [domain_kind abs_kind_sort]; gen_presups; assumption | exact (per_univ_then_per_top_typ Hper) |].
    intros Δ φ A' Hφ Hr; cbn [domain_kind abs_kind_sort].
    inversion Hr; subst.
    match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
    match goal with H : ind_member D k = Some ?M1 |- _ => assert (M1 = Mk) as -> by congruence end.
    destruct (Hk Δ φ Hφ) as ([HPl HPt HPr] & Hs & _).
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ms |- _ => pose proof (HPr Δ wk_id Ms Hid H) as HMs end.
    rewrite map_wk_id_exp in HMs.
    (** The parameters are their annotated readbacks *)
    destruct HMs as (HMl & HMs).
    unfold glu_nf_eq; cbn [nf_annotate_proofs nf_to_exp]; transitivity (apps (a_ind p k) (List.map (fun P => P[φ]ʷ) Ps)); [ rewrite <- wk_apps_ind; mauto 3 |].
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
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Ps HPs _).
    { eapply per_bot_then_per_elem; [ eassumption |].
      exact Hm. }
    intros Δ φ Ps' Hφ HPs'.
    pose proof (ind_typ_at_params_conv p D ups ns NP NEl AP AEl DP DEl k Mk pm _ Γ A Ps Δ φ Ps' Hl HMk Hh HPs Hφ HPs') as HPeq.
    destruct HPs as [HAPs _].
    eapply ind_glu_elem_neut; [ exact HMk | unfold im_is_rview; rewrite Hh; reflexivity | unfold im_ref; rewrite Hh; reflexivity
                              | exact (proj1 (proj2 Hm)) |].
    intros Θ ψ M' Hψ Hr.
    pose proof (kripke_compose _ _ _ _ _ Hψ Hφ) as Hc.
    rewrite exp_wk_wk, (im_ty_at_decl _ _ _ _ _ _ Hh), List.firstn_skipn.
    eapply glu_ne_eq_conv with (κ := ak_relevant); [| exact (Hrb _ _ _ Hc Hr) ]; cbn [abs_kind_sort].
    transitivity ((apps (a_ind p k) (List.map (fun P => P[φ]ʷ) Ps))[ψ]ʷ); [| mauto 3 ].
    rewrite wk_apps_ind, map_wk_wk, <- wk_apps_ind; mauto 3.
  Qed.

  Hypothesis
    (HeA : forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b)
    (HgA : forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem i ↘ AP m ms c j vs ↘ AEl m ms c j vs)
    (HtA : forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b ->
       forall Γ M A' n R, DG b ∈ glu_univ_elem i ↘ AP m ms c j vs ↘ AEl m ms c j vs ->
         Γ ⊢ M : A' ® n ∈ AEl m ms c j vs -> DF b ≈ b ∈ per_univ_elem i ↘ R -> Dom n ≈ n ∈ R ->
         Γ ⊢ M : A' ® n ∈ glu_elem_top i b)
    (HeD : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       exists b, ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                         (ms ++ ws ++ ys) ↘ b)
    (HgD : forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ b ->
       DG b ∈ glu_univ_elem i
         ↘ DP m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B
         ↘ DEl m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B)
    (HrD : forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ b ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       (forall Γ A R, DF b ≈ b ∈ per_univ_elem i ↘ R -> not_level_sort b -> Γ ⊢ A ® DP m (ms ++ ws ++ ys) Ts B ->
          Γ ⊢ A ® glu_typ_top i b) /\
       (forall Γ M A n, Γ ⊢ M : A ® n ∈ glu_elem_bot i b -> Γ ⊢ M : A ® ⇑ b n ∈ DEl m (ms ++ ws ++ ys) Ts B))
    (** A non-recursive argument's gluing moves to related non-uniform
        parameters, at a type glued there *)
    (HmA : forall m Mm ms ms' c gs j A vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms' ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       forall Γ T N n, Γ ⊢ N : T ® n ∈ AEl m ms c j vs -> Γ ⊢ T ® AP m ms' c j vs -> Γ ⊢ N : T ® n ∈ AEl m ms' c j vs)
    (** So does a domain's of a recursive argument's shape *)
    (HmD : forall m Mm ms ms' c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms' ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       forall Γ T N n, Γ ⊢ N : T ® n ∈ DEl m (ms ++ ws ++ ys) Ts B -> Γ ⊢ T ® DP m (ms' ++ ws ++ ys) Ts B ->
         Γ ⊢ N : T ® n ∈ DEl m (ms' ++ ws ++ ys) Ts B).

  (** The readback of an element of any member of the group, a view too,
      at the type's parameters [ns'] (the element is related at its own):
      a constructor at the member's own telescopes, a recursive argument
      by its shape, read at the type's prefix [xs], the element's own
      prefix [ms] related to it. *)
  Lemma ind_glu_elem_readback :
      forall k' Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k' Γ Us Ns M m -> ⊢ Γ ->
      forall Mk' ns', ind_member D k' = Some Mk' -> glu_params_top D Mk' Γ (Us ++ Ns) (ups ++ ns') ->
      ind_rel p D (admissible_index_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups)
        (canon_doms_rel D ups) k' ups ups ns' ns' m m ->
      forall (w : nf), Rnf ⇓ (d_ind p k' (ups ++ ns')) m in length Γ ↘ w -> glu_nf_eq Γ M w (im_ty_at p k' Mk' Us Ns).
  Proof.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as [_ _ Hcp _ _ Hcd _ _].
    destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ _ Hper Hl Hu Hu) as (HevN & HevAr & HevD).
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    set (nr := canon_nparams_rel D ups) in *; set (ar := canon_args_rel D ups) in *; set (dr := canon_doms_rel D ups) in *.
    pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
    pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
    pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as Hidx.
    apply (ind_glu_elem_mut_ind p D ups NEl AEl DP DEl
             (fun k' Γ Us Ns M m _ => ⊢ Γ -> forall Mk' ns', ind_member D k' = Some Mk' ->
                glu_params_top D Mk' Γ (Us ++ Ns) (ups ++ ns') ->
                ind_rel p D (admissible_index_at D ups nr) nr ar dr k' ups ups ns' ns' m m ->
                forall (w : nf), Rnf ⇓ (d_ind p k' (ups ++ ns')) m in length Γ ↘ w -> glu_nf_eq Γ M w (im_ty_at p k' Mk' Us Ns))
             (fun k' Γ Us pre Ts t A N v _ => ⊢ Γ -> Γ ⊢ N : A -> (exists σ', A = ptyp_ty_at p D Us σ' t) ->
                forall Mk' xs ms c0 gs1 t0 gs2 ws kk ys, ind_member D k' = Some Mk' -> pre = ms ++ ws ++ ys ->
                Ts = List.rev (im_nparams Mk') ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t0) ->
                tele_rel (nr k') (List.rev (im_nparams Mk')) xs ms ->
                ind_con Mk' c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_prefix_rel (ar k' ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
                ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
                tele_prefix_rel (shape_doms_rel (dr k') (List.rev (im_nparams Mk')) (cargs_nonrec_tele gs1) ms ws t0) kk ys ys ->
                rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k' ups ups pre pre Ts t v v ->
                List.length Us = ind_nu D ->
                forall (V : nf), Rsh v at t of p ups in gc_deps ⍮ gc_stack ⍮ components_env D ups Ts (xs ++ ws ++ ys) ⍮ length Γ ↘ V ->
                glu_nf_eq Γ N V A)).
    2:{ (** A neutral reads back by its gluing. *)
        intros k' Mk0 hd k'' m Γ Us Ns M as' HMk0 Hrv Href Hm Hr HΓ Mk' ns' HMk' Hpt Hrel w Hw.
        rewrite HMk0 in HMk'; injection HMk' as <-.
        clear - Hr Hw HΓ HMk0 Hrv Hl. inversion Hw; subst;
          try (match goal with H : domain_kind (d_ind _ _ _) = _ |- _ => cbn in H; discriminate H end);
          try solve [ match goal with H : ind_lookup _ _ p = Some ?D1 |- _ =>
                        assert_fails (unify D1 D); rewrite Hl in H; injection H as <- end;
                      match goal with H : ind_member D k' = Some ?M1 |- _ =>
                        assert_fails (unify M1 Mk0); rewrite HMk0 in H; injection H as <- end;
                      exfalso; eapply not_rview_record; eassumption ].
        assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
        match goal with H : Rne m in _ ↘ ?M0 |- _ => pose proof (Hr _ _ _ Hid H) as Heq end.
        rewrite !exp_wk_id in Heq; apply glu_nf_eq_neut; exact Heq. }
    - (** A constructor: its parameters and arguments read back as the
          constructor's, at the type's parameters. *)
      intros k' Mk0 hd k'' c gs Us Ns bs vs As Γ M HMk0 Hrv Href Hc HUl HNl Hbl Hvl HAl Heq Hnr Har Hnp Htyp Harg Hrec IHrec
        HΓ Mk' ns' HMk' Hpt Hrel w Hw.
      rewrite HMk0 in HMk'; injection HMk' as <-.
      destruct (ind_rel_con_inv p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel HMk0 Hrv Hbl)
        as (gs0 & bs' & vs' & Heqd & _ & Hns & Hc0 & Hbl' & Ho & _ & Ha & Hia).
      rewrite Hc in Hc0; injection Hc0 as <-.
      injection Heqd as Heqd.
      destruct (app_split_eq _ _ _ _ Heqd ltac:(congruence)) as [<- <-].
      clear Hrel.
      destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hdc].
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      apply (read_nf_con_member_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HMk0 Hrv Href Hc Hbl Hvl Hw); intros PN Args HRps HRc.
      rewrite firstn_app_exact in HRc by exact Hu.
      rewrite env_params_components in HRc by exact Hu.
      assert (Hxl : List.length ns' = List.length (im_nparams Mk0))
        by (pose proof Ho as Hxl; rewrite tele_rel_iff in Hxl; destruct Hxl as (Hxl & _ & _); rewrite List.length_rev in Hxl; exact Hxl).
      destruct Hpt as [HPsl HPst HPsr].
      pose proof (HPsr Γ wk_id PN Hid HRps) as HPsN; rewrite map_wk_id_exp in HPsN.
      destruct HPsN as (PN' & EPN & HlN & HPcN).
      clear HPsr HPst.
      destruct (read_cargs_nth _ _ _ _ _ _ _ HRc) as (HArl & HArg & HArec).
      (** Each argument reads back, up to proofs, as a normal form equal to
          it, at its type. *)
      assert (Hpw : forall j V, List.nth_error Args j = Some V -> exists V', nf_eq_upto_proofs V V' /\
                 forall N T, List.nth_error As j = Some N ->
                   List.nth_error (tele_insts (cargs_ctx p D Mk0 gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T ->
                   Γ ⊢ N ≈ nf_annotate_proofs V' : T).
      { intros j V HV.
        destruct (List.nth_error As j) as [N |] eqn:HN;
          [| exists V; split; [ apply nf_eq_upto_proofs_of_eq; reflexivity | intros; discriminate ] ].
        destruct (List.nth_error (tele_insts (cargs_ctx p D Mk0 gs) (sb_of_list Id (Us ++ Ns)) As) j) as [T |] eqn:HT;
          [| exists V; split; [ apply nf_eq_upto_proofs_of_eq; reflexivity | intros; discriminate ] ].
        enough (HV' : glu_nf_eq Γ N V T).
        { destruct HV' as (V' & EV & HV'); exists V'; split; [ exact EV |].
          intros N0 T0 HN0 HT0; injection HN0 as <-; injection HT0 as <-; exact HV'. }
      assert (Hj : j < length gs) by (rewrite <- HArl; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' gs j Hj) as [g Hg].
      destruct (List.nth_error_split gs j Hg) as (gs1 & gs2 & Heq0 & Hlg).
      subst j.
      destruct (nth_error_lt_some' vs (length gs1) ltac:(lia)) as [v Hv0].
      set (ms := List.skipn (im_unu D Mk0) bs) in *.
      assert (Hpl : List.length (List.firstn (length gs1) vs) = length gs1) by (rewrite List.length_firstn; lia).
      pose proof (tsym _ _ HMk0 _ _ Ho) as Hsm.
      destruct g as [r0 A0 | Pr].
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
        pose proof (nonrec_nth_arg _ _ _ _ _ _ _ Heq0 Hvl Hv0) as Hn1.
        pose proof Har as Hv'; rewrite tele_rel_iff in Hv'; destruct Hv' as (_ & _ & Hvr).
        pose proof (Hvr _ _ _ Hn1 Hn1) as Hvv0.
        rewrite (nonrec_firstn _ _ _ _ _ Heq0 Hvl) in Hvv0.
        pose proof Hvv0 as Hvv.
        unfold ar, canon_args_rel in Hvv;
          rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMk0 Hc HA0'), (member_nparams_eq _ _ _ HMk0), (member_con_tele_eq _ _ _ _ _ HMk0 Hc) in Hvv.
        pose proof (per_head_iff Eb Eb HRb) as HRh.
        assert (Hvv' : Rb v v) by (apply HRh; exact Hvv).
        pose proof (HtA _ _ _ _ _ _ _ _ _ HMk0 Hnr Hc HA0' Hpre Eb _ _ _ _ _ Hgb (Harg _ _ _ _ _ _ _ Heq0 HN HT Hv0) HRb Hvv')
          as Htop.
        destruct Htop as [P' El' _ _ _ _ Hrbt].
        destruct (HArg _ _ _ _ _ Heq0 Hv0) as (a & V' & Ea & HRa & HnV).
        assert (V' = V) as -> by congruence.
        rewrite <- components_env_nparams_args in Ea by exact Hxl.
        destruct (HevAr _ _ _ _ _ _ _ _ _ _ HMk0 Hsm Hc HA0' Hpre) as [a0 a1 Ea0 Ea1 Ha01].
        (** The argument's type reads only the telescope before it. *)
        pose proof (components_env_args_prefix D ups Mk0 gs1 (ca_arg r0 A0 :: gs2) ns' _ Hxl Hpl) as Epre.
        rewrite <- Heq0 in Epre; rewrite Epre in Ea1.
        assert (a0 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (per_elem_then_per_top Ha01 Hvv0) as Htp.
        destruct (Htp (length Γ)) as [W1 W2 HW1 HW2 EW].
        pose proof (functional_read_nf _ _ _ _ HW2 HRa) as ->.
        pose proof (Hrbt Γ wk_id W1 Hid HW1) as Heqn.
        rewrite !exp_wk_id in Heqn.
        exact (glu_nf_eq_upto _ _ _ _ _ EW Heqn).
      + (** A recursive argument, by induction on its shape. *)
        destruct (HArec _ _ _ _ Heq0 Hv0) as (V' & HRV & HnV).
        assert (V' = V) as -> by congruence.
        rewrite <- components_env_nparams_args in HRV by exact Hxl.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        pose proof (con_args_rel_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia _ _ _ _ _ Heq0 Hv0 Hv0) as Hsh0.
        assert (HTf : exists σ', T = ptyp_ty_at p D Us σ' Pr).
        { eexists; rewrite (cargs_rec_type_at p D Mk0 gs gs1 Pr gs2 (Us ++ Ns) As T Heq0 Hdc
                              ltac:(rewrite List.length_app; unfold im_np; lia) HT).
          rewrite firstn_app_exact by exact HUl; reflexivity. }
        eapply (IHrec _ _ _ _ _ _ Heq0 HN HT Hv0 HΓ (Htyp _ _ _ HN HT) HTf Mk0 ns' ms c gs1 Pr gs2
                  (nonrec_arg_vals gs1 (List.firstn (length gs1) vs)) 0 nil);
          [ exact HMk0 | rewrite List.app_nil_r; reflexivity | cbn [List.firstn]; rewrite List.app_nil_r; reflexivity
          | exact Ho | rewrite <- Heq0; exact Hc | exact Hpre | reflexivity
          | lia | apply tele_prefix_rel_nil | exact Hsh0 | exact HUl | cbn [List.firstn]; rewrite !List.app_nil_r; exact HRV ]. }
      (** The constructor at the parameters and the arguments so chosen *)
      destruct (list_choice_nth _ Args Hpw) as (Args' & HlA' & HA').
      exists (nf_con p k' c (PN' ++ Args')); split.
      { apply nf_con_upto_proofs, nfs_eq_upto_proofs_app; [ exact EPN |].
        apply nfs_eq_upto_proofs_of_nth; [ symmetry; exact HlA' | intros j V V' HV HV'; exact (proj1 (HA' _ _ _ HV HV')) ]. }
      cbn [nf_annotate_proofs nf_to_exp]; rewrite !List.map_app.
      etransitivity; [ exact Heq |].
      replace (im_ty_at p k' Mk0 Us Ns) with (ind_mty p D k' (List.firstn (ind_nu D) (Us ++ Ns)) (List.skipn (ind_nu D) (Us ++ Ns)))
        by (unfold ind_mty; rewrite HMk0, firstn_app_exact, skipn_app_exact by exact HUl; reflexivity).
      rewrite List.app_assoc.
      eapply wf_exp_eq_con_apps_member; [ exact Hl | exact HMk0 | exact Hc | exact HΓ | rewrite List.length_app; unfold im_np; lia
                                        | rewrite <- HlN, List.length_app; unfold im_np; lia | exact HPcN | exact HAl
                                        | rewrite !List.length_map; lia |].
      intros j N N' T HN HN' HT.
      rewrite !List.nth_error_map in HN'.
      destruct (List.nth_error Args' j) as [V' |] eqn:HV'; cbn in HN'; [| discriminate HN' ]; injection HN' as <-.
      assert (Hj : j < length Args) by (rewrite <- HlA'; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' Args j Hj) as [V HV].
      exact (proj2 (HA' _ _ _ HV HV') _ _ HN HT).
    - (** A record view: its projections read back as the view's
          constructor's arguments, at the group's uniform parameters. *)
      intros k' Mk0 qr Is fl c gs Us Ns As m vs Γ M HMk0 Hhr Hcs HUl HNl HAl Hps Heq Har Htyp Harg Hrec IHrec
        HΓ Mk' ns' HMk' Hpt Hrel w Hw.
      rewrite HMk0 in HMk'; injection HMk' as <-.
      destruct (ind_rel_record_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel HMk0 Hhr Hcs) as [vs0 vs1 -> _ Hps0 Hps1 _ Hia].
      pose proof (functional_eval_projs _ _ _ _ Hps Hps0) as <-.
      pose proof (functional_eval_projs _ _ _ _ Hps Hps1) as <-.
      clear Hrel.
      pose proof (rview_struct_nparams _ _ _ (group_structure_record_struct _ Hass) _ _ _ _ _ HMk0 Hhr) as Hnp0.
      pose proof (ind_con_single _ _ _ Hcs) as Hc.
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Hvl _].
      assert (Hn0 : tele_rel (nr k') (List.rev (im_nparams Mk0)) nil nil) by (rewrite Hnp0; split; reflexivity + exact I).
      assert (HNs : Ns = nil) by (destruct Ns; [ reflexivity | unfold im_nn in HNl; rewrite Hnp0 in HNl; discriminate HNl ]).
      subst Ns; rewrite !List.app_nil_r in Hw, Hpt, Htyp, Harg, Hrec, IHrec; cbn [List.app] in Heq.
      assert (HPeq : im_params D Mk0 = ind_uparams D) by (unfold im_params; rewrite Hnp0; reflexivity).
      destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hdc].
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      apply (read_nf_rview_member_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HMk0 Hhr Hcs Hw); intros ws PN Args Hws HRps HRc.
      pose proof (functional_eval_projs _ _ _ _ Hws Hps) as ->.
      destruct Hpt as [HPsl HPst HPsr].
      rewrite HPeq, ?List.app_nil_r in HPsr.
      pose proof (HPsr Γ wk_id PN Hid HRps) as HPsN; rewrite map_wk_id_exp in HPsN.
      destruct HPsN as (PN' & EPN & HlN & HPcN).
      clear HPsr HPst.
      destruct (read_cargs_nth _ _ _ _ _ _ _ HRc) as (HArl & HArg & HArec).
      assert (Hxl0 : List.length (@nil domain) = List.length (im_nparams Mk0)) by (rewrite Hnp0; reflexivity).
      (** Each field reads back, up to proofs, as a normal form equal to it,
          at its type. *)
      assert (Hpw : forall j V, List.nth_error Args j = Some V -> exists V', nf_eq_upto_proofs V V' /\
                 forall N T, List.nth_error As j = Some N ->
                   List.nth_error (tele_insts (cargs_ctx p D Mk0 gs) (sb_of_list Id Us) As) j = Some T ->
                   Γ ⊢ N ≈ nf_annotate_proofs V' : T).
      { intros j V HV.
        destruct (List.nth_error As j) as [N |] eqn:HN;
          [| exists V; split; [ apply nf_eq_upto_proofs_of_eq; reflexivity | intros; discriminate ] ].
        destruct (List.nth_error (tele_insts (cargs_ctx p D Mk0 gs) (sb_of_list Id Us) As) j) as [T |] eqn:HT;
          [| exists V; split; [ apply nf_eq_upto_proofs_of_eq; reflexivity | intros; discriminate ] ].
        enough (HV' : glu_nf_eq Γ N V T).
        { destruct HV' as (V' & EV & HV'); exists V'; split; [ exact EV |].
          intros N0 T0 HN0 HT0; injection HN0 as <-; injection HT0 as <-; exact HV'. }
      assert (Hj : j < length gs) by (rewrite <- HArl; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' gs j Hj) as [g Hg].
      destruct (List.nth_error_split gs j Hg) as (gs1 & gs2 & Heq0 & Hlg).
      subst j.
      destruct (nth_error_lt_some' vs (length gs1) ltac:(lia)) as [v Hv0].
      assert (Hpl : List.length (List.firstn (length gs1) vs) = length gs1) by (rewrite List.length_firstn; lia).
      (** The view has no non-uniform parameters: the fields' environment
          is the group's own. *)
      assert (Eρ : components_env D ups (List.rev (im_nparams Mk0) ++ cargs_nonrec_tele gs1)
                     (nil ++ nonrec_arg_vals gs1 (List.firstn (length gs1) vs))
                   = env_tele (decl_env D ups) (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (length gs1) vs)))
        by (rewrite components_env_nparams_args by exact Hxl0; reflexivity).
      destruct g as [r0 A0 | Pr].
      + (** A non-recursive field reads back by its gluing. *)
        assert (HK : length (cargs_nonrec gs1) < length (cargs_nonrec gs))
          by (rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia).
        assert (HA0' : List.nth_error (cargs_nonrec gs) (length (cargs_nonrec gs1)) = Some A0)
          by (rewrite Heq0, cargs_nonrec_app, List.nth_error_app2 by lia;
              replace (length (cargs_nonrec gs1) - length (cargs_nonrec gs1)) with 0 by lia; reflexivity).
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        destruct (HeA _ _ _ _ _ _ _ _ HMk0 Hn0 Hc HA0' Hpre) as [b Eb].
        pose proof (HgA _ _ _ _ _ _ _ _ _ HMk0 Hn0 Hc HA0' Hpre Eb) as Hgb.
        destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
        pose proof (nonrec_nth_arg _ _ _ _ _ _ _ Heq0 Hvl Hv0) as Hn1.
        pose proof Har as Hv'; rewrite tele_rel_iff in Hv'; destruct Hv' as (_ & _ & Hvr).
        pose proof (Hvr _ _ _ Hn1 Hn1) as Hvv0.
        rewrite (nonrec_firstn _ _ _ _ _ Heq0 Hvl) in Hvv0.
        pose proof Hvv0 as Hvv.
        unfold ar, canon_args_rel in Hvv;
          rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMk0 Hc HA0'), (member_nparams_eq _ _ _ HMk0), (member_con_tele_eq _ _ _ _ _ HMk0 Hc) in Hvv.
        pose proof (per_head_iff Eb Eb HRb) as HRh.
        assert (Hvv' : Rb v v) by (apply HRh; exact Hvv).
        pose proof (HtA _ _ _ _ _ _ _ _ _ HMk0 Hn0 Hc HA0' Hpre Eb _ _ _ _ _ Hgb (Harg _ _ _ _ _ _ _ Heq0 HN HT Hv0) HRb Hvv')
          as Htop.
        destruct Htop as [P' El' _ _ _ _ Hrbt].
        destruct (HArg _ _ _ _ _ Heq0 Hv0) as (a & V' & Ea & HRa & HnV).
        assert (V' = V) as -> by congruence.
        destruct (HevAr _ _ _ _ _ _ _ _ _ _ HMk0 Hn0 Hc HA0' Hpre) as [a0 a1 Ea0 Ea1 Ha01].
        (** The field's type reads only the telescope before it. *)
        pose proof (components_env_args_prefix D ups Mk0 gs1 (ca_arg r0 A0 :: gs2) nil _ Hxl0 Hpl) as Epre.
        rewrite <- Heq0 in Epre; rewrite Epre, Eρ in Ea1.
        assert (a0 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (per_elem_then_per_top Ha01 Hvv0) as Htp.
        destruct (Htp (length Γ)) as [W1 W2 HW1 HW2 EW].
        pose proof (functional_read_nf _ _ _ _ HW2 HRa) as ->.
        pose proof (Hrbt Γ wk_id W1 Hid HW1) as Heqn.
        rewrite !exp_wk_id in Heqn.
        exact (glu_nf_eq_upto _ _ _ _ _ EW Heqn).
      + (** A recursive field, by induction on its shape. *)
        destruct (HArec _ _ _ _ Heq0 Hv0) as (V' & HRV & HnV).
        assert (V' = V) as -> by congruence.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        pose proof (con_args_rel_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia _ _ _ _ _ Heq0 Hv0 Hv0) as Hsh0.
        assert (HTf : exists σ', T = ptyp_ty_at p D Us σ' Pr).
        { eexists; rewrite (cargs_rec_type_at p D Mk0 gs gs1 Pr gs2 Us As T Heq0 Hdc
                              ltac:(unfold im_np, im_nn; rewrite Hnp0; cbn; lia) HT).
          rewrite <- HUl, List.firstn_all; reflexivity. }
        eapply (IHrec _ _ _ _ _ _ Heq0 HN HT Hv0 HΓ (Htyp _ _ _ HN HT) HTf Mk0 nil nil c gs1 Pr gs2
                  (nonrec_arg_vals gs1 (List.firstn (length gs1) vs)) 0 nil);
          [ exact HMk0 | rewrite List.app_nil_r; reflexivity | rewrite Hnp0; cbn [List.firstn List.rev List.app]; rewrite List.app_nil_r; reflexivity
          | exact Hn0 | rewrite <- Heq0; exact Hc | exact Hpre | reflexivity
          | lia | apply tele_prefix_rel_nil | exact Hsh0 | exact HUl
          | rewrite !List.app_nil_r, List.app_nil_l; exact HRV ]. }
      (** The view's constructor at the uniform parameters and the fields
          so chosen *)
      destruct (list_choice_nth _ Args Hpw) as (Args' & HlA' & HA').
      exists (nf_con p k' c (PN' ++ Args')); split.
      { apply nf_con_upto_proofs, nfs_eq_upto_proofs_app; [ exact EPN |].
        apply nfs_eq_upto_proofs_of_nth; [ symmetry; exact HlA' | intros j V V' HV HV'; exact (proj1 (HA' _ _ _ HV HV')) ]. }
      cbn [nf_annotate_proofs nf_to_exp]; rewrite !List.map_app.
      etransitivity; [ exact Heq |].
      replace (im_ty_at p k' Mk0 Us nil) with (ind_mty p D k' (List.firstn (ind_nu D) Us) (List.skipn (ind_nu D) Us))
        by (unfold ind_mty; rewrite HMk0, <- HUl, List.firstn_all, List.skipn_all; reflexivity).
      eapply wf_exp_eq_con_apps_member; [ exact Hl | exact HMk0 | exact Hc | exact HΓ | unfold im_np, im_nn; rewrite Hnp0; cbn; lia
                                        | rewrite <- HlN; unfold im_np, im_nn; rewrite Hnp0; cbn; lia
                                        | rewrite HPeq; exact HPcN | exact HAl | rewrite !List.length_map; lia |].
      intros j N N' T HN HN' HT.
      rewrite !List.nth_error_map in HN'.
      destruct (List.nth_error Args' j) as [V' |] eqn:HV'; cbn in HN'; [| discriminate HN' ]; injection HN' as <-.
      assert (Hj : j < length Args) by (rewrite <- HlA'; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' Args j Hj) as [V HV].
      exact (proj2 (HA' _ _ _ HV HV') _ _ HN HT).
    - (** The end of a shape: the element read back at the parameters the
          shape evaluates to at the type's prefix, related to those at the
          element's own by the admissibility of [ups] beside itself. *)
      intros j Mj Ps Ts pre A Us Γ N x k' HMj Hc1 Hc2 IH2 HΓ HN HAf Mk' xs ms c0 gs1 t0 gs2 ws k1 ys HMk' Hpre HTs Hx Hc Hw Hsk
        Hk Hy Hsh HUl V HV.
      inversion HV; subst.
      match goal with Hbs : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs0 |- _ => rename Hbs into Ebt; rename bs0 into bT end.
      match goal with HR0 : Rnf ⇓ (d_ind p j (ups ++ bT)) x in _ ⍮ _ ⍮ _ ↘ V |- _ => rename HR0 into HRV end.
      destruct (ptyp_skip_self _ _ _ _ Hsk) as (HkL & Hj & HPs).
      (** At the end of the shape, the telescope is all of its domains. *)
      rewrite shape_doms_tele_firstn_all in Ebt, Hc1, IH2, Hsh by exact HkL.
      assert (Hk1 : k1 = List.length (ptyp_doms t0)) by lia.
      assert (Hys : tele_rel (shape_doms_rel (dr k') (List.rev (im_nparams Mk')) (cargs_nonrec_tele gs1) ms ws t0)
                      (ptyp_doms t0) ys ys)
        by (apply tele_rel_of_pre; rewrite <- Hk1; exact Hy).
      destruct HAf as (σ' & HA); cbn [ptyp_ty_at] in HA; unfold ind_mty in HA; rewrite HMj in HA.
      destruct (adm_rec_params _ _ _ _ _ _ Hcd k' Mk' ms xs c0 _ gs1 t0 gs2 ws ws ys ys HMk' (tsym _ _ HMk' _ _ Hx) Hc eq_refl Hw Hys)
        as [b0 bT' E0 ET R0T].
      rewrite HPs in E0, ET; rewrite Hj in R0T.
      pose proof (functional_eval_exps' _ _ _ _ ET Ebt) as ->.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs' & Ebs & Ebs' & _ & _ & Hvv).
      pose proof (functional_eval_exps' _ _ _ _ Ebs E0) as ->; pose proof (functional_eval_exps' _ _ _ _ Ebs' E0) as ->.
      unfold nparams_tele_rel in R0T; rewrite HMj in R0T.
      destruct (Hc1 _ _ E0 HA) as (HQl & _ & Hgn).
      destruct (Hgn _ R0T) as [_ HQt].
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      pose proof (HQt Γ wk_id Hid) as Hpt0; rewrite map_wk_id_exp in Hpt0.
      pose proof (IH2 _ _ E0 HA Γ wk_id Us _ Hid HUl ltac:(rewrite map_wk_id_exp; exact (glu_params_top_refl _ _ _ _ _ Hpt0))
                    HΓ Mj bT HMj Hpt0 (Hidx _ _ _ _ _ _ _ _ _ _ _ HMj Hvv R0T R0T) V HRV) as Heqn.
      rewrite exp_wk_id in Heqn; rewrite HA; exact Heqn.
    - (** A domain of a shape: the function η-expanded, its body read back
          at a fresh variable of the domain. *)
      intros A Γ k' pre Ts B x Us t N Hd He Hg IH HΓ HN HAf Mk' xs ms c0 gs1 t0 gs2 ws k1 ys HMk' Hpre HTs Hx Hc Hw Hsk Hk Hy
        Hsh HUl V HRV.
      subst pre Ts.
      inversion HRV; subst.
      match goal with Eb : ⟦ B ⟧ components_env _ _ _ _ ↘ ?b0 |- _ => rename Eb into Ebt; rename b0 into bt end.
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
      (** The lengths of the components before the domain *)
      assert (Hxl : List.length xs = List.length (im_nparams Mk'))
        by (pose proof Hx as Hxl; rewrite tele_rel_iff in Hxl; destruct Hxl as (Hxl & _ & _); rewrite List.length_rev in Hxl; exact Hxl).
      assert (Hwl : List.length ws = List.length (cargs_nonrec gs1))
        by (pose proof Hw as Hwl; rewrite tele_prefix_rel_iff in Hwl; destruct Hwl as (Hwl & _ & _); exact Hwl).
      assert (Hyl : List.length ys = k1)
        by (pose proof Hy as Hyl; rewrite tele_prefix_rel_iff in Hyl; destruct Hyl as (Hyl & _ & _); exact Hyl).
      (** The domain's type reads only the domains before it. *)
      rewrite components_env_shape_prefix in Ea1 by (assumption || lia).
      rewrite Hyl in Ea1.
      pose proof (functional_eval_exp _ _ _ _ Ea0 Ebg) as ->; pose proof (functional_eval_exp _ _ _ _ Ea1 Ebt) as ->.
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      match type of HA with _ = a_pi _ _ ?IT0 ?OT0 => set (IT := IT0) in *; set (OT := OT0) in * end.
      assert (HNpi : Γ ⊢ N : Π{ak_relevant} IT OT) by (rewrite <- HA; exact HN).
      (** The domain and the codomain are types of a large universe. *)
      assert (HPI : exists j, Γ ⊢ IT : Typeω@j /\ Γ ▹{ak_relevant} IT ⊢ OT : Typeω@j).
      { assert (HP0 : exists S, Γ ⊢ Π{ak_relevant} IT OT : S) by (gen_presups; eauto).
        destruct HP0 as [S HP0].
        destruct (wf_pi_inversion HP0) as [(j & HITj & HOTj & _) | (L & n & HL & HITj & HOTj & _)];
          cbn [abs_kind_sort] in HITj.
        - exists j; split; assumption.
        - assert (HΓIT : ⊢ Γ ▹{ak_relevant} IT) by mauto 3.
          exists 0; split; [ eapply wf_exp_suniv_large; eassumption |].
          eapply wf_exp_suniv_large; [| exact HOTj ]; mauto 3. }
      destruct HPI as (j & HITj & HOTj).
      (** The domain reads back as the type of the fresh variable; it is
          relevant, and not [LevelSort], as the domain of a [Π] over a
          universe. *)
      pose proof (Hd _ _ HA Γ wk_id Hid) as HITg; rewrite exp_wk_id in HITg.
      destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant _ Hgbg HITg HITj) as [Hkg Hng].
      destruct (glu_univ_elem_per_univ _ _ _ _ Hgbg) as [Rg HRg].
      destruct (HrT Γ IT Rg HRg Hng HITg) as [_ _ HITrb].
      destruct (per_univ_then_per_top_typ Ha01 (length Γ)) as [T1 T2 HT1 HT2 ET].
      pose proof (functional_read_typ _ _ _ _ HT2 HRT) as ->.
      pose proof (glu_nf_eq_upto _ _ _ _ _ ET (HITrb Γ wk_id T1 Hid HT1)) as HITeq.
      rewrite exp_wk_id, Hkg in HITeq; cbn [abs_kind_sort] in HITeq.
      destruct HITeq as (A'' & EA & HITeq).
      (** The fresh variable, glued at the domain. *)
      set (c := ⇑! bt (length Γ)).
      assert (HΓIT : ⊢ Γ ▹{ak_relevant} IT) by mauto 3.
      assert (Hwk : Γ ▹{ak_relevant} IT ⊢ᵏ ↑ : Γ) by mauto 3.
      pose proof (var_glu_elem_bot _ _ _ _ _ _ Hgbg Hng HITg) as Hvg0; rewrite Hkg in Hvg0.
      pose proof (HrB _ _ _ _ Hvg0) as Hvg.
      pose proof (var_per_elem (length Γ) Ha01 Hng) as Hcc0.
      assert (ERg : dr k' (ms ++ ws ++ ys) (List.rev (im_nparams Mk') ++ cargs_nonrec_tele gs1 ++ List.firstn k1 (shape_doms_tele t0)) B
                    <~> Rg) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (Hvc : Γ ▹{ak_relevant} IT ⊢ #0 : IT[↑]ʷ ® c
                      ∈ DEl k' (ms ++ ws ++ ys) (List.rev (im_nparams Mk') ++ cargs_nonrec_tele gs1 ++ List.firstn k1 (shape_doms_tele t0)) B)
        by (eapply glu_univ_elem_trm_resp_per_elem; [ exact Hgbg | exact HRg | exact Hvg | apply ERg; exact Hcc0 ]).
      assert (Hcc : dr k' (ms ++ ws ++ ys) (List.rev (im_nparams Mk') ++ cargs_nonrec_tele gs1 ++ List.firstn k1 (shape_doms_tele t0)) B c c)
        by (etransitivity; [ symmetry |]; exact Hcc0).
      (** The rest of the shape, at the variable. *)
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hcc) as (r & r' & Er & Er' & Hsh').
      pose proof (functional_eval_app _ _ _ _ Er Hvapp) as ->.
      pose proof (functional_eval_app _ _ _ _ Er' Hvapp) as ->.
      assert (HNw : Γ ▹{ak_relevant} IT ⊢ N[↑]ʷ : Π{ak_relevant} IT[↑]ʷ OT[wk_q ↑]ʷ) by (rewrite <- exp_wk_pi; mauto 3).
      assert (HNapp : Γ ▹{ak_relevant} IT ⊢ N[↑]ʷ $ #0 : OT[(ι ↑),,#0])
        by (rewrite <- exp_sub_wk_q_extend; eapply wf_app'; [ exact HNw | mauto 3 ]).
      assert (HOTf : exists σ'', OT[(ι ↑),,#0] = ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us) σ'' t).
      { eexists; unfold OT; rewrite ptyp_ty_at_sub by (try exact Hdc; rewrite List.length_map; exact HUl).
        f_equal; rewrite List.map_map; apply List.map_ext; intros U; apply exp_shift_extend_wk. }
      (** The body's environment: the domains so far and the variable *)
      assert (Ecod'' : Rsh r0 at t of p ups in gc_deps ⍮ gc_stack
                         ⍮ components_env D ups
                             ((List.rev (im_nparams Mk') ++ cargs_nonrec_tele gs1 ++ List.firstn k1 (shape_doms_tele t0))
                                ++ ce_ass ak_relevant B :: nil)
                             (xs ++ ws ++ ys ++ c :: nil)
                         ⍮ length (Γ ▹{ak_relevant} IT) ↘ V0).
      { replace (xs ++ ws ++ ys ++ c :: nil) with ((xs ++ ws ++ ys) ++ c :: nil) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite components_env_snoc
          by (rewrite !List.length_app, List.length_rev, List.length_firstn, length_cargs_nonrec_tele; unfold shape_doms_tele;
              rewrite List.length_map; lia).
        exact HRM. }
      pose proof (IH _ _ HA (Γ ▹{ak_relevant} IT) ↑ #0 c r0 Hwk Hcc Hvc Hvapp HΓIT HNapp HOTf Mk' xs ms c0 gs1 t0 gs2 ws (S k1) (ys ++ c :: nil)
                    HMk' ltac:(rewrite <- !List.app_assoc; reflexivity) ltac:(apply prefix_tele_snoc_dom; exact HB)
                    Hx Hc Hw Hs' Hk' (Hstep _ _ Hcc)
                    Hsh' ltac:(rewrite List.length_map; exact HUl) V0 Ecod'')
        as (V0' & EV0 & Hbody).
      assert (HOT : Γ ▹{ak_relevant} IT ⊢ OT[(ι ↑),,#0] ≈ OT : Typeω@j).
      { pose proof (kripke_q_var_eq Γ Γ ak_relevant IT (Typeω@j) OT wk_id (Typeω@j) HOTj HITj ltac:(constructor) Hid) as H.
        rewrite exp_wk_id in H; rewrite (exp_wk_id_ext OT _ wk_q_id) in H; cbn in H; exact H. }
      (** The function, η-long *)
      exists (λⁿ A'' V0'); split; [ apply nf_fn_upto_proofs; assumption |].
      rewrite HA; cbn [nf_annotate_proofs nf_to_exp].
      etransitivity; [ eapply wf_exp_eq_fn_eta'; exact HNpi |].
      eapply wf_exp_eq_fn_cong'; [ exact HITeq | constructor | exact HOTj | constructor
                                 | eapply wf_exp_eq_conv'; [ exact Hbody | exact HOT ] ].
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
    eapply glu_nf_eq_conv with (κ := ak_relevant) (i := large_level i); [| exact Hrb ]; cbn [abs_kind_sort].
    rewrite <- wk_apps_ind; symmetry; mauto 3.
  Qed.
End IndRealize.

(** ** Record Types

    A type of a record type reads back as the type former at the readback
    of its parameters.  A neutral is glued by its neutral projections, each
    a neutral of its field's type, field by field.  An element reads back
    as the tuple of the readbacks of its projections, equal to it by η, at
    the readback of its parameters. *)
(** The fields of a record read back position by position: the readback
    of each, at its type in the environment of the projections before
    it. *)
Lemma read_fields_nth_nf : forall s ρ fl v Fs, Rflds v at fl in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Fs ->
    forall vs, List.Forall2 (fun fT r => eval_proj gc_deps gc_stack (fst fT) v r) fl vs ->
    List.length Fs = List.length fl /\
    forall κs j g T r, List.nth_error fl j = Some (g, T) -> List.nth_error vs j = Some r ->
      exists t F, ⟦ T ⟧ env_tele ρ (fields_tele_in_order fl κs) (List.firstn j vs) ↘ t /\
        Rnf ⇓ t r in gc_deps ⍮ gc_stack ⍮ s ↘ F /\ List.nth_error Fs j = Some F.
Proof.
  induction 1 as [| f v r T ρ t s F fl Fs Hp Et HF HFs IH]; intros vs Hvs.
  - inversion Hvs; subst; split; [ reflexivity |]; intros κs [| j]; discriminate.
  - inversion Hvs as [| ? r' ? vs' Hr' Hvs']; subst; cbn [fst] in Hr'.
    pose proof (functional_eval_proj _ _ _ _ Hp Hr') as <-.
    destruct (IH vs' Hvs') as [Hl IHn].
    split; [ cbn; congruence |].
    intros κs [| j] g U r0 Hj Hr0; cbn in Hj, Hr0.
    + injection Hj as <- <-; injection Hr0 as <-; exists t, F; split; [| split; [ exact HF | reflexivity ] ].
      exact Et.
    + destruct (IHn (List.tl κs) _ _ _ _ Hj Hr0) as (t' & F' & Et' & HF' & HnF); exists t', F'; split; [| split; [ exact HF' | exact HnF ] ].
      exact Et'.
Qed.

Section RecordRealize.
  Variables (i : universe_index) (p : qname) (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
    (elem_rel : relation domain) (P : glu_typ_pred) (El : glu_exp_pred).
  Hypothesis (Hl : record_lookup gc_deps gc_stack p = Some R)
    (Hper : DF d_record p ns ≈ d_record p ns ∈ per_univ_elem i ↘ elem_rel)
    (HgF : forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ record_fields_env R ns vs ↘ b ->
       DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs)
    (HrF : forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ record_fields_env R ns vs ↘ b ->
       (forall Γ A R0, DF b ≈ b ∈ per_univ_elem i ↘ R0 -> not_level_sort b -> Γ ⊢ A ® FP k vs -> Γ ⊢ A ® glu_typ_top i b) /\
       (forall Γ M A m, DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs ->
          Γ ⊢ M : A ® m ∈ glu_elem_bot i b -> Γ ⊢ M : A ® ⇑ b m ∈ FEl k vs) /\
       (forall Γ M A m R0, DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs ->
          Γ ⊢ M : A ® m ∈ FEl k vs -> DF b ≈ b ∈ per_univ_elem i ↘ R0 -> Dom m ≈ m ∈ R0 ->
          Γ ⊢ M : A ® m ∈ glu_elem_top i b))
    (HP : P <∙> record_glu_typ_pred p R ns FP FEl (Typeω@(large_level i)))
    (HEl : El <∙> record_glu_exp_pred p R ns FP FEl elem_rel (Typeω@(large_level i))).

  (** A type at syntactic parameters, at a weakening: equal to the type
      former at them, which are typed at its telescope, its sort in the
      ambient universe. *)
  Lemma record_typ_at_facts : forall Γ A Ns Δ φ, record_typ_at p R ns FP FEl (Typeω@(large_level i)) Γ A Ns -> Δ ⊢ᵏ φ : Γ ->
      Δ ⊢ A[φ]ʷ ≈ apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns) : Typeω@(large_level i) /\
      Δ ⊢ a_record p : record_ty R /\
      List.length (List.map (fun N => N[φ]ʷ) Ns) = List.length (record_params R) /\
      (forall j N A0, List.nth_error (List.map (fun N => N[φ]ʷ) Ns) j = Some N ->
         List.nth_error (tele_insts (record_params R) Id (List.map (fun N => N[φ]ʷ) Ns)) j = Some A0 -> Δ ⊢ N : A0) /\
      Δ ⊢ (record_sort R)[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns)] ⊆ Typeω@(large_level i).
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
    econstructor; [ cbn [domain_kind abs_kind_sort]; destruct HNs as [HA _]; gen_presups; assumption
                  | exact (per_univ_then_per_top_typ Hper) |].
    intros Δ φ A' Hφ Hr.
    inversion Hr; subst.
    match goal with H : record_lookup _ _ p = Some ?R1 |- _ => assert (R1 = R) as -> by congruence end.
    destruct (record_typ_at_facts _ _ _ _ _ HNs Hφ) as (HAφ & Hrt & HNl & HNt & HS).
    pose proof HNs as [_ Hwk]; destruct (Hwk Δ φ Hφ) as [[_ _ HPr] _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ms |- _ => pose proof (HPr Δ wk_id Ms Hid H) as HMs end.
    rewrite map_wk_id_exp in HMs.
    (** The parameters read back up to proofs, annotated *)
    destruct HMs as (Ms' & EMs & HMl & HMs).
    exists (nf_record p Ms'); split.
    { unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs]; rewrite dec_eqb_refl; exact EMs. }
    cbn [domain_kind abs_kind_sort nf_annotate_proofs nf_to_exp]; etransitivity; [ exact HAφ |].
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
    assert (Hrel : Dom ⇑ (d_record p ns) m ≈ ⇑ (d_record p ns) m ∈ elem_rel).
    { eapply per_bot_then_per_elem; [ eassumption |].
      exact Hm. }
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
    assert (Happs : Δ ⊢ apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns) ≈ apps_exp (a_record p) Ns' : Typeω@(large_level i))
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
    (** The field's type is of the sort of the field's kind: the type at
        the parameters of the type is ([record_field_params_cong]). *)
    assert (HTeq : Δ ⊢ T[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns ++ record_pre R k M[φ]ʷ)]
                     ≈ T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)]
                     : abs_kind_sort (record_field_kind R k) Typeω@(large_level i))
      by (eapply record_field_params_cong; [ exact HMφ | exact Hrt | exact Hl | exact HNl | exact HNl'' | exact HNt
                                            | exact HNN | exact HS | exact Hjf ]).
    pose proof (presup_exp_eq_right HTeq) as HTw.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hga HTP HTw) as [Hka Hna].
    assert (HfK : field_kind (record_field_kind R k)).
    { destruct (wf_record_inversion Hrt);
        match goal with H : record_lookup _ _ p = Some ?R1, Hk : forall k, field_kind (record_field_kind ?R1 k) |- _ =>
          rewrite Hl in H; injection H as <-; apply Hk end. }
    apply HrB; [ exact Hga |].
    assert (Hp : Δ ⊢ a_proj f M[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)])
      by (eapply wf_proj; [ exact HMb | exact Hrt | exact Hl | exact HNl'' | exact HNt' | exact Hjf | exact HTw
                          | apply type_sort_abs_kind; constructor ]).
    econstructor; [ exact Hp | exact Hga | exact HTP | |].
    - (** The projection is a neutral of the field's type, which is not
          [LevelSort] and not a type of levels ([field_kind]) *)
      apply per_bot_neutral_at; [ exact Hna | rewrite Hka; apply field_kind_not_level; exact HfK |].
      intros s; destruct (proj1 (proj2 Hm) s) as [W1 W2 H1 H2 E]; econstructor;
        [ constructor; exact H1 | constructor; exact H2 | apply ne_proj_upto_proofs; exact E ].
    - (** The readback: the projection of the readback of the neutral, at
          the field's type at the parameters of the weakening. *)
      intros Δ' φ' W Hφ' HW.
      inversion HW; subst.
      match goal with H : Rne m in _ ↘ ?W0 |- _ => rename H into HW0; rename W0 into W1 end.
      pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hc'.
      destruct (Hrb _ _ _ Hc' HW0) as (W1' & EW & HMW).
      exists (ne_proj f W1'); split; [ apply ne_proj_upto_proofs; exact EW |].
      cbn [ne_annotate_proofs ne_to_exp].
      destruct (record_typ_at_facts _ _ _ _ _ HNs Hc') as (HAd & Hrt' & HNld & HNtd & HSd).
      assert (HMW' : Δ' ⊢ M[φ ⊙ φ']ʷ ≈ ne_annotate_proofs W1' : apps_exp (a_record p) (List.map (fun N => N[φ ⊙ φ']ʷ) Ns))
        by (eapply wf_exp_eq_conv'; [ exact HMW | exact HAd ]).
      destruct (record_proj_cong_at _ _ _ _ _ p R _ (large_level i) k f T HMW' Hrt' Hl HNld HNtd HSd Hjf) as [_ Hpp].
      assert (HTeq' : Δ' ⊢ T[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns ++ record_pre R k M[φ]ʷ)][φ']ʷ
                        ≈ T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)][φ']ʷ
                        : abs_kind_sort (record_field_kind R k) Typeω@(large_level i))
        by (eapply kripke_preserves_kind_sort_eq; eassumption).
      assert (HLk : List.length (record_pre R k M[φ]ʷ) = k) by (apply length_record_pre; lia).
      rewrite (record_field_wk R k f T (List.map (fun N => N[φ]ʷ) Ns) (record_pre R k M[φ]ʷ) φ' Hc Hjf HNl HLk) in HTeq'.
      rewrite (record_field_wk R k f T Ns' (record_pre R k M[φ]ʷ) φ' Hc Hjf HNl'' HLk) in HTeq'.
      rewrite (record_field_wk R k f T Ns' (record_pre R k M[φ]ʷ) φ' Hc Hjf HNl'' HLk).
      rewrite !record_pre_wk, map_wk_wk, exp_wk_wk in HTeq'.
      rewrite record_pre_wk, exp_wk_wk.
      replace ((a_proj f M[φ]ʷ)[φ']ʷ) with (a_proj f M[φ ⊙ φ']ʷ) by (cbn [exp_wk]; rewrite exp_wk_wk; reflexivity).
      eapply wf_exp_eq_conv_kind; [ exact Hpp | exact HTeq' ].
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
    inversion Hw; subst;
      (** a proof: no record type is a proposition *)
      try (match goal with H : domain_kind (d_record _ _) = _ |- _ => cbn in H; discriminate H end).
    match goal with H : record_lookup _ _ p = Some ?R1 |- _ => assert (R1 = R) as -> by congruence end.
    match goal with H1 : Rps ns at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ps0, H2 : Rflds m at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Fs0 |- _ =>
      rename H1 into HRps; rename H2 into HRf; rename Ps0 into Ps; rename Fs0 into Fs end.
    destruct (record_typ_at_facts _ _ _ _ _ HNs Hφ) as (HAφ & Hrt & HNl & HNt & HS).
    pose proof HNs as [_ Hwk]; destruct (Hwk Δ φ Hφ) as [[_ _ HPr] _ _].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    pose proof (HPr Δ wk_id Ps Hid HRps) as HPs; rewrite map_wk_id_exp in HPs; destruct HPs as (Ps' & EPs & HPl & HPs).
    assert (HMφ : Δ ⊢ M[φ]ʷ : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)) by (eapply wf_conv'; [ mauto 3 | exact HAφ ]).
    assert (HT : Δ ⊢ apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns) : Typeω@(large_level i)) by (gen_presups; eassumption).
    pose proof (wf_record_eta_tuple _ _ _ _ _ _ _ _ HMφ Hrt Hl HNl HNt HS HT) as Hetat.
    assert (Heta : Δ ⊢ M[φ]ʷ ≈ a_tuple (apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)) (record_eta_fields R M[φ]ʷ)
                     : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns))
      by (eapply wf_exp_eq_record_eta; [ exact HMφ | exact Hl | exact HNl | exact Hetat ]).
    destruct (read_fields_nth_nf _ _ _ _ _ HRf vs Hvs) as [HFl HFn].
    assert (Hlv : List.length vs = List.length (record_fields R)) by (symmetry; exact (List.Forall2_length Hvs)).
    assert (HNdrefl : exps_eq_at Δ (record_params R) (List.map (fun N => N[φ]ʷ) Ns) (List.map (fun N => N[φ]ʷ) Ns)).
    { split; [ reflexivity |].
      intros k X Y A0 HX HY HA0; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; exact (HNt _ _ _ HX HA0). }
    (** Each field reads back, up to proofs, as a normal form equal to its
        projection, at its type: by the realisability of the type. *)
    assert (Hfw : forall k F, List.nth_error Fs k = Some F -> exists F', nf_eq_upto_proofs F F' /\
               forall f U, List.nth_error (record_fields R) k = Some (f, U) ->
                 Δ ⊢ a_proj f M[φ]ʷ ≈ nf_annotate_proofs F'
                   : U[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns ++ record_pre R k M[φ]ʷ)]).
    { intros k F HF0.
      assert (Hlt : k < List.length (record_fields R)) by (rewrite <- HFl; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' (record_fields R) k Hlt) as [[f U] Hfk].
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [r Hr].
      destruct (HFn (record_field_kinds R) _ _ _ _ Hfk Hr) as (t & F0 & Et & HF & HnF).
      rewrite HF0 in HnF; injection HnF as <-.
      assert (Et' : ⟦ U ⟧ record_fields_env R ns (List.firstn k vs) ↘ t)
        by (unfold record_fields_env, record_fields_tele; rewrite rev_fields_tele; exact Et).
      pose proof (record_projs_prefix_diag _ _ _ _ k Hrr Hvs ltac:(lia)) as Hpre.
      pose proof (HgF _ _ _ _ _ Hfk Hpre Et') as Hgt.
      destruct (HrF _ _ _ _ _ Hfk Hpre Et') as (_ & _ & HrT).
      destruct (glu_univ_elem_per_univ _ _ _ _ Hgt) as [Rt HRt].
      assert (Hrr' : Dom r ≈ r ∈ Rt).
      { destruct Hrr as [vs1 vs2 Hv1 Hv2 Hrel].
        pose proof (record_projs_functional _ _ _ _ Hv1 Hvs) as ->; pose proof (record_projs_functional _ _ _ _ Hv2 Hvs) as ->.
        rewrite tele_rel_iff in Hrel; destruct Hrel as (_ & _ & Hrel).
        pose proof (Hrel _ _ _ Hr Hr) as Hrk; unfold canon_fields_rel in Hrk; rewrite (nth_ftyp_eq _ _ _ _ Hfk) in Hrk.
        exact (proj2 (per_head_iff Et' Et' HRt _ _) Hrk). }
      pose proof (Hk Δ φ (List.map (fun N => N[φ]ʷ) Ns) Hφ HNdrefl k f U r Hfk Hr) as Hgl.
      destruct (HrT _ _ _ _ _ Hgt Hgl HRt Hrr') as [_ _ _ _ _ _ Hrbt].
      pose proof (Hrbt Δ wk_id F Hid HF) as Heq; rewrite !exp_wk_id in Heq.
      destruct Heq as (F' & HEF & Heq); exists F'; split; [ exact HEF |].
      intros f' U' Hfk'; rewrite Hfk in Hfk'; injection Hfk' as <- <-; exact Heq. }
    (** The tuple at the parameters and the fields so chosen *)
    destruct (list_choice_nth _ Fs Hfw) as (Fs' & HlF' & HFc).
    exists (nf_tuple p Ps' (List.map fst (record_fields R)) Fs'); split.
    { apply nf_tuple_upto_proofs; [ exact EPs |].
      apply nfs_eq_upto_proofs_of_nth; [ symmetry; exact HlF' | intros j F F' HFj HFj'; exact (proj1 (HFc _ _ _ HFj HFj')) ]. }
    cbn [nf_annotate_proofs nf_to_exp].
    assert (Htc : Δ ⊢ a_tuple (apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)) (record_eta_fields R M[φ]ʷ)
                    ≈ a_tuple (apps_exp (a_record p) (List.map nf_to_exp (List.map nf_annotate_proofs Ps')))
                        (List.combine (List.map fst (record_fields R)) (List.map nf_to_exp (List.map nf_annotate_proofs Fs')))
                    : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)).
    { eapply wf_exp_eq_tuple_fields;
        [ exact Hetat | exact Hrt | exact Hl | exact HNl | rewrite <- HPl; exact HNl | exact HPs | exact HS
        | apply record_eta_fields_names
        | rewrite record_eta_fields_names; apply map_fst_combine; rewrite !List.length_map; lia |].
      intros k f M1 M1' U Hk1 Hk1' Hfk.
      rewrite (record_eta_fields_nth _ _ _ _ _ Hfk) in Hk1; injection Hk1 as <-.
      rewrite record_eta_fields_pre.
      assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      destruct (nth_error_lt_some' Fs' k ltac:(lia)) as [F' HF'k].
      destruct (nth_error_lt_some' Fs k ltac:(lia)) as [F HFk].
      assert (M1' = nf_to_exp (nf_annotate_proofs F')) as ->.
      { pose proof (nth_error_combine_both (List.map fst (record_fields R)) (List.map nf_to_exp (List.map nf_annotate_proofs Fs'))
                      k f (nf_to_exp (nf_annotate_proofs F'))
                      ltac:(rewrite List.nth_error_map, Hfk; reflexivity)
                      ltac:(rewrite !List.nth_error_map, HF'k; reflexivity)) as E.
        rewrite E in Hk1'; injection Hk1' as <-; reflexivity. }
      exact (proj2 (HFc _ _ _ HFk HF'k) _ _ Hfk). }
    eapply wf_exp_eq_conv'; [ etransitivity; [ exact Heta | exact Htc ] | symmetry; exact HAφ ].
  Qed.
End RecordRealize.

Theorem realize_glu_univ_elem_gen : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    (forall Γ A R,
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        (** [LevelSort] is of no sort ([level_sort_untyped]) *)
        not_level_sort a ->
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
  10:{ (** A record type. *)
      split; [| split]; intros.
      - eapply record_realize_typ; eassumption.
      - eapply record_realize_bot; eassumption.
      - match goal with H : _ <∙> record_glu_exp_pred _ _ _ _ _ ?er _ |- _ =>
          eapply record_realize_top with (elem_rel := er); eassumption end. }
  9:{ (** An inductive type. *)
      split; [| split]; intros.
      - eapply ind_realize_typ; eassumption.
      - eapply ind_realize_bot; eassumption.
      - eapply ind_realize_top with (elem_rel := elem_rel); try eassumption.
        + intros * HM Hm Hc HA Hp Eb; exact (proj2 (proj2 (H10 _ _ _ _ _ _ _ _ _ HM Hm Hc HA Hp Eb))).
        + intros * HM Hm Hc Heq Hw HB Hy Eb.
          destruct (H13 _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy Eb) as (Ht & Hbt & _).
          split; [ exact Ht | intros; eapply Hbt; [ eapply H12; eassumption | eassumption ] ]. }
  (** A large universe: its types read back as themselves, its neutrals
      are neutral types of the index below, and its elements types glued
      there, relevant ones ([glu_univ_elem_typ_kind]). *)
  1:{ split; [| split ].
      - intros Γ A R HR _ HA; apply_equiv_left.
        econstructor; [ cbn [domain_kind abs_kind_sort]; gen_presups; eassumption | exact (per_univ_then_per_top_typ HR) |].
        intros Δ φ A' Hφ Hr; inversion Hr; subst.
        eexists; split; [ apply nf_eq_upto_proofs_of_eq; reflexivity |]; cbn; mauto 3.
      - intros Γ M A m Hglu [P' El' HM Hglu' HAP' Hm Hrb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
        pose proof (proj2 (HPP Γ A) HAP') as HA0; apply H0 in HA0; cbn in HA0.
        apply_equiv_left.
        econstructor; [ exact HM | exact HA0 |].
        econstructor; [ basic_glu_univ_elem_econstructor; [ reflexivity | exact (proj1 (proj2 Hm)) | reflexivity | reflexivity ] |].
        split; [ eapply wf_conv'; [ exact HM | exact HA0 ] |].
        intros Δ φ A' Hφ HA'.
        eapply glu_ne_eq_conv with (κ := ak_relevant); [| exact (Hrb _ _ _ Hφ HA') ]; cbn [abs_kind_sort]; mauto 3.
      - intros Γ M A m R Hglu HEl HR Hm.
        pose proof HEl as HEl'; apply H1 in HEl'; destruct HEl' as [HMt HAeq [P0 El0 Hg0 HM0]].
        assert (HMj : Γ ⊢ M : Typeω@j) by (eapply wf_conv'; eassumption).
        destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant _ Hg0 HM0 HMj) as [Hk Hn].
        econstructor; [ exact HMt | exact Hglu | apply H0; exact HAeq | eapply per_elem_then_per_top; eassumption |].
        intros Δ φ w Hφ Hw.
        inversion Hw; subst; try (cbn in *; discriminate).
        destruct (H _ _ _ Hg0) as (Htop & _ & _).
        destruct (glu_univ_elem_per_univ _ _ _ _ Hg0) as [R0 HR0].
        destruct (Htop _ _ _ HR0 Hn HM0) as [_ _ Hrd].
        match goal with Hr : Rtyp m in _ ↘ _ |- _ => pose proof (Hrd _ _ _ Hφ Hr) as Hg end.
        rewrite Hk in Hg; cbn [abs_kind_sort] in Hg.
        eapply glu_nf_eq_conv with (κ := ak_relevant); [| exact Hg ]; cbn [abs_kind_sort].
        symmetry; mauto 3. }
  (** A small universe: as a type it reads back as the universe at the
      canonical form of its level, which its glued level term is equal to,
      free of proofs; its neutrals are neutral types of the index below,
      lifted to a large universe by cumulativity; its elements carry their
      own readback clause. *)
  1:{ split; [| split ].
      - intros Γ A R HR _ HA; apply_equiv_left; destruct HA as [t n Hg HAt].
        econstructor; [ cbn [domain_kind abs_kind_sort]; gen_presups; eassumption | exact (per_univ_then_per_top_typ HR) |].
        intros Δ φ W Hφ Hr.
        assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
        inversion Hr; subst.
        match goal with HL : Rnf ⇓ Levelᵈ l in _ ↘ nf_lvl_of ?L0 |- _ => rename HL into HRL; rename L0 into L end.
        pose proof (glu_lvl_readback _ _ _ _ Hg _ _ _ Hφ HRL) as Ht.
        assert (HAφ : Δ ⊢ A[φ]ʷ ≈ Type⟨t[φ]ʷ⟩ : Typeω@(large_level i)) by mauto 3.
        apply glu_nf_eq_proof_free.
        + destruct (per_lvl_reads _ _ H (length Δ)) as (L' & HL' & _ & Hpf).
          pose proof (functional_read_nf _ _ _ _ HRL HL') as HeqL; rewrite <- HeqL in Hpf.
          destruct L; exact Hpf.
        + etransitivity; [ exact HAφ |].
          eapply wf_exp_eq_univ_cong_large_tm; [ assumption | gen_presups; eassumption | eassumption ].
      - intros Γ M A m Hglu [P' El' HM Hglu' HAP' Hm Hrb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
        pose proof (proj2 (HPP Γ A) HAP') as HA0; apply H1 in HA0.
        pose proof HA0 as [t n Hg HAt].
        apply_equiv_left.
        econstructor; [ exact HM | exact HA0 | |].
        + econstructor; [ basic_glu_univ_elem_econstructor; [ reflexivity | exact (proj1 (proj2 Hm)) | reflexivity | reflexivity ] |].
          split; [ eapply suniv_elem_large; eassumption |].
          intros Δ φ A' Hφ HA'.
          destruct (Hrb _ _ _ Hφ HA') as (W' & EW & HW); exists W'; split; [ exact EW |].
          eapply suniv_elem_eq_large; [ exact HW | mauto 3 ].
        + intros Δ φ W Hφ Hr; inversion Hr; subst.
          apply glu_nf_eq_neut; eauto.
      - intros Γ M A m R Hglu HEl HR Hm.
        pose proof HEl as HEl'; apply H2 in HEl'; destruct HEl' as [HMt HAs HMg Hrd].
        econstructor; [ exact HMt | exact Hglu | apply H1; exact HAs | eapply per_elem_then_per_top; eassumption |].
        intros Δ φ w Hφ Hw; inversion Hw; subst; try (cbn in *; discriminate); eauto. }
  (** [Level@n]: as a type it reads back as itself, at [LevelSort]; a
      neutral level, free of proofs ([neutral_at]), reads back as the atom
      of its sort; an element by its readback equation, free of proofs. *)
  1:{ split; [| split ].
      - intros Γ A R HR _ HA; apply_equiv_left.
        econstructor; [ cbn [domain_kind abs_kind_sort]; gen_presups; eassumption | exact (per_univ_then_per_top_typ HR) |].
        intros Δ φ A' Hφ Hr; inversion Hr; subst.
        apply glu_nf_eq_proof_free; [ exact I |]; cbn [domain_kind abs_kind_sort nf_to_exp]; mauto 3.
      - intros Γ M A m Hglu [P' El' HM Hglu' HAP' Hm Hrb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
        pose proof (proj2 (HPP Γ A) HAP') as HA0; apply H in HA0; cbn in HA0.
        apply_equiv_left.
        pose proof (per_bot_then_per_lvl_at n m m (proj2 Hm)) as Hpl.
        econstructor; [ exact HA0 | exact Hpl |].
        intros Δ φ L Hφ Hr.
        destruct (Hpl (length Δ)) as [L1 HL1 _ _ Hpf].
        pose proof (functional_read_nf _ _ _ _ HL1 Hr) as HeqL.
        inversion Hr; subst; [| cbn in *; discriminate ].
        (** The readback is free of proofs, so it is its own annotation *)
        match goal with H3 : _ = nf_lvl_of L1 |- _ => rewrite <- H3 in Hpf end; cbn in Hpf; destruct Hpf as [HM0f _].
        match goal with H6 : Rne m in _ ↘ ?M1 |- _ => destruct (Hrb _ _ _ Hφ H6) as (W' & EW & HW) end.
        pose proof (proj2 nf_ne_proof_free_eq _ HM0f _ EW) as <-.
        rewrite (proj2 nf_ne_annotate_proofs_proof_free _ HM0f) in HW.
        assert (HMeq : Δ ⊢ M[φ]ʷ ≈ M0 : Level@n)
          by (eapply wf_exp_eq_conv_kind with (κ := ak_level) (i := 0); [ exact HW | cbn; mauto 3 ]).
        split; [ exact HMeq |].
        cbn; split; [ lia | split; [ split; [ lia | gen_presups; eassumption ] | exact I ] ].
      - intros Γ M A m R Hglu HEl HR Hm.
        pose proof HEl as HEl'; apply H0 in HEl'; destruct HEl' as [HA Hpl Hg].
        assert (HAP : Γ ⊢ A ® P) by (apply H; exact HA).
        econstructor; [ | exact Hglu | exact HAP | eapply per_elem_then_per_top; eassumption |].
        + destruct (Hpl (length Γ)) as [L0 HL0 _ _ _].
          assert (Hid : Γ ⊢ᵏ wk_id : Γ) by (gen_presups; mauto 3).
          pose proof (glu_lvl_readback _ _ _ _ Hg _ _ _ Hid HL0) as HM0; rewrite exp_wk_id in HM0.
          eapply wf_conv_rel with (r := ak_level) (n := 0); [ exact (presup_exp_eq_left HM0) | cbn; symmetry; exact HA ].
        + intros Δ φ w Hφ Hw.
          destruct (Hpl (length Δ)) as [L1 HL1 _ _ Hpf].
          pose proof (read_nf_level_sort _ _ 0 _ _ Hw) as Hw0.
          pose proof (functional_read_nf _ _ _ _ HL1 Hw0) as <-.
          apply glu_nf_eq_proof_free; [ exact Hpf |].
          eapply wf_exp_eq_conv_kind with (κ := ak_level) (i := 0);
            [ eapply glu_lvl_readback; eassumption | cbn; symmetry; mauto 3 ]. }
  (** [Prop]: as a type it reads back as itself; a neutral of it is a
      neutral proposition; an element is glued as a proposition, by its
      readback at [Prop]. *)
  1:{ split; [| split ].
      - intros Γ A R HR _ HA; apply_equiv_left.
        econstructor; [ cbn [domain_kind abs_kind_sort]; gen_presups; eassumption | exact (per_univ_then_per_top_typ HR) |].
        intros Δ φ A' Hφ Hr; inversion Hr; subst.
        apply glu_nf_eq_proof_free; [ exact I |]; cbn [domain_kind abs_kind_sort nf_to_exp]; mauto 3.
      - intros Γ M A m Hglu [P' El' HM Hglu' HAP' Hm Hrb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
        pose proof (proj2 (HPP Γ A) HAP') as HA0; apply H in HA0; cbn in HA0.
        apply_equiv_left.
        econstructor; [ exact HA0 | exact HM | | split ].
        + constructor; [ reflexivity | reflexivity |].
          intros s; destruct (proj1 (proj2 Hm) s) as [W1 W2 H1 H2 E].
          econstructor; [ econstructor; exact H1 | econstructor; exact H2 |].
          unfold nf_eq_upto_proofs, ne_eq_upto_proofs in *; cbn [nf_eqb_upto_proofs]; rewrite dec_eqb_refl; exact E.
        + eapply wf_conv'; [ exact HM | exact HA0 ].
        + intros Δ φ W Hφ Hr; inversion Hr; subst.
          apply glu_nf_eq_neut.
          eapply glu_ne_eq_conv with (κ := ak_relevant); [| eauto ]; cbn [abs_kind_sort]; mauto 3.
      - intros Γ M A m R Hglu HEl HR Hm.
        pose proof HEl as HEl'; apply H0 in HEl'; destruct HEl' as [HA HMt Hpp [_ HMg]].
        econstructor; [ exact HMt | exact Hglu | apply H; exact HA | eapply per_elem_then_per_top; eassumption |].
        intros Δ φ w Hφ Hw; inversion Hw; subst; try (cbn in *; discriminate).
        eapply glu_nf_eq_conv with (κ := ak_relevant); [| eauto ]; cbn [abs_kind_sort]; symmetry; mauto 3. }
  (** [LevelSort]: no type is of it and no neutral either ([neutral_at]);
      an element, a type of levels, reads back as a type glued at the least
      small index, at [LevelSort], its kind ([glu_univ_elem_typ_kind]). *)
  1:{ split; [| split ].
      - intros Γ A R _ Hn _; exfalso; apply Hn; reflexivity.
      - intros Γ M A m _ [P' El' _ _ _ [Hn _] _]; exfalso; apply Hn; reflexivity.
      - intros Γ M A m R Hglu HEl HR Hm.
        pose proof HEl as HEl'; apply H1 in HEl'; destruct HEl' as [HA HMt Hcode [P0 El0 Hg0 HM0]]; subst A.
        assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
        econstructor; [ exact HMt | exact Hglu | apply H0; split; [ reflexivity | exact HΓ ] | eapply per_elem_then_per_top; eassumption |].
        destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_level 0 Hg0 HM0 HMt) as [Hk Hn].
        destruct (H _ _ _ Hg0) as (Htop & _ & _).
        destruct (glu_univ_elem_per_univ _ _ _ _ Hg0) as [R0 HR0].
        destruct (Htop _ _ _ HR0 Hn HM0) as [_ _ Hrd].
        intros Δ φ w Hφ Hw; inversion Hw; subst; try (cbn in *; discriminate).
        match goal with Hr : Rtyp m in _ ↘ _ |- _ => pose proof (Hrd _ _ _ Hφ Hr) as Hg end.
        rewrite Hk in Hg; cbn in Hg |- *; exact Hg. }
  (** A proposition: as a type, glued by its readback at [Prop]; a
      neutral of it is a proof that reads back; an element reads back as a
      proof, which the term ascribed its proposition is equal to, by
      irrelevance. *)
  2:{ pose proof (per_prop_left _ _ H) as Hka.
      split; [| split ].
      - intros Γ A R HR _ HA; apply H0 in HA; destruct HA as [HAt HAr].
        econstructor; [ rewrite Hka; exact HAt | exact (per_univ_then_per_top_typ HR) |].
        intros Δ φ A' Hφ Hr; rewrite Hka; exact (HAr _ _ _ Hφ Hr).
      - intros Γ M A m Hglu [P' El' HM Hglu' HAP' Hm Hrb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
        pose proof (proj2 (HPP Γ A) HAP') as HA0; apply H0 in HA0.
        apply H1; econstructor; [ exact HA0 | exact HM |].
        apply per_proof_refl; intros s; destruct (proj1 (proj2 Hm) s) as [W1 W2 H3 H4 E].
        eexists; econstructor; exact H3.
      - intros Γ M A m R Hglu HEl HR Hm.
        pose proof HEl as HEl'; apply H1 in HEl'; destruct HEl' as [HAg HMt Hpp].
        pose proof HAg as [HAt HAr].
        econstructor; [ exact HMt | exact Hglu | apply H0; exact HAg | eapply per_elem_then_per_top; eassumption |].
        intros Δ φ w Hφ Hw.
        destruct (read_nf_propositional _ _ _ _ Hka Hw) as (P1 & M1 & -> & HP1).
        destruct (HAr _ _ _ Hφ HP1) as (P2 & EP & HAeq).
        exists (nf_proof P2 M[φ]ʷ); split; [ unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs]; exact EP |].
        cbn [nf_annotate_proofs nf_to_exp].
        assert (HMφ : Δ ⊢ M[φ]ʷ : A[φ]ʷ) by mauto 3.
        assert (HAφ : Δ ⊢ A[φ]ʷ : Propₘ) by (eapply kripke_preserves_prop; eassumption).
        assert (HP2 : Δ ⊢ nf_annotate_proofs P2 : Propₘ) by (gen_presups; assumption).
        apply wf_exp_eq_irrelevant; [ exact HAφ | exact HMφ |].
        eapply wf_conv_rel with (r := ak_propositional) (n := 0); [| cbn; symmetry; exact HAeq ].
        apply proof_ascription_typed; [ exact HP2 |].
        eapply wf_conv_rel with (r := ak_propositional) (n := 0); [ exact HMφ | cbn; exact HAeq ]. }
  (** A neutral type, relevant: glued by its readback, its neutrals and
      elements by theirs. *)
  2:{ split; [| split ].
      - intros Γ A R HR _ HA; apply H1 in HA; destruct HA as [HAt HAr].
        econstructor; [ rewrite H; exact HAt | exact (per_univ_then_per_top_typ HR) |].
        intros Δ φ A' Hφ Hr; rewrite H; inversion Hr; subst.
        apply glu_nf_eq_neut; eauto.
      - intros Γ M A m Hglu [P' El' HM Hglu' HAP' Hm Hrb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
        pose proof (proj2 (HPP Γ A) HAP') as HA0; apply H1 in HA0.
        apply H2; econstructor; [ exact HA0 | exact HM | exact (proj1 (proj2 Hm)) | exact Hrb ].
      - intros Γ M A m R Hglu HEl HR Hm.
        pose proof HEl as HEl'; apply H2 in HEl'; destruct HEl' as [b' m0 Γ A M HAg HMt Hm0 Hrb].
        econstructor; [ exact HMt | exact Hglu | apply H1; exact HAg | eapply per_elem_then_per_top; eassumption |].
        intros Δ φ w Hφ Hw; inversion Hw; subst; try (cbn in *; congruence).
        apply glu_nf_eq_neut; eauto. }
  (** A [Π] of the kinds [κd] (the domain's) and [κc]: as a type it reads
      back as the [Π] of the readbacks of the domain and of the codomain at
      a fresh variable; a neutral applied is a neutral of the codomain; an
      element reads back η-long, its body at a fresh variable. *)
  1:{ pose proof H3 as Hpi; basic_invert_per_univ_elem Hpi.
  rename H8 into Hout, H9 into Hkc, H12 into Hpk, H14 into Hna, H15 into Hnb, H16 into Helem.
  assert (Ein : in_rel0 <~> in_rel) by (eapply per_univ_elem_right_irrel; eassumption).
  destruct IH as (IHt & IHb & IHe).
  (** The codomain at an argument is of the kind [κc], and not [LevelSort] *)
  assert (Hbk : forall c b, in_rel c c -> ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b -> domain_kind b = κc /\ not_level_sort b).
  { intros * Hc Eb; destruct (Hkc _ _ (proj2 (Ein _ _) Hc)) as (b0 & Eb0 & Hb0).
    destruct (Hnb _ _ (proj2 (Ein _ _) Hc)) as (b1 & Eb1 & Hb1).
    assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption); split; assumption. }
  assert (HTs : type_sort (abs_kind_sort κc Typeω@(large_level i))) by (apply type_sort_abs_kind; constructor).
  split; [| split ].
  - intros Γ A R HR _ HA; apply H5 in HA; destruct HA as [? ? IT OT HAeq HIT HOT HIP HOP].
    econstructor; [ cbn [domain_kind]; gen_presups; eassumption | exact (per_univ_then_per_top_typ HR) |].
    intros Δ φ W Hφ Hr; cbn [domain_kind].
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    inversion Hr; subst.
    match goal with HRa : Rtyp a in _ ↘ ?A0, Eb0 : ⟦ B ⟧ _ ↘ ?b0, HRb : Rtyp ?b0 in _ ↘ ?B0 |- _ =>
      rename HRa into HRA; rename A0 into A'; rename Eb0 into Eb; rename b0 into b; rename HRb into HRB; rename B0 into B' end.
    (** The domain *)
    pose proof (HIP _ _ Hφ) as HITφ.
    destruct (IHt _ _ _ H0 Hna HITφ) as [HITt _ HITrb].
    destruct (HITrb Δ wk_id A' Hid HRA) as (A'' & EA & HITeq); rewrite exp_wk_id in HITeq.
    (** The codomain at the fresh variable *)
    assert (HΔIT : ⊢ Δ ▹{domain_kind a} IT[φ]ʷ) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
    assert (Hwk : Δ ▹{domain_kind a} IT[φ]ʷ ⊢ᵏ φ ⊙ ↑ : Γ) by mauto 3.
    pose proof (IHb _ _ _ _ H (var_glu_elem_bot _ _ _ _ _ _ H Hna HITφ)) as HEl; rewrite exp_wk_wk in HEl.
    pose proof (var_per_elem (length Δ) H0 Hna) as Hc.
    pose proof (HOP _ _ _ _ Hwk HEl Hc) as HOPc.
    destruct (Hbk _ _ Hc Eb) as [Hkb Hnbb].
    destruct (H2 _ Hc _ Eb) as (HOt & _ & _).
    destruct (glu_univ_elem_per_univ _ _ _ _ (H1 _ Hc _ Eb)) as [Rb HRb].
    destruct (HOt _ _ _ HRb Hnbb HOPc) as [HOTt _ HOTrb].
    assert (Hid' : Δ ▹{domain_kind a} IT[φ]ʷ ⊢ᵏ wk_id : Δ ▹{domain_kind a} IT[φ]ʷ) by mauto 3.
    destruct (HOTrb _ wk_id B' Hid' HRB) as (B'' & EB & HBeq); rewrite exp_wk_id, Hkb in HBeq.
    exists (nf_pi (domain_kind a) κc A'' B''); split; [ apply nf_pi_upto_proofs; assumption |].
    cbn [nf_annotate_proofs nf_to_exp].
    assert (HAφ : Δ ⊢ A[φ]ʷ ≈ a_pi (domain_kind a) κc IT[φ]ʷ OT[wk_q φ]ʷ : abs_kind_sort κc Typeω@(large_level i))
      by (rewrite <- exp_wk_pi; eapply kripke_preserves_kind_sort_eq; eassumption).
    pose proof (kripke_q_var_eq Δ Γ (domain_kind a) IT (abs_kind_sort κc Typeω@(large_level i)) OT φ _ HOT HIT
                  (sort_kind_abs_kind_sort _ _) Hφ) as Hq.
    rewrite (type_sort_wk _ _ HTs) in Hq.
    etransitivity; [ exact HAφ |].
    eapply wf_exp_eq_pi_cong; [ apply wf_is_univ_large; exact HΔ | exact HITt | exact HITeq | | exact Hpk ].
    rewrite (type_sort_wk _ _ HTs).
    etransitivity; [ symmetry; exact Hq | exact HBeq ].
  - intros Γ M A m Hglu [P' El' HM Hglu' HAP' Hm Hrb].
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hglu') as [HPP _].
    pose proof (proj2 (HPP Γ A) HAP') as HA0; apply H5 in HA0; destruct HA0 as [? ? IT OT HAeq HIT HOT HIP HOP].
    (** The type at a weakening *)
    assert (HAw : forall Δ φ, Δ ⊢ᵏ φ : Γ ->
              Δ ⊢ A[φ]ʷ ≈ a_pi (domain_kind a) κc IT[φ]ʷ OT[wk_q φ]ʷ : abs_kind_sort κc Typeω@(large_level i))
      by (intros; rewrite <- exp_wk_pi; eapply kripke_preserves_kind_sort_eq; eassumption).
    apply H6; econstructor; [ exact HM | exact (per_bot_then_per_elem H3 Hm) | exact HAeq | exact HIT | exact HOT | exact HIP |].
    (** The neutral applied to a glued argument: a neutral of the codomain *)
    intros Δ φ N n Hφ HN equiv_n.
    destruct (Hout _ _ (proj2 (Ein _ _) equiv_n)) as [b b' Eb Eb' HRb].
    destruct (Hbk _ _ equiv_n Eb) as [Hkb Hnbb].
    exists (⇑ b (m $ᵈ ⇓ a n)); split; [ eapply eval_app_neut; [ exact H4 | exact Eb ] |].
    destruct (H2 _ equiv_n _ Eb) as (_ & Hbb & _).
    apply Hbb; [ exact (H1 _ equiv_n _ Eb) |].
    assert (HMφ : Δ ⊢ M[φ]ʷ : a_pi (domain_kind a) κc IT[φ]ʷ OT[wk_q φ]ʷ)
      by (eapply wf_conv_rel; [ mauto 3 | exact (HAw _ _ Hφ) ]).
    destruct (IHe _ _ _ _ _ H HN H0 equiv_n) as [_ _ HNt _ _ _ HNrb].
    assert (HMN : Δ ⊢ M[φ]ʷ $ N : OT[ι φ,,N]) by (rewrite <- exp_sub_wk_q_extend; eapply wf_app_at'; eassumption).
    econstructor; [ exact HMN | exact (H1 _ equiv_n _ Eb) | exact (HOP _ _ _ _ Hφ HN equiv_n) | |].
    + (** At a type of levels, the domain is one too ([pi_kinds]), and
          neither the function nor the argument holds a proof *)
      split; [ exact Hnbb | split; [ apply domain_app_per; [ exact (proj1 (proj2 Hm)) | exact (per_elem_then_per_top H0 equiv_n) ] |] ].
      intros Hkl; rewrite Hkb in Hkl.
      destruct (proj2 (proj2 Hm) Hkl) as [Hmpf _].
      assert (Hka : domain_kind a = ak_level) by (rewrite Hkl in Hpk; exact (pi_kinds_level_domain _ Hpk)).
      split; intros s M0 HM0; inversion HM0; subst; cbn; split;
        [ eapply Hmpf; eassumption | eapply read_at_level_type_proof_free; [ exact H0 | exact Hka | exact equiv_n | eassumption ]
        | eapply Hmpf; eassumption | eapply read_at_level_type_proof_free; [ exact H0 | exact Hka | exact equiv_n | eassumption ] ].
    + (** The readback: the application of the readbacks *)
      intros Δ' φ' M' Hφ' HM'; inversion HM'; subst.
      match goal with H1m : Rne m in _ ↘ ?M1, H1n : Rnf ⇓ a n in _ ↘ ?N1 |- _ =>
        rename H1m into HM1; rename H1n into HN1; rename M1 into M1; rename N1 into N1 end.
      assert (Hc : Δ' ⊢ᵏ φ ⊙ φ' : Γ) by (eapply kripke_compose; eassumption).
      destruct (Hrb _ _ _ Hc HM1) as (M1' & EM & HMeq).
      destruct (HNrb _ _ _ Hφ' HN1) as (N1' & EN & HNeq).
      exists (ne_app M1' N1'); split; [ apply ne_app_upto_proofs; assumption |].
      cbn [ne_annotate_proofs ne_to_exp].
      rewrite exp_wk_sub_of_wk_extend, <- exp_sub_wk_q_extend, exp_wk_app, exp_wk_wk.
      eapply wf_exp_eq_app_cong'.
      * eapply wf_exp_eq_conv_kind; [ exact HMeq | exact (HAw _ _ Hc) ].
      * rewrite <- exp_wk_wk; exact HNeq.
  - intros Γ M A m R Hglu HEl HR Hm.
    pose proof HEl as HEl'; apply H6 in HEl'; destruct HEl' as [? ? ? ? IT OT HMt Hme HAeq HIT HOT HIP Happ].
    assert (HAw : forall Δ φ, Δ ⊢ᵏ φ : Γ ->
              Δ ⊢ A[φ]ʷ ≈ a_pi (domain_kind a) κc IT[φ]ʷ OT[wk_q φ]ʷ : abs_kind_sort κc Typeω@(large_level i))
      by (intros; rewrite <- exp_wk_pi; eapply kripke_preserves_kind_sort_eq; eassumption).
    econstructor; [ exact HMt | exact Hglu | eapply glu_univ_elem_trm_typ; eassumption | eapply per_elem_then_per_top; eassumption |].
    intros Δ φ w Hφ Hw.
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
    (** A function reads back η-long: its codomain is not propositional *)
    inversion Hw; subst;
      try (match goal with Hp : domain_kind (d_pi _ _ _ _ _) = ak_propositional |- _ => cbn in Hp; subst; inversion H4 end).
    match goal with HRa : Rtyp a in _ ↘ ?A0, Ea0 : $| m & _ | _ ⍮ _ ↘ ?m1, Eb0 : ⟦ B ⟧ _ ↘ ?b0, HRb : Rnf ⇓ ?b0 ?m1 in _ ↘ ?M0 |- _ =>
      rename HRa into HRA; rename A0 into A'; rename Ea0 into Ea; rename m1 into m'; rename Eb0 into Eb; rename b0 into b;
      rename HRb into HRM; rename M0 into M' end.
    (** The domain *)
    pose proof (HIP _ _ Hφ) as HITφ.
    destruct (IHt _ _ _ H0 Hna HITφ) as [HITt _ HITrb].
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    destruct (HITrb Δ wk_id A' Hid HRA) as (A'' & EA & HITeq); rewrite exp_wk_id in HITeq.
    (** The body, at the fresh variable *)
    assert (HΔIT : ⊢ Δ ▹{domain_kind a} IT[φ]ʷ) by (econstructor; [ eassumption | apply sort_kind_abs_kind_sort ]).
    assert (Hwk : Δ ▹{domain_kind a} IT[φ]ʷ ⊢ᵏ φ ⊙ ↑ : Γ) by mauto 3.
    assert (Hid' : Δ ▹{domain_kind a} IT[φ]ʷ ⊢ᵏ wk_id : Δ ▹{domain_kind a} IT[φ]ʷ) by mauto 3.
    pose proof (IHb _ _ _ _ H (var_glu_elem_bot _ _ _ _ _ _ H Hna HITφ)) as HEl0; rewrite exp_wk_wk in HEl0.
    pose proof (var_per_elem (length Δ) H0 Hna) as Hc.
    destruct (Happ _ _ _ _ Hwk HEl0 Hc) as (mn & Emn & HOEl).
    pose proof (functional_eval_app _ _ _ _ Emn Ea) as ->.
    assert (ER : R <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
    destruct (proj1 (Helem _ _) (proj1 (ER _ _) Hm)) as [_ _ Hpa].
    pose proof (proj2 (Ein _ _) Hc) as Hc0.
    destruct (Hpa _ _ Hc0) as [fa fa' Hfa Hfa' Hrel].
    pose proof (functional_eval_app _ _ _ _ Hfa Ea) as ->.
    pose proof (functional_eval_app _ _ _ _ Hfa' Ea) as ->.
    destruct (Hout _ _ Hc0) as [b1 b1' Eb1 Eb1' HRb1].
    assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (b1' = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (H2 _ Hc _ Eb) as (_ & _ & Htop).
    destruct (Htop _ _ _ _ _ (H1 _ Hc _ Eb) HOEl HRb1 Hrel) as [_ _ _ _ _ _ Hrbtop].
    destruct (Hrbtop _ wk_id M' Hid' HRM) as (M'' & EM & Hbeq); rewrite !exp_wk_id in Hbeq.
    exists (λⁿ A'' M''); split; [ apply nf_fn_upto_proofs; assumption |].
    cbn [nf_annotate_proofs nf_to_exp].
    pose proof (HAw _ _ Hφ) as HAφ.
    assert (HMφ : Δ ⊢ M[φ]ʷ : a_pi (domain_kind a) κc IT[φ]ʷ OT[wk_q φ]ʷ) by (eapply wf_conv_rel; [ mauto 3 | exact HAφ ]).
    pose proof (kripke_q_var_eq Δ Γ (domain_kind a) IT (abs_kind_sort κc Typeω@(large_level i)) OT φ _ HOT HIT
                  (sort_kind_abs_kind_sort _ _) Hφ) as Hq.
    rewrite (type_sort_wk _ _ HTs) in Hq.
    eapply wf_exp_eq_conv_kind; [| symmetry; exact HAφ ].
    etransitivity; [ eapply wf_exp_eq_fn_eta'; exact HMφ |].
    eapply wf_exp_eq_fn_cong'; [ exact HITeq | apply sort_kind_abs_kind_sort | exact (presup_exp_eq_right Hq) | exact Hpk |].
    rewrite exp_wk_wk; eapply wf_exp_eq_conv_kind; [ exact Hbeq | exact Hq ]. }
Qed.

Corollary realize_glu_typ_top : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort a ->
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

Corollary var0_glu_elem : forall {i : universe_index} {a P El Γ A},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort a ->
    Γ ⊢ A ® P ->
    Γ ▹{domain_kind a} A ⊢ #0 : A[↑]ʷ ® ⇑! a (length Γ) ∈ El.
Proof.
  intros.
  eapply realize_glu_elem_bot; [ eassumption |].
  eauto using var_glu_elem_bot.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.
