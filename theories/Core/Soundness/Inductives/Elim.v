(** * The Eliminator of a Group in the Gluing Model

    The soundness counterpart of [Core/Completeness/Inductives/Elim.v]: an
    elimination of a member of a group, by its blocks, is glued at the
    motive's instance, by induction on the gluing of the scrutinee in the
    group.  On a constructor, the branch of its member's block is glued at
    the substitution of the constructor's non-uniform parameters, its
    arguments and the recursive results, and the type of the motive is the
    branch's through the equation [ι] gives.  On a neutral, the eliminator
    reads back as the stuck one: at a declared member the group's, at a
    view the container's (E1′), whose branches the view's read at fresh
    variables and, where the view nests through an argument, at the
    eliminator stuck at a member of lower rank.  The values the gluings are
    at are related to those the evaluation reaches through the PER model,
    as [Core/Completeness/Inductives/Elim.v] and
    [Core/Semantic/Inductives/IndElim.v] relate them. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes ViewBranch.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.Inductives Require Elim.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.LogicalRelation Require Instance.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup DescTyping.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Inductives Require Views.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon Bridge ElimBase AtType.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A valid type at a valid substitution: the value of the instance
    against the type's at the substitution's value. *)
Lemma typ_inst_val : forall Δ0 Γ0 A (i : nat) τ RΓ0 E Eτ a b,
    Δ0 ⊨ A : Typeω@i -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨ˢ τ ≈ τ : Δ0 ->
    RΓ0 E E -> ⟦ τ ⟧s E ↘ Eτ -> ⟦ A[τ] ⟧ E ↘ a -> ⟦ A ⟧ Eτ ↘ b -> Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HA HΓ0 Hτ HE Hev Ea Eb.
  destruct (rel_exp_of_typ_inversion HA) as (R & HR & Hgen).
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev) as [a1 b1 c1 d1 Ea1 Eb1 Ec1 Ed1 Hch].
  assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (c1 = b) as -> by (eapply functional_eval_exp; eassumption).
  pairwise.
Qed.

(** The eliminator at typed blocks, at equal scrutinees
    ([wf_exp_eq_elim_cong] with the same parameters and blocks). *)
Lemma wf_elim_scrut_eq : forall Γ p D oq m Mm bm Bks Ps M M' (i : nat),
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
    Γ ⊢ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Γ ⊢ a_elim oq (List.firstn (ind_nu D) Ps) m Bks M ≈ a_elim oq (List.firstn (ind_nu D) Ps) m Bks M'
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hg HMm Hbm HPl HPs HBt HMM.
  eapply wf_exp_eq_elim_cong with (Bks' := Bks) (Ps' := Ps);
    first [ exact Hl | exact Hg | exact HMm | exact Hbm | exact (bt_len _ _ _ _ _ _ _ _ HBt) | exact HPl | exact HPs | exact HMM
          | reflexivity | exact (bt_nm _ _ _ _ _ _ _ _ HBt) | exact (bt_ann _ _ _ _ _ _ _ _ HBt) | exact (bt_motive _ _ _ _ _ _ _ _ HBt)
          | exact (bt_mctx _ _ _ _ _ _ _ _ HBt) | exact (bt_names _ _ _ _ _ _ _ _ HBt) | exact (bt_bctx _ _ _ _ _ _ _ _ HBt)
          | exact (bt_counts _ _ _ _ _ _ _ _ HBt) | idtac ].
  - intros k P P' T HP HP' HT; rewrite HP in HP'; injection HP' as <-; apply wf_exp_eq_refl; exact (HPs _ _ _ HP HT).
  - intros k Mk b b' HMk Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; apply wf_exp_eq_refl; exact (bt_motive _ _ _ _ _ _ _ _ HBt _ _ _ HMk Hb).
  - intros k b b' Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; reflexivity.
  - intros k Mk b b' i0 c gs n B B' HMk Hb Hb' HB HB' Hcon; rewrite Hb in Hb'; injection Hb' as <-.
    rewrite HB in HB'; injection HB' as <-; apply wf_exp_eq_refl.
    exact (bt_brs _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ HMk Hb Hcon (List.nth_error_In _ _ HB)).
Qed.

(** [ι] at typed blocks ([wf_exp_eq_elim_iota] with the blocks' typing
    premises read off [blocks_typed]). *)
Lemma wf_elim_iota_bt : forall Γ p D oq m Mm bm Bks c gs Ps As (i : nat) n B,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm -> ind_con Mm c = Some gs -> List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
       Γ ⊢ N : T) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
    brs_lookup (eb_brs bm) c = Some (n, B) ->
    Γ ⊢ a_elim oq (List.firstn (ind_nu D) Ps) m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                    (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As))
       ≈ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++
                          elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As)]
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                          apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                            (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)].
Proof.
  intros * HΓ Hl Hg HMm Hbm Hcon HPl HPs HAl HAs HBt HlB.
  eapply wf_exp_eq_elim_iota;
    first [ exact HΓ | exact Hl | exact Hg | exact HMm | exact Hbm | exact Hcon | exact (bt_len _ _ _ _ _ _ _ _ HBt) | exact HPl
          | exact HPs | exact HAl | exact HAs | reflexivity | exact (bt_nm _ _ _ _ _ _ _ _ HBt) | exact (bt_ann _ _ _ _ _ _ _ _ HBt)
          | exact (bt_motive _ _ _ _ _ _ _ _ HBt) | exact (bt_mctx _ _ _ _ _ _ _ _ HBt) | exact (bt_names _ _ _ _ _ _ _ _ HBt)
          | exact (bt_bctx _ _ _ _ _ _ _ _ HBt) | exact (bt_counts _ _ _ _ _ _ _ _ HBt) | exact (bt_brs _ _ _ _ _ _ _ _ HBt)
          | exact HlB ].
Qed.

(** The type of a view's branch, instantiated in the container's branch's
    context ([wrap_br]), is the container's branch type: the view's
    constructor applied is the container's ([Views.vb_con_conv]), the same
    one at a declared member of the container. *)
Lemma view_bty_conv : forall Γ0 p D m Mm qc k' Is vm D' Us0 Bks0 (i : nat),
    ⊢ᵍ gc_deps ⍮ gc_stack -> decls_typed gc_deps gc_stack -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some D' -> vwrap_ok D D' vm -> ⊢ Γ0 ->
    List.length Us0 = ind_nu D ->
    (forall k U T, List.nth_error Us0 k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us0) k = Some T -> Γ0 ⊢ U : T) ->
    blocks_typed gc_deps gc_stack Γ0 p D Us0 Bks0 i ->
    forall i' Mi' v Mv c gs' gs b W, ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs -> List.nth_error Bks0 v = Some b ->
      List.length W = cargs_nrec gs ->
      elim_bctx qc D' Mi' gs' (blocks_motives (vwrap p D D' vm Us0 Bks0)) (List.map (fun I => I[sb_of_list Id Us0]) Is) ++ Γ0
        ⊢ (elim_bty p v Mv c gs (eb_motive b) Us0)[sb_of_list (ι (wk_shiftn (im_nn Mv + List.length gs' + cargs_nrec gs')))
             (vars_from (cargs_nrec gs' + List.length gs') (im_nn Mv) ++ vars_from (cargs_nrec gs') (List.length gs') ++ W)]
        ≈ elim_bty qc i' Mi' c gs' (eb_motive b) (List.map (fun I => I[sb_of_list Id Us0]) Is) : Typeω@i.
Proof.
  intros * Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt * Hi' Hv Hmv Hcon' Hcon Hcorr Hb HW.
  pose proof (vb_bty_view _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' HΓ HUl HUs v Mv c gs' gs Hmv Hcorr (eb_motive b) W HW) as E1.
  cbn beta in E1; rewrite E1; clear E1.
  rewrite (vb_bty_cont _ _ _ _ _ _ _ _ _ _ _ _ Hvw HBt i' Mi' v Mv c gs' Hi' Hv Hmv).
  destruct (vw_facts _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' HΓ HUl HUs) as (HD & Hc & HD' & Hc' & HIl & HIs).
  set (Is' := List.map (fun I => I[sb_of_list Id Us0]) Is) in *.
  pose proof (vw_motives_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt _ _ Hi') as HA.
  rewrite (vwrap_motive_nth _ _ _ _ _ _ _ _ _ _ Hi' Hv Hb ltac:(eauto)) in HA.
  assert (HM : forall j Mj, ind_member D' j = Some Mj -> ⊢ elim_mctx qc D' j Mj Is' ++ Γ0)
    by (intros j Mj Hj; exact (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl' Hj HΓ HIl HIs)).
  pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl' Hi' HΓ HIl HIs HM
                (vw_motives_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt) Hcon') as Hρc.
  rewrite (vb_nn _ _ _ _ _ _ _ _ _ _ Hvw HBt i' Mi' v Mv Hi' Hv Hmv) in Hρc.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hρc) as Hty; cbn [exp_sub] in Hty.
  set (n' := im_nn Mv + List.length gs' + cargs_nrec gs') in *.
  set (nvars := vars_from (cargs_nrec gs' + List.length gs') (im_nn Mv)) in *.
  set (avars := vars_from (cargs_nrec gs') (List.length gs')) in *.
  destruct (im_head Mi') as [pm | q'' k'' Is'' vm''] eqn:Hhi.
  - (** A declared member of the container: the same constructor. *)
    destruct (dt_view_decl _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hhi Hv) as (Mv0 & vm' & Hmv0 & Hhv).
    rewrite Hmv in Hmv0; injection Hmv0 as <-.
    assert (Econ : apps_exp (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                     (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us0) ++ nvars ++ avars)
                   = apps_exp (a_con (fst (im_ref qc i' Mi')) (snd (im_ref qc i' Mi')) c)
                     (im_pre Mi' (List.map (fun U => U[wk_shiftn n']ʷ) Is') ++ nvars ++ avars)).
    { unfold im_ref, im_pre; rewrite Hhi, Hhv; cbn [fst snd]; do 2 f_equal.
      pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ Hm Hh) as HsIs.
      rewrite <- map_sub_of_wk, (inst_sub_comm Is Us0 (ind_nu D)) by assumption.
      unfold Is'; rewrite !List.map_map; apply List.map_ext; intros; apply exp_sub_of_wk. }
    rewrite Econ; apply wf_exp_eq_refl; exact Hty.
  - (** A view: the constructors equal. *)
    pose proof (vb_con_conv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt i' Mi' v Mv c gs' gs
                  Hi' Hv Hmv Hcon' Hcon Hcorr _ _ _ _ Hhi) as Hcv; cbv zeta in Hcv; destruct Hcv as [HcV Hcc].
    set (conV := apps_exp (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                   (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us0) ++ nvars ++ avars)) in *.
    set (conC := apps_exp (a_con (fst (im_ref qc i' Mi')) (snd (im_ref qc i' Mi')) c)
                   (im_pre Mi' (List.map (fun U => U[wk_shiftn n']ʷ) Is') ++ nvars ++ avars)) in *.
    assert (HNl : List.length nvars = im_nn Mi')
      by (unfold nvars; rewrite length_vars_from, (vb_nn _ _ _ _ _ _ _ _ _ _ Hvw HBt i' Mi' v Mv Hi' Hv Hmv); reflexivity).
    assert (Hlen : forall x, List.length (nvars ++ x :: nil) = List.length (elim_mctx qc D' i' Mi' Is'))
      by (intros; rewrite List.length_app, length_elim_mctx, HNl; cbn; lia).
    pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_mctx_ass _ _ _ _ Is' Hc' Hi') (Hlen conC) Hρc) as HMs.
    pose proof (fun x => elim_mctx_insts qc D' i' Mi' Is' (ι wk_shiftn n') nvars x Hc' Hi' HIl HNl) as E.
    assert (Hl2 : List.length (tele_insts (im_nparams Mi') (sb_of_list Id Is' ⨟ ι wk_shiftn n') nvars) = im_nn Mi')
      by (rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption); rewrite HNl; unfold im_nn; lia).
    assert (Hσ : elim_bctx qc D' Mi' gs' (blocks_motives (vwrap p D D' vm Us0 Bks0)) Is' ++ Γ0
                   ⊢ˢ sb_of_list (ι wk_shiftn n') (nvars ++ conC :: nil) ≈ sb_of_list (ι wk_shiftn n') (nvars ++ conV :: nil)
                   : elim_mctx qc D' i' Mi' Is' ++ Γ0).
    { eapply wf_sub_eq_of_list_left;
        [ exact (elim_mctx_ass _ _ _ _ _ Hc' Hi') | exact (HM _ _ Hi')
        | apply wf_sub_eq_refl; exact (vb_wk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt i' Mi' v Mv c gs'
                                         Hi' Hv Hmv Hcon')
        | exact (Hlen conC) | exact (Hlen conV) | exact HMs | |].
      - intros k0 N T0 HN HT; rewrite E in HT.
        destruct (Nat.lt_ge_cases k0 (im_nn Mi')) as [Hk | Hk].
        + rewrite List.nth_error_app1 in HN by lia.
          apply (HMs k0); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite E; exact HT ].
        + rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
          rewrite HNl in HN; rewrite Hl2 in HT.
          destruct (k0 - im_nn Mi') as [| k1] eqn:Hk0; cbn in HN, HT; [| destruct k1; discriminate ].
          injection HN as <-; injection HT as <-; exact HcV.
      - intros k0 N N' T0 HN HN' HT; rewrite E in HT.
        destruct (Nat.lt_ge_cases k0 (im_nn Mi')) as [Hk | Hk].
        + rewrite List.nth_error_app1 in HN, HN' by lia; rewrite HN in HN'; injection HN' as <-.
          apply wf_exp_eq_refl; apply (HMs k0); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite E; exact HT ].
        + rewrite List.nth_error_app2 in HN, HN' by lia; rewrite List.nth_error_app2 in HT by lia.
          rewrite HNl in HN, HN'; rewrite Hl2 in HT.
          destruct (k0 - im_nn Mi') as [| k1] eqn:Hk0; cbn in HN, HN', HT; [| destruct k1; discriminate ].
          injection HN as <-; injection HN' as <-; injection HT as <-; exact Hcc. }
    pose proof (sub_eq_preserves_exp _ _ _ _ _ HA _ _ _ Hσ) as Heq; cbn [exp_sub] in Heq.
    apply wf_exp_eq_sym; exact Heq.
Qed.

(** ** The Arguments a View Nests Through, Position by Position *)

Lemma cargs_nest_ok_zero : forall gs' gs, cargs_nest_ok (fun _ => 0) 1 gs' gs.
Proof.
  induction gs' as [| g' gs' IH]; intros gs; [ destruct gs; cbn; auto |].
  destruct gs as [| g gs]; [ destruct g'; cbn; auto |].
  destruct g', g; cbn; auto.
Qed.

Lemma cargs_nest_ok_at : forall rk r gs1' A' gs2' gs1 t gs2, List.length gs1' = List.length gs1 ->
    cargs_nest_ok rk r (gs1' ++ ca_arg A' :: gs2') (gs1 ++ ca_rec t :: gs2) -> rk (ptyp_mem t) < r.
Proof.
  intros rk r gs1'; induction gs1' as [| g' gs1' IH]; intros A' gs2' [| g gs1] t gs2 Hl H; cbn in Hl; try discriminate; cbn in H.
  - exact (proj1 H).
  - injection Hl as Hl; destruct g', g; cbn in H; first [ exact (IH _ _ _ _ _ Hl H) | exact (IH _ _ _ _ _ Hl (proj2 H)) ].
Qed.

(** The recursive result of a view's branch at a recursive argument: the
    container's variable where the container has it recursive, the
    eliminator's otherwise. *)
Lemma wrap_ihs_at : forall gs1' g' gs2' gs1 t gs2 ihs r' nr' vm, List.length gs1' = List.length gs1 ->
    cargs_corr vm (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2) ->
    List.nth_error (wrap_ihs (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2) ihs r' nr') (cargs_nrec gs1)
      = Some (match g' with ca_rec _ => a_var (nr' - 1 - (r' + cargs_nrec gs1')) | ca_arg _ => List.nth (cargs_nrec gs1) ihs a_True end).
Proof.
  induction gs1' as [| h' gs1' IH]; intros g' gs2' [| h gs1] t gs2 ihs r' nr' vm Hl Hc; cbn in Hl; try discriminate.
  - destruct g'; cbn in Hc |- *; [ destruct ihs; reflexivity | rewrite Nat.add_0_r; reflexivity ].
  - injection Hl as Hl; destruct h', h; cbn in Hc |- *; try contradiction.
    + rewrite (IH _ _ _ _ _ _ _ _ _ Hl Hc); reflexivity.
    + rewrite (IH _ _ _ _ _ _ _ _ _ Hl Hc); destruct g'; [| reflexivity ].
      destruct ihs; cbn; [ destruct (cargs_nrec gs1); reflexivity | reflexivity ].
    + rewrite (IH _ _ _ _ _ _ _ _ _ Hl (proj2 (proj2 Hc))); destruct g'; [| f_equal; f_equal; lia ].
      destruct ihs; cbn; [ destruct (cargs_nrec gs1); reflexivity | reflexivity ].
Qed.

Lemma wrap_ihs_eval_at : forall ρ0 p0 ups0 Bks0 gs1' g' gs2' gs1 t gs2 vs ihs r, List.length gs1' = List.length gs1 ->
    ⟦wihs vs of (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2) with ihs under p0 ups0 Bks0 ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ r ->
    exists v' x, List.nth_error vs (List.length gs1) = Some v' /\ List.nth_error r (cargs_nrec gs1) = Some x /\
      match g' with
      | ca_rec _ => List.nth_error ihs (cargs_nrec gs1') = Some x
      | ca_arg _ => ⟦ih v' of t under p0 ups0 Bks0 ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ x
      end.
Proof.
  intros ρ0 p0 ups0 Bks0 gs1'; induction gs1' as [| h' gs1' IH]; intros g' gs2' [| h gs1] t gs2 vs ihs r Hl H; cbn in Hl; try discriminate.
  - cbn in H; inversion H; subst; cbn; eauto 6.
  - injection Hl as Hl; cbn in H; inversion H; subst;
      match goal with H1 : ⟦wihs _ of _ _ with _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
        destruct (IH _ _ _ _ _ _ _ _ Hl H1) as (v' & x & Hv & Hx & Hg) end;
      exists v', x; cbn; repeat split; auto.
Qed.

(** The fresh recursive result of an argument recursive in both kinds. *)
Lemma fresh_ihs_at : forall ρm As ρa gs1' t' gs2' gs1 t gs2 vs s ihs, List.length gs1' = List.length gs1 ->
    Fihs vs at (gs1' ++ ca_rec t' :: gs2') (gs1 ++ ca_rec t :: gs2) under ρm As in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ ihs ->
    exists v a, List.nth_error vs (List.length gs1) = Some v /\
      ⟦ihty v of t under ρm As ⟧ gc_deps ⍮ gc_stack ⍮ env_args ρa (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
      List.nth_error ihs (cargs_nrec gs1') = Some (⇑! a (s + cargs_nrec gs1')).
Proof.
  intros ρm As ρa gs1'; revert ρa; induction gs1' as [| h' gs1' IH]; intros ρa t' gs2' [| h gs1] t gs2 vs s ihs Hl H; cbn in Hl; try discriminate.
  - cbn in H; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto 10.
  - injection Hl as Hl; destruct h', h; cbn in H; inversion H; subst.
    all: match goal with H1 : fresh_ihs _ _ _ _ _ _ _ _ _ _ |- _ => destruct (IH _ _ _ _ _ _ _ _ _ Hl H1) as (v0 & a0 & Hv & Ea & Hi) end.
    all: exists v0, a0; cbn; repeat split; auto; rewrite Hi; do 3 f_equal; lia.
Qed.

(** The readback of the branches of a block, entry by entry. *)
Lemma read_brs_nth : forall p D ups Bks ρ s Mi r Mv A cs Bs Bs', ind_lookup gc_deps gc_stack p = Some D ->
    Rbrs Bs at cs of Mi r from p ups Bks Mv A in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Bs' ->
    List.length (nbrs_to_brs Bs') = List.length cs /\ List.length Bs = List.length cs /\
    forall idx c n B', List.nth_error (nbrs_to_brs Bs') idx = Some (c, n, B') ->
      exists gs' gs n0 B ns vs ihs wihs bv t Bn, List.nth_error Bs idx = Some (c, n0, B) /\
        List.nth_error cs idx = Some (c, gs') /\ ind_con Mv c = Some gs /\
        n0 = (im_nn Mi + List.length gs' + cargs_nrec gs)%nat /\ n = (im_nn Mi + List.length gs' + cargs_nrec gs')%nat /\
        cargs_plen D gs /\
        Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns /\
        Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mi) ↘ vs /\
        Fihs vs at gs' gs under ρ (blocks_motives Bks) in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns)
          ⍮ (s + im_nn Mi + List.length gs') ↘ ihs /\
        ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ wihs /\
        ⟦ B ⟧ env_args ρ (ns ++ vs ++ wihs) ↘ bv /\
        ⟦ A ⟧ env_args ρ (ns ++ d_con (fst (fst r)) (snd (fst r)) c (snd r ++ ns ++ vs) :: nil) ↘ t /\
        Rnf ⇓ t bv in gc_deps ⍮ gc_stack ⍮ (s + n) ↘ Bn /\ B' = nf_to_exp Bn.
Proof.
  intros * Hl HR; induction HR as [| ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hc En0 En Hl' Hpl Fn Fc Fi Wi Eb Et Rn HR IH].
  - split; [ reflexivity | split; [ reflexivity | intros [] *; discriminate ] ].
  - destruct (IH Hl) as (L1 & L2 & IH').
    rewrite Hl in Hl'; injection Hl' as <-.
    split; [ cbn; f_equal; exact L1 | split; [ cbn; f_equal; exact L2 |] ].
    intros [| idx] c1 n1 B1 Hn; cbn in Hn.
    + injection Hn as <- <- <-.
      do 11 eexists; split; [ reflexivity | split; [ reflexivity |] ].
      repeat split; eassumption.
    + exact (IH' idx c1 n1 B1 Hn).
Qed.

(** The recursive results of a branch read as its own group's: the fresh
    ones. *)
Lemma wihs_same : forall ρ p ups Bks gs vs ihs r, ⟦wihs vs of gs gs with ihs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
    r = ihs.
Proof.
  intros * H; remember gs as gs' eqn:E in H at 1.
  revert E; induction H; intros E; try discriminate.
  - reflexivity.
  - injection E as -> E; f_equal; exact (IHwrap_ihs_eval E).
  - injection E as -> E; exact (IHwrap_ihs_eval E).
Qed.

(** Terms glued along a closed telescope are equal to the readback of
    their values, at every weakening. *)
Lemma glu_args_read : forall Δ C Ms vs, tele_ass C -> ctx_scoped 0 C -> glu_args Δ C Id nil Ms vs ->
    forall Δ' φ Rs, Δ' ⊢ᵏ φ : Δ -> Rps vs at List.rev C in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ' ↘ Rs ->
      exps_eq_at Δ' C (List.map (fun P => P[φ]ʷ) Ms) (nfs_to_exps Rs).
Proof.
  intros * Hass Hs Hg; pose proof Hg as [L1 L2 H].
  intros Δ' φ Rs Hφ HRs.
  destruct (read_ps_nth _ _ _ _ _ HRs) as [HRl HRn].
  split; [ rewrite List.length_map, HRl; congruence |].
  intros k X Y T HX HY HT.
  rewrite List.nth_error_map in HX.
  destruct (List.nth_error Ms k) as [M |] eqn:HM; [| discriminate ]; injection HX as <-.
  rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
  destruct (List.nth_error (tele_insts C Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
  assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
  destruct (glu_args_ass_nth _ _ Hass Hk) as [A He].
  destruct (HRn _ _ _ Hv He) as (a' & V & Ha' & HV & HY').
  rewrite HY' in HY; injection HY as <-.
  destruct (H _ _ _ _ _ HM HT0 Hv He) as [i a P El Ha Hglu HP HMg].
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  destruct (realize_glu_elem_top _ _ _ _ Hglu _ _ _ _ HMg) as [? ? _ _ _ _ Hrb].
  exact (Hrb _ _ _ Hφ HV).
Qed.

(** ** The Blocks, Glued

    The gluing premises of an eliminator's blocks at uniform parameters
    [Us]: each block's motive in its member's context, and each branch at
    its type in its context. *)
#[warnings="-cannot-define-projection"]
Record glu_blocks (Γ : ctx) (p : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock) (i : nat) : Prop := mk_glu_blocks
  { gbk_motive : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      elim_mctx p D k Mk Us ++ Γ ⊩ eb_motive b : Typeω@i
  ; gbk_branch : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
      elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ⊩ B : elim_bty p k Mk c gs (eb_motive b) Us }.

(** ** The Eliminator, at an Environment

    The group [D] at [p], valid; the context [Γ] of the eliminator, the
    uniform parameters [Us] and the blocks [Bks] there; an environment [ρ]
    of [Γ], at which [Us] are [ups]; and the gluings of the clause of
    [d_ind] at [ups]. *)
Section ElimGlu.
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HGall : forall qn G, VP qn G -> glu_ind_decl G)
    (Hviewsall : forall qn G, VP qn G -> glu_views_ok qn G) (HPD : VP p D).
  Let HG := HGall _ _ HPD.
  Let Hvg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := vgr_lookup _ _ Hvg.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hsu := vgr_sort _ _ Hvg.
  Let Hass := vgr_ass _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := dc_ass _ Hc.
  Let Usem : ⊨ ind_uparams D := vid_uparams _ HD.

  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (SbΓ : glu_sub_pred).
  Hypothesis (HSbΓ : EG Γ ∈ glu_ctx_env ↘ SbΓ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).

  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUt : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊢ N : T)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T)
    (HUg : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊩ N : T).
  Let τU := sb_of_list Id Us.

  Variable (Bks : list eblock) (iA : nat).
  Hypotheses (HBt : blocks_typed gc_deps gc_stack Γ p D Us Bks iA) (HBv : valid_blocks p D Γ Us Bks iA)
    (HBg : glu_blocks Γ p D Us Bks iA).
  Let HBks := vbs_has _ _ _ _ _ _ HBv.
  Let HMall := vbs_mctx _ _ _ _ _ _ HBv.
  Let HAv := vbs_motive _ _ _ _ _ _ HBv.

  Variable (ρ : env) (ups : list domain).
  Hypotheses (Hρ : RΓ ρ ρ) (HUv : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ups).

  Variable (bu : domain) (u : uidx)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypotheses (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).
  (** A level above [u] and the sorts of the containers of the views, as
      [AtType] needs ([nb_exists] gives one). *)
  Variable (nb : nat).
  Hypotheses (Hnbu : uidx_le u (ul nb))
    (Hnbq : forall j Mj qc kc Is vm Dq, ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
              ind_lookup gc_deps gc_stack qc = Some Dq -> forall ρ bq, ⟦ ind_sort Dq ⟧ ρ ↘ bq ->
              uidx_le (Completeness.Inductives.Decl.univ_idx bq) (ul nb)).

  #[local] Abbreviation nr := (canon_nparams_rel D ups).
  #[local] Abbreviation ar := (canon_args_rel D ups).
  #[local] Abbreviation dr := (canon_doms_rel ups).
  #[local] Abbreviation G := (grp_rel p D ups nr ar dr).
  #[local] Abbreviation EB f := (f VP p D HVP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ρ ups Hρ HUv).

  (** ** What an Elimination Yields

      An element [mv] of the member [k], its type's non-uniform parameters
      [ns]: the value of the eliminator at it, the value of the motive of
      [k]'s block at it, and the elimination of a term [M'] of it, at the
      instance of the blocks by [σ'], glued at the motive there.  The
      motive is [List.nth k (blocks_motives Bks) a_True]: every member has
      its block ([bt_len]), so the default is never taken. *)
  #[warnings="-cannot-define-projection"]
  Record elim_out (k : nat) (Mk : imember) (Δ' : ctx) (σ' : sub) (oq' : option qname) (Ns' : list exp) (M' : exp)
      (mv : domain) (ns : list domain) : Prop := mk_elim_out
    { eo_val : domain
    ; eo_motive : domain
    ; eo_eval : ⟦elim mv at k of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ eo_val
    ; eo_eval_motive : ⟦ List.nth k (blocks_motives Bks) a_True ⟧ env_args ρ (ns ++ mv :: nil) ↘ eo_motive
    ; eo_per : Dom eo_motive ≈ eo_motive ∈ per_univ iA
    ; eo_glu : forall P El, DG eo_motive ∈ glu_univ_elem iA ↘ P ↘ El ->
        Δ' ⊢ a_elim oq' (List.map (fun U => U[σ']) Us) k (blocks_sub Bks σ') M'
          : (List.nth k (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mk)) σ'][sb_of_list Id (Ns' ++ M' :: nil)] ® eo_val ∈ El }.

  (** The motive of the induction on the gluing of an element of the member
      [k] at the uniform parameters [Us'] and non-uniform ones [Ns']: at a
      substitution [σ'] glued to [ρ] that sends [Us] to [Us'], the
      elimination of the element is glued. *)
  Definition elim_prop (k : nat) (Δ' : ctx) (Us' Ns' : list exp) (M' : exp) (mv : domain) : Prop :=
    forall Mk σ' oq' ns, ind_member D k = Some Mk -> elim_grp D oq' p k ->
      Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> Us' = List.map (fun U => U[σ']) Us -> Δ' ⊢ M' : im_ty_at p k Mk Us' Ns' ->
      glu_nparams k Mk NEl Δ' Us' Ns' ns -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns ->
      G k ups ups ns ns mv mv ->
      elim_out k Mk Δ' σ' oq' Ns' M' mv ns.

  (** The motive at a recursive argument [N] of shape [t], of a constructor
      [c0] of the member [k], after [d] domains of the shape of the
      argument at the uniform parameters [Us'], the values [pre] of the
      shape's components: its recursive result is glued at the type of the
      recursive result. *)
  Definition rec_prop (k : nat) (Δ' : ctx) (Us' : list exp) (pre : list domain) (t : ptyp) (A : typ) (N : exp) (v : domain) : Prop :=
    forall Mk ms c0 gs1 t0 gs2 ws d ys σ' oq' σs r a (j : nat) R P El,
      ind_member D k = Some Mk -> ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) -> pre = ms ++ ws ++ ys ->
      tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
      tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
      ptyp_skip d t0 = t -> tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) d ys ys ->
      (oq' = Some p \/ oq' = None) -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> Us' = List.map (fun U => U[σ']) Us ->
      A = ptyp_ty_at p D Us' σs t -> Δ' ⊢ N : A ->
      rec_arg_rel p D (okr_at D ups nr) nr ar dr k ups ups pre pre t v v ->
      ⟦ih v of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
      ⟦ihty v of t under ρ (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ a ->
      DF a ≈ a ∈ per_univ_elem j ↘ R -> R r r -> uidx_le u (ul j) -> iA <= j -> DG a ∈ glu_univ_elem j ↘ P ↘ El ->
      Δ' ⊢ ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σs N t : Typeω@j ->
      Δ' ⊢ ptyp_ih p D oq' Us' (blocks_sub Bks σ') σs N t : ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σs N t ® r ∈ El.

  (** The neutral case at the member [j], which the induction on the ranks
      of the members proves. *)
  Definition neut_ok (j : nat) : Prop :=
    forall Mj hd k' as' e Δ' Us' Ns' M', ind_member D j = Some Mj -> im_ref p j Mj = (hd, k') -> Dom e ≈ e ∈ per_bot ->
      (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (im_ty_at p j Mj Us' Ns')[φ]ʷ) ->
      elim_prop j Δ' Us' Ns' M' (⇑ (d_ind hd k' as') e).

  (** ** The Uniform Parameters *)

  Lemma ups_len : List.length ups = ind_nu D.
  Proof. rewrite (Completeness.Inductives.Model.eval_exps_length _ _ _ HUv); exact HUl. Qed.

  Lemma ups_gargs : per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof. exact (EB Elim.u0_gargs). Qed.

  Lemma ups_RU : RU (env_args nil ups) (env_args nil ups).
  Proof. exact (EB Elim.u0_env). Qed.

  (** The uniform parameters at a substitution glued to [ρ], glued at
      their telescope at [ups]. *)
  Lemma us_glu_args : forall Δ σ, Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
      glu_args Δ (ind_uparams D) Id nil (List.map (fun U => U[σ]) Us) ups.
  Proof.
    intros * Hσ.
    eapply params_glu_args; [ exact Ua | exact (dc_uparams _ Hc) | exact Usem | exact HΓ | exact HRΓ | exact HSbΓ | exact Hσ
                            | rewrite HUl; reflexivity | exact HUs | exact HUg | exact HUv ].
  Qed.

  (** ** The PER Model at [ρ]

      The canonical relations at [ups], and the family of the motives at
      [ρ] on both sides: the eliminator at related elements, and its
      recursive results, are related at it ([per_ind_elim_all]). *)
  Let Hcp := vg_canon p D Hvg ups ups_gargs ups_len.
  #[local] Abbreviation HnP := (icp_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (icp_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (icp_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (icp_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (icp_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (icp_dom_iff _ _ Hcp).
  Let Had := vg_adm p D Hvg ups ups ups_gargs ups_len ups_gargs.
  Let Hups := EB Elim.ups_ok ups ups ups_RU ups_RU ups_len ups_len.
  Let Hnm : blocks_nm_ok D Bks := vbs_nm _ _ _ _ _ _ HBv.
  Let Hna := vbs_names _ _ _ _ _ _ HBv.
  Let Har := vbs_arity _ _ _ _ _ _ HBv.
  Let Hnd := dt_nodup _ _ _ Hdt.
  #[local] Abbreviation Rel := (fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args ρ (ns ++ m :: nil)) (env_args ρ (ns' ++ m' :: nil))).

  Lemma mot_rel : forall j Mj ba bb u u' ns ns' m m', ind_member D j = Some Mj ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> G j u u' ns ns' m m' ->
      exists a a', ⟦ eb_motive ba ⟧ env_args ρ (ns ++ m :: nil) ↘ a /\ ⟦ eb_motive bb ⟧ env_args ρ (ns' ++ m' :: nil) ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns m ns' m'.
  Proof.
    intros * HMj Hba Hbb Hm; rewrite Hba in Hbb; injection Hbb as <-.
    exact (EB Elim.mot_mid ρ Hρ Bks iA HMall j Mj ba (eb_motive ba) HMj Hba (HAv _ _ _ HMj Hba) _ _ _ _ _ _ Hm).
  Qed.

  Lemma br_rel : forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k', ind_member D j = Some Mj ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> ind_con Mj c = Some gs ->
      brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
      G j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
      rec_results_rel dr Rel j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') gs vs vs' ihs ihs' ->
      exists r r', ⟦ Ba ⟧ env_args ρ (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ↘ r /\
        ⟦ Bb ⟧ env_args ρ (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ↘ r' /\
        Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs)) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r'.
  Proof.
    refine (EB Elim.br_mid ρ Hρ Bks iA HBks HMall HAv (vbs_bctx _ _ _ _ _ _ HBv) Bks _).
    intros * HMj Hb Hb' Hcon HlB HlB'; rewrite Hb in Hb'; injection Hb' as <-.
    rewrite HlB in HlB'; injection HlB' as <-.
    exact (vbs_branch _ _ _ _ _ _ HBv _ _ _ _ _ _ _ HMj Hb Hcon (brs_lookup_in _ _ _ _ HlB)).
  Qed.

  #[local] Abbreviation ER f := (f p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had (ul iA) ρ ρ Bks Bks ups ups Hups Rel
     HBks HBks Hnm Hnm Hna Hna Har Har Hnd mot_rel br_rel).
  (** The eliminator's PER facts at [ρ] and [ups] ([per_ind_elim_all]); a
      definition, so that its statement stays out of proof contexts. *)
  Definition per_elim_at_ups := ER per_ind_elim_all.

  (** ** Instances of Closed Telescopes at [ρ]

      A type of a closed telescope over the uniform parameters, at its
      instance at [τU] in [ρ] extended by values related at the telescope
      at [ups], against the type at [ups] and those values. *)
  Lemma inst_link : forall Pre X (j : nat) zs, tele_ass (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
      ⊨ tele_sub Pre τU ++ Γ -> Pre ++ ind_uparams D ⊨ X : Typeω@j ->
      per_gargs (List.rev Pre) (env_args nil ups) (env_args nil ups) zs zs -> List.length zs = List.length Pre ->
      exists a b, ⟦ X[sb_qn (List.length Pre) τU] ⟧ env_args ρ zs ↘ a /\ ⟦ X ⟧ env_args nil (ups ++ zs) ↘ b /\
        Dom a ≈ b ∈ per_univ j.
  Proof.
    intros * HKa HK HS HX Hg Hlz.
    pose proof (EB Elim.cv_gen Pre HKa HK HS ρ ρ ups ups Hρ HUv HUv ups_RU ups_RU zs zs Hg Hlz) as Hg'.
    destruct (rel_ctx_wf_per_ctx_env HS) as [RS HRS].
    pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS HS Hρ ltac:(rewrite length_tele_sub; exact Hlz) Hg') as HE.
    destruct (rel_ctx_wf_per_ctx_env HK) as [RK HRK].
    pose proof (EB Elim.closed_pre_base Pre RK HKa HK HRK ρ ups zs ups_RU ups_len Hg Hlz) as HF.
    exact (closed_typ_inst Pre (ind_uparams D) Γ X j τU RΓ RK RS ρ zs (env_args ρ ups) (env_args nil (ups ++ zs))
             HKa HK Ua Usem HΓ HRΓ HRK HRS HX
             (Instance.gsub_valid (Elim.gsub_U VP p D HVP HPD Γ HΓ Us HUl HUs)) HE Hlz
             (Decl.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) HUv) HF).
  Qed.

  (** The type of an entry of the instance at [τU] of a closed telescope,
      against the entry's type at [ups]. *)
  Lemma inst_entry_link : forall C, tele_ass (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D -> ⊨ tele_sub C τU ++ Γ ->
      forall zs, per_gargs (List.rev C) (env_args nil ups) (env_args nil ups) zs zs -> List.length zs = List.length C ->
      forall k A' a, List.nth_error (List.rev (tele_sub C τU)) k = Some (ce_ass A') -> ⟦ A' ⟧ env_args ρ (List.firstn k zs) ↘ a ->
        exists A b (j : nat), List.nth_error (List.rev C) k = Some (ce_ass A) /\
          ⟦ A ⟧ env_args nil (ups ++ List.firstn k zs) ↘ b /\ Dom a ≈ b ∈ per_univ j.
  Proof.
    intros C HCa HCs HCS zs Hpg Hlz k A' a HA' Ea.
    assert (HCa' : tele_ass C) by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
    assert (HeA : exists A, e = ce_ass A).
    { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
      unfold tele_ass in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
    destruct HeA as [A ->].
    pose proof He as He0.
    destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
    rewrite <- HPl in HA'; rewrite nth_rev_tele_sub in HA'; injection HA' as <-.
    rewrite <- List.app_assoc in HCa, HCs; cbn [List.app] in HCa, HCs.
    assert (HKa : tele_ass (Pre ++ ind_uparams D))
      by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [_ H]; inversion H; assumption).
    pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCs) as HK1.
    destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HK1) as [j HX].
    pose proof (rel_ctx_wf_tail HK1) as HK.
    rewrite tele_sub_app, <- List.app_assoc in HCS; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCS) as HS1.
    cbn [tele_sub List.app] in HS1; pose proof (rel_ctx_wf_tail HS1) as HS.
    rewrite List.rev_app_distr in Hpg; cbn [List.rev] in Hpg; rewrite <- List.app_assoc in Hpg.
    rewrite <- (List.firstn_skipn k zs) in Hpg.
    rewrite !List.length_app in Hlz; cbn in Hlz.
    assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_firstn, List.length_rev; lia).
    destruct (Decl.per_gargs_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
      as [Hg1 _].
    destruct (inst_link Pre A j (List.firstn k zs) HKa HK HS HX Hg1 ltac:(rewrite List.length_firstn; lia)) as (a1 & b & Ea1 & Eb & Hab).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    exists A, b, j; split; [ exact He0 | split; [ exact Eb | exact Hab ] ].
  Qed.

  (** Glued arguments of a closed telescope over the uniform parameters,
      at its types at [ups], are glued arguments of its instance at [τU],
      over a substitution glued to [ρ]. *)
  Lemma tele_inst_args : forall C, tele_ass (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D ->
      ⊨ tele_sub C τU ++ Γ -> ctx_scoped (ind_nu D) C ->
      forall Δ' σ' Ms zs, glu_args Δ' C (sb_of_list Id (List.map (fun U => U[σ']) Us)) (env_args nil ups) Ms zs ->
        per_gargs (List.rev C) (env_args nil ups) (env_args nil ups) zs zs ->
        glu_args Δ' (tele_sub C τU) σ' ρ Ms zs.
  Proof.
    intros C HCa HCs HCS HCsc Δ' σ' Ms zs Hg Hpg.
    assert (HCa' : tele_ass C) by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [LM Lz].
    apply (glu_args_link Δ' C (tele_sub C τU) (sb_of_list Id (List.map (fun U => U[σ']) Us)) σ' (env_args nil ups) ρ Ms zs);
      [ rewrite length_tele_sub; reflexivity | | exact Hg | |].
    - rewrite tele_insts_tele_sub; symmetry; apply (tele_insts_base_agree _ (ind_nu D)); [ exact HCa' | exact HCsc |].
      intros x Hx; cbn [sb_compose]; unfold τU; apply sb_of_list_lt_compose; lia.
    - intros k A A' a HA HA' Hk Ea.
      destruct (ctx_rev_split C k _ HA) as (C1 & Pre & -> & HPl).
      rewrite <- HPl in HA'; rewrite nth_rev_tele_sub in HA'; injection HA' as <-.
      rewrite <- List.app_assoc in HCa, HCs; cbn [List.app] in HCa, HCs.
      assert (HKa : tele_ass (Pre ++ ind_uparams D))
        by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [_ H]; inversion H; assumption).
      pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCs) as HK1.
      destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HK1) as [j HX].
      pose proof (rel_ctx_wf_tail HK1) as HK.
      rewrite tele_sub_app, <- List.app_assoc in HCS; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCS) as HS1.
      cbn [tele_sub List.app] in HS1; pose proof (rel_ctx_wf_tail HS1) as HS.
      rewrite List.rev_app_distr in Hpg; cbn [List.rev] in Hpg; rewrite <- List.app_assoc in Hpg.
      rewrite <- (List.firstn_skipn k zs) in Hpg.
      assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_rev, List.length_firstn; lia).
      destruct (Decl.per_gargs_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
        as [Hg1 _].
      destruct (inst_link Pre A j (List.firstn k zs) HKa HK HS HX Hg1 ltac:(rewrite List.length_firstn; lia)) as (a1 & b & Ea1 & Eb & Hab).
      rewrite <- env_args_app in Ea.
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      exists a1, j; split; assumption.
    - intros k e' He'.
      assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
      assert (HeA : exists A, e = ce_ass A).
      { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
        unfold tele_ass in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
      destruct HeA as [A ->].
      destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
      rewrite <- HPl in He'; rewrite nth_rev_tele_sub in He'; injection He' as <-.
      exists A; split; [ exact He | eexists; reflexivity ].
  Qed.

  (** ** The Motive's Context, Glued

      The instance of the member [j]'s type at a substitution [σ'] glued
      to [ρ] and non-uniform parameters [Ns']. *)
  Lemma mty_inst : forall j Mj σ' Ns', ind_member D j = Some Mj -> List.length Ns' = im_nn Mj ->
      (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))[sb_of_list σ' Ns']
      = im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns'.
  Proof.
    intros * HMj HNl.
    rewrite ind_mty_sub by (try exact Hc; rewrite List.length_map; exact HUl).
    rewrite List.map_map, <- HNl, map_shift_sb_of_list, vars_from_sb_of_list.
    unfold ind_mty; rewrite HMj; reflexivity.
  Qed.

  (** The substitution of the motive's context at glued non-uniform
      parameters and a scrutinee glued at its type's value. *)
  Lemma mctx_glu_sub : forall j Mj SbM, ind_member D j = Some Mj -> EG elim_mctx p D j Mj Us ++ Γ ∈ glu_ctx_env ↘ SbM ->
      forall Δ' σ' Ns' ns M' m hd k' pre, Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      glu_nparams j Mj NEl Δ' (List.map (fun U => U[σ']) Us) Ns' ns ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      (forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
         Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
         Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® m ∈ El) ->
      Δ' ⊢ˢ sb_of_list σ' (Ns' ++ M' :: nil) ® env_args ρ (ns ++ m :: nil) ∈ SbM.
  Proof.
    intros j Mj SbM HMj HSbM * Hσ' Hgn Hns Hr Hgl.
    pose proof (HMall _ _ HMj) as HMm.
    pose proof (rel_ctx_wf_tail HMm) as HNt.
    pose proof (member_params_ass D Hc _ _ HMj) as HPa.
    pose proof (vid_params _ HD _ _ HMj) as HPs.
    pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf j Mj Δ' _ Ns' ns HMj Hgn Hns) as Hg0.
    pose proof (EB Completeness.Inductives.Elim.nparams_closed_of_canon j Mj HMj ns ns Hns) as Hpg.
    pose proof (tele_inst_args (im_nparams Mj) HPa HPs HNt (decl_closed_nparams_scoped D Hc j Mj HMj) Δ' σ' Ns' ns Hg0 Hpg) as Hg1.
    destruct (glu_args_length _ _ _ _ _ _ Hg1) as [LN Ln]; rewrite length_tele_sub, length_im_nparams in LN, Ln.
    assert (HassN : tele_ass (tele_sub (im_nparams Mj) τU)) by (apply tele_ass_sub, (decl_closed_nparams_ass D Hc _ _ HMj)).
    eapply glu_sub_of_list; [ exact (elim_mctx_ass p D j Mj Us Hc HMj) | exact HSbM | exact HSbΓ | exact Hσ' |].
    unfold elim_mctx; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R).
    apply glu_args_app; [ exact HassN | rewrite length_tele_sub, length_im_nparams; exact LN
                        | rewrite length_tele_sub, length_im_nparams; exact Ln |].
    split; [ exact Hg1 |].
    change (ce_ass ?H0 :: nil) with (nil ++ ce_ass H0 :: nil).
    apply (proj2 (glu_args_snoc _ nil _ _ _ _ _ _ _)); split; [| apply glu_args_nil ].
    rewrite (mty_inst j Mj σ' Ns' HMj LN).
    (** The type's value at [ρ] and [ns], against the scrutinee's. *)
    destruct (Completeness.Inductives.Elim.mty_vars_valid p D Hvg Hcv j Mj HMj) as [jx HX].
    destruct (inst_link (im_nparams Mj) _ jx ns HPa HPs HNt HX Hpg ltac:(rewrite length_im_nparams; exact Ln))
      as (a & b & Ea & Eb & Hab).
    unfold τU in Ea; rewrite length_im_nparams, (Completeness.Inductives.Elim.mty_vars_inst p D j Mj Us Hc HUl) in Ea.
    destruct (rel_ctx_wf_per_ctx_env HPs) as [RK HRK].
    assert (HKE : RK (env_args nil (ups ++ ns ++ nil)) (env_args nil (ups ++ ns ++ nil))).
    { rewrite List.app_nil_r.
      apply (gargs_env_rel _ _ _ _ _ _ HRK HPs); [ rewrite !List.length_app, length_im_params, ups_len; unfold im_np, ind_nu in *; lia |].
      exact (Completeness.Inductives.Model.params_gargs D HD Hc Hsu j Mj HMj ups ups bu ns ns ups_gargs ups_len Hbu Hns). }
    replace (ups ++ ns) with (ups ++ ns ++ nil) in Eb by (rewrite List.app_nil_r; reflexivity).
    destruct (mty_val_rel VP HVP p D HPD ups ups_len ups_gargs j Mj hd k' pre (im_nparams Mj) RK ns nil 0 b ns HMj Hr HPs HRK
                ltac:(rewrite List.app_nil_r, length_im_nparams; exact Ln) Ln eq_refl HKE Eb Hns) as (i0 & R0 & H0).
    destruct (Decl.per_univ_elem_to_nat _ _ _ _ H0) as [n0 Hn0].
    assert (Hda : Dom d_ind hd k' (pre ++ ns) ≈ a ∈ per_univ n0)
      by (eapply per_univ_trans'; [ exists R0; exact Hn0 | apply per_univ_sym'; exact Hab ]).
    (** The scrutinee, glued at a gluing of its type's value above [nb]. *)
    assert (Hdd : Dom d_ind hd k' (pre ++ ns) ≈ d_ind hd k' (pre ++ ns) ∈ per_univ n0)
      by (eapply per_univ_trans'; [ exact Hda | apply per_univ_sym'; exact Hda ]).
    set (i := Nat.max n0 nb).
    destruct Hdd as [Rd HRd]; pose proof (per_univ_elem_cumu_ge n0 i _ _ _ ltac:(unfold i; lia) HRd) as HRdi.
    destruct (per_univ_glu_univ_elem i _ (ex_intro _ Rd HRdi)) as (P & El & Hglu).
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    pose proof (mty_glu VP HVP HGall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf nb Hnbu Hnbq
                  j Mj hd k' pre Δ' _ Ns' ns i P El ltac:(unfold i; lia) HMj Hr HΔ' (us_glu_args Δ' σ' Hσ') Hgn Hns Hglu) as HTP.
    pose proof (Hgl i P El ltac:(unfold i; lia) Hglu HTP) as HMg.
    destruct (glu_transfer_per_elem i n0 _ _ P El Δ' _ M' m Hglu Hda HTP HMg) as (k1 & P1 & El1 & Hg1' & HP1 & HM1).
    exact (mk_glu_arg _ _ _ _ _ _ k1 a P1 El1 Ea Hg1' HP1 HM1).
  Qed.

  (** The motive of the member [j]'s block at glued non-uniform parameters
      and scrutinee: its value, and its instance glued at any gluing of
      it. *)
  Lemma motive_glu : forall j Mj Δ' σ' Ns' ns M' m hd k' pre, ind_member D j = Some Mj -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      glu_nparams j Mj NEl Δ' (List.map (fun U => U[σ']) Us) Ns' ns ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      (forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
         Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
         Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® m ∈ El) ->
      exists a, ⟦ List.nth j (blocks_motives Bks) a_True ⟧ env_args ρ (ns ++ m :: nil) ↘ a /\ Dom a ≈ a ∈ per_univ iA /\
        forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
          Δ' ⊢ (List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)] ® P.
  Proof.
    intros * HMj Hσ' Hgn Hns Hr Hgl.
    destruct (HBks _ _ HMj) as [b Hb]; rewrite (blocks_motives_nth _ _ _ Hb).
    pose proof (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMj Hb) as HAg.
    destruct HAg as [SbM HSbM iM HAg'].
    pose proof (mctx_glu_sub j Mj SbM HMj HSbM Δ' σ' Ns' ns M' m hd k' pre Hσ' Hgn Hns Hr Hgl) as Hτ.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMj Hb) Hτ) as (_ & a & Ea & Hpa & HPa).
    exists a; split; [ exact Ea | split; [ exact Hpa |] ].
    intros P El Hg; pose proof (HPa P El Hg) as H.
    rewrite <- exp_sub_qn_of_list in H.
    pose proof (gnp_len _ _ _ _ _ _ _ Hgn) as LN.
    replace (List.length (Ns' ++ M' :: nil)) with (S (im_nn Mj)) in H by (rewrite List.length_app, LN; cbn; lia).
    exact H.
  Qed.

  (** ** Recursive Results

      The group of the eliminator at a member, as [elim_at] writes it. *)
  Lemma elim_at_grp' : forall oq j Mj, (oq = Some p \/ oq = None) -> ind_member D j = Some Mj ->
      elim_grp D (if ind_has_views D then Some p else oq) p j.
  Proof.
    intros oq j Mj Hoq HMj.
    destruct (ind_has_views D) eqn:Hv; [ left; reflexivity |].
    destruct Hoq as [-> | ->]; [ left; reflexivity | right; split; [ reflexivity |] ].
    apply (dt_order _ _ _ Hdt _ _ HMj); exact (no_views_decl _ _ _ Hv HMj).
  Qed.

  (** At the end of a shape, the recursive result is the eliminator at the
      argument, an element of the member the shape ends in. *)
  Lemma rec_self_case : forall k Δ' Us' pre j0 Mj Ps A N v, ind_member D j0 = Some Mj ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr -> A = im_ty_at p j0 Mj Us' Q ->
         List.length Q = im_nn Mj /\ tele_rel (nr j0) (List.rev (im_nparams Mj)) bsr bsr /\
         (forall bsr', tele_rel (nr j0) (List.rev (im_nparams Mj)) bsr bsr' ->
            glu_nparams j0 Mj NEl Δ' Us' Q bsr' /\
            forall Δ φ, Δ ⊢ᵏ φ : Δ' -> glu_params_top D Mj Δ (List.map (fun P => P[φ]ʷ) (Us' ++ Q)) (ups ++ bsr'))) ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr -> A = im_ty_at p j0 Mj Us' Q ->
         forall Δ φ Us'' Q', Δ ⊢ᵏ φ : Δ' -> List.length Us'' = ind_nu D ->
           exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us' ++ Q)) (Us'' ++ Q') ->
           elim_prop j0 Δ Us'' Q' N[φ]ʷ v) ->
      rec_prop k Δ' Us' pre (pt_self j0 Ps) A N v.
  Proof.
    intros * HMj Hs1 IH; unfold rec_prop.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σ' oq' σs r a j R P El HMk Hc0 Hpre Hms Hws Hsk Hys Hoq Hσ' HUs' HA HN Hsh Er Ea HR Hr
           Huj HiAj Hg HIT.
    destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs0 & Ebs & Ebs0 & _ & _ & Hir).
    pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->.
    inversion Er; subst.
    match goal with H : ⟦elim v at j0 of _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H into Er' end.
    inversion Ea; subst.
    match goal with H : ⟦ List.nth j0 _ _ ⟧ _ ⍮ _ ⍮ env_args ρ (?b0 ++ v :: nil) ↘ a |- _ => rename H into Ea'; rename b0 into bs' end.
    match goal with H : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ bs' |- _ => pose proof (functional_eval_exps' _ _ _ _ H Ebs) as -> end.
    set (Q := List.map (fun P0 => P0[σs]) Ps) in *.
    assert (HAQ : ptyp_ty_at p D (List.map (fun U => U[σ']) Us) σs (pt_self j0 Ps) = im_ty_at p j0 Mj (List.map (fun U => U[σ']) Us) Q)
      by (cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
    pose proof HN as HN'; rewrite HAQ in HN'.
    destruct (Hs1 _ Q Ebs HAQ) as (HQl & Hbs & Hgn).
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    pose proof (kripke_id _ HΔ') as Hid.
    destruct (Hgn bs Hbs) as [Hgn' Htop].
    assert (HUl' : List.length (List.map (fun U => U[σ']) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
    pose proof (IH _ Q Ebs HAQ Δ' wk_id _ Q Hid HUl'
                  ltac:(pose proof (glu_params_top_refl _ _ _ _ _ (Htop _ _ Hid)) as H; rewrite map_wk_id in H; rewrite map_wk_id; exact H)) as HE.
    rewrite exp_wk_id in HE.
    destruct (HE Mj σ' _ bs HMj (elim_at_grp' oq' j0 Mj Hoq HMj) Hσ' eq_refl HN' Hgn' Hbs Hir) as [r' a' Er'' Ea'' Haa Hgl].
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Er'' Er') as ->.
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Haa) as (P0 & El0 & Hg0).
    pose proof (Hgl P0 El0 Hg0) as HE0.
    cbn [ptyp_ih ptyp_ihty]; unfold elim_at; rewrite (blocks_motives_sub D Bks σ' j0 Mj Hnm HMj).
    eapply glu_univ_elem_exp_cumu_ge; [ exact HiAj | exact Hg0 | exact Hg | exact HE0 ].
  Qed.

  (** The recursive result of a function shape and its type, under the
      binder, at a weakening and an argument. *)
  Lemma ih_body_inst : forall oq σ' σs N t φ e,
      (ptyp_ih p D oq (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (blocks_wk (blocks_sub Bks σ') ↑)
         (q σs) (a_app N[↑]ʷ (a_var 0)) t)[sb_extend (ι φ) e]
      = ptyp_ih p D oq (List.map (fun U => U[sb_wk σ' φ]) Us) (blocks_sub Bks (sb_wk σ' φ))
          (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) t.
  Proof.
    intros; rewrite ptyp_ih_sub
      by (first [ exact Hc | rewrite !List.length_map; exact HUl | apply blocks_nm_ok_wk, blocks_nm_ok_sub, Hnm ]).
    f_equal.
    - rewrite !List.map_map; apply List.map_ext; intros U; rewrite exp_shift_extend_wk_e, exp_wk_sub; reflexivity.
    - apply blocks_step.
    - cbn [exp_sub]; rewrite exp_shift_extend_wk_e; reflexivity.
  Qed.

  Lemma ih_cod_inst : forall σ' σs N t φ e Mm, ind_member D (ptyp_mem t) = Some Mm ->
      List.length (ptyp_ps t) = im_nn Mm ->
      (ptyp_ihty (blocks_motives (blocks_sub Bks σ')) (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t)[sb_extend (ι φ) e]
      = ptyp_ihty (blocks_motives (blocks_sub Bks (sb_wk σ' φ))) Id (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) t.
  Proof.
    intros * HMm HPl; rewrite ptyp_ihty_sub; cbn [exp_sub]; rewrite exp_shift_extend_wk_e.
    rewrite (ptyp_ihty_sb_eq _ _ _ (ι φ ⨟ Id) _ _ _ (fun z => eq_refl) (fun z => eq_refl)).
    apply ptyp_ihty_base.
    rewrite HPl, !(blocks_motives_sub D Bks _ _ Mm Hnm HMm).
    symmetry; apply exp_sub_sub_ext, sb_qn_compose_ext; symmetry; apply sb_wk_compose.
  Qed.

  (** The member a recursive argument's shape ends in, and the shape's
      terms' freedom from module variables. *)
  Lemma rec_shape_facts : forall k Mk c0 gs1 t0 gs2 d, ind_member D k = Some Mk ->
      ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
      (exists Mj, ind_member D (ptyp_mem (ptyp_skip d t0)) = Some Mj /\ List.length (ptyp_ps (ptyp_skip d t0)) = im_nn Mj) /\
      List.Forall (exp_mvc 0) (ptyp_doms (ptyp_skip d t0)) /\ List.Forall (exp_mvc 0) (ptyp_ps (ptyp_skip d t0)).
  Proof.
    intros * HMk Hc0.
    rewrite ptyp_mem_skip, ptyp_ps_skip, ptyp_doms_skip.
    split; [ exact (vid_plen _ HD k Mk c0 _ HMk Hc0 gs1 t0 gs2 eq_refl) |].
    destruct (dmv_members _ (dt_mvc _ _ _ Hdt) _ _ HMk) as (_ & _ & Hcm).
    pose proof (Hcm _ _ (cons_lookup_in _ _ _ Hc0)) as Hf0.
    apply List.Forall_app in Hf0 as [_ Hf0]; inversion Hf0 as [| ? ? Hct _]; subst; cbn in Hct; destruct Hct as [Hd Hp].
    split; [| exact Hp ].
    rewrite <- (List.firstn_skipn d (ptyp_doms t0)) in Hd; apply List.Forall_app in Hd as [_ Hd]; exact Hd.
  Qed.

  (** At a domain of a shape, the recursive result is a function of the
      domain, glued at the [Π] by the induction at the rest of the shape. *)
  Lemma rec_pi_case : forall k Δ' Us' pre B t A N v,
      (forall IT OT, A = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® DP k pre B) ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Δ' -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
         rec_prop k Δ (List.map (fun U => U[φ]ʷ) Us') (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
      rec_prop k Δ' Us' pre (pt_pi B t) A N v.
  Proof.
    intros * Hq1 Hq2 IH3; unfold rec_prop.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σ' oq' σs r a j R P El HMk Hc0 Hpre Hms Hws Hsk Hys Hoq Hσ' HUs' HA HN Hsh Er Ea HR Hr
           Huj HiAj Hg HIT.
    subst A pre Us'.
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hsk'].
    destruct (rec_shape_facts k Mk c0 gs1 t0 gs2 (S d) HMk Hc0) as ((Mj & HMj & HPl) & Hmd & Hmp).
    rewrite Hsk' in HMj, HPl, Hmd, Hmp.
    cbn [ptyp_ty_at ptyp_ih ptyp_ihty] in HN, HIT, Hq1, Hq2, IH3 |- *.
    set (IT := B[σs]) in *.
    set (OTy := ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (q σs) t) in *.
    specialize (Hq1 _ _ eq_refl); specialize (Hq2 _ _ eq_refl); specialize (IH3 _ _ eq_refl).
    pose proof (eval_ih_pi_inv _ _ _ _ _ _ _ _ Er) as ->.
    destruct (eval_ihty_pi_inv _ _ _ _ _ _ _ Ea) as (b1 & Eb1 & ->).
    pose proof HR as HRsave.
    basic_invert_per_univ_elem HR.
    match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
    match goal with H : _ <~> (fun _ _ => forall _ _ _, rel_mod_app _ _ _ _ _) |- _ => rename H into HRE end.
    destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' Hg) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & HEleq).
    pose proof (ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hms Hc0 eq_refl Hws HB Hys Eb1) as HgD.
    destruct (wf_pi_inversion' HIT) as [HITt HOTt].
    assert (HIT' : forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® IP).
    { intros Δ φ Hφ.
      eapply (glu_typ_transfer u (ul j) (ul j)); [ exact Huj | apply uidx_le_refl | eexists; exact equiv_a_a' | exact HgD
                                                 | exact Hgb1 | exact (Hq1 _ _ Hφ) ]. }
    assert (HDEl : forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                     Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k (ms ++ ws ++ ys) B).
    { intros * Hφ Hb.
      eapply glu_elem_retype; [ exact Hgb1 | exact HgD | exact (glu_univ_elem_trm_typ _ _ _ _ Hgb1 _ _ _ _ Hb) | exact Hb
                              | exact (Hq1 _ _ Hφ) ]. }
    set (body := ptyp_ih p D oq' (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (blocks_wk (blocks_sub Bks σ') ↑)
                   (q σs) (a_app N[↑]ʷ (a_var 0)) t).
    set (OTi := ptyp_ihty (blocks_motives (blocks_sub Bks σ')) (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t).
    assert (Happ : forall Δ φ b c (equiv_c : in_rel c c), Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                     exists rc a2, $| d_ihfn ρ Bks p ups t v & c | gc_deps ⍮ gc_stack ↘ rc /\
                       ⟦ fam_cod ⟧ (nil ↦ d_ihfam ρ (blocks_motives Bks) (env_args nil (ups ++ ms ++ ws ++ ys)) t v) ↦ c ↘ a2 /\
                       Δ ⊢ body[(ι φ),,b] : OTi[(ι φ),,b] ® rc ∈ OEl c equiv_c).
    { intros * Hφ Hb.
      pose proof (rel_dr ups k _ _ _ _ _ c Eb1 equiv_a_a' equiv_c) as Hdc.
      pose proof (HDEl _ _ _ _ Hφ Hb) as HbD.
      destruct (Hq2 _ _ _ _ Hφ Hdc HbD) as [fc Efc].
      pose proof (IH3 _ _ _ _ _ Hφ Hdc HbD Efc) as IH'.
      destruct (Hcod _ _ equiv_c) as [a2 a2' Ea2 Ea2' Ha22].
      assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
      destruct (proj1 (HRE _ _) Hr _ _ equiv_c) as [rc rc' Erc Erc' Hrc].
      assert (rc' = rc) as -> by (eapply functional_eval_app; eassumption).
      destruct (eval_fam_cod_ihfam_inv _ _ _ _ _ _ _ Ea2) as (fx & Efx & Ea2i).
      assert (fx = fc) as -> by (eapply functional_eval_app; eassumption).
      destruct (eval_app_ihfn_inv _ _ _ _ _ _ _ _ Erc) as (y & Ey & Erc0).
      assert (y = fc) as -> by (eapply functional_eval_app; eassumption).
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hdc) as (r0 & r0' & Er0 & Er0' & Hsh').
      assert (r0 = fc) as -> by (eapply functional_eval_app; eassumption).
      assert (r0' = fc) as -> by (eapply functional_eval_app; eassumption).
      exists rc, a2; split; [ exact Erc | split; [ exact Ea2 |] ].
      pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hb) as Hbt.
      unfold body, OTi; rewrite ih_body_inst, (ih_cod_inst _ _ _ _ _ _ Mj HMj HPl); cbn [sentry_exp].
      replace (List.map (fun U => U[sb_wk σ' φ]) Us) with (List.map (fun U => U[φ]ʷ) (List.map (fun U => U[σ']) Us))
        by (rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub).
      eapply (IH' Mk ms c0 gs1 t0 gs2 ws (S d) (ys ++ c :: nil) (sb_wk σ' φ) oq' (q σs ⨟ ((ι φ),,b)) rc a2 j _ _ _);
        [ exact HMk | exact Hc0 | rewrite <- !List.app_assoc; reflexivity | exact Hms | exact Hws | exact Hsk'
        | | exact Hoq | exact (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) | | | | exact Hsh' | exact Erc0 | | exact Ha22
        | exact Hrc | exact Huj | exact HiAj | exact (Hcodg _ equiv_c _ Ea2) |].
      - apply tele_prefix_rel_snoc; [ exact Hys |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hdc.
      - rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub.
      - unfold OTy; apply (shape_ty_step VP HVP p D HPD); rewrite List.length_map; exact HUl.
      - exact (app_wk_typed _ _ _ _ _ _ _ HN Hφ Hbt).
      - replace (ups ++ (ms ++ ws ++ ys) ++ c :: nil) with ((ups ++ ms ++ ws ++ ys) ++ c :: nil)
          by (rewrite <- !List.app_assoc; reflexivity).
        rewrite env_args_snoc; exact Ea2i.
      - pose proof (ih_cod_inst σ' σs N t φ (se_exp b) Mj HMj HPl) as E; cbn [sentry_exp] in E; rewrite <- E.
        exact (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ Hbt). }
    (** The body's type, at the generic variable. *)
    assert (HITid : Δ' ⊢ IT ® IP) by (pose proof (HIT' Δ' wk_id (kripke_id _ HΔ')) as Hx0; rewrite exp_wk_id in Hx0; exact Hx0).
    assert (HΔIT : ⊢ Δ' ▹ IT) by mauto 3.
    pose proof (var0_glu_elem Hgb1 HITid) as Hvar.
    pose proof (var_per_elem (length Δ') equiv_a_a') as Heqv.
    destruct (Happ _ _ _ _ Heqv (kripke_shift _ _ HΔIT) Hvar) as (rc0 & a0 & _ & Ea0 & Hg0).
    pose proof (glu_univ_elem_trm_escape _ _ _ _ (Hcodg _ Heqv _ Ea0) _ _ _ _ Hg0) as Hbodyt.
    assert (Ebv : body[(ι ↑),,#0] = body).
    { transitivity (body[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold body; rewrite !ih_body_inst; cbn [sentry_exp].
      apply ptyp_ih_exp_agree; [ exact Hmd | apply sb_exp_agree_var0 ]. }
    assert (Eov : OTi[(ι ↑),,#0] = OTi).
    { transitivity (OTi[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold OTi; rewrite !(ih_cod_inst σ' σs N t ↑ _ Mj HMj HPl); cbn [sentry_exp].
      apply ptyp_ihty_agree_exp; [ exact Hmd | exact Hmp | reflexivity | apply sb_exp_agree_var0 ]. }
    rewrite Ebv, Eov in Hbodyt.
    apply HEleq; eapply mk_pi_glu_exp_pred with (IT := IT) (OT := OTi);
      [ apply wf_fn with (i := j); [ exact HITt | exact Hbodyt ]
      | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRsave Hper); exact Hr
      | apply wf_exp_eq_refl; exact HIT | exact HITt | exact HOTt | exact HIT' |].
    intros Δ φ N0 n0 Hφ HN0 equiv_n.
    destruct (Happ _ _ _ _ equiv_n Hφ HN0) as (rc & a2 & Erc & Ea2 & Hgl).
    exists rc; split; [ exact Erc |].
    pose proof (Hcodg _ equiv_n _ Ea2) as Hga2.
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hga2 | exact Hgl |].
    apply wf_exp_eq_sym; eapply fn_wk_beta; [ exact HITt | exact HOTt | exact Hbodyt | exact Hφ
                                          | exact (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ HN0) ].
  Qed.

  (** The recursive results' telescope of a branch, at a substitution
      [σ'] past the non-uniform parameters and the arguments: the
      telescope of the eliminator at [σ']. *)
  Lemma ihs_insts_move : forall k Mk c gs σ' Ns' As L, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      List.length Ns' = im_nn Mk -> List.length As = List.length gs ->
      tele_insts (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs) (sb_of_list σ' (Ns' ++ As)) L
      = tele_insts (ihs_ctx_aux (im_nn Mk) (blocks_motives (blocks_sub Bks σ')) (List.map (fun U => U[σ']) Us)
                      (List.length gs) nil 0 gs) (sb_of_list Id (Ns' ++ As)) L.
  Proof.
    intros * HMk Hcon HNl HAl.
    rewrite (tele_insts_sb_eq _ _ (sb_qn (0 + List.length gs + im_nn Mk) σ' ⨟ sb_of_list Id (Ns' ++ As))).
    2:{ replace (0 + List.length gs + im_nn Mk) with (List.length (Ns' ++ As)) by (rewrite List.length_app; lia).
        symmetry; etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ]. }
    rewrite <- tele_insts_tele_sub.
    rewrite (ihs_ctx_aux_sub (im_nn Mk) (blocks_motives Bks) (blocks_motives (blocks_sub Bks σ')) Us (List.length gs) σ' gs nil 0
               eq_refl); [ reflexivity |].
    intros gs1 t gs2 Heq.
    pose proof (dc_members _ Hc _ _ HMk) as HMc.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    split.
    - rewrite HUl; exact (mc_recs _ _ HMc _ _ _ _ _ Hin Heq).
    - destruct (mc_rec_len _ _ HMc _ _ Hin _ _ _ Heq) as (Mj & HMj & HlMj).
      rewrite HlMj; apply (blocks_motives_sub D Bks σ' _ Mj Hnm HMj).
  Qed.

  (** The value of a branch's type at a constructor's components and
      recursive results in the group, against the motive's at the
      constructor: the branch's type is the motive at the constructor as
      the group reads it ([τb]), related to the constructor in the group. *)
  Lemma bty_val_rel : forall v Mv c gs b, ind_member D v = Some Mv -> ind_con Mv c = Some gs -> List.nth_error Bks v = Some b ->
      forall hd k bs vs ihs ns' abt a0, im_ref p v Mv = (hd, k) ->
      List.length bs = (im_unu D Mv + im_nn Mv)%nat ->
      G v ups ups (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs)) (d_con hd k c (bs ++ vs)) ->
      rec_results_rel dr Rel v ups ups (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs) gs vs vs ihs ihs ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns' (List.skipn (im_unu D Mv) bs) ->
      ⟦ elim_bty p v Mv c gs (eb_motive b) Us ⟧ env_args ρ (List.skipn (im_unu D Mv) bs ++ vs ++ ihs) ↘ abt ->
      ⟦ eb_motive b ⟧ env_args ρ (ns' ++ d_con hd k c (bs ++ vs) :: nil) ↘ a0 ->
      Dom abt ≈ a0 ∈ per_univ iA.
  Proof.
    intros v Mv c gs b HMv Hcon Hbk hd k bs vs ihs ns' abt a0 Href Lbs HGX Hir HnX Eabt Ea0.
    set (X := List.skipn (im_unu D Mv) bs) in *.
    pose proof (vbs_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as HBs.
    destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
    pose proof (EB Completeness.Inductives.Elim.cv_bctx_elem ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs ρ ρ Hρ Hρ
                  ups ups hd k bs bs vs vs ihs ihs HGX Hir RB HRB) as HZ.
    destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lih _].
    destruct (Completeness.Inductives.Elim.rec_results_rel_vs_len _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Hvl _].
    assert (LX : List.length X = im_nn Mv) by (unfold X; rewrite List.length_skipn; lia).
    destruct (rel_exp_under_ctx_simple_at HRB
                (Completeness.Inductives.Elim.bty_con_valid VP p D HVP HPD Γ Us HUl HUs Bks v Mv c gs HMv Hcon HBs) _ _ HZ)
      as (l1 & l2 & El1 & El2 & _).
    pose proof (Completeness.Inductives.Elim.eval_bty p D Us HUl v Mv c gs ρ X vs ihs l1 LX Hvl Lih El1) as Hev.
    pose proof (Completeness.Inductives.Elim.gsub_bty VP p D HVP HPD Γ HΓ Us HUl HUs Bks HMall v Mv c gs HMv Hcon HBs) as Hgs.
    assert (HUb : List.length (List.map (fun U => U[wk_shiftn (im_nn Mv + List.length gs + cargs_nrec gs)]ʷ) Us) = ind_nu D)
      by (rewrite List.length_map; exact HUl).
    assert (LNA : List.length (vars_from (cargs_nrec gs + List.length gs) (im_nn Mv) ++ vars_from (cargs_nrec gs) (List.length gs))
                  = (im_nn Mv + List.length gs)%nat)
      by (rewrite List.length_app, !length_vars_from; lia).
    destruct (Completeness.Inductives.Elim.con_ref_apps_value VP p D HVP HPD v Mv c gs _ _ _ (X ++ vs) l1 HMv Hcon HUb
                (Completeness.Inductives.Elim.eval_bty_args Mv gs ρ X vs ihs LX Hvl Lih) LNA El1) as (cs1 & Lcs1 & El1v).
    rewrite Href in El1v; cbn [fst snd] in El1v; subst l1.
    (** The constructor the branch's type has, against the stored one. *)
    assert (HG1 : G v ups ups X ns' (d_con hd k c (cs1 ++ X ++ vs)) (d_con hd k c (bs ++ vs))).
    { pose proof HGX as H.
      assert (Ebs : bs ++ vs = List.firstn (im_unu D Mv) bs ++ X ++ vs) by (rewrite List.app_assoc, List.firstn_skipn; reflexivity).
      rewrite Ebs in H at 1.
      assert (L1 : List.length (List.firstn (im_unu D Mv) bs) = im_unu D Mv) by (rewrite List.length_firstn; lia).
      assert (L2 : List.length cs1 = List.length (List.firstn (im_unu D Mv) bs)) by (rewrite L1; exact Lcs1).
      pose proof (Completeness.Inductives.Elim.ind_rel_con_prefix_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (List.firstn (im_unu D Mv) bs) cs1 (X ++ vs) Mv HMv L1 L2 H) as H'.
      pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
      pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HMv _ _ HnX) as HXX.
      exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ v Mv _ _ _ _ _ _ _ _ HMv H' HXX (tsym _ _ HMv _ _ HnX)). }
    destruct (mot_rel v Mv b b ups ups X ns' _ _ HMv Hbk Hbk HG1) as (a1 & a2 & Ea1 & Ea2 & Hr12).
    assert (a2 = a0) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (typ_inst_val _ _ _ _ _ _ _ _ _ _ (HAv _ _ _ HMv Hbk) HRB (Instance.gsub_valid Hgs) HZ Hev Eabt Ea1) as H1.
    eapply per_univ_trans'; [ exact H1 | exists (Rel v X (d_con hd k c (cs1 ++ X ++ vs)) ns' (d_con hd k c (bs ++ vs))); exact Hr12 ].
  Qed.

  (** ** On a Constructor

      The constructor [c] of the member [k], glued in the group, at a
      substitution [σ'] glued to [ρ]: the eliminator is the branch of [c]
      in [k]'s block at the non-uniform parameters, the arguments and the
      recursive results ([ι]); the branch is glued at the substitution of
      them, the arguments glued at their own types ([AtType]), the
      recursive results by the induction. *)
  Section ConCase.
    Variables (k : nat) (Mk : imember) (hd : qname) (k' : nat) (c : String.string) (gs : list carg)
      (Us' Ns' : list exp) (bs vs : list domain) (As : list exp) (Δ' : ctx) (M' : exp).
    Hypotheses (HMk : ind_member D k = Some Mk) (Href : im_ref p k Mk = (hd, k')) (Hcon : ind_con Mk c = Some gs)
      (HUl' : List.length Us' = ind_nu D) (HNl' : List.length Ns' = im_nn Mk)
      (Hbl : List.length bs = (im_unu D Mk + im_nn Mk)%nat) (Hvl : List.length vs = List.length gs)
      (HAl : List.length As = List.length gs)
      (HMeq : Δ' ⊢ M' ≈ apps (a_con p k c) (Us' ++ Ns' ++ As) : im_ty_at p k Mk Us' Ns')
      (Hb : tele_rel (nr k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs))
      (Hv : tele_rel (ar k (List.skipn (im_unu D Mk) bs) c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs))
      (Hnp : glu_nparams k Mk NEl Δ' Us' Ns' (List.skipn (im_unu D Mk) bs))
      (HAs : forall j N A, List.nth_error As j = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) j = Some A -> Δ' ⊢ N : A)
      (Harg : forall gs1 A0 gs2 N A v, gs = gs1 ++ ca_arg A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Δ' ⊢ N : A ® v ∈ AEl k (List.skipn (im_unu D Mk) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)))
      (Hrec : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec p D ups NEl AEl DP DEl k Δ' Us' (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N v)
      (IH : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          rec_prop k Δ' Us' (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N v).
    Variables (σ' : sub) (oq' : option qname) (ns : list domain).
    Hypotheses (Hgrp : elim_grp D oq' p k) (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HUs' : Us' = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : im_ty_at p k Mk Us' Ns') (Hgn : glu_nparams k Mk NEl Δ' Us' Ns' ns)
      (Hns : tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns)
      (HGm : G k ups ups ns ns (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs ++ vs))).
    #[local] Abbreviation X := (List.skipn (im_unu D Mk) bs).

    (** The scrutinee's parameters against the stored ones, and the
        arguments related. *)
    Lemma cc_rel : tele_rel (nr k) (List.rev (im_nparams Mk)) ns X /\
        con_args_rel p D (okr_at D ups nr) nr ar dr k ups ups X X gs vs vs.
    Proof.
      unfold grp_rel in HGm; inversion HGm; subst.
      match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HMk in H1; injection H1 as <- end.
      match goal with H1 : ind_con Mk c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
      repeat match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => apply app_split_eq in E; [| lia ]; destruct E as [-> ->] end.
      split; assumption.
    Qed.

    Lemma cc_LX : List.length X = im_nn Mk.
    Proof. rewrite List.length_skipn; lia. Qed.

    (** The non-uniform parameters and the arguments, glued at the instance
        of their closed telescope at [τU]: at their own types ([AtType]). *)
    Lemma cc_args : glu_args Δ' (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) σ' ρ (Ns' ++ As) (X ++ vs).
    Proof.
      destruct cc_rel as [_ Hia].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf
                  nb Hnbu Hnbq) as [_ Hrt].
      pose proof (ac_args_prefix VP HVP HGall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf nb Hnbu Hnbq
                    k Mk c gs Us' Ns' bs vs As Δ' HMk Hcon HNl' Hbl Hvl HAl Hb Hv Hnp HAs Harg Hrec
                    (fun gs1 t gs2 N A v H1 H2 H3 H4 => Hrt _ _ _ _ _ _ _ _ (Hrec gs1 t gs2 N A v H1 H2 H3 H4)) HUg' Hia
                    (List.length gs) (le_n _)) as HgA.
      rewrite (List.firstn_all2 (n := List.length gs) gs), (List.firstn_all2 (n := List.length gs) As),
        (List.firstn_all2 (n := List.length gs) vs) in HgA by lia.
      pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf k Mk Δ' Us' Ns' X HMk Hnp Hb) as HgN.
      assert (Hg : glu_args Δ' (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list Id Us') (env_args nil ups) (Ns' ++ As) (X ++ vs)).
      { apply glu_args_app; [ exact (decl_closed_nparams_ass D Hc _ _ HMk) | rewrite length_im_nparams; exact HNl'
                            | rewrite length_im_nparams; exact cc_LX |].
        split; [ exact HgN | rewrite sb_of_list_app, env_args_app in HgA; exact HgA ]. }
      rewrite HUs' in Hg.
      apply tele_inst_args; [ | | | | exact Hg |].
      - rewrite <- List.app_assoc; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMk) ].
      - rewrite <- List.app_assoc; exact (vg_cargs_sem p D Hvg Hcv k Mk c gs HMk Hcon).
      - pose proof (Completeness.Inductives.Elim.ihs_pre_sem p D Γ Us Bks Mk gs (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon)
                      nil gs eq_refl) as H.
        cbn [ihs_ctx_aux List.app] in H; unfold cinst in H.
        rewrite tele_sub_app, length_im_nparams, <- List.app_assoc; exact H.
      - pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk (cons_lookup_in _ _ _ Hcon) (eq_sym (List.app_nil_r gs))) as H.
        unfold im_params in H; rewrite List.app_assoc in H.
        apply ctx_scoped_app in H as [H _]; rewrite Nat.add_0_r in H; exact H.
      - pose proof (EB Completeness.Inductives.Elim.closed_args_gargs k Mk c gs HMk Hcon X X vs vs Hb Hv Hia (List.length gs) (le_n _))
          as H.
        rewrite (List.firstn_all2 (n := List.length gs) gs), (List.firstn_all2 (n := List.length gs) vs) in H by lia; exact H.
    Qed.

    Lemma cc_oq : oq' = Some p \/ oq' = None.
    Proof. destruct Hgrp as [-> | [-> _]]; auto. Qed.

    Lemma cc_Ps_typed : forall j P T, List.nth_error (Us' ++ Ns') j = Some P ->
        List.nth_error (tele_insts (im_params D Mk) Id (Us' ++ Ns')) j = Some T -> Δ' ⊢ P : T.
    Proof.
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf k Mk Δ' Us' Ns' X HMk Hnp Hb) as HgN.
      assert (Hga : glu_args Δ' (im_params D Mk) Id nil (Us' ++ Ns') (ups ++ X)).
      { unfold im_params; apply glu_args_app; [ exact Ua | exact HUl' | exact ups_len |].
        split; [ exact HUg' | exact HgN ]. }
      exact (glu_args_typed _ _ _ _ _ _ (member_params_ass D Hc _ _ HMk) Hga).
    Qed.

    (** The substitution [ι] instantiates the branch's context with, typed. *)
    Lemma cc_iota_sub : Δ' ⊢ˢ sb_of_list Id (Ns' ++ As ++ elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As)
        : elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us' ++ Δ'.
    Proof.
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      assert (HΔ' : ⊢ Δ') by (gen_presups; assumption).
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      pose proof (wf_iota_sub _ _ _ p D oq' k Mk c gs (Us' ++ Ns') As (blocks_sub Bks σ') iA Hl cc_oq HMk Hcon HΔ'
                    ltac:(rewrite List.length_app, HUl', HNl'; unfold im_np; lia) cc_Ps_typed HAl HAs
                    ltac:(rewrite firstn_app_exact by exact HUl'; exact HBt')) as H.
      rewrite firstn_app_exact, skipn_app_exact in H by exact HUl'; exact H.
    Qed.

    (** The recursive results of the branch, glued: each is the
        eliminator at the matching recursive argument, glued by the
        induction hypothesis [IH] at its motive. *)
    Lemma cc_ihs_args : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        forall RB, EF elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                     ∈ per_ctx_env ↘ RB ->
        RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs)) ->
        glu_args Δ' (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs) (sb_of_list σ' (Ns' ++ As))
          (env_args ρ (X ++ vs)) (elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As) ihs.
    Proof.
      intros ihs Ei RB HRB HZ.
      pose proof (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      destruct cc_rel as [HnX Hia].
      pose proof cc_LX as LX.
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      assert (Esplit : elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                       = ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs ++ cinst Γ p D Mk Us gs)
        by (unfold elim_bctx, cinst; rewrite <- !List.app_assoc; reflexivity).
      assert (Hpgi : per_gargs (List.rev (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs))
                       (env_args ρ (X ++ vs)) (env_args ρ (X ++ vs)) ihs ihs).
      { pose proof (Completeness.Inductives.Elim.ihs_pre_sem p D Γ Us Bks Mk gs HBs nil gs eq_refl) as HC0.
        cbn [ihs_ctx_aux List.app] in HC0.
        destruct (rel_ctx_wf_per_ctx_env HC0) as [RC HRC].
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite Esplit in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs)) in HRB', HBs'.
        assert (Lr : List.length ihs = List.length (List.rev (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs)))
          by (rewrite List.length_rev, length_ihs_ctx_aux; exact Lih).
        assert (HZ' : RB (env_args (env_args ρ (X ++ vs)) ihs) (env_args (env_args ρ (X ++ vs)) ihs))
          by (rewrite <- env_args_app, <- List.app_assoc; exact HZ).
        destruct (Decl.rel_gargs _ _ _ _ HRC HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ')
          as [_ H].
        exact H. }
      constructor; [ rewrite length_elim_ihs, length_ihs_ctx_aux by exact HAl; reflexivity | rewrite length_ihs_ctx_aux; exact Lih |].
      intros j0 M T r B0 HMj0 HT Hr HB0.
      destruct (ihs_rev_nth (im_nn Mk) (blocks_motives Bks) Us (List.length gs) gs j0 _ HB0) as (gs1 & t & gs2 & Heq & Hk & EB).
      injection EB as ->; subst j0.
      set (j := cargs_nrec gs1) in *.
      assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [N HN].
      rewrite (elim_ihs_nth _ _ _ _ _ gs1 _ gs t gs2 As N Heq HAl HN) in HMj0; injection HMj0 as <-.
      destruct (Completeness.Inductives.Elim.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (v & v' & Hv1 & Hv1' & Hsh).
      rewrite Hv1' in Hv1; injection Hv1 as <-.
      destruct (eval_ihs_nth _ _ _ _ gs1 _ _ _ Ei t gs2 v' Heq Hv1') as (r' & Hr' & Er').
      fold j in Hr'; rewrite Hr in Hr'; injection Hr' as <-.
      set (σg := cargs_sub (sb_of_list Id (Us' ++ Ns')) gs1 As).
      rewrite (ihs_insts_move k Mk c gs σ' Ns' As _ HMk Hcon HNl' HAl) in HT.
      rewrite <- HUs' in HT.
      (** The syntactic type of the entry. *)
      assert (ET : T = ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σg N t).
      { destruct (tele_insts_nth _ _ _ _ _ HT) as (B'' & HB'' & ET).
        rewrite (ihs_ctx_nth _ _ _ _ gs gs1 t gs2 Heq) in HB''; fold j in HB''; injection HB'' as <-.
        subst T; rewrite <- sb_of_list_app, <- List.app_assoc.
        set (L' := List.firstn j (elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As)).
        assert (LL' : List.length L' = j)
          by (unfold L'; rewrite List.length_firstn, length_elim_ihs by exact HAl; unfold j; rewrite Heq, Views.cargs_nrec_app; lia).
        set (δ := sb_of_list Id (Ns' ++ As ++ L')).
        assert (Hθδ : sb_eq (ihs_sub (im_nn Mk) Us' (List.length gs) (cargs_pat gs1) j ⨟ δ) σg).
        { unfold δ, σg; rewrite <- LL'.
          pose proof (ihs_sub_iota D Mk (Us' ++ Ns') As L' gs1 gs ltac:(rewrite List.length_app, HUl', HNl'; unfold im_np; lia) HAl
                        ltac:(rewrite Heq, List.length_app; lia)) as H.
          rewrite firstn_app_exact, skipn_app_exact in H by exact HUl'; exact H. }
        assert (Hβδ : sb_eq (sb_of_wk (wk_shiftn (j + List.length gs + im_nn Mk)) ⨟ δ) Id).
        { intros z; unfold δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
          replace (z + (j + List.length gs + im_nn Mk)) with (List.length (Ns' ++ As ++ L') + z)
            by (rewrite !List.length_app, HNl', HAl, LL'; lia).
          rewrite sb_of_list_ge; reflexivity. }
        assert (Hidx : (a_var (j + List.length gs - 1 - List.length (cargs_pat gs1)))[δ] = N).
        { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ.
          rewrite (sb_of_list_nth _ _ _ N) by (rewrite !List.length_app, HNl', HAl, LL', Heq, List.length_app, length_cargs_pat; cbn; lia).
          rewrite !List.length_app, HNl', HAl, LL', length_cargs_pat.
          replace (im_nn Mk + (List.length gs + j) - 1 - (j + List.length gs - 1 - List.length gs1))
            with (im_nn Mk + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
          cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl'; replace (im_nn Mk + List.length gs1 - im_nn Mk) with (List.length gs1) by lia.
          rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact HN. }
        rewrite ptyp_ihty_sub, Hidx.
        rewrite (ptyp_ihty_sb_eq t _ _ Id _ σg N Hβδ Hθδ); reflexivity. }
      (** The entry is typed, by the typing of [ι]. *)
      assert (HMt' : Δ' ⊢ ptyp_ih p D oq' Us' (blocks_sub Bks σ') σg N t : T).
      { set (Ihs := elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As) in *.
        assert (Lei : List.length Ihs = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
        set (Rst := tele_sub (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) (sb_of_list Id Us')) ++ tele_sub (im_nparams Mk) (sb_of_list Id Us')).
        assert (HRa : tele_ass Rst)
          by (unfold Rst; apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | apply (decl_closed_nparams_ass D Hc _ _ HMk) ]).
        assert (LRst : List.length Rst = List.length (Ns' ++ As))
          by (unfold Rst; rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams, HNl', HAl; lia).
        assert (Hlen : List.length (Ns' ++ As ++ Ihs) = List.length (elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us'))
          by (rewrite length_elim_bctx, !List.length_app, HNl', HAl, Lei; lia).
        apply (wf_sub_of_list_inv _ _ _ (elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us') Δ' Id (Ns' ++ As ++ Ihs)
                  (elim_bctx_ass p D k Mk gs _ Us' Hc HMk) Hlen cc_iota_sub (im_nn Mk + List.length gs + j)).
        - rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
          rewrite List.length_app, HNl', HAl.
          replace (im_nn Mk + List.length gs + j - (im_nn Mk + List.length gs)) with j by lia.
          exact (elim_ihs_nth _ _ _ _ _ gs1 _ gs t gs2 As N Heq HAl HN).
        - unfold elim_bctx; fold Rst.
          assert (LRi : List.length (tele_insts Rst Id (Ns' ++ As)) = im_nn Mk + List.length gs)
            by (rewrite length_tele_insts by exact HRa; rewrite LRst, Nat.min_id, List.length_app, HNl', HAl; reflexivity).
          rewrite List.app_assoc, tele_insts_app by (first [ exact HRa | exact (eq_sym LRst) ]).
          rewrite List.nth_error_app2 by lia; rewrite LRi.
          replace (im_nn Mk + List.length gs + j - (im_nn Mk + List.length gs)) with j by lia.
          exact HT. }
      destruct (presup_exp HMt') as [_ [jT HjT]].
      rewrite ET in HjT.
      (** The type of the recursive argument. *)
      destruct (nth_error_lt_some (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1)) as [TN HTN].
      { rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. }
      assert (HTNeq : TN = ptyp_ty_at p D Us' σg t).
      { rewrite (cargs_rec_type_at p D Mk gs gs1 t gs2 (Us' ++ Ns') As TN Heq Hc
                   ltac:(rewrite List.length_app, HUl', HNl'; unfold im_np; lia) HTN).
        rewrite firstn_app_exact by exact HUl'.
        apply ptyp_ty_at_sb_eq; rewrite sb_of_list_app; unfold σg; rewrite <- (cargs_sub_firstn gs1 (sb_of_list Id (Us' ++ Ns')) As).
        apply cargs_sub_pat; rewrite List.length_firstn; lia. }
      pose proof (IH gs1 t gs2 N TN v' Heq HN HTN Hv1') as IHr.
      (** The semantic type of the entry. *)
      destruct (per_gargs_nth_el _ _ _ _ _ j _ Hpgi HB0 ltac:(rewrite Lih; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia))
        as (i0 & Rae & ae & ae' & x & x' & Eae & Eae' & HRae & Hx & Hx' & Hrr).
      assert (ae' = ae) as -> by (eapply functional_eval_exp; eassumption).
      rewrite Hr in Hx; injection Hx as <-; rewrite Hr in Hx'; injection Hx' as <-.
      set (fa := List.firstn (List.length gs1) vs) in *.
      set (aft := List.skipn (S (List.length gs1)) vs).
      assert (Evs : vs = fa ++ v' :: aft) by (unfold fa, aft; rewrite <- (skipn_nth_cons' _ _ _ Hv1'), List.firstn_skipn; reflexivity).
      set (ihp := List.firstn j ihs) in *.
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn, Hvl, Heq, List.length_app; cbn; lia).
      assert (Laft : List.length aft = List.length gs2) by (unfold aft; rewrite List.length_skipn, Hvl, Heq, List.length_app; cbn; lia).
      assert (Lihp : List.length ihp = j) by (unfold ihp; rewrite List.length_firstn, Lih; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
      pose proof (EB Completeness.Inductives.Elim.e_HCtxT ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs gs1 t gs2 Heq) as HCtxT.
      pose proof (rel_ctx_wf_tail HCtxT) as HCtx.
      destruct (rel_ctx_wf_per_ctx_env HCtx) as [RS HRS].
      assert (HEE : RS (env_args ρ (X ++ vs ++ ihp)) (env_args ρ (X ++ vs ++ ihp))).
      { assert (Esp : ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                     = ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)
                       ++ ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs1)
          by (rewrite Heq at 2; rewrite Views.ihs_ctx_aux_app, List.app_nil_r; reflexivity).
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite Esplit, Esp, <- List.app_assoc in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)))
          in HRB', HBs'.
        assert (Lr : List.length (List.skipn j ihs)
                     = List.length (List.rev (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))))
          by (rewrite List.length_rev, length_ihs_ctx_aux, List.length_skipn, Lih; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
        assert (HZ' : RB (env_args (env_args ρ (X ++ vs ++ ihp)) (List.skipn j ihs)) (env_args (env_args ρ (X ++ vs ++ ihp)) (List.skipn j ihs)))
          by (rewrite <- env_args_app, <- !List.app_assoc; unfold ihp; rewrite List.firstn_skipn; exact HZ).
        destruct (Decl.rel_gargs _ _ _ _ HRS HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ') as [H _].
        exact H. }
      rewrite Evs, <- !List.app_assoc in HEE; cbn [List.app] in HEE.
      pose proof Eae as Eae0; rewrite <- env_args_app in Eae0; fold ihp in Eae0.
      rewrite Evs, <- !List.app_assoc in Eae0; cbn [List.app] in Eae0.
      destruct (EB Completeness.Inductives.Elim.side_w ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs gs1 t gs2 Heq RS HRS
                  ρ X fa v' aft ihp Hρ LX Lfa Laft Lihp HEE) as (w & Hw & HwU & Lw).
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk; fold fa in Hpk.
      destruct (rec_shape_facts k Mk c gs1 t gs2 0 HMk ltac:(rewrite <- Heq; exact Hcon)) as ((Mj & HMj & _) & _ & _).
      cbn [ptyp_skip] in HMj.
      destruct (HBks _ _ HMj) as [bj Hbj].
      assert (Hsh0 : rec_arg_rel p D (okr_at D ups nr) nr ar dr k ups ups (X ++ nonrec_arg_vals gs1 fa ++ nil)
                       (X ++ nonrec_arg_vals gs1 fa ++ nil) (ptyp_skip 0 t) v' v')
        by (rewrite List.app_nil_r; exact Hsh).
      (** The motive at the recursive argument, as the induction
          hypothesis sees it. *)
      destruct (EB Completeness.Inductives.Elim.ihty_link ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs gs1 t gs2 Heq RS HRS
                  Mj bj HMj Hbj (List.length (ptyp_doms t)) 0 ρ X fa v' aft ihp w nil v' ae i0 Rae eq_refl LX Lfa Laft Lihp eq_refl
                  Hρ HEE Hw HwU Lw Hb Hpk (tele_prefix_rel_nil _) (eval_apps_nil _ _ _) Hsh0 Eae0 HRae) as (b & Eb & Hab).
      rewrite List.app_nil_r in Eb.
      set (J := max (max (ulvl u) iA) (max i0 jT)).
      destruct Hab as [Rab HRab].
      destruct (per_univ_elem_sym _ _ _ _ HRab) as [HRba _].
      pose proof (per_univ_trans _ _ _ _ _ _ HRba HRab) as HRbb.
      pose proof (per_univ_elem_cumu_ge i0 J _ _ _ ltac:(unfold J; lia) HRbb) as HRbbJ.
      assert (HRr : Rab r r) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRae HRab); exact Hrr).
      destruct (per_univ_glu_univ_elem J b (ex_intro _ Rab HRbbJ)) as (Pb & Elb & Hgb).
      pose proof (lift_exp_ge _ _ _ _ jT J ltac:(unfold J; lia) HjT) as HjJ.
      assert (HuJ : uidx_le u (ul J)) by (apply uidx_le_ul_max; unfold J; lia).
      assert (HiAJ : iA <= J) by (unfold J; lia).
      assert (Hc1 : ind_con Mk c = Some (gs1 ++ ca_rec t :: gs2)) by (rewrite <- Heq; exact Hcon).
      assert (Hpre1 : X ++ nonrec_arg_vals gs1 fa = X ++ nonrec_arg_vals gs1 fa ++ nil) by (rewrite List.app_nil_r; reflexivity).
      pose proof (IHr Mk X c gs1 t gs2 (nonrec_arg_vals gs1 fa) 0 nil σ' oq' σg r b J Rab Pb Elb HMk
                    Hc1 Hpre1 Hb Hpk eq_refl (tele_prefix_rel_nil _)
                    cc_oq Hσ' HUs' HTNeq (HAs _ _ _ HN HTN) Hsh Er' Eb HRbbJ HRr HuJ HiAJ Hgb HjJ) as HMg.
      destruct (glu_transfer_per_elem _ i0 _ _ _ _ _ _ _ _ Hgb (ex_intro _ Rab HRba) (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HMg) HMg)
        as (kk & P' & El' & Hg' & HTP' & HMg').
      rewrite ET; exact (mk_glu_arg _ _ _ _ _ _ kk ae P' El' Eae Hg' HTP' HMg').
    Qed.

    (** The constructor in the group at its stored parameters. *)
    Lemma cc_GX : G k ups ups X X (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs ++ vs)).
    Proof.
      destruct cc_rel as [HnX _].
      exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ k Mk _ _ _ _ _ _ _ _ HMk HGm HnX HnX).
    Qed.

    (** The recursive results, related at the motives. *)
    Lemma cc_ihs : exists ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs /\
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs.
    Proof.
      destruct cc_rel as [_ Hia].
      destruct per_elim_at_ups as (_ & H2 & _).
      destruct (H2 _ _ _ _ _ _ _ _ Hia) as (ihs & ihs' & Ei & Ei' & Hir).
      pose proof (functional_eval_ihs _ _ _ _ _ _ _ _ Ei Ei') as <-.
      exists ihs; split; assumption.
    Qed.

    (** The environment of the branch's context the branch is evaluated
        in. *)
    Lemma cc_env : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs ->
        forall RB, EF elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                     ∈ per_ctx_env ↘ RB ->
        RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs)).
    Proof.
      intros ihs Ei Hir RB HRB.
      exact (EB Completeness.Inductives.Elim.cv_bctx_elem ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon
               (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) ρ ρ Hρ Hρ ups ups hd k' bs bs vs vs ihs ihs cc_GX Hir RB HRB).
    Qed.

    (** The substitution [ι] at [σ'], glued to that environment. *)
    Lemma cc_sub : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs ->
        forall Sb, EG elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ∈ glu_ctx_env ↘ Sb ->
        Δ' ⊢ˢ sb_of_list σ' (Ns' ++ As ++ elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As)
          ® env_args ρ (X ++ vs ++ ihs) ∈ Sb.
    Proof.
      intros ihs Ei Hir Sb HSb.
      pose proof (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
      pose proof (cc_ihs_args ihs Ei RB HRB (cc_env ihs Ei Hir RB HRB)) as Hgi.
      pose proof cc_args as Hga.
      destruct (glu_args_length _ _ _ _ _ _ Hga) as [L1 L2].
      assert (HCa : tele_ass (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU))
        by (apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_nparams_ass D Hc _ _ HMk) ]).
      assert (Esp : elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                    = (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                       ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) ++ Γ)
        by (rewrite tele_sub_app, length_im_nparams; unfold elim_bctx; rewrite <- !List.app_assoc; reflexivity).
      rewrite Esp in HSb.
      eapply glu_sub_of_list; [ | exact HSb | exact HSbΓ | exact Hσ' |].
      - apply List.Forall_app; split; [ apply ihs_ctx_aux_ass | exact HCa ].
      - rewrite (List.app_assoc Ns'), (List.app_assoc X).
        apply glu_args_app; [ exact HCa | exact L1 | exact L2 |].
        split; [ exact Hga | exact Hgi ].
    Qed.

    (** The value of the branch's type in that environment, against the
        motive's at the scrutinee: the branch's type is the motive at the
        constructor as the group reads it ([τb]), related to the scrutinee
        in the group. *)
    Lemma cc_bty_rel : forall b ihs abt a0, List.nth_error Bks k = Some b ->
        ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs ->
        ⟦ elim_bty p k Mk c gs (eb_motive b) Us ⟧ env_args ρ (X ++ vs ++ ihs) ↘ abt ->
        ⟦ eb_motive b ⟧ env_args ρ (ns ++ d_con hd k' c (bs ++ vs) :: nil) ↘ a0 ->
        Dom abt ≈ a0 ∈ per_univ iA.
    Proof.
      intros b ihs abt a0 Hbk _ Hir Eabt Ea0.
      destruct cc_rel as [HnX _].
      exact (bty_val_rel k Mk c gs b HMk Hcon Hbk hd k' bs vs ihs ns abt a0 Href Hbl cc_GX Hir HnX Eabt Ea0).
    Qed.

    (** The constructor applied, as the member it is at reads it
        ([im_ref], [im_pre]): itself at a declared member, the container's
        at a view. *)
    Lemma cc_con_ref : Δ' ⊢ apps (a_con p k c) (Us' ++ Ns' ++ As) ≈ apps (a_con hd k' c) (im_pre Mk Us' ++ Ns' ++ As)
        : im_ty_at p k Mk Us' Ns'.
    Proof.
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      pose proof Href as Href'.
      unfold im_ref in Href'; destruct (im_head Mk) as [pm | qc kc Is vm] eqn:Hh; injection Href' as <- <-.
      - unfold im_pre; rewrite Hh; apply wf_exp_eq_refl; gen_presups; eassumption.
      - destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mq & Hq & HMq & _ & _ & _ & _ & Hfst & _).
        destruct (cons_lookup_names (im_cons Mq) c) as [gh Hgh].
        { rewrite <- Hfst; apply (List.in_map fst _ (c, gs)), cons_lookup_in; exact Hcon. }
        unfold im_pre; rewrite Hh.
        exact (view_head_con_eq p D k Mk qc kc Is vm Dq Mq Hdt Hl Hc HMk Hh Hq HMq Δ' Us' Ns' As c gs gh HΔ' HUl' HNl'
                 cc_Ps_typed Hgh Hcon HAl HAs).
    Qed.

    (** The constructor case: the eliminator evaluates to the branch at
        [ι]'s values, glued there; the elimination of [M'] is the branch at
        [ι] by [ι] and the congruence of the scrutinee, and the type of the
        branch is the motive's at the constructor, equal to its at [M']. *)
    Lemma cc_main : elim_out k Mk Δ' σ' oq' Ns' M' (d_con hd k' c (bs ++ vs)) ns.
    Proof.
      destruct cc_ihs as (ihs & Ei & Hir).
      destruct (HBks _ _ HMk) as [b Hbk].
      destruct (brs_names_lookup _ _ _ _ (Hna _ _ _ HMk Hbk) Hcon) as (n & B & HlB & HinB).
      pose proof (Har _ _ _ _ _ _ _ HMk Hbk Hcon HinB) as Hn.
      destruct (gbk_branch _ _ _ _ _ _ HBg _ _ _ _ _ _ _ HMk Hbk Hcon HinB) as [Sbb HSbb lvl Hbody].
      pose proof (cc_sub ihs Ei Hir Sbb HSbb) as Hτ.
      destruct (Hbody _ _ _ Hτ) as [abt rB Pb Elb Eabt ErB Hgb HBgl].
      destruct (ER im_ref_target k Mk hd k' HMk Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      (** The eliminator's value. *)
      assert (Ee : ⟦elim d_con hd k' c (bs ++ vs) at k of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rB).
      { eapply eval_elim_con; [ exact Hl | exact HMk | exact Href | exact Hq | exact HMq | exact Hcon
                              | rewrite List.length_app; unfold im_np; lia | exact Hbk | exact HlB | rewrite Hnnq; exact Hn | |].
        - rewrite skipn_app_exact by (unfold im_np; lia); exact Ei.
        - rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact ErB. }
      (** The motive at the scrutinee, glued in the group ([AtType]). *)
      destruct (Completeness.Inductives.ViewReadback.mref_exists VP HVP p D HPD ups ups_gargs ups_len k Mk HMk) as [[[hd0 k0] pre] Er].
      destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D k Mk ups hd0 k0 pre Hl HMk ups_len Er) as [Href0 Lpre].
      rewrite Href in Href0; injection Href0 as E1 E2; subst hd0 k0.
      assert (HIG : ind_glu_elem p D ups NEl AEl DP DEl k Δ' Us' Ns' M' (d_con hd k' c (bs ++ vs)))
        by (eapply ind_glu_elem_con; eassumption).
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf
                  nb Hnbu Hnbq) as [Hel _].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (Hgl : forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
                Δ' ⊢ im_ty_at p k Mk (List.map (fun U => U[σ']) Us) Ns' ® P ->
                Δ' ⊢ M' : im_ty_at p k Mk (List.map (fun U => U[σ']) Us) Ns' ® d_con hd k' c (bs ++ vs) ∈ El).
      { intros i P El _ Hglu HT; rewrite <- HUs' in HT |- *.
        exact (Hel _ _ _ _ _ _ HIG Mk ns hd k' pre i P El HMk Er HUg' HMt Hgn Hns HGm Hglu HT). }
      pose proof Hgn as Hgn'; rewrite HUs' in Hgn'.
      destruct (motive_glu k Mk Δ' σ' Ns' ns M' _ hd k' pre HMk Hσ' Hgn' Hns Er Hgl) as (a0 & Ea0 & Hpa0 & HPa0).
      exists rB a0; [ exact Ee | exact Ea0 | exact Hpa0 |].
      intros P El Hg.
      pose proof (HPa0 P El Hg) as HTP.
      rewrite (blocks_motives_nth _ _ _ Hbk) in Ea0, HTP |- *.
      pose proof (cc_bty_rel b ihs abt a0 Hbk Ei Hir Eabt Ea0) as Hrel.
      (** [ι], at the blocks at [σ']. *)
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      assert (HBt2 : blocks_typed gc_deps gc_stack Δ' p D (List.firstn (ind_nu D) (Us' ++ Ns')) (blocks_sub Bks σ') iA)
        by (rewrite firstn_app_exact by exact HUl'; exact HBt').
      assert (HPl : List.length (Us' ++ Ns') = im_np D Mk) by (rewrite List.length_app, HUl', HNl'; unfold im_np; lia).
      assert (Hbk' : List.nth_error (blocks_sub Bks σ') k = Some (eblock_sub b σ')) by (rewrite nth_error_blocks_sub, Hbk; reflexivity).
      assert (HlB' : brs_lookup (eb_brs (eblock_sub b σ')) c = Some (n, B[sb_qn n σ']))
        by (rewrite Completeness.Inductives.Elim.eb_brs_sub, brs_lookup_sub, HlB; reflexivity).
      set (Ihs := elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As) in *.
      assert (LIhs : List.length Ihs = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
      pose proof (wf_elim_iota_bt Δ' p D oq' k Mk (eblock_sub b σ') (blocks_sub Bks σ') c gs (Us' ++ Ns') As iA n (B[sb_qn n σ'])
                    HΔ' Hl Hgrp HMk Hbk' Hcon HPl cc_Ps_typed HAl HAs HBt2 HlB') as E1.
      rewrite firstn_app_exact, skipn_app_exact in E1 by exact HUl'.
      fold Ihs in E1; rewrite Href in E1; cbn [fst snd] in E1.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in E1.
      set (conA := apps (a_con hd k' c) (im_pre Mk Us' ++ Ns' ++ As)) in *.
      set (A' := (eb_motive b)[sb_qn (S (im_nn Mk)) σ']) in *.
      (** The scrutinee is the constructor, as its member reads it. *)
      assert (Emt : ind_mty p D k Us' Ns' = im_ty_at p k Mk Us' Ns') by (unfold ind_mty; rewrite HMk; reflexivity).
      assert (HMM : Δ' ⊢ M' ≈ conA : ind_mty p D k (List.firstn (ind_nu D) (Us' ++ Ns')) (List.skipn (ind_nu D) (Us' ++ Ns')))
        by (rewrite firstn_app_exact, skipn_app_exact, Emt by exact HUl'; exact (wf_exp_eq_trans _ _ _ _ _ _ _ HMeq cc_con_ref)).
      pose proof (wf_elim_scrut_eq Δ' p D oq' k Mk (eblock_sub b σ') (blocks_sub Bks σ') (Us' ++ Ns') M' conA iA Hl Hgrp HMk Hbk' HPl
                    cc_Ps_typed HBt2 HMM) as E2.
      rewrite firstn_app_exact, skipn_app_exact in E2 by exact HUl'.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in E2; fold A' in E2.
      pose proof (bt_motive _ _ _ _ _ _ _ _ HBt' _ _ _ HMk Hbk') as HAt.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in HAt; fold A' in HAt.
      assert (HΨ : ⊢ elim_mctx p D k Mk (List.firstn (ind_nu D) (Us' ++ Ns')) ++ Δ')
        by (rewrite firstn_app_exact by exact HUl'; gen_presups; assumption).
      destruct (presup_exp_eq HMM) as (_ & HM1 & HM2 & _).
      pose proof (wf_elim_inst_sub_eq _ _ Δ' p D k Mk (Us' ++ Ns') M' conA Hl HMk HΔ' HPl cc_Ps_typed HM1 HM2 HMM HΨ) as Esub.
      rewrite firstn_app_exact, skipn_app_exact in Esub by exact HUl'.
      pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HAt Esub) as E3.
      (** The branch's type at [ι] at [σ'] is the motive at the constructor. *)
      assert (LL : List.length (Ns' ++ As ++ Ihs) = n) by (rewrite !List.length_app, HNl', HAl, LIhs, Hn; lia).
      assert (T1 : (elim_bty p k Mk c gs (eb_motive b) Us)[sb_of_list σ' (Ns' ++ As ++ Ihs)] = A'[sb_of_list Id (Ns' ++ conA :: nil)]).
      { rewrite <- exp_sub_qn_of_list, LL, Hn, (elim_bty_sub p D k Mk c gs (eb_motive b) Us σ' Hc HMk HUl).
        fold A'; rewrite <- HUs', (elim_bty_iota p D k Mk c gs A' Us' Ns' As Ihs Hc HMk HUl' HNl' HAl LIhs).
        rewrite Href; reflexivity. }
      assert (T2 : B[sb_of_list σ' (Ns' ++ As ++ Ihs)] = B[sb_qn n σ'][sb_of_list Id (Ns' ++ As ++ Ihs)])
        by (rewrite <- LL, exp_sub_qn_of_list; reflexivity).
      rewrite T1, T2 in HBgl.
      destruct (presup_exp_eq E3) as (_ & HTm & _).
      assert (Eall : Δ' ⊢ a_elim oq' Us' k (blocks_sub Bks σ') M' ≈ B[sb_qn n σ'][sb_of_list Id (Ns' ++ As ++ Ihs)]
                       : A'[sb_of_list Id (Ns' ++ M' :: nil)]).
      { eapply wf_exp_eq_trans; [ exact E2 |].
        eapply wf_exp_eq_conv; [ exact E1 | exact HTm | apply wf_exp_eq_sym; exact E3 ]. }
      (** The branch's gluing moved to the motive's. *)
      assert (HTbr : Δ' ⊢ A'[sb_of_list Id (Ns' ++ conA :: nil)] ® P)
        by (eapply glu_univ_elem_typ_resp_exp_eq; [ exact Hg | exact HTP | exact E3 ]).
      pose proof (glu_univ_elem_exp_conv Hrel Hgb Hg HBgl HTbr) as HM3.
      pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hg _ _ _ _ _ HM3 (wf_exp_eq_sym _ _ _ _ _ _ E3)) as HM4.
      rewrite <- HUs'.
      exact (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hg _ _ _ _ _ HM4 (wf_exp_eq_sym _ _ _ _ _ _ Eall)).
    Qed.
  End ConCase.

  (** ** Fresh Variables, Glued

      The fresh variables a stuck eliminator's readback reads a block's
      motive under, at [ups], against the entries of the motive's context
      in [ρ]: each of a type related to its entry's. *)
  Lemma mctx_entry_link : forall v Mv, ind_member D v = Some Mv -> forall s ns hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      forall kk X a, List.nth_error (List.rev (elim_mctx p D v Mv Us)) kk = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn kk (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv) :: nil)) ↘ a ->
        exists b (n : nat), List.nth_error (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv) :: nil) kk = Some (⇑! b (s + kk)) /\
          Dom a ≈ b ∈ per_univ n.
  Proof.
    intros v Mv HMv s ns hd k pre Fn Hns Er kk X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (HMall _ _ HMv) as HMm.
    pose proof (rel_ctx_wf_tail HMm) as HNt.
    pose proof (member_params_ass D Hc _ _ HMv) as HPa.
    pose proof (vid_params _ HD _ _ HMv) as HPs.
    pose proof (EB Completeness.Inductives.Elim.nparams_closed_of_canon v Mv HMv ns ns Hns) as Hpg.
    unfold elim_mctx in HX; cbn [List.rev] in HX.
    destruct (Nat.lt_ge_cases kk (im_nn Mv)) as [Hk | Hk].
    - (** A non-uniform parameter. *)
      rewrite List.nth_error_app1 in HX by (rewrite List.length_rev, length_tele_sub, length_im_nparams; lia).
      rewrite firstn_app_le in Ea by lia.
      destruct (inst_entry_link (im_nparams Mv) HPa HPs HNt ns Hpg ltac:(rewrite length_im_nparams; exact Ln) kk X a HX Ea)
        as (A0 & b & n & HA & Eb & Hab).
      destruct (fresh_tele_nth _ _ _ _ Fn kk A0 HA) as (b' & Eb' & Hb').
      rewrite <- env_args_app in Eb'.
      assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
      exists b, n; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
    - (** The scrutinee: at the member's type. *)
      assert (kk = im_nn Mv) as ->.
      { match type of HX with List.nth_error ?l _ = _ =>
          assert (Hlt : kk < List.length l) by (apply List.nth_error_Some; rewrite HX; discriminate) end.
        rewrite List.length_app, List.length_rev, length_tele_sub, length_im_nparams in Hlt; cbn in Hlt; lia. }
      rewrite List.nth_error_app2 in HX by (rewrite List.length_rev, length_tele_sub, length_im_nparams; lia).
      rewrite List.length_rev, length_tele_sub, length_im_nparams, Nat.sub_diag in HX; cbn in HX; injection HX as <-.
      rewrite firstn_app_le, List.firstn_all2 in Ea by lia.
      destruct (Completeness.Inductives.Elim.mty_vars_valid p D Hvg Hcv v Mv HMv) as [jx HXv].
      destruct (inst_link (im_nparams Mv) _ jx ns HPa HPs HNt HXv Hpg ltac:(rewrite length_im_nparams; exact Ln))
        as (a1 & b & Ea1 & Eb & Hab).
      unfold τU in Ea1; rewrite length_im_nparams, (Completeness.Inductives.Elim.mty_vars_inst p D v Mv Us Hc HUl) in Ea1.
      assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (rel_ctx_wf_per_ctx_env HPs) as [RK HRK].
      assert (HKE : RK (env_args nil (ups ++ ns ++ nil)) (env_args nil (ups ++ ns ++ nil))).
      { rewrite List.app_nil_r.
        apply (gargs_env_rel _ _ _ _ _ _ HRK HPs); [ rewrite !List.length_app, length_im_params, ups_len; unfold im_np, ind_nu in *; lia |].
        exact (Completeness.Inductives.Model.params_gargs D HD Hc Hsu v Mv HMv ups ups bu ns ns ups_gargs ups_len Hbu Hns). }
      replace (ups ++ ns) with (ups ++ ns ++ nil) in Eb by (rewrite List.app_nil_r; reflexivity).
      destruct (mty_val_rel VP HVP p D HPD ups ups_len ups_gargs v Mv hd k pre (im_nparams Mv) RK ns nil 0 b ns HMv Er HPs HRK
                  ltac:(rewrite List.app_nil_r, length_im_nparams; exact Ln) Ln eq_refl HKE Eb Hns) as (i0 & R0 & H0).
      destruct (Decl.per_univ_elem_to_nat _ _ _ _ H0) as [n0 Hn0].
      exists (d_ind hd k (pre ++ ns)), n0; split.
      + rewrite List.nth_error_app2, Ln, Nat.sub_diag by lia; reflexivity.
      + apply per_univ_sym'; eapply per_univ_trans'; [ exists R0; exact Hn0 | apply per_univ_sym'; exact Hab ].
  Qed.

  (** The readback of the motive of the block of the member [v] under the
      fresh variables, against the motive at [σ''] past its context. *)
  Lemma rb_motive : forall v Mv b, ind_member D v = Some Mv -> List.nth_error Bks v = Some b ->
      forall Δ σ'' hd k pre ns a A', Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ length Δ ↘ ns ->
      ⟦ eb_motive b ⟧ env_args ρ (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (length Δ + im_nn Mv) :: nil) ↘ a ->
      Rtyp a in gc_deps ⍮ gc_stack ⍮ S (length Δ + im_nn Mv) ↘ A' ->
      elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ (eb_motive b)[sb_qn (S (im_nn Mv)) σ''] ≈ A' : Typeω@iA.
  Proof.
    intros v Mv b HMv Hb Δ σ'' hd k pre ns a A' Hσ'' Er Fn Ea HRA.
    destruct (Completeness.Inductives.ViewReadback.fresh_nparams_exist p D Hvg ups ups_gargs ups_len v Mv (List.length Δ) HMv)
      as (ns' & Fn' & Hns).
    pose proof (functional_fresh_tele' _ _ _ _ _ Fn' Fn) as <-.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMv Hb) as HAg.
    destruct HAg as [SbM HSbM iM HAg'].
    assert (HMl : List.length (elim_mctx p D v Mv Us) = S (im_nn Mv)) by (rewrite length_elim_mctx; reflexivity).
    assert (Lx : List.length (ns' ++ ⇑! (d_ind hd k (pre ++ ns')) (List.length Δ + im_nn Mv) :: nil) = List.length (elim_mctx p D v Mv Us))
      by (rewrite HMl, List.length_app, Ln; cbn; lia).
    pose proof (glu_sub_fresh _ Γ SbΓ (elim_mctx_ass p D v Mv Us Hc HMv) HSbΓ SbM HSbM Δ σ'' ρ _ Hσ'' Lx
                  (mctx_entry_link v Mv HMv (List.length Δ) ns' hd k pre Fn Hns Er)) as Hτ.
    rewrite (elim_mctx_sub p D v Mv Us σ'' Hc HMv HUl), HMl in Hτ.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMv Hb) Hτ) as (HAτ & a0 & Ea0 & Hpa & HPa).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (P & El & Hg).
    pose proof (HPa P El Hg) as HP.
    destruct (realize_glu_typ_top _ _ _ _ Hg _ _ HP) as [_ _ Hrbt].
    assert (HΔm : ⊢ elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ) by (gen_presups; assumption).
    assert (Hlen : List.length (elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ) = S (List.length Δ + im_nn Mv))
      by (rewrite List.length_app, length_elim_mctx; lia).
    rewrite <- Hlen in HRA.
    pose proof (Hrbt _ wk_id _ (kripke_id _ HΔm) HRA) as H.
    rewrite exp_wk_id in H; exact H.
  Qed.

  (** The fresh variables a stuck eliminator's readback reads a branch of
      the member [v] under, at [ups] (the non-uniform parameters, the
      arguments and the recursive results), against the entries of the
      branch's context in [ρ]: each of a type related to its entry's. *)
  Lemma bctx_link_gen : forall v Mv c gs, ind_member D v = Some Mv -> ind_con Mv c = Some gs ->
      forall s ns vs ihs hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mv) ↘ vs ->
      List.length pre = im_unu D Mv ->
      G v ups ups ns ns (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)) ->
      rec_results_rel dr Rel v ups ups ns ns gs vs vs ihs ihs ->
      forall kk X a, List.nth_error (List.rev (elim_bctx p D Mv gs (blocks_motives Bks) Us)) kk = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn kk (ns ++ vs ++ ihs)) ↘ a ->
        (kk < im_nn Mv + List.length gs /\
           exists b (n : nat), List.nth_error (ns ++ vs ++ ihs) kk = Some (⇑! b (s + kk)) /\ Dom a ≈ b ∈ per_univ n) \/
        (exists gs1 t gs2 v' b (n : nat), gs = gs1 ++ ca_rec t :: gs2 /\ kk = (im_nn Mv + List.length gs + cargs_nrec gs1)%nat /\
           List.nth_error vs (List.length gs1) = Some v' /\
           ⟦ihty v' of t under ρ (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack
             ⍮ env_args nil (ups ++ ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ b /\
           Dom a ≈ b ∈ per_univ n /\
           exists (i0 : nat) R x, List.nth_error ihs (cargs_nrec gs1) = Some x /\ DF a ≈ a ∈ per_univ_elem i0 ↘ R /\ R x x).
  Proof.
    intros v Mv c gs HMv Hcon s ns vs ihs hd k pre Fn Fc Lpre Hm Hir kk X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    assert (Hns : tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns /\ con_args_rel p D (okr_at D ups nr) nr ar dr v ups ups ns ns gs vs vs /\
                  tele_rel (ar v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs)).
    { unfold grp_rel in Hm; inversion Hm; subst.
      match goal with H1 : ind_member D v = Some ?M1 |- _ => rewrite HMv in H1; injection H1 as <- end.
      match goal with H1 : ind_con Mv c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app; lia ]; destruct E as [-> ->] end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app in *; lia ]; destruct E as [-> ->] end.
      rewrite skipn_app_exact in * by exact Lpre.
      split; [ assumption | split; assumption ]. }
    destruct Hns as (Hns & Hia & Hav).
    destruct (ER con_args_rel_length _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
    destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
    assert (Hbe : elim_bctx p D Mv gs (blocks_motives Bks) Us
                  = ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                    ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)
      by (unfold elim_bctx; rewrite tele_sub_app, length_im_nparams; reflexivity).
    rewrite Hbe, List.rev_app_distr in HX.
    assert (LC : List.length (List.rev (tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)) = (im_nn Mv + List.length gs)%nat)
      by (rewrite List.length_rev, length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams; lia).
    destruct (Nat.lt_ge_cases kk (im_nn Mv + List.length gs)) as [Hk | Hk].
    - (** The non-uniform parameters and the arguments: entries of the
          instance at [τU] of a closed telescope. *)
      left; split; [ exact Hk |].
      rewrite List.nth_error_app1 in HX by lia.
      assert (Hfk : List.firstn kk (ns ++ vs ++ ihs) = List.firstn kk (ns ++ vs))
        by (rewrite List.app_assoc, firstn_app_le by (rewrite List.length_app; lia); reflexivity).
      rewrite Hfk in Ea.
      pose proof (EB Completeness.Inductives.Elim.closed_args_gargs v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                    (List.length gs) (le_n _)) as Hpg.
      rewrite List.firstn_all2, List.firstn_all2 in Hpg by lia.
      assert (HCa : tele_ass ((cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D))
        by (rewrite <- List.app_assoc; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMv) ]).
      assert (HCs : ⊨ (cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; exact (vg_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon)).
      assert (HCS : ⊨ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU ++ Γ).
      { pose proof (Completeness.Inductives.Elim.ihs_pre_sem p D Γ Us Bks Mv gs (vbs_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon)
                      nil gs eq_refl) as H.
        cbn [ihs_ctx_aux List.app] in H; unfold cinst in H.
        rewrite tele_sub_app, length_im_nparams, <- List.app_assoc; exact H. }
      destruct (inst_entry_link _ HCa HCs HCS (ns ++ vs) Hpg
                  ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia) kk X a HX Ea) as (A0 & b & n & HA0 & Eb & Hab).
      rewrite List.rev_app_distr in HA0.
      destruct (Nat.lt_ge_cases kk (im_nn Mv)) as [Hk1 | Hk1].
      + rewrite List.nth_error_app1 in HA0 by (rewrite List.length_rev, length_im_nparams; lia).
        destruct (fresh_tele_nth _ _ _ _ Fn kk A0 HA0) as (b' & Eb' & Hb').
        rewrite <- env_args_app in Eb'.
        rewrite firstn_app_le in Eb by lia.
        assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
        exists b, n; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
      + rewrite List.nth_error_app2 in HA0 by (rewrite List.length_rev, length_im_nparams; lia).
        rewrite List.length_rev, length_im_nparams in HA0.
        destruct (nth_error_lt_some gs (kk - im_nn Mv) ltac:(lia)) as [g Hg].
        destruct (List.nth_error_split _ _ Hg) as (gs1 & gs2 & Heq & Hl1).
        rewrite <- Hl1 in HA0.
        rewrite firstn_app_ge in Eb by lia; rewrite Ln in Eb; rewrite <- Hl1 in Eb.
        assert (Hnthw : forall x, List.nth_error vs (List.length gs1) = Some x -> List.nth_error (ns ++ vs ++ ihs) kk = Some x).
        { intros x Hx; rewrite List.nth_error_app2 by lia; rewrite Ln, <- Hl1; rewrite List.nth_error_app1 by lia; exact Hx. }
        destruct (fresh_cargs_nth _ _ _ _ _ _ Fc gs1 g gs2 Heq) as [Fa Fr].
        pose proof (EB Completeness.Inductives.Elim.closed_args_gargs v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                      (List.length gs1) ltac:(lia)) as Hpg1.
        replace (List.firstn (List.length gs1) gs) with gs1 in Hpg1 by (rewrite Heq; symmetry; apply firstn_app_len; reflexivity).
        assert (Hpg2 : per_gargs (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) nil nil
                         (ups ++ ns ++ List.firstn (List.length gs1) vs) (ups ++ ns ++ List.firstn (List.length gs1) vs)).
        { unfold im_params; rewrite List.app_assoc, List.rev_app_distr.
          apply Decl.per_gargs_app_intro; [ rewrite List.length_rev; exact ups_len | exact ups_gargs | exact Hpg1 ]. }
        assert (Lfa : List.length (List.firstn (List.length gs1) vs) = List.length gs1) by (rewrite List.length_firstn; lia).
        destruct g as [B0 | t].
        * (** A non-recursive argument: its type at the non-recursive
              values. *)
          pose proof (cargs_rev_nth_arg p D Mv gs gs1 B0 gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as ->.
          destruct (Fa B0 eq_refl) as (a' & Ea' & Hv).
          rewrite <- env_args_app, <- List.app_assoc in Ea'.
          destruct (vg_arg_types p D Hvg Hcv v Mv c gs gs1 B0 gs2 ups ns (List.firstn (List.length gs1) vs) HMv Hcon Heq ups_len Ln Lfa Hpg2)
            as (i & R & a1 & a1' & Ea1 & Ea1' & HR).
          assert (a1 = b) as -> by (eapply functional_eval_exp; eassumption).
          assert (a1' = a') as -> by (eapply functional_eval_exp; eassumption).
          exists a', n; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia |].
          eapply per_univ_trans'; [ exact Hab | exists R; exact HR ].
        * (** A recursive argument: the type of its shape ([shty_link]). *)
          pose proof (cargs_rev_nth_rec p D Mv gs gs1 t gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as ->.
          destruct (Fr t eq_refl) as (a' & Ea' & Hv).
          rewrite <- env_args_app, <- List.app_assoc in Ea'.
          set (fa := List.firstn (List.length gs1) vs) in *.
          pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hav Lv Heq) as Hpk; fold fa in Hpk.
          destruct (vg_cargs_sem_all p D Hvg Hcv v Mv c gs HMv Hcon gs1 (ca_rec t :: gs2) Heq) as [HW0 _].
          destruct (rel_ctx_wf_per_ctx_env HW0) as [R0 HR0].
          assert (HE0 : R0 (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))).
          { apply (gargs_env_rel _ _ _ _ _ _ HR0 HW0);
              [ rewrite !List.length_app, length_cargs_ctx, length_im_params, Ln, Lfa, ups_len; unfold im_np, ind_nu in *; lia |].
            exact Hpg2. }
          assert (Hpre_env : forall R, EF cargs_ctx p D Mv gs1 ++ im_params D Mv ≈ cargs_ctx p D Mv gs1 ++ im_params D Mv
                                          ∈ per_ctx_env ↘ R ->
                               R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))).
          { intros R HR; apply (per_ctx_env_right_irrel _ _ _ _ _ HR0 HR); exact HE0. }
          pose proof (fun Mj qc kc Is vm Dq cups cs bs0 bs0' =>
                        ViewReadback.view_end_type VP HVP p D HPD ups ups_gargs ups_len (ptyp_mem t) Mj qc kc Is vm Dq cups cs bs0 bs0') as Hend.
          assert (Hbb : Dom b ≈ b ∈ per_univ n) by (eapply per_univ_trans'; [ apply per_univ_sym'; exact Hab | exact Hab ]).
          destruct Hbb as [Rb HRb].
          destruct (shty_link p D Hvg Hcv v Mv c gs HMv Hcon (vg_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon) gs1 t gs2 Heq
                      ups ns fa ups_len Ln Lfa ups_gargs Hns Hpk Hpre_env Hend
                      (List.length (ptyp_doms t)) 0 nil b n Rb ltac:(lia) (tele_prefix_rel_nil _) ltac:(cbn; apply per_gargs_nil)
                      ltac:(cbn [List.repeat List.app ptyp_skip]; rewrite List.app_nil_r; exact Eb) HRb)
            as (bsh & Ebsh & Hbs).
          cbn [ptyp_skip] in Ebsh; rewrite List.app_nil_r in Ebsh.
          pose proof (functional_eval_shty _ _ _ _ _ _ Ebsh Ea') as <-.
          exists bsh, n; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia |].
          eapply per_univ_trans'; [ exact Hab | exact Hbs ].
    - (** A recursive result: the type of the recursive result
          ([ihty_link]). *)
      rewrite List.nth_error_app2 in HX by lia; rewrite LC in HX.
      destruct (ihs_rev_nth (im_nn Mv) (blocks_motives Bks) Us (List.length gs) gs (kk - (im_nn Mv + List.length gs)) _ HX)
        as (gs1 & t & gs2 & Heq & Hi' & HXe).
      rewrite <- Hi' in HXe; injection HXe as ->.
      set (j := cargs_nrec gs1) in *.
      assert (Hfk : List.firstn kk (ns ++ vs ++ ihs) = (ns ++ vs) ++ List.firstn j ihs)
        by (rewrite List.app_assoc, firstn_app_ge by (rewrite List.length_app; lia); rewrite List.length_app, Ln, Lv, Hi'; reflexivity).
      rewrite Hfk in Ea.
      pose proof Ea as Ea0.
      destruct (Completeness.Inductives.Elim.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & v' & Hx & Hv1' & Hsh).
      rewrite Hv1' in Hx; injection Hx as <-.
      set (fa := List.firstn (List.length gs1) vs) in *.
      set (aft := List.skipn (S (List.length gs1)) vs).
      assert (Evs : vs = fa ++ v' :: aft) by (unfold fa, aft; rewrite <- (skipn_nth_cons' _ _ _ Hv1'), List.firstn_skipn; reflexivity).
      assert (Lj : j <= List.length ihs) by (rewrite Li; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
      set (ihp := List.firstn j ihs) in *.
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn, Lv, Heq, List.length_app; cbn; lia).
      assert (Laft : List.length aft = List.length gs2) by (unfold aft; rewrite List.length_skipn, Lv, Heq, List.length_app; cbn; lia).
      assert (Lihp : List.length ihp = j) by (unfold ihp; rewrite List.length_firstn; lia).
      pose proof (vbs_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as HBs.
      pose proof (EB Completeness.Inductives.Elim.e_HCtxT ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs gs1 t gs2 Heq) as HCtxT.
      destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HCtxT) as [jT HT].
      pose proof (rel_ctx_wf_tail HCtxT) as HCtx.
      destruct (rel_ctx_wf_per_ctx_env HCtx) as [RS HRS].
      destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
      assert (Hm' : G v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                      (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)))
        by (rewrite skipn_app_exact by exact Lpre; exact Hm).
      assert (Hir' : rec_results_rel dr Rel v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                       gs vs vs ihs ihs)
        by (rewrite skipn_app_exact by exact Lpre; exact Hir).
      pose proof (EB Completeness.Inductives.Elim.cv_bctx_elem ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs ρ ρ Hρ Hρ
                    ups ups hd k (pre ++ ns) (pre ++ ns) vs vs ihs ihs Hm' Hir' RB HRB) as HZ.
      rewrite skipn_app_exact in HZ by exact Lpre.
      assert (HEE : RS (env_args ρ (ns ++ vs ++ ihp)) (env_args ρ (ns ++ vs ++ ihp))).
      { assert (Esp : ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                     = ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)
                       ++ ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs1)
          by (rewrite Heq at 2; rewrite Views.ihs_ctx_aux_app, List.app_nil_r; reflexivity).
        assert (Esplit : elim_bctx p D Mv gs (blocks_motives Bks) Us ++ Γ
                         = ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs ++ cinst Γ p D Mv Us gs)
          by (unfold elim_bctx, cinst; rewrite <- !List.app_assoc; reflexivity).
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite Esplit, Esp, <- List.app_assoc in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)))
          in HRB', HBs'.
        assert (Lr : List.length (List.skipn j ihs)
                     = List.length (List.rev (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))))
          by (rewrite List.length_rev, length_ihs_ctx_aux, List.length_skipn, Li; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
        assert (HZ' : RB (env_args (env_args ρ (ns ++ vs ++ ihp)) (List.skipn j ihs)) (env_args (env_args ρ (ns ++ vs ++ ihp)) (List.skipn j ihs)))
          by (rewrite <- env_args_app, <- !List.app_assoc; unfold ihp; rewrite List.firstn_skipn; exact HZ).
        destruct (Decl.rel_gargs _ _ _ _ HRS HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ') as [H _].
        exact H. }
      rewrite Evs, <- !List.app_assoc in HEE; cbn [List.app] in HEE.
      rewrite <- List.app_assoc, Evs, <- !List.app_assoc in Ea; cbn [List.app] in Ea.
      destruct (rel_exp_of_typ_inversion_simple_at HRS HT _ _ HEE) as (ty & ty' & Et & Et' & [R HR]).
      assert (ty = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (ty' = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (EB Completeness.Inductives.Elim.side_w ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs gs1 t gs2 Heq RS HRS
                  ρ ns fa v' aft ihp Hρ Ln Lfa Laft Lihp HEE) as (w & Hw & HwU & Lw).
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hav Lv Heq) as Hpk; fold fa in Hpk.
      destruct (rec_shape_facts v Mv c gs1 t gs2 0 HMv ltac:(rewrite <- Heq; exact Hcon)) as ((Mj & HMj & _) & _ & _).
      cbn [ptyp_skip] in HMj.
      destruct (HBks _ _ HMj) as [bj Hbj].
      assert (Hsh0 : rec_arg_rel p D (okr_at D ups nr) nr ar dr v ups ups (ns ++ nonrec_arg_vals gs1 fa ++ nil)
                       (ns ++ nonrec_arg_vals gs1 fa ++ nil) (ptyp_skip 0 t) v' v')
        by (rewrite List.app_nil_r; exact Hsh).
      destruct (EB Completeness.Inductives.Elim.ihty_link ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs gs1 t gs2 Heq RS HRS
                  Mj bj HMj Hbj (List.length (ptyp_doms t)) 0 ρ ns fa v' aft ihp w nil v' a jT R eq_refl Ln Lfa Laft Lihp eq_refl
                  Hρ HEE Hw HwU Lw Hns Hpk (tele_prefix_rel_nil _) (eval_apps_nil _ _ _) Hsh0 Ea HR) as (b & Eb & Hab).
      rewrite List.app_nil_r in Eb; cbn [ptyp_skip] in Eb.
      right; exists gs1, t, gs2, v', b, jT.
      split; [ exact Heq | split; [ unfold j in *; lia | split; [ exact Hv1' | split; [ exact Eb | split; [ exact Hab |] ] ] ] ].
      (** The recursive result, related at its type's value. *)
      assert (Esplit : elim_bctx p D Mv gs (blocks_motives Bks) Us ++ Γ
                       = ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs ++ cinst Γ p D Mv Us gs)
        by (unfold elim_bctx, cinst; rewrite <- !List.app_assoc; reflexivity).
      assert (Hpgi : per_gargs (List.rev (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs))
                       (env_args ρ (ns ++ vs)) (env_args ρ (ns ++ vs)) ihs ihs).
      { pose proof (Completeness.Inductives.Elim.ihs_pre_sem p D Γ Us Bks Mv gs HBs nil gs eq_refl) as HC0.
        cbn [ihs_ctx_aux List.app] in HC0.
        destruct (rel_ctx_wf_per_ctx_env HC0) as [RC HRC].
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite Esplit in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs)) in HRB', HBs'.
        assert (Lr : List.length ihs = List.length (List.rev (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs)))
          by (rewrite List.length_rev, length_ihs_ctx_aux; exact Li).
        assert (HZ' : RB (env_args (env_args ρ (ns ++ vs)) ihs) (env_args (env_args ρ (ns ++ vs)) ihs))
          by (rewrite <- env_args_app, <- List.app_assoc; exact HZ).
        destruct (Decl.rel_gargs _ _ _ _ HRC HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ')
          as [_ H].
        exact H. }
      assert (HXj : List.nth_error (List.rev (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs)) j
                    = Some (ce_ass (ptyp_ihty (blocks_motives Bks) (ι wk_shiftn (j + List.length gs + im_nn Mv))
                                      (ihs_sub (im_nn Mv) Us (List.length gs) (cargs_pat gs1) j)
                                      #(j + List.length gs - 1 - List.length (cargs_pat gs1)) t)))
        by (replace j with (kk - (im_nn Mv + List.length gs)) at 1 by (unfold j; lia); exact HX).
      destruct (per_gargs_nth_el _ _ _ _ _ j _ Hpgi HXj ltac:(rewrite Li; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia))
        as (i0 & Rae & ae & ae' & x0 & x0' & Eae & Eae' & HRae & Hx0 & Hx0' & Hrr).
      rewrite Hx0 in Hx0'; injection Hx0' as <-.
      rewrite <- env_args_app in Eae, Eae'; fold ihp in Eae, Eae'.
      assert (ae = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (ae' = a) as -> by (eapply functional_eval_exp; eassumption).
      exists i0, Rae, x0; split; [ exact Hx0 | split; [ exact HRae | exact Hrr ] ].
  Qed.

  (** At fresh recursive results, every entry is a fresh variable of a
      type related to its entry's. *)
  Lemma bctx_entry_link : forall v Mv c gs, ind_member D v = Some Mv -> ind_con Mv c = Some gs ->
      forall s ns vs ihs hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mv) ↘ vs ->
      Fihs vs at gs gs under ρ (blocks_motives Bks) in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns)
        ⍮ (s + im_nn Mv + List.length gs) ↘ ihs ->
      List.length pre = im_unu D Mv ->
      G v ups ups ns ns (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)) ->
      rec_results_rel dr Rel v ups ups ns ns gs vs vs ihs ihs ->
      forall kk X a, List.nth_error (List.rev (elim_bctx p D Mv gs (blocks_motives Bks) Us)) kk = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn kk (ns ++ vs ++ ihs)) ↘ a ->
        exists b (n : nat), List.nth_error (ns ++ vs ++ ihs) kk = Some (⇑! b (s + kk)) /\ Dom a ≈ b ∈ per_univ n.
  Proof.
    intros v Mv c gs HMv Hcon s ns vs ihs hd k pre Fn Fc Fi Lpre Hm Hir kk X a HX Ea.
    destruct (bctx_link_gen v Mv c gs HMv Hcon s ns vs ihs hd k pre Fn Fc Lpre Hm Hir kk X a HX Ea)
      as [[_ H] | (gs1 & t & gs2 & v' & b & n & Heq & -> & Hv' & Eb & Hab & _)]; [ exact H |].
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
    destruct (fresh_ihs_nth _ _ _ _ _ _ _ Fi gs1 t gs2 Heq) as (v0 & a' & Hv0 & Ea' & Hih).
    rewrite Hv' in Hv0; injection Hv0 as <-.
    rewrite <- env_args_app, <- List.app_assoc in Ea'.
    pose proof (functional_eval_ihty _ _ _ _ _ _ _ Eb Ea') as <-.
    exists b, n; split; [| exact Hab ].
    rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
    rewrite List.length_app, Ln, Lv.
    replace (im_nn Mv + List.length gs + cargs_nrec gs1 - (im_nn Mv + List.length gs)) with (cargs_nrec gs1) by lia.
    rewrite Hih; do 3 f_equal; lia.
  Qed.

  (** The readback of a branch of the block of the member [v] under the
      fresh variables, recursive results included, against the branch at
      [σ''] past its context: the branch is glued at the fresh
      substitution, at the motive's value at the constructor. *)
  Lemma rb_branch : forall v Mv b c gs n B, ind_member D v = Some Mv -> List.nth_error Bks v = Some b ->
      ind_con Mv c = Some gs -> In (c, n, B) (eb_brs b) ->
      forall Δ σ'' hd k pre ns vs ihs bv t0 Bn, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> im_ref p v Mv = (hd, k) ->
      List.length pre = im_unu D Mv ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ length Δ ↘ ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns) ⍮ (length Δ + im_nn Mv) ↘ vs ->
      Fihs vs at gs gs under ρ (blocks_motives Bks) in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns)
        ⍮ (length Δ + im_nn Mv + List.length gs) ↘ ihs ->
      G v ups ups ns ns (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)) ->
      rec_results_rel dr Rel v ups ups ns ns gs vs vs ihs ihs ->
      ⟦ B ⟧ env_args ρ (ns ++ vs ++ ihs) ↘ bv ->
      ⟦ eb_motive b ⟧ env_args ρ (ns ++ d_con hd k c (pre ++ ns ++ vs) :: nil) ↘ t0 ->
      Rnf ⇓ t0 bv in gc_deps ⍮ gc_stack ⍮ (length Δ + n) ↘ Bn ->
      elim_bctx p D Mv gs (blocks_motives (blocks_sub Bks σ'')) (List.map (fun U => U[σ'']) Us) ++ Δ
        ⊢ B[sb_qn n σ''] ≈ Bn : elim_bty p v Mv c gs (eb_motive b)[sb_qn (S (im_nn Mv)) σ''] (List.map (fun U => U[σ'']) Us).
  Proof.
    intros v Mv b c gs n B HMv Hb Hcon HinB Δ σ'' hd k pre ns vs ihs bv t0 Bn Hσ'' Href Lpre Fn Fc Fi Hm Hir Ebv Et0 HRn.
    pose proof (Har _ _ _ _ _ _ _ HMv Hb Hcon HinB) as Hn.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
    destruct (Completeness.Inductives.Elim.rec_results_rel_vs_len _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lv _].
    destruct (gbk_branch _ _ _ _ _ _ HBg _ _ _ _ _ _ _ HMv Hb Hcon HinB) as [SbB HSbB lvl Hbody].
    assert (Lb : List.length (elim_bctx p D Mv gs (blocks_motives Bks) Us) = (im_nn Mv + List.length gs + cargs_nrec gs)%nat)
      by (rewrite length_elim_bctx; lia).
    assert (Lx : List.length (ns ++ vs ++ ihs) = List.length (elim_bctx p D Mv gs (blocks_motives Bks) Us))
      by (rewrite Lb, !List.length_app, Ln, Lv, Li; lia).
    pose proof (glu_sub_fresh _ Γ SbΓ (elim_bctx_ass p D v Mv gs _ Us Hc HMv) HSbΓ SbB HSbB Δ σ'' ρ _ Hσ'' Lx
                  (bctx_entry_link v Mv c gs HMv Hcon (List.length Δ) ns vs ihs hd k pre Fn Fc Fi Lpre Hm Hir)) as Hτ.
    destruct (Hbody _ _ _ Hτ) as [eb rb Pb Elb Eeb Erb Hgb HBgl].
    assert (rb = bv) as -> by (eapply functional_eval_exp; eassumption).
    (** The branch type's value, against the motive's at the constructor. *)
    assert (Lbs : List.length (pre ++ ns) = (im_unu D Mv + im_nn Mv)%nat) by (rewrite List.length_app; lia).
    assert (HG' : G v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                    (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)))
      by (rewrite skipn_app_exact by exact Lpre; exact Hm).
    assert (Hir' : rec_results_rel dr Rel v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                     gs vs vs ihs ihs)
      by (rewrite skipn_app_exact by exact Lpre; exact Hir).
    assert (Hnn : tele_rel (nr v) (List.rev (im_nparams Mv)) ns (List.skipn (im_unu D Mv) (pre ++ ns))).
    { rewrite skipn_app_exact by exact Lpre.
      destruct (Completeness.Inductives.ViewReadback.fresh_nparams_exist p D Hvg ups ups_gargs ups_len v Mv (List.length Δ) HMv)
        as (ns' & Fn' & Hns).
      pose proof (functional_fresh_tele' _ _ _ _ _ Fn' Fn) as <-; exact Hns. }
    assert (Eeb' : ⟦ elim_bty p v Mv c gs (eb_motive b) Us ⟧ env_args ρ (List.skipn (im_unu D Mv) (pre ++ ns) ++ vs ++ ihs) ↘ eb)
      by (rewrite skipn_app_exact by exact Lpre; exact Eeb).
    rewrite List.app_assoc in Et0.
    pose proof (bty_val_rel v Mv c gs b HMv Hcon Hb hd k (pre ++ ns) vs ihs ns eb t0 Href Lbs HG' Hir' Hnn Eeb' Et0) as Hrel.
    (** The branch glued at the motive's value, read back. *)
    pose proof (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HBgl) as HTP.
    destruct (glu_transfer_per lvl iA eb t0 Pb Elb _ _ _ bv Hgb Hrel HTP HBgl) as (k' & P' & El' & Hg' & HP' & HM').
    destruct (realize_glu_elem_top _ _ _ _ Hg' _ _ _ _ HM') as [? ? _ _ _ _ Hrbs].
    assert (HΔb : ⊢ tele_sub (elim_bctx p D Mv gs (blocks_motives Bks) Us) σ'' ++ Δ)
      by (pose proof (glu_ctx_env_sub_escape HSbB _ _ _ Hτ); gen_presups; assumption).
    assert (Hlen : List.length (tele_sub (elim_bctx p D Mv gs (blocks_motives Bks) Us) σ'' ++ Δ) = (List.length Δ + n)%nat)
      by (rewrite List.length_app, length_tele_sub, Lb, Hn; lia).
    rewrite <- Hlen in HRn.
    pose proof (Hrbs _ wk_id _ (kripke_id _ HΔb) HRn) as H.
    rewrite !exp_wk_id in H.
    rewrite (elim_bctx_sub p D v Mv c gs (blocks_motives Bks) (blocks_motives (blocks_sub Bks σ'')) Us σ'' Hc HMv
               (cons_lookup_in _ _ _ Hcon) HUl (fun j0 Mj0 HMj0 => blocks_motives_sub D Bks σ'' j0 Mj0 Hnm HMj0)) in H.
    rewrite Lb, (elim_bty_sub p D v Mv c gs (eb_motive b) Us σ'' Hc HMv HUl) in H.
    rewrite Hn; exact H.
  Qed.

  (** The readback of a stuck eliminator's blocks, block by block. *)
  Lemma read_blocks_nth : forall s sel Ms i NBks, Rblks i Ms from p ups Bks sel in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ NBks ->
      List.length (nblocks_to_blocks NBks) = List.length Ms /\
      forall n b', List.nth_error (nblocks_to_blocks NBks) n = Some b' ->
        exists Mi Mv b hd k pre ns a A' Bs', List.nth_error Ms n = Some Mi /\
          ind_member D (elim_src sel (i + n)) = Some Mv /\ List.nth_error Bks (elim_src sel (i + n)) = Some b /\
          eb_nm b = S (im_nn Mi) /\ ⟦mref elim_src sel (i + n) of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) /\
          Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns /\
          ⟦ eb_motive b ⟧ env_args ρ (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mi) :: nil) ↘ a /\
          Rtyp a in gc_deps ⍮ gc_stack ⍮ S (s + im_nn Mi) ↘ A' /\
          Rbrs (eb_brs b) at (im_cons Mi) of Mi (hd, k, pre) from p ups Bks Mv (eb_motive b) in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Bs' /\
          b' = eb_mk (S (im_nn Mi)) None (nf_to_exp A') (nbrs_to_brs Bs').
  Proof.
    intros s sel Ms; induction Ms as [| Mi Ms IH]; intros i NBks HR; inversion HR; subst.
    - split; [ reflexivity | intros [] *; discriminate ].
    - match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H; injection H as <- end.
      match goal with H : Rblks (S i) Ms from _ _ _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => destruct (IH _ _ H) as [L1 HN1] end.
      split; [ cbn; f_equal; exact L1 |].
      intros [| n] b' Hn; cbn in Hn.
      + injection Hn as <-; rewrite Nat.add_0_r.
        do 10 eexists; split; [ reflexivity | repeat split; eassumption ].
      + destruct (HN1 n b' Hn) as (Mi' & Mv' & b0 & hd0 & k0 & pre0 & ns0 & a0 & A0 & Bs0 & HN2).
        replace (i + S n) with (S i + n) by lia.
        exists Mi', Mv', b0, hd0, k0, pre0, ns0, a0, A0, Bs0; exact HN2.
  Qed.

  (** What the PER model gives of the fresh variables of a block of the
      group read as its own ([member_pair], at [ups] on both sides): no
      argument nests through a view. *)
  Lemma own_member_pair : forall s i Mi, ind_member D i = Some Mi ->
      member_pair p D ups nr ar dr ρ ρ Bks Bks ups ups Rel s None i Mi.
  Proof.
    intros s i Mi HMi.
    pose proof (adm_fresh_of_uparams p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups (euo_adm_a _ _ _ _ _ _ _ _ Hups)) as Ha.
    refine (ER member_pair_of s None i Mi Mi (fun _ => 0) 0 Ha Ha ups_len ups_len (euo_mref_a _ _ _ _ _ _ _ _ Hups)
              (euo_mref_a _ _ _ _ _ _ _ _ Hups) HMi eq_refl eq_refl _ _).
    - intros c gs' gs Hin Hcn.
      assert (gs = gs') as -> by (pose proof (cons_lookup_nodup_in _ _ _ (Hnd _ _ HMi) Hin) as Hc0; unfold ind_con in Hcn; congruence).
      split; [ apply cargs_kinds_refl | apply cargs_nest_ok_refl ].
    - intros j0 Hj; lia.
  Qed.

  (** A block of the readback of a stuck eliminator at a declared member,
      against the group's own block at [σ'']: the same count and names,
      and equal motives and branches. *)
  Lemma own_block_rb : forall Δ σ'' NBks, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      Rblks 0 (ind_members D) from p ups Bks None in gc_deps ⍮ gc_stack ⍮ ρ ⍮ length Δ ↘ NBks ->
      forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        List.nth_error (nblocks_to_blocks NBks) k = Some b' ->
        eb_nm b' = S (im_nn Mk) /\ eb_ann b' = None /\
        elim_mctx p D k Mk (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ (eb_motive b)[sb_qn (S (im_nn Mk)) σ''] ≈ eb_motive b' : Typeω@iA /\
        List.map fst (brs_sub (eb_brs b) σ'') = List.map fst (eb_brs b') /\
        forall i c n B B' gs, List.nth_error (eb_brs b) i = Some (c, n, B) -> List.nth_error (eb_brs b') i = Some (c, n, B') ->
          ind_con Mk c = Some gs ->
          elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ'')) (List.map (fun U => U[σ'']) Us) ++ Δ
            ⊢ B[sb_qn n σ''] ≈ B' : elim_bty p k Mk c gs (eb_motive b)[sb_qn (S (im_nn Mk)) σ''] (List.map (fun U => U[σ'']) Us).
  Proof.
    intros Δ σ'' NBks Hσ'' HR k Mk b b' HMk Hb Hb'.
    destruct (read_blocks_nth _ _ _ _ _ HR) as [_ HRn].
    destruct (HRn k b' Hb') as (Mi & Mv & b0 & hd & k0 & pre & ns & a & A' & Bs' & HMi & HMv & Hb0 & Hnm0 & Er & Fn & Ea & HRA & HRB & ->).
    cbn [Nat.add elim_src] in *.
    assert (Mi = Mk) as -> by (unfold ind_member in HMk; congruence).
    rewrite HMk in HMv; injection HMv as <-.
    rewrite Hb in Hb0; injection Hb0 as <-.
    cbn [eb_nm eb_ann eb_motive eb_brs].
    destruct (read_brs_nth _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HRB) as (LB1 & LB2 & HBn).
    assert (Hgs : forall c gs' gs, List.In (c, gs') (im_cons Mk) -> ind_con Mk c = Some gs -> gs = gs')
      by (intros c gs' gs Hin Hcn; pose proof (cons_lookup_nodup_in _ _ _ (Hnd _ _ HMk) Hin) as Hc0; unfold ind_con in Hcn; congruence).
    split; [ reflexivity | split; [ reflexivity | split ] ].
    - exact (rb_motive k Mk b HMk Hb Δ σ'' hd k0 pre ns a A' Hσ'' Er Fn Ea HRA).
    - split.
      + (** The names and counts. *)
        assert (Efst : List.map fst (brs_sub (eb_brs b) σ'') = List.map fst (eb_brs b))
          by (unfold brs_sub; rewrite List.map_map; apply List.map_ext; intros [[c0 n0] B0]; reflexivity).
        rewrite Efst; apply List.nth_error_ext; intros idx; rewrite !List.nth_error_map.
        destruct (List.nth_error (nbrs_to_brs Bs') idx) as [[[c1 n1] B1] |] eqn:E1.
        * destruct (HBn idx c1 n1 B1 E1) as (gs' & gs & n0 & B0 & ns' & vs & ihs & wihs & bv & t & Bn & HB0 & Hcs & Hcn & En0 & En & _).
          rewrite HB0; cbn.
          pose proof (Hgs _ _ _ (List.nth_error_In _ _ Hcs) Hcn) as ->.
          rewrite En0, En; reflexivity.
        * rewrite (proj2 (List.nth_error_None _ _)); [ reflexivity |].
          apply List.nth_error_None in E1; lia.
      + (** A branch, by the fresh variables the PER model has. *)
        intros i c n B B' gs HBi HBi' Hcn.
        destruct (HBn i c n B' HBi') as (gs' & gs0 & n0 & B0 & ns' & vs & ihs & wihs & bv & t & Bn & HB0 & Hcs & Hcn0 & En0 & En
                                        & Hpl & Fn' & Fc & Fi & Wi & Ebv & Et & Rn & ->).
        rewrite HBi in HB0; injection HB0 as -> <-.
        rewrite Hcn in Hcn0; injection Hcn0 as <-.
        pose proof (Hgs _ _ _ (List.nth_error_In _ _ Hcs) Hcn) as <-.
        pose proof (wihs_same _ _ _ _ _ _ _ _ Wi) as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fn Fn') as <-.
        destruct (own_member_pair (List.length Δ) k Mk HMk) as [Mv HMv Hnn hd1 k1 pre1 pre2 R1 R2 Lp1 Lp2 nsa nsb Fa Fb Hneut Hnames Hbrs].
        cbn [elim_src] in HMv, R1, R2; rewrite HMk in HMv; injection HMv as <-.
        pose proof (functional_eval_mref _ _ _ _ _ R1 Er) as E1; injection E1 as -> -> ->.
        pose proof (functional_eval_mref _ _ _ _ _ R2 Er) as E2; injection E2 as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fa Fn) as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fb Fn) as ->.
        destruct (Hbrs c gs (List.nth_error_In _ _ Hcs)) as (gs1 & Hcn1 & _ & _ & BP).
        rewrite Hcn in Hcn1; injection Hcn1 as <-.
        destruct BP as [vsa vsb ihsa ihsb wa wb Fa' Fb' Ia Ib Wa Wb Hrel Hrecs].
        pose proof (functional_fresh_cargs _ _ _ _ _ _ Fa' _ Fc) as ->.
        pose proof (functional_fresh_cargs _ _ _ _ _ _ Fb' _ Fc) as ->.
        pose proof (functional_fresh_ihs _ _ _ _ _ _ _ _ Ia _ Fi) as ->.
        pose proof (functional_fresh_ihs _ _ _ _ _ _ _ _ Ib _ Fi) as ->.
        pose proof (wihs_same _ _ _ _ _ _ _ _ Wa) as ->.
        pose proof (wihs_same _ _ _ _ _ _ _ _ Wb) as ->.
        destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D k Mk ups hd k0 pre Hl HMk ups_len Er) as [Href Lpre].
        cbn [elim_src] in Hrel, Hrecs.
        rewrite !List.app_assoc in Hrel.
        exact (rb_branch k Mk b c gs n0 B HMk Hb Hcn (List.nth_error_In _ _ HBi) Δ σ'' hd k0 pre ns vs ihs bv t Bn Hσ'' Href Lpre
                 Fn Fc Fi Hrel Hrecs Ebv Et Rn).
  Qed.

  (** The readback of a stuck eliminator at a declared member is the
      elimination's at [σ'']: by the congruence, with the uniform
      parameters read back ([glu_args_read]), the blocks read back
      ([own_block_rb]) and the scrutinee read back. *)
  Lemma elim_rb_decl : forall j Mj pm, ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      forall as' e Δ σ'' Ns M oq (M0 : ne), elim_grp D oq p j -> Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> List.length Ns = im_nn Mj ->
      (forall i P T, List.nth_error (List.map (fun U => U[σ'']) Us ++ Ns) i = Some P ->
         List.nth_error (tele_insts (im_params D Mj) Id (List.map (fun U => U[σ'']) Us ++ Ns)) i = Some T -> Δ ⊢ P : T) ->
      (forall Mr, Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ Mr -> Δ ⊢ M ≈ Mr : im_ty_at p j Mj (List.map (fun U => U[σ'']) Us) Ns) ->
      Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
      Δ ⊢ a_elim oq (List.map (fun U => U[σ'']) Us) j (blocks_sub Bks σ'') M ≈ M0
        : (List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) σ''][sb_of_list Id (Ns ++ M :: nil)].
  Proof.
    intros j Mj pm HMj Hh as' e Δ σ'' Ns M oq M0 Hgrp Hσ'' HNl HPs HMr HR.
    inversion HR; subst.
    repeat match goal with
      | H1 : ind_lookup gc_deps gc_stack p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <-
      | H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <-
      end.
    match goal with H1 : im_ref p j Mj = _ |- _ => unfold im_ref in H1; rewrite Hh in H1; injection H1 as <- <- end.
    repeat match goal with
      | H1 : ind_lookup gc_deps gc_stack p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <-
      | H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <-
      end.
    match goal with H1 : ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ _ |- _ =>
      pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMj Hh H1) as E; injection E as -> end.
    assert (Hsel : im_sel Mj = None) by (unfold im_sel; rewrite Hh; reflexivity).
    rewrite Hsel in *.
    match goal with H1 : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRU0 end.
    match goal with H1 : Rblks _ _ from _ _ _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRB end.
    match goal with H1 : Rne e in _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRM end.
    set (Us' := List.map (fun U => U[σ'']) Us) in *.
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
    destruct (read_ps_nth _ _ _ _ _ HRU0) as [LUr _].
    assert (LUr' : List.length (nfs_to_exps Us0) = ind_nu D) by (rewrite LUr; exact ups_len).
    destruct (HBks _ _ HMj) as [b Hb].
    assert (Hσt : Δ ⊢ˢ σ'' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'').
    pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; fold Us' in HBt'.
    assert (Hbk' : List.nth_error (blocks_sub Bks σ'') j = Some (eblock_sub b σ'')) by (rewrite nth_error_blocks_sub, Hb; reflexivity).
    assert (HPl : List.length (Us' ++ Ns) = im_np D Mj) by (rewrite List.length_app, HUl', HNl; unfold im_np; lia).
    destruct (read_blocks_nth _ _ _ _ _ HRB) as [LNB _].
    rewrite (blocks_motives_nth _ _ _ Hb).
    change (ne_to_exp (ne_elim p Us0 j NBks M1)) with (a_elim (Some p) (nfs_to_exps Us0) j (nblocks_to_blocks NBks) (ne_to_exp M1)).
    rewrite <- (Hnm _ _ _ HMj Hb), <- Completeness.Inductives.Elim.eb_motive_sub.
    assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
    pose proof (own_block_rb Δ σ'' NBks Hσ'' HRB) as Hown.
    assert (E : Δ ⊢ a_elim oq (List.firstn (ind_nu D) (Us' ++ Ns)) j (blocks_sub Bks σ'') M
              ≈ a_elim (Some p) (List.firstn (ind_nu D) (nfs_to_exps Us0 ++ Ns)) j (nblocks_to_blocks NBks) (ne_to_exp M1)
              : (eb_motive (eblock_sub b σ''))[sb_of_list Id (List.skipn (ind_nu D) (Us' ++ Ns) ++ M :: nil)]).
    { eapply wf_exp_eq_elim_cong with (Ps' := nfs_to_exps Us0 ++ Ns) (Bks' := nblocks_to_blocks NBks);
      first [ exact Hl | exact Hgrp | exact HMj | exact Hbk' | exact HPl | exact HPs | reflexivity | exact LNB
            | exact (bt_len _ _ _ _ _ _ _ _ HBt') | idtac ];
      rewrite ?firstn_app_exact, ?skipn_app_exact by first [ exact HUl' | exact LUr' ];
      first [ exact (bt_nm _ _ _ _ _ _ _ _ HBt') | exact (bt_ann _ _ _ _ _ _ _ _ HBt') | exact (bt_motive _ _ _ _ _ _ _ _ HBt')
            | exact (bt_mctx _ _ _ _ _ _ _ _ HBt') | exact (bt_names _ _ _ _ _ _ _ _ HBt') | exact (bt_bctx _ _ _ _ _ _ _ _ HBt')
            | exact (bt_counts _ _ _ _ _ _ _ _ HBt') | idtac ].
      - left; reflexivity.
      - rewrite List.length_app, LUr', HNl; unfold im_np; lia.
      - (** The uniform parameters, against their readback. *)
        pose proof (glu_args_read Δ (ind_uparams D) Us' ups Ua (dc_uparams _ Hc) (us_glu_args Δ σ'' Hσ'') Δ wk_id Us0
                      (kripke_id Δ HΔ) HRU0) as Hu.
        rewrite map_wk_id in Hu.
        rewrite <- (firstn_app_exact Us' Ns (ind_nu D) HUl') in Hu.
        pose proof (exps_eq_at_params_of_uparams D Mj Δ (Us' ++ Ns) (nfs_to_exps Us0) Hc HPl HPs Hu) as [_ Hu'].
        rewrite skipn_app_exact in Hu' by exact HUl'.
        exact Hu'.
      - assert (Emt : ind_mty p D j Us' Ns = im_ty_at p j Mj Us' Ns) by (unfold ind_mty; rewrite HMj; reflexivity).
        rewrite Emt; exact (HMr M1 HRM).
      - intros k Mk b' HMk Hb'; destruct (HBks _ _ HMk) as [b0 Hb0]; exact (proj1 (Hown k Mk b0 b' HMk Hb0 Hb')).
      - intros k Mk b' Z HMk Hb' HZ; destruct (HBks _ _ HMk) as [b0 Hb0].
        rewrite (proj1 (proj2 (Hown k Mk b0 b' HMk Hb0 Hb'))) in HZ; discriminate.
      - intros k Mk ba b' HMk Hba Hb'.
        destruct (Completeness.Inductives.Elim.nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hb0).
        exact (proj1 (proj2 (proj2 (Hown k Mk b0 b' HMk Hb0 Hb')))).
      - intros k ba b' Hba Hb'.
        destruct (Completeness.Inductives.Elim.nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        destruct (ind_member D k) as [Mk |] eqn:HMk.
        2: { exfalso; unfold ind_member in HMk; apply List.nth_error_None in HMk.
             pose proof (bt_len _ _ _ _ _ _ _ _ HBt) as Lb.
             assert (k < List.length Bks) by (apply List.nth_error_Some; congruence); lia. }
        rewrite Completeness.Inductives.Elim.eb_brs_sub.
        exact (proj1 (proj2 (proj2 (proj2 (Hown k Mk b0 b' HMk Hb0 Hb'))))).
      - intros k Mk ba b' i c gs n B B' HMk Hba Hb' HB HB' Hcn.
        destruct (Completeness.Inductives.Elim.nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        rewrite Completeness.Inductives.Elim.eb_brs_sub in HB; unfold brs_sub in HB; rewrite List.nth_error_map in HB.
        destruct (List.nth_error (eb_brs b0) i) as [[[c0 n0] B0] |] eqn:HB0; cbn in HB; [| discriminate ].
        injection HB as -> -> <-.
        rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hb0).
        exact (proj2 (proj2 (proj2 (proj2 (Hown k Mk b0 b' HMk Hb0 Hb')))) i c n B0 B' gs HB0 HB' Hcn). }
    rewrite !firstn_app_exact, skipn_app_exact in E by first [ exact HUl' | exact LUr' ].
    exact E.
  Qed.

  (** The readback of a stuck eliminator at the member [j] is the
      elimination's at every substitution glued to [ρ]: at a declared
      member by [elim_rb_decl], at a view by the readback at the members
      of lower rank. *)
  Definition elim_rb_ok (j : nat) : Prop :=
    forall Mj as' e Δ σ'' Ns M oq (M0 : ne), ind_member D j = Some Mj -> elim_grp D oq p j -> Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      List.length Ns = im_nn Mj ->
      (forall i P T, List.nth_error (List.map (fun U => U[σ'']) Us ++ Ns) i = Some P ->
         List.nth_error (tele_insts (im_params D Mj) Id (List.map (fun U => U[σ'']) Us ++ Ns)) i = Some T -> Δ ⊢ P : T) ->
      (forall Mr, Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ Mr -> Δ ⊢ M ≈ Mr : im_ty_at p j Mj (List.map (fun U => U[σ'']) Us) Ns) ->
      Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
      Δ ⊢ a_elim oq (List.map (fun U => U[σ'']) Us) j (blocks_sub Bks σ'') M ≈ M0
        : (List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) σ''][sb_of_list Id (Ns ++ M :: nil)].

  Lemma elim_rb_decl_ok : forall j Mj pm, ind_member D j = Some Mj -> im_head Mj = mh_decl pm -> elim_rb_ok j.
  Proof.
    intros j Mj pm HMj Hh Mj' as' e Δ σ'' Ns M oq M0 HMj'; rewrite HMj in HMj'; injection HMj' as <-.
    exact (elim_rb_decl j Mj pm HMj Hh as' e Δ σ'' Ns M oq M0).
  Qed.

  Lemma motive_inst_wk : forall X n σ' L φ, List.length L = n ->
      (X[sb_qn n σ'][sb_of_list Id L])[φ]ʷ = X[sb_qn n (sb_wk σ' φ)][sb_of_list Id (List.map (fun N => N[φ]ʷ) L)].
  Proof.
    intros * <-.
    rewrite exp_sub_qn_of_list, <- (List.length_map (fun N => N[φ]ʷ) L), exp_sub_qn_of_list.
    rewrite <- exp_sub_of_wk, exp_sub_sub; apply exp_sub_sb_eq.
    etransitivity; [ apply sb_of_list_compose_gen |].
    rewrite (List.map_ext (fun M => M[ι φ]) (fun N => N[φ]ʷ)) by (intros; apply exp_sub_of_wk).
    apply sb_of_list_cong; symmetry; apply sb_wk_compose.
  Qed.

  (** The readback, at every weakening of a substitution glued to [ρ]. *)
  Lemma elim_rb_wk : forall j, elim_rb_ok j ->
      forall Mj as' e Δ' σ' oq' Ns' M', ind_member D j = Some Mj -> elim_grp D oq' p j -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      List.length Ns' = im_nn Mj ->
      (forall i P T, List.nth_error (List.map (fun U => U[σ']) Us ++ Ns') i = Some P ->
         List.nth_error (tele_insts (im_params D Mj) Id (List.map (fun U => U[σ']) Us ++ Ns')) i = Some T -> Δ' ⊢ P : T) ->
      (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns')[φ]ʷ) ->
      forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
        Δ ⊢ (a_elim oq' (List.map (fun U => U[σ']) Us) j (blocks_sub Bks σ') M')[φ]ʷ ≈ M0
          : ((List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)])[φ]ʷ.
  Proof.
    intros j Hok Mj as' e Δ' σ' oq' Ns' M' HMj Hg Hσ' HNl HPs HMr Δ φ M0 Hφ HR.
    pose proof (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) as Hσ2.
    assert (EU : List.map (fun U0 => U0[φ]ʷ) (List.map (fun U => U[σ']) Us) = List.map (fun U => U[sb_wk σ' φ]) Us)
      by (rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub).
    assert (EB : blocks_wk (blocks_sub Bks σ') φ = blocks_sub Bks (sb_wk σ' φ))
      by (rewrite <- blocks_sub_of_wk, blocks_sub_sub; apply blocks_sub_sb_eq; symmetry; apply sb_wk_compose).
    rewrite exp_wk_elim, EU, EB.
    rewrite (motive_inst_wk _ (S (im_nn Mj)) σ' (Ns' ++ M' :: nil) φ) by (rewrite List.length_app, HNl; cbn; lia).
    rewrite List.map_app; cbn [List.map].
    apply (Hok Mj as' e Δ (sb_wk σ' φ) (List.map (fun N => N[φ]ʷ) Ns') M'[φ]ʷ oq' M0 HMj Hg Hσ2);
      [ rewrite List.length_map; exact HNl | | | exact HR ].
    - intros i P T HP HT.
      rewrite <- EU, <- List.map_app in HP, HT.
      rewrite <- (params_insts_wk D j Mj _ φ Hc HMj) in HT.
      apply nth_error_map_inv in HP as (P0 & HP0 & ->).
      apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      exact (kripke_preserves_exp _ _ _ _ _ (HPs _ _ _ HP0 HT0) Hφ).
    - intros Mr HMr0.
      pose proof (HMr Δ φ Mr Hφ HMr0) as H.
      assert (Emt : forall Us0 Ns0, im_ty_at p j Mj Us0 Ns0 = ind_mty p D j Us0 Ns0) by (intros; unfold ind_mty; rewrite HMj; reflexivity).
      rewrite Emt, ind_mty_wk in H by (try exact Hc; rewrite List.length_map; exact HUl).
      rewrite EU, <- Emt in H; exact H.
  Qed.

  (** At the end of a shape, the recursive result of a neutral argument is
      glued: it is a stuck eliminator, whose readback is the elimination's
      ([elim_rb_ok] at the member the shape ends in). *)
  Lemma rec_neut_self : forall j0 Ps Mj pre bs Δ' σ' oq' σs N pc k' as' e r a (i : nat) P El,
      elim_rb_ok j0 -> ind_member D j0 = Some Mj -> List.length Ps = im_nn Mj ->
      (oq' = Some p \/ oq' = None) -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      (forall k P0 T, List.nth_error (List.map (fun P1 => P1[σs]) Ps) k = Some P0 ->
         List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (List.map (fun U => U[σ']) Us)) (List.map (fun P1 => P1[σs]) Ps)) k
           = Some T -> Δ' ⊢ P0 : T) ->
      (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ N[φ]ʷ ≈ M0 : (ptyp_ty_at p D (List.map (fun U => U[σ']) Us) σs (pt_self j0 Ps))[φ]ʷ) ->
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bs ->
      G j0 ups ups bs bs (⇑ (d_ind pc k' as') e) (⇑ (d_ind pc k' as') e) ->
      ⟦ih ⇑ (d_ind pc k' as') e of pt_self j0 Ps under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
      ⟦ihty ⇑ (d_ind pc k' as') e of pt_self j0 Ps under ρ (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ a ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El ->
      Δ' ⊢ ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σs N (pt_self j0 Ps) ® P ->
      Δ' ⊢ ptyp_ih p D oq' (List.map (fun U => U[σ']) Us) (blocks_sub Bks σ') σs N (pt_self j0 Ps)
          : ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σs N (pt_self j0 Ps) ® r ∈ El.
  Proof.
    intros * Hok HMj HPl Hoq Hσ' HQ Hn Ebs Hm Er Ea Hg HT.
    set (Us' := List.map (fun U => U[σ']) Us) in *.
    set (Q := List.map (fun P1 => P1[σs]) Ps) in *.
    assert (HAQ : ptyp_ty_at p D Us' σs (pt_self j0 Ps) = im_ty_at p j0 Mj Us' Q)
      by (cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
    rewrite HAQ in Hn.
    inversion Er; subst.
    match goal with H : ⟦elim _ at j0 of _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
    match goal with H1 : ind_lookup gc_deps gc_stack p = Some _ |- _ => rewrite Hl in H1; injection H1 as <- end.
    match goal with H1 : ind_member D j0 = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end.
    match goal with H1 : im_ref p j0 Mj = (pc, k') |- _ => rename H1 into Href end.
    match goal with H1 : ind_lookup gc_deps gc_stack pc = Some _ |- _ => rename H1 into Hq0 end.
    match goal with H1 : ind_member _ k' = Some _ |- _ => rename H1 into HMk0 end.
    match goal with H1 : List.nth_error Bks j0 = Some _ |- _ => rename H1 into Hb end.
    match goal with H1 : ⟦ eb_motive _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into Ea0 end.
    destruct (ER im_ref_target j0 Mj pc k' HMj Href) as (Dq' & Mq & Hq & HMq & Hnnq & Hnuq).
    rewrite Hq0 in Hq; injection Hq as <-; rewrite HMk0 in HMq; injection HMq as <-.
    pose proof Hm as Hm'; unfold grp_rel in Hm'; inversion Hm'; subst.
    match goal with H1 : ind_member D j0 = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end.
    match goal with H1 : tele_rel _ _ bs (List.skipn _ _) |- _ => rename H1 into Hsn end.
    match goal with H1 : tele_rel _ _ bs bs |- _ => rename H1 into Hbs end.
    pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ j0 Mj _ _ _ _ _ _ _ _ HMj Hm Hsn Hbs) as HG2.
    destruct (mot_rel j0 Mj _ _ ups ups _ bs _ _ HMj Hb Hb HG2) as (a1 & a2 & Ea1 & Ea2 & Hr12).
    rewrite Hnuq in Ea0.
    assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption).
    inversion Ea; subst.
    match goal with H : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs1 |- _ => assert (bs1 = bs) as -> by (eapply functional_eval_exps'; eassumption) end.
    match goal with H : ⟦ List.nth j0 _ _ ⟧ _ ⍮ _ ⍮ _ ↘ a |- _ => rewrite (blocks_motives_nth _ _ _ Hb) in H; rename H into Ea' end.
    assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [Ra HRa].
    destruct (per_univ_elem_sym _ _ _ _ Hr12) as [Hr21 _].
    destruct (Instance.per_univ_elem_trans_any _ _ _ _ _ _ _ HRa Hr21) as (R2 & HR2 & _).
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R2 HR2) Hg) as Hg1.
    cbn [ptyp_ih ptyp_ihty] in HT |- *; unfold elim_at.
    rewrite (blocks_motives_sub D Bks σ' j0 Mj Hnm HMj) in HT |- *.
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
    assert (HPs : forall i0 P0 T, List.nth_error (Us' ++ Q) i0 = Some P0 ->
                    List.nth_error (tele_insts (im_params D Mj) Id (Us' ++ Q)) i0 = Some T -> Δ' ⊢ P0 : T)
      by exact (params_typed_join gc_deps gc_stack D Hc j0 Mj Δ' Us' Q HMj HUl'
                  (glu_args_typed _ _ _ _ _ _ Ua (us_glu_args Δ' σ' Hσ')) HQ).
    assert (HQl : List.length Q = im_nn Mj) by (unfold Q; rewrite List.length_map; exact HPl).
    pose proof (elim_rb_wk j0 Hok Mj as' e Δ' σ' _ Q N HMj (elim_at_grp' oq' j0 Mj Hoq HMj) Hσ' HQl HPs Hn) as Hrd.
    pose proof (ER per_bot_elim j0 Mj pc k' as' as' e e ups ups bs bs HMj Hm) as Hper.
    destruct (Hper (length Δ')) as (L0 & HL0 & _).
    pose proof (Hrd Δ' wk_id L0 (kripke_id _ HΔ') HL0) as Hid.
    rewrite !exp_wk_id in Hid.
    destruct (presup_exp_eq Hid) as (_ & Hty & _).
    eapply realize_glu_elem_bot; [ exact Hg1 |].
    econstructor; [ exact Hty | exact Hg1 | exact HT | exact Hper | exact Hrd ].
  Qed.

  (** The recursive result of a neutral argument of a shape, the shape's
      components glued ([shape_typ_glu]'s substitution): glued at every
      gluing of the value of its type.  At the end of the shape by
      [rec_neut_self], the motive's instance glued by [motive_glu] at the
      shape's parameters glued ([Con.rec_params_args]); at a domain, a
      function of the domain, by the shape's rest at the neutral applied. *)
  Lemma rec_neut_glu : forall k Mk c gs gs1 t0 gs2 ns nv, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      gs = gs1 ++ ca_rec t0 :: gs2 ->
      tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns ->
      tele_prefix_rel (ar k ns c) (List.length (cargs_nonrec gs1)) nv nv ->
      List.length ns = im_nn Mk -> List.length nv = List.length (cargs_nonrec gs1) ->
      elim_rb_ok (ptyp_mem t0) ->
      forall t d ys Δ' σ' oq' τ Ys SbC N a_sh e r a (i : nat) R P El,
        ptyp_skip d t0 = t -> d <= List.length (ptyp_doms t0) ->
        tele_prefix_rel (shape_doms_rel (dr k) ns nv (ptyp_doms t0)) d ys ys ->
        (oq' = Some p \/ oq' = None) -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
        List.length Ys = d + List.length (cargs_nonrec gs1) + im_nn Mk ->
        EG doms_ctx (List.firstn d (ptyp_doms t0)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
          ∈ glu_ctx_env ↘ SbC ->
        Δ' ⊢ˢ sb_of_list τ (List.map (fun U => U[σ']) Us ++ Ys) ® env_args nil (ups ++ ns ++ nv ++ ys) ∈ SbC ->
        ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nv ++ ys) ↘ a_sh ->
        (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
           Δ ⊢ N[φ]ʷ ≈ M0 : (ptyp_ty_at p D (List.map (fun U => U[σ']) Us) (sb_of_list τ (List.map (fun U => U[σ']) Us ++ Ys)) t)[φ]ʷ) ->
        rec_arg_rel p D (okr_at D ups nr) nr ar dr k ups ups (ns ++ nv ++ ys) (ns ++ nv ++ ys) t (⇑ a_sh e) (⇑ a_sh e) ->
        ⟦ih ⇑ a_sh e of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
        ⟦ihty ⇑ a_sh e of t under ρ (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nv ++ ys) ↘ a ->
        DF a ≈ a ∈ per_univ_elem i ↘ R -> R r r -> uidx_le u (ul i) -> iA <= i -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ' ⊢ ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id (sb_of_list τ (List.map (fun U => U[σ']) Us ++ Ys)) N t : Typeω@i ->
        Δ' ⊢ ptyp_ih p D oq' (List.map (fun U => U[σ']) Us) (blocks_sub Bks σ') (sb_of_list τ (List.map (fun U => U[σ']) Us ++ Ys)) N t
            : ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id (sb_of_list τ (List.map (fun U => U[σ']) Us ++ Ys)) N t ® r ∈ El.
  Proof.
    intros k Mk c gs gs1 t0 gs2 ns nv HMk Hcon Heq Hns Hnv Hnsl Hnvl Hok t.
    induction t as [j0 Ps | B t IH];
      intros d ys Δ' σ' oq' τ Ys SbC N a_sh e r a i R P El Hsk Hd Hy Hoq Hσ' HYl HSbC Hσs Esh Hn Hsh Er Ea HR Hr Hui HiA Hg HIT.
    - (** The end of the shape. *)
      destruct (ptyp_skip_self _ _ _ _ Hsk) as (Hdd & Hm0 & Hp0).
      assert (Hdeq : d = List.length (ptyp_doms t0)) by lia; subst d.
      rewrite Hm0 in Hok.
      destruct (rec_shape_facts k Mk c gs1 t0 gs2 0 HMk ltac:(rewrite <- Heq; exact Hcon)) as ((Mj & HMj & HPl) & _ & _).
      cbn [ptyp_skip] in HMj, HPl; rewrite Hm0 in HMj; rewrite Hp0 in HPl.
      inversion Esh; subst.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs1 & bs1' & Ebs1 & Ebs1' & _ & _ & Hir).
      match goal with H : ⟦mref _ of _ _ ⟧ _ ⍮ _ ↘ _ |- _ => rename H into Er0 end.
      match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ _ ↘ ?bs0, H' : ⟦shty _ of _ _ ⟧ _ ⍮ _ ⍮ _ ↘ d_ind _ _ (_ ++ ?bs0) |- _ => rename H into Ebs end.
      assert (bs1 = bs) as -> by (eapply functional_eval_exps'; eassumption).
      assert (bs1' = bs) as -> by (eapply functional_eval_exps'; eassumption).
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (HUl' : List.length (List.map (fun U => U[σ']) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
      assert (Hysl : List.length ys = ptyp_depth t0) by (destruct Hy as [Hyl _]; unfold ptyp_depth; lia).
      assert (HSbC' : EG ptyp_tele t0 ++ nonrec_args_prefix (gs1 ++ ca_rec t0 :: gs2) (List.length (cargs_nonrec gs1)) ++ im_params D Mk
                        ∈ glu_ctx_env ↘ SbC) by (rewrite List.firstn_all in HSbC; exact HSbC).
      pose proof (Con.rec_params_args VP p D HVP HPD HG k Mk c _ HMk Hcon ups ups_len Δ' gs1 t0 gs2 Mj τ _ Ys ns nv ys SbC bs eq_refl
                    HMj HUl' ltac:(unfold ptyp_depth; lia) Hnsl Hnvl Hysl HSbC' Hσs Ebs) as HQg.
      pose proof (glu_args_typed _ _ _ _ _ _ (decl_closed_nparams_ass D Hc _ _ HMj) HQg) as HQ.
      pose proof Hir as Hir'; unfold grp_rel in Hir'; inversion Hir'; subst.
      match goal with H1 : tele_rel _ _ bs bs |- _ => rename H1 into Hbs end.
      match goal with H1 : per_bot e e |- _ => rename H1 into He end.
      pose proof (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl ups_len Hbu Hule Hf Δ' _ HΔ'
                    (us_glu_args Δ' σ' Hσ')) as HIGC.
      match goal with H1 : ind_member D (ptyp_mem t0) = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end.
      pose proof (nparams_of_glu_args p D Hass ups u NP NEl AP AEl DP DEl ups_len Hf _ Mj Δ' _ _ bs HMj HIGC HQg Hbs) as Hgn.
      set (Us' := List.map (fun U => U[σ']) Us) in *.
      set (Q := List.map (fun P0 => P0[sb_of_list τ (Us' ++ Ys)]) (ptyp_ps t0)) in *.
      assert (HAQ : ptyp_ty_at p D Us' (sb_of_list τ (Us' ++ Ys)) (pt_self (ptyp_mem t0) (ptyp_ps t0)) = im_ty_at p (ptyp_mem t0) Mj Us' Q)
        by (cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
      (** The scrutinee, glued at every gluing of its type's value. *)
      assert (Hgl : forall (i' : nat) P' El', nb <= i' -> DG d_ind pc k0 (pre ++ bs) ∈ glu_univ_elem i' ↘ P' ↘ El' ->
                Δ' ⊢ im_ty_at p (ptyp_mem t0) Mj Us' Q ® P' ->
                Δ' ⊢ N : im_ty_at p (ptyp_mem t0) Mj Us' Q ® ⇑ (d_ind pc k0 (pre ++ bs)) e ∈ El').
      { intros i' P' El' _ Hglu HTP.
        destruct (He (length Δ')) as (L0 & HL0 & _).
        pose proof (Hn Δ' wk_id L0 (kripke_id _ HΔ') HL0) as Hid; rewrite HAQ, !exp_wk_id in Hid.
        destruct (presup_exp_eq Hid) as (_ & HNt & _).
        eapply realize_glu_elem_bot; [ exact Hglu |].
        econstructor; [ exact HNt | exact Hglu | exact HTP | exact He |].
        intros Δ φ M0 Hφ HR0; rewrite <- HAQ; exact (Hn Δ φ M0 Hφ HR0). }
      destruct (motive_glu (ptyp_mem t0) Mj Δ' σ' Q bs N _ pc k0 pre HMj Hσ' Hgn Hbs Er0 Hgl) as (a0 & Ea0 & Hpa0 & HPa0).
      inversion Ea; subst.
      match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ _ ↘ ?bs2, H' : ⟦ List.nth _ _ _ ⟧ _ ⍮ _ ⍮ env_args _ (?bs2 ++ _) ↘ a |- _ =>
        assert (bs2 = bs) as -> by (eapply functional_eval_exps'; eassumption) end.
      assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_glu_univ_elem _ _ Hpa0) as (Pa & Ela & Hga).
      pose proof (HPa0 Pa Ela Hga) as HTa.
      assert (HT : Δ' ⊢ ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id (sb_of_list τ (Us' ++ Ys)) N (pt_self (ptyp_mem t0) (ptyp_ps t0)) ® P).
      { cbn [ptyp_ihty]; rewrite (blocks_motives_sub D Bks σ' _ Mj Hnm HMj).
        eapply glu_univ_elem_typ_cumu_ge; [ exact HiA | exact Hga | exact Hg | exact HTa ]. }
      exact (rec_neut_self (ptyp_mem t0) (ptyp_ps t0) Mj (ns ++ nv ++ ys) bs Δ' σ' oq' _ N pc k0 (pre ++ bs) e r a i P El
               Hok HMj HPl Hoq Hσ' HQ Hn Ebs Hir Er Ea Hg HT).
    - (** A domain of the shape. *)
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (HUl' : List.length (List.map (fun U => U[σ']) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
      pose proof (shape_typ_glu p D HG Hc Hdt Hsu ups bu u NP NEl AP AEl DP DEl ups_len Hbu Hule Hf k Mk c gs gs1 t0 gs2 ns nv
                    HMk Hcon Heq Hns Hnv Hnsl Hnvl (pt_pi B t) d ys Δ' τ _ Ys SbC Hsk Hd Hy HΔ' HUl' HYl HSbC Hσs) as Hshg.
      destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hsk'].
      assert (Hkl : d < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
      destruct (rec_shape_facts k Mk c gs1 t0 gs2 (S d) HMk ltac:(rewrite <- Heq; exact Hcon)) as ((Mj & HMj & HPl) & Hmd & Hmp).
      rewrite Hsk' in HMj, HPl, Hmd, Hmp.
      set (Us' := List.map (fun U => U[σ']) Us) in *.
      set (σs := sb_of_list τ (Us' ++ Ys)) in *.
      cbn [ptyp_ty_at ptyp_ih ptyp_ihty glu_shape_typ] in Hn, HIT, Hshg |- *.
      destruct (Hshg _ _ eq_refl) as [Hq1 _].
      pose proof (eval_ih_pi_inv _ _ _ _ _ _ _ _ Er) as ->.
      destruct (eval_ihty_pi_inv _ _ _ _ _ _ _ Ea) as (b1 & Eb1 & ->).
      inversion Esh; subst.
      match goal with H : ⟦ B ⟧ _ ⍮ _ ⍮ _ ↘ ?b2 |- _ => assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption) end.
      set (t := ptyp_skip (S d) t0) in *.
      pose proof HR as HRsave.
      basic_invert_per_univ_elem HR.
      match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
      match goal with H : _ <~> (fun _ _ => forall _ _ _, rel_mod_app _ _ _ _ _) |- _ => rename H into HRE end.
      destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' Hg) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & HEleq).
      pose proof (ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hns Hcon eq_refl Hnv HB Hy Eb1) as HgD.
      destruct (wf_pi_inversion' HIT) as [HITt HOTt].
      set (IT := B[σs]) in *.
      set (OTy := ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us') (q σs) t) in *.
      assert (HIT' : forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® IP).
      { intros Δ φ Hφ.
        eapply (glu_typ_transfer u (ul i) (ul i)); [ exact Hui | apply uidx_le_refl | eexists; exact equiv_a_a' | exact HgD
                                                   | exact Hgb1 | exact (Hq1 _ _ Hφ) ]. }
      assert (HDEl : forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                       Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k (ns ++ nv ++ ys) B).
      { intros * Hφ Hb.
        eapply glu_elem_retype; [ exact Hgb1 | exact HgD | exact (glu_univ_elem_trm_typ _ _ _ _ Hgb1 _ _ _ _ Hb) | exact Hb
                                | exact (Hq1 _ _ Hφ) ]. }
      set (body := ptyp_ih p D oq' (List.map (fun U => U[↑]ʷ) Us') (blocks_wk (blocks_sub Bks σ') ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t).
      set (OTi := ptyp_ihty (blocks_motives (blocks_sub Bks σ')) (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t) in *.
      assert (EUs : forall φ, List.map (fun U0 => U0[φ]ʷ) Us' = List.map (fun U => U[sb_wk σ' φ]) Us)
        by (intros φ; unfold Us'; rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub).
      assert (Esb : forall φ b, sb_eq (q σs ⨟ ((ι φ),,b))
                      (sb_of_list (sb_wk τ φ) (List.map (fun U => U[sb_wk σ' φ]) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil)))).
      { intros φ b0; etransitivity; [ apply sb_q_extend_wk |].
        rewrite List.app_assoc, sb_of_list_app; cbn [sb_of_list].
        apply sb_extend_cong; unfold σs; etransitivity; [ apply sb_wk_sb_of_list |].
        rewrite List.map_app, EUs; reflexivity. }
      assert (Happ : forall Δ φ b cc (equiv_c : in_rel cc cc), Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® cc ∈ IEl ->
                       exists rc a2, $| d_ihfn ρ Bks p ups t (⇑ (Πᵈ b1 (nil ↦ d_shfam p ups (env_args nil (ups ++ ns ++ nv ++ ys)) t) fam_cod) e)
                                         & cc | gc_deps ⍮ gc_stack ↘ rc /\
                         ⟦ fam_cod ⟧ (nil ↦ d_ihfam ρ (blocks_motives Bks) (env_args nil (ups ++ ns ++ nv ++ ys)) t
                                        (⇑ (Πᵈ b1 (nil ↦ d_shfam p ups (env_args nil (ups ++ ns ++ nv ++ ys)) t) fam_cod) e)) ↦ cc ↘ a2 /\
                         Δ ⊢ body[(ι φ),,b] : OTi[(ι φ),,b] ® rc ∈ OEl cc equiv_c).
      { intros Δ φ b cc equiv_c Hφ Hb.
        pose proof (rel_dr ups k (ns ++ nv ++ ys) B b1 i in_rel cc Eb1 equiv_a_a' equiv_c) as Hdc.
        pose proof (HDEl _ _ _ _ Hφ Hb) as HbD.
        destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh cc cc Hdc) as (fc & fc' & Efc & Efc' & Hsh').
        assert (fc' = fc) as -> by (eapply functional_eval_app; eassumption).
        destruct (Hcod _ _ equiv_c) as [a2 a2' Ea2 Ea2' Ha22].
        assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
        destruct (proj1 (HRE _ _) Hr _ _ equiv_c) as [rc rc' Erc Erc' Hrc].
        assert (rc' = rc) as -> by (eapply functional_eval_app; eassumption).
        destruct (eval_fam_cod_ihfam_inv _ _ _ _ _ _ _ Ea2) as (fx & Efx & Ea2i).
        assert (fx = fc) as -> by (eapply functional_eval_app; eassumption).
        destruct (eval_app_ihfn_inv _ _ _ _ _ _ _ _ Erc) as (y & Ey & Erc0).
        assert (y = fc) as -> by (eapply functional_eval_app; eassumption).
        inversion Efc; subst.
        pose proof (eval_fam_cod_shfam_inv p ups (env_args nil (ups ++ ns ++ nv ++ ys)) t cc _ ltac:(eassumption)) as Esh'.
        exists rc, a2; split; [ exact Erc | split; [ exact Ea2 |] ].
        assert (HΔ : ⊢ Δ) by (eapply kripke_dom; exact Hφ).
        pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hb) as Hbt.
        destruct (gid_dctx _ HG _ _ _ _ _ _ _ (S d) HMk Hcon eq_refl ltac:(lia)) as [SbC' HSbC'].
        pose proof (shape_sub_step D ups u DP DEl k Mk c _ gs1 t0 gs2 d B ns nv ys Δ' τ Us' Ys SbC SbC' Δ φ b b1 cc
                      HMk Hcon eq_refl HB HSbC HSbC' Hσs Hφ Eb1 HgD (Hq1 _ _ Hφ) HbD) as Hσs'.
        rewrite EUs in Hσs'.
        assert (ETy : ptyp_ty_at p D (List.map (fun U => U[sb_wk σ' φ]) Us)
                        (sb_of_list (sb_wk τ φ) (List.map (fun U => U[sb_wk σ' φ]) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))) t
                      = OTy[(ι φ),,b]).
        { unfold OTy; rewrite (shape_ty_step VP HVP p D HPD t Us' σs φ b HUl'), EUs.
          apply ptyp_ty_at_sb_eq; symmetry; apply Esb. }
        (** The neutral applied, read back. *)
        assert (Hn' : forall Δ1 φ1 M1, Δ1 ⊢ᵏ φ1 : Δ -> Rne (e $ᵈ ⇓ b1 cc) in gc_deps ⍮ gc_stack ⍮ length Δ1 ↘ M1 ->
                  Δ1 ⊢ (a_app N[φ]ʷ b)[φ1]ʷ ≈ M1
                    : (ptyp_ty_at p D (List.map (fun U => U[sb_wk σ' φ]) Us)
                        (sb_of_list (sb_wk τ φ) (List.map (fun U => U[sb_wk σ' φ]) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))) t)[φ1]ʷ).
        { intros Δ1 φ1 M1 Hφ1 HR1; rewrite ETy.
          inversion HR1; subst.
          match goal with H1 : Rne e in _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRe end.
          match goal with H1 : Rnf ⇓ b1 cc in _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRc end.
          pose proof (kripke_compose _ _ _ _ _ Hφ1 Hφ) as Hφφ.
          pose proof (Hn _ _ _ Hφφ HRe) as HNe.
          destruct (realize_glu_elem_top _ _ _ _ Hgb1 _ _ _ _ Hb) as [_ _ _ _ _ _ Hbr].
          pose proof (Hbr _ _ _ Hφ1 HRc) as Hbe.
          rewrite (exp_wk_wk_ext IT φ φ1 (φ ⊙ φ1)) in Hbe by (intros ?; reflexivity).
          cbn [exp_wk ne_to_exp] in HNe |- *.
          rewrite (exp_wk_wk_ext N φ φ1 (φ ⊙ φ1)) by (intros ?; reflexivity).
          destruct (presup_exp_eq HNe) as (_ & _ & _ & [jn Hjn]).
          destruct (wf_pi_inversion' Hjn) as [HA HB'].
          assert (ET2 : (OTy[(ι φ),,b])[φ1]ʷ = OTy[wk_q (φ ⊙ φ1)]ʷ[Id,,b[φ1]ʷ]).
          { rewrite exp_sub_wk_q_extend, exp_wk_sub; apply exp_sub_sb_eq.
            etransitivity; [ apply sb_wk_extend |]; apply sb_extend_cong; intros ?; reflexivity. }
          rewrite ET2.
          eapply wf_exp_eq_app_cong; [ exact HA | exact HB' | exact HNe | exact Hbe ]. }
        unfold body, OTi, Us'.
        rewrite ih_body_inst, (ih_cod_inst _ _ _ _ _ _ Mj HMj HPl); cbn [sentry_exp].
        rewrite (ptyp_ih_sb_eq p D oq' t _ _ _ _ _ (Esb φ b)), (ptyp_ihty_sb_eq t _ Id Id _ _ _ (fun z => eq_refl) (Esb φ b)).
        pose proof (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) as Hσw.
        pose proof (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ Hbt) as HOTb.
        unfold OTi in HOTb; rewrite (ih_cod_inst _ _ _ _ _ _ Mj HMj HPl) in HOTb; cbn [sentry_exp] in HOTb.
        rewrite (ptyp_ihty_sb_eq t _ Id Id _ _ _ (fun z => eq_refl) (Esb φ b)) in HOTb.
        replace (env_args nil (ups ++ ns ++ nv ++ ys) ↦ cc) with (env_args nil (ups ++ ns ++ nv ++ ys ++ cc :: nil)) in Esh', Ea2i
          by (replace (ups ++ ns ++ nv ++ ys ++ cc :: nil) with ((ups ++ ns ++ nv ++ ys) ++ cc :: nil)
                by (rewrite <- !List.app_assoc; reflexivity); rewrite env_args_snoc; reflexivity).
        rewrite <- !List.app_assoc in Hsh'.
        eapply (IH (S d) (ys ++ cc :: nil) Δ (sb_wk σ' φ) oq' (sb_wk τ φ) (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil) SbC'
                  (a_app N[φ]ʷ b) _ _ rc a2 i (out_rel cc cc equiv_c) (OP cc equiv_c) (OEl cc equiv_c));
          [ reflexivity | lia | | exact Hoq | exact Hσw | rewrite List.length_app, List.length_map; cbn; lia | exact HSbC' | exact Hσs'
          | exact Esh' | exact Hn' | exact Hsh' | exact Erc0 | exact Ea2i | exact Ha22 | exact Hrc | exact Hui | exact HiA
          | exact (Hcodg _ equiv_c _ Ea2) | exact HOTb ].
        apply tele_prefix_rel_snoc; [ exact Hy |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hdc. }
      (** The body's type, at the generic variable. *)
      assert (HITid : Δ' ⊢ IT ® IP) by (pose proof (HIT' Δ' wk_id (kripke_id _ HΔ')) as Hx0; rewrite exp_wk_id in Hx0; exact Hx0).
      assert (HΔIT : ⊢ Δ' ▹ IT) by mauto 3.
      pose proof (var0_glu_elem Hgb1 HITid) as Hvar.
      pose proof (var_per_elem (length Δ') equiv_a_a') as Heqv.
      destruct (Happ _ _ _ _ Heqv (kripke_shift _ _ HΔIT) Hvar) as (rc0 & a0 & _ & Ea0 & Hg0).
      pose proof (glu_univ_elem_trm_escape _ _ _ _ (Hcodg _ Heqv _ Ea0) _ _ _ _ Hg0) as Hbodyt.
      assert (Ebv : body[(ι ↑),,#0] = body).
      { transitivity (body[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
        unfold body, Us'; rewrite !ih_body_inst; cbn [sentry_exp].
        apply ptyp_ih_exp_agree; [ exact Hmd | apply sb_exp_agree_var0 ]. }
      assert (Eov : OTi[(ι ↑),,#0] = OTi).
      { transitivity (OTi[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
        unfold OTi; rewrite !(ih_cod_inst σ' σs N t ↑ _ Mj HMj HPl); cbn [sentry_exp].
        apply ptyp_ihty_agree_exp; [ exact Hmd | exact Hmp | reflexivity | apply sb_exp_agree_var0 ]. }
      rewrite Ebv, Eov in Hbodyt.
      apply HEleq; eapply mk_pi_glu_exp_pred with (IT := IT) (OT := OTi);
        [ apply wf_fn with (i := i); [ exact HITt | exact Hbodyt ]
        | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRsave Hper); exact Hr
        | apply wf_exp_eq_refl; exact HIT | exact HITt | exact HOTt | exact HIT' |].
      intros Δ φ N0 n0 Hφ HN0 equiv_n.
      destruct (Happ _ _ _ _ equiv_n Hφ HN0) as (rc & a2 & Erc & Ea2 & Hgl).
      exists rc; split; [ exact Erc |].
      pose proof (Hcodg _ equiv_n _ Ea2) as Hga2.
      eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hga2 | exact Hgl |].
      apply wf_exp_eq_sym; eapply fn_wk_beta; [ exact HITt | exact HOTt | exact Hbodyt | exact Hφ
                                            | exact (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ HN0) ].
  Qed.

  (** Fresh variables of the non-uniform parameters of the member [v],
      variables of a context at their types, are glued at the gluings of
      the parameters' types ([NEl]). *)
  Lemma glu_fresh_nparams : forall v Mv Δx Usx j0 s ns, ind_member D v = Some Mv -> ⊢ Δx ->
      glu_args Δx (ind_uparams D) Id nil Usx ups -> (s + j0 + im_nn Mv = length Δx)%nat ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      (forall j N T, List.nth_error (vars_from j0 (im_nn Mv)) j = Some N ->
         List.nth_error (tele_insts (im_nparams Mv) (sb_of_list Id Usx) (vars_from j0 (im_nn Mv))) j = Some T -> Δx ⊢ N : T) ->
      glu_nparams v Mv NEl Δx Usx (vars_from j0 (im_nn Mv)) ns.
  Proof.
    intros v Mv Δx Usx j0 s ns HMv HΔx HUsx Hlen Fn Hns HNt.
    pose proof (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl ups_len Hbu Hule Hf Δx Usx HΔx HUsx)
      as [HCN _ _].
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    constructor; [ apply length_vars_from | exact Ln |].
    enough (H : forall n, n <= im_nn Mv -> forall j N T w, j < n -> List.nth_error (vars_from j0 (im_nn Mv)) j = Some N ->
              List.nth_error (tele_insts (im_nparams Mv) (sb_of_list Id Usx) (vars_from j0 (im_nn Mv))) j = Some T ->
              List.nth_error ns j = Some w -> Δx ⊢ N : T ® w ∈ NEl v j (List.firstn j ns)).
    { intros j N T w HN HT Hw.
      assert (Hj : j < im_nn Mv) by (rewrite <- Ln; apply List.nth_error_Some; congruence).
      exact (H (im_nn Mv) (le_n _) _ _ _ _ Hj HN HT Hw). }
    induction n as [| n IH]; intros Hn j N T w Hj HN HT Hw; [ lia |].
    destruct (Nat.eq_dec j n) as [-> | Hne]; [| eapply IH; eauto; lia ].
    assert (Hk' : n < List.length (List.rev (im_nparams Mv))) by (rewrite List.length_rev, length_im_nparams; lia).
    destruct (nparams_lt_ass D v Mv n Hass HMv Hk') as [A HA].
    destruct (fresh_tele_nth _ _ _ _ Fn n A HA) as (b & Eb & Hb).
    rewrite Hw in Hb; injection Hb as ->.
    assert (Hpm : tele_prefix_rel (nr v) n (List.firstn n ns) (List.firstn n ns))
      by (eapply tele_prefix_rel_of_full; [ exact Hns | rewrite List.length_rev, length_im_nparams; lia ]).
    rewrite <- env_args_app in Eb.
    pose proof (ifg_npar_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ HMv HA Hpm Eb) as Hgu.
    assert (HTP : Δx ⊢ T ® NP v n (List.firstn n ns)).
    { eapply (HCN v Mv n _ (List.firstn n ns) T HMv); [ rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
      intros j' N' T' w' Hj' HN' HT' Hw'.
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hw'; destruct (Nat.ltb_spec j' n); [| discriminate ].
      eapply IH; eauto; lia. }
    pose proof (HNt n N T HN HT) as HNtn.
    apply vars_from_nth_error in HN as [Hnn ->].
    pose proof (var_glu_elem_at u b _ _ Δx T _ Hgu HTP HNtn ltac:(lia)) as Hv.
    replace (List.length Δx - 1 - (j0 + (im_nn Mv - 1 - n))) with (s + n) in Hv by lia.
    exact Hv.
  Qed.

  (** Fresh variables of the non-recursive arguments of a constructor, at
      their types, are glued at the gluings of the arguments' types
      ([AEl]). *)
  Lemma glu_fresh_args : forall v Mv c gs Δx Usx Ns j1 s ns vs, ind_member D v = Some Mv -> ind_con Mv c = Some gs -> ⊢ Δx ->
      glu_args Δx (ind_uparams D) Id nil Usx ups -> (s + im_nn Mv + j1 + List.length gs = length Δx)%nat ->
      glu_nparams v Mv NEl Δx Usx Ns ns -> tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mv) ↘ vs ->
      tele_rel (ar v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs) ->
      (forall j N T, List.nth_error (vars_from j1 (List.length gs)) j = Some N ->
         List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Usx ++ Ns)) (vars_from j1 (List.length gs))) j = Some T ->
         Δx ⊢ N : T) ->
      forall hs1 B hs2 N T w, gs = hs1 ++ ca_arg B :: hs2 -> List.nth_error (vars_from j1 (List.length gs)) (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Usx ++ Ns)) (vars_from j1 (List.length gs))) (List.length hs1) = Some T ->
        List.nth_error vs (List.length hs1) = Some w ->
        Δx ⊢ N : T ® w ∈ AEl v ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)).
  Proof.
    intros v Mv c gs Δx Usx Ns j1 s ns vs HMv Hcon HΔx HUsx Hlen Hgn Hns Fc Hav HAt.
    pose proof (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl ups_len Hbu Hule Hf Δx Usx HΔx HUsx)
      as [_ HCA _].
    pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
    enough (H : forall n hs1 B hs2 N T w, List.length hs1 < n -> gs = hs1 ++ ca_arg B :: hs2 ->
              List.nth_error (vars_from j1 (List.length gs)) (List.length hs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Usx ++ Ns)) (vars_from j1 (List.length gs))) (List.length hs1) = Some T ->
              List.nth_error vs (List.length hs1) = Some w ->
              Δx ⊢ N : T ® w ∈ AEl v ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
    { intros hs1 B hs2 N T w Heq HN HT Hw; exact (H (S (List.length hs1)) hs1 B hs2 N T w ltac:(lia) Heq HN HT Hw). }
    induction n as [| n IH]; intros hs1 B hs2 N T w Hn Heq HN HT Hw; [ lia |].
    assert (Hlt : List.length hs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
    pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hav Lv Heq) as Hpre.
    assert (HTP : Δx ⊢ T ® AP v ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
    { eapply (HCA v Mv c gs hs1 B hs2 Ns ns (vars_from j1 (List.length gs)) (List.firstn (List.length hs1) vs) T HMv Hcon Heq Hgn Hns);
        [ rewrite List.length_firstn; lia | exact HT | | exact Hpre ].
      intros hs1' B' hs2' N' T' w' Heq1 HN' HT' Hw'.
      subst hs1.
      rewrite List.nth_error_firstn in Hw'; destruct (Nat.ltb_spec (List.length hs1') (List.length (hs1' ++ ca_arg B' :: hs2'))); [| discriminate ].
      rewrite List.firstn_firstn, Nat.min_l by lia.
      eapply (IH hs1' B' (hs2' ++ ca_arg B :: hs2)); [ rewrite List.length_app in Hn; cbn in Hn; lia
                                                   | rewrite Heq, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hw' ]. }
    destruct (fresh_cargs_nth _ _ _ _ _ _ Fc hs1 (ca_arg B) hs2 Heq) as [Fa _].
    destruct (Fa B eq_refl) as (a' & Ea' & Hv).
    rewrite Hw in Hv; injection Hv as ->.
    rewrite <- !env_args_app, <- List.app_assoc in Ea'.
    assert (HnB : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec hs1)) = Some B)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    pose proof (ifg_arg_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ HMv Hns Hcon HnB Hpre Ea') as Hgu.
    pose proof (HAt _ _ _ HN HT) as HNt.
    apply vars_from_nth_error in HN as [Hnn ->].
    pose proof (var_glu_elem_at u a' _ _ Δx T _ Hgu HTP HNt ltac:(lia)) as Hvv.
    replace (List.length Δx - 1 - (j1 + (List.length gs - 1 - List.length hs1))) with (s + im_nn Mv + List.length hs1) in Hvv by lia.
    exact Hvv.
  Qed.

  (** ** On a Neutral

      A neutral of the member [j], glued in the group, at a substitution
      [σ'] glued to [ρ]: the eliminator is stuck, at the motive's value at
      the scrutinee; it is glued there when its readback is the
      elimination's ([nc_out]), which the readback of its blocks under
      fresh variables gives. *)
  Section NeutCase.
    Variables (j : nat) (Mj : imember) (hd : qname) (k' : nat) (as' : list domain) (e : domain_ne)
      (Δ' : ctx) (Us' Ns' : list exp) (M' : exp).
    Hypotheses (HMj : ind_member D j = Some Mj) (Href : im_ref p j Mj = (hd, k')) (He : Dom e ≈ e ∈ per_bot)
      (Hrb : forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (im_ty_at p j Mj Us' Ns')[φ]ʷ).
    Variables (σ' : sub) (oq' : option qname) (ns : list domain).
    Hypotheses (Hgrp : elim_grp D oq' p j) (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HUs' : Us' = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : im_ty_at p j Mj Us' Ns') (Hgn : glu_nparams j Mj NEl Δ' Us' Ns' ns)
      (Hns : tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns)
      (HGm : G j ups ups ns ns (⇑ (d_ind hd k' as') e) (⇑ (d_ind hd k' as') e)).

    Lemma nc_inv : List.length as' = (im_unu D Mj + im_nn Mj)%nat /\
        tele_rel (nr j) (List.rev (im_nparams Mj)) ns (List.skipn (im_unu D Mj) as').
    Proof.
      unfold grp_rel in HGm; inversion HGm; subst.
      match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end.
      split; assumption.
    Qed.

    Lemma nc_Ps_typed : forall i P T, List.nth_error (Us' ++ Ns') i = Some P ->
        List.nth_error (tele_insts (im_params D Mj) Id (Us' ++ Ns')) i = Some T -> Δ' ⊢ P : T.
    Proof.
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (HUl' : List.length Us' = ind_nu D) by (rewrite HUs', List.length_map; exact HUl).
      pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf j Mj Δ' Us' Ns' ns HMj Hgn Hns) as HgN.
      assert (Hga : glu_args Δ' (im_params D Mj) Id nil (Us' ++ Ns') (ups ++ ns)).
      { unfold im_params; apply glu_args_app; [ exact Ua | exact HUl' | exact ups_len |].
        split; [ exact HUg' | exact HgN ]. }
      exact (glu_args_typed _ _ _ _ _ _ (member_params_ass D Hc _ _ HMj) Hga).
    Qed.

    (** The neutral case, given the readback of the stuck eliminator: its
        value is the stuck eliminator at the motive's value at the stored
        parameters, related to the motive's at [ns]. *)
    Lemma nc_out :
        (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
           Δ ⊢ (a_elim oq' (List.map (fun U => U[σ']) Us) j (blocks_sub Bks σ') M')[φ]ʷ ≈ M0
             : ((List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)])[φ]ʷ) ->
        elim_out j Mj Δ' σ' oq' Ns' M' (⇑ (d_ind hd k' as') e) ns.
    Proof.
      intros Hrbe.
      destruct nc_inv as [La Hsn].
      destruct (ER im_ref_target j Mj hd k' HMj Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
      destruct (HBks _ _ HMj) as [b Hb].
      pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ j Mj _ _ _ _ _ _ _ _ HMj HGm Hsn Hns) as HG2.
      destruct (mot_rel j Mj b b ups ups _ ns _ _ HMj Hb Hb HG2) as (a1 & a2 & Ea1 & Ea2 & Hr12).
      assert (Ee : ⟦elim ⇑ (d_ind hd k' as') e at j of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ⇑ a1 (d_elim ρ Bks p ups j as' e)).
      { eapply eval_elim_neut; [ exact Hl | exact HMj | exact Href | exact Hq | exact HMq | unfold im_np; lia | exact Hb
                               | rewrite (Hnm _ _ _ HMj Hb), Hnnq; reflexivity | rewrite Hnuq; exact Ea1 ]. }
      (** The motive at the scrutinee, glued in the group ([AtType]). *)
      destruct (Completeness.Inductives.ViewReadback.mref_exists VP HVP p D HPD ups ups_gargs ups_len j Mj HMj) as [[[hd0 k0] pre] Er].
      destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D j Mj ups hd0 k0 pre Hl HMj ups_len Er) as [Href0 Lpre].
      rewrite Href in Href0; injection Href0 as E1 E2; subst hd0 k0.
      assert (HIG : ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' Ns' M' (⇑ (d_ind hd k' as') e))
        by (eapply ind_glu_elem_neut; eassumption).
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf
                  nb Hnbu Hnbq) as [Hel _].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (Hgl : forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
                Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
                Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® ⇑ (d_ind hd k' as') e ∈ El).
      { intros i P El _ Hglu HT; rewrite <- HUs' in HT |- *.
        exact (Hel _ _ _ _ _ _ HIG Mj ns hd k' pre i P El HMj Er HUg' HMt Hgn Hns HGm Hglu HT). }
      pose proof Hgn as Hgn'; rewrite HUs' in Hgn'.
      destruct (motive_glu j Mj Δ' σ' Ns' ns M' _ hd k' pre HMj Hσ' Hgn' Hns Er Hgl) as (a0 & Ea0 & Hpa0 & HPa0).
      pose proof Ea0 as Ea0'; rewrite (blocks_motives_nth _ _ _ Hb) in Ea0'.
      assert (a0 = a2) as -> by (eapply functional_eval_exp; eassumption).
      exists (⇑ a1 (d_elim ρ Bks p ups j as' e)) a2; [ exact Ee | exact Ea0 | exact Hpa0 |].
      intros P El Hg.
      pose proof (HPa0 P El Hg) as HTP.
      assert (Haa : Dom a2 ≈ a1 ∈ per_univ iA) by (apply per_univ_sym'; eexists; exact Hr12).
      pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ Haa Hg) as Hg1.
      (** The elimination, typed. *)
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      pose proof (gnp_len _ _ _ _ _ _ _ Hgn) as HNl'.
      assert (HUl' : List.length Us' = ind_nu D) by (rewrite HUs', List.length_map; exact HUl).
      assert (HBt2 : blocks_typed gc_deps gc_stack Δ' p D (List.firstn (ind_nu D) (Us' ++ Ns')) (blocks_sub Bks σ') iA)
        by (rewrite firstn_app_exact by exact HUl'; exact HBt').
      assert (HPl : List.length (Us' ++ Ns') = im_np D Mj) by (rewrite List.length_app, HUl', HNl'; unfold im_np; lia).
      assert (Hbk' : List.nth_error (blocks_sub Bks σ') j = Some (eblock_sub b σ')) by (rewrite nth_error_blocks_sub, Hb; reflexivity).
      assert (Emt : ind_mty p D j Us' Ns' = im_ty_at p j Mj Us' Ns') by (unfold ind_mty; rewrite HMj; reflexivity).
      assert (HMM : Δ' ⊢ M' ≈ M' : ind_mty p D j (List.firstn (ind_nu D) (Us' ++ Ns')) (List.skipn (ind_nu D) (Us' ++ Ns')))
        by (rewrite firstn_app_exact, skipn_app_exact, Emt by exact HUl'; apply wf_exp_eq_refl; exact HMt).
      pose proof (wf_elim_scrut_eq Δ' p D oq' j Mj (eblock_sub b σ') (blocks_sub Bks σ') (Us' ++ Ns') M' M' iA Hl Hgrp HMj Hbk' HPl
                    nc_Ps_typed HBt2 HMM) as E2.
      rewrite firstn_app_exact, skipn_app_exact in E2 by exact HUl'.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMj Hb) in E2.
      destruct (presup_exp_eq E2) as (_ & Hty & _).
      rewrite (blocks_motives_nth _ _ _ Hb) in HTP, Hrbe |- *.
      rewrite <- HUs' in Hrbe |- *.
      eapply realize_glu_elem_bot; [ exact Hg1 |].
      econstructor; [ exact Hty | exact Hg1 | exact HTP | |].
      - exact (ER per_bot_elim j Mj hd k' as' as' e e ups ups ns ns HMj HGm).
      - exact Hrbe.
    Qed.
  End NeutCase.

End ElimGlu.

End Fixed_GCtx.
