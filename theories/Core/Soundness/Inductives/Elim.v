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
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCount IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
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
    RΓ0 E E -> ⟦ τ : Δ0 ⟧s E ↘ Eτ -> ⟦ A[τ] ⟧ E ↘ a -> ⟦ A ⟧ Eτ ↘ b -> Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HA HΓ0 Hτ HE Hev Ea Eb.
  destruct (rel_exp_of_typ_inversion HA) as (R & HR & Hgen).
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev) as [a1 b1 c1 d1 Ea1 Eb1 Ec1 Ed1 Hch].
  assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (c1 = b) as -> by (eapply functional_eval_exp; eassumption).
  pairwise.
Qed.

(** A substitution read back from a list of terms: the type of a
    relevant entry, at the terms before it, is of a large universe. *)
Lemma wf_sub_of_list_relevant_entry : forall Γ0 Δ0 Γ1 σ Ms,
    List.length Ms = List.length Δ0 ->
    Γ0 ⊢ˢ sb_of_list σ Ms : Δ0 ++ Γ1 ->
    forall k A, List.nth_error (List.rev Δ0) k = Some (ce_ass ak_relevant A) ->
    exists i, Γ0 ⊢ A[sb_of_list σ (List.firstn k Ms)] : Typeω@i.
Proof.
  intros * Hl Hσ k A HA.
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ0 = List.rev l2 ++ ce_ass ak_relevant A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ0), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ0 = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HC : ⊢ Δ0 ++ Γ1) by (gen_presups; assumption).
  rewrite HΔeq, <- List.app_assoc in HC; cbn [List.app] in HC.
  pose proof HC as HCw.
  apply ctx_app_wf_tail in HC.
  destruct (ctx_decomp_kind HC) as (Srt & HS & HAt).
  inversion HS; subst Srt.
  (** The entry's type, past its own entry and those after it. *)
  assert (Hw : (List.rev l2 ++ ce_ass ak_relevant A :: nil) ++ List.rev l1 ++ Γ1
               ⊢ʷ wk_shiftn (List.length (List.rev l2 ++ ce_ass ak_relevant A :: nil)) : List.rev l1 ++ Γ1)
    by (apply wf_wk_shiftn_app; [ rewrite <- List.app_assoc; exact HCw | exact (proj1 (ctx_decomp HC)) ]).
  assert (Hσ' : Γ0 ⊢ˢ sb_of_list σ Ms : (List.rev l2 ++ ce_ass ak_relevant A :: nil) ++ List.rev l1 ++ Γ1)
    by (rewrite <- List.app_assoc; rewrite HΔeq, <- List.app_assoc in Hσ; exact Hσ).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HAt (wf_sub_compose _ _ _ _ _ _ _ (wf_sub_of_wk _ _ _ _ _ Hw) Hσ')) as H.
  exists i.
  replace (A[sb_of_list σ (List.firstn k Ms)]) with (A[ι (wk_shiftn (List.length (List.rev l2 ++ ce_ass ak_relevant A :: nil))) ⨟ sb_of_list σ Ms]);
    [ exact H |].
  apply exp_sub_sb_eq; intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite <- (List.firstn_skipn k Ms) at 1; rewrite sb_of_list_app.
  replace (x + List.length (List.rev l2 ++ ce_ass ak_relevant A :: nil)) with (List.length (List.skipn k Ms) + x)
    by (rewrite List.length_skipn, List.length_app, List.length_rev; cbn [List.length]; lia).
  rewrite sb_of_list_ge; reflexivity.
Qed.

(** The eliminator at typed blocks, at equal scrutinees
    ([wf_exp_eq_elim_cong] with the same parameters and blocks). *)
Lemma wf_elim_scrut_eq : forall Γ p D m Mm bm Bks Ps M M' r (i : nat),
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks r i ->
    Γ ⊢ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Γ ⊢ a_elim r p (List.firstn (ind_nu D) Ps) m Bks M ≈ a_elim r p (List.firstn (ind_nu D) Ps) m Bks M'
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl HMm Hbm HPl HPs HBt HMM.
  destruct HBt as [HlB Hnm HZ HA HΨ Hn HΨB Hk HB Hr].
  eapply wf_exp_eq_elim_cong with (Bks' := Bks) (Ps' := Ps);
    first [ exact Hl | exact HMm | exact Hbm | exact HlB | exact HPl | exact HPs | exact HMM
          | reflexivity | exact Hnm | exact HZ | exact HA | exact HΨ | exact Hn | exact HΨB | exact Hk | exact Hr | idtac ].
  - intros k P P' T HP HP' HT; rewrite HP in HP'; injection HP' as <-; apply wf_exp_eq_refl; exact (HPs _ _ _ HP HT).
  - intros k Mk b b' HMk Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; apply wf_exp_eq_refl; exact (HA _ _ _ HMk Hb).
  - intros k b b' Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; reflexivity.
  - intros k Mk b b' i0 c gs n B B' HMk Hb Hb' HB0 HB' Hcon; rewrite Hb in Hb'; injection Hb' as <-.
    rewrite HB0 in HB'; injection HB' as <-; apply wf_exp_eq_refl.
    exact (HB _ _ _ _ _ _ _ HMk Hb Hcon (List.nth_error_In _ _ HB0)).
Qed.

(** [ι] at typed blocks ([wf_exp_eq_elim_iota] with the blocks' typing
    premises read off [blocks_typed]). *)
Lemma wf_elim_iota_blocks_typed : forall Γ p D m Mm bm Bks c gs Ps As r (i : nat) n B,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm -> ind_con Mm c = Some gs -> List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
       Γ ⊢ N : T) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks r i ->
    brs_lookup (eb_brs bm) c = Some (n, B) ->
    Γ ⊢ a_elim r p (List.firstn (ind_nu D) Ps) m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                    (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As))
       ≈ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++
                          elim_ihs r p D (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) (im_nn Mm) gs As)]
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                          apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                            (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)].
Proof.
  intros * HΓ Hl HMm Hbm Hcon HPl HPs HAl HAs HBt HlB.
  destruct HBt as [HlBk Hnm HZ HA HΨ Hn HΨB Hk HB Hr].
  eapply wf_exp_eq_elim_iota;
    first [ exact HΓ | exact Hl | exact HMm | exact Hbm | exact Hcon | exact HlBk | exact HPl
          | exact HPs | exact HAl | exact HAs | reflexivity | exact Hnm | exact HZ | exact HA | exact HΨ | exact Hn
          | exact HΨB | exact Hk | exact HB | exact HlB | exact Hr ].
Qed.

(** The type of a view's branch, instantiated in the container's branch's
    context ([wrap_branch]), is the container's branch type: the view's
    constructor applied is the container's ([Views.view_blocks_branch_con_conv]), the same
    one at a declared member of the container. *)
Lemma view_branch_type_conv : forall Γ0 p D m Mm qc k' Is vm D' Us0 Bks0 (r : abs_kind) (i : nat),
    ⊢ᵍ gc_deps ⍮ gc_stack -> decls_typed gc_deps gc_stack -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some D' -> view_wrap_ok D D' vm -> ⊢ Γ0 ->
    List.length Us0 = ind_nu D ->
    (forall k U T, List.nth_error Us0 k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us0) k = Some T -> Γ0 ⊢ U : T) ->
    blocks_typed gc_deps gc_stack Γ0 p D Us0 Bks0 r i ->
    forall i' Mi' v Mv c gs' gs b W, ind_member D' i' = Some Mi' -> im_is_rview Mi' = false -> List.nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> cargs_correspond vm gs' gs ->
      List.nth_error Bks0 v = Some b -> List.length W = cargs_nrec D gs ->
      elim_bctx r qc D' Mi' gs' (blocks_motives (view_wrap r p qc D D' vm Us0 (List.map (fun I => I[sb_of_list Id Us0]) Is) Bks0))
        (List.map (fun I => I[sb_of_list Id Us0]) Is) ++ Γ0
        ⊢ (elim_branch_type p D v Mv c gs (eb_motive b) Us0)[sb_of_list (ι (wk_shiftn (im_nn Mv + List.length gs' + cargs_nrec D' gs')))
             (vars_from (cargs_nrec D' gs' + List.length gs') (im_nn Mv) ++ vars_from (cargs_nrec D' gs') (List.length gs') ++ W)]
        ≈ elim_branch_type qc D' i' Mi' c gs' (eb_motive b) (List.map (fun I => I[sb_of_list Id Us0]) Is) : abs_kind_sort r Typeω@i.
Proof.
  intros * Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt * Hi' Hri' Hv Hmv Hcon' Hcon Hcorr Hb HW.
  assert (HS : type_sort (abs_kind_sort r Typeω@i)) by (apply type_sort_abs_kind; constructor).
  pose proof (view_blocks_branch_type_view _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' HΓ HUl HUs v Mv c gs' gs Hmv Hcorr (eb_motive b) W HW) as E1.
  cbn beta in E1; rewrite E1; clear E1.
  rewrite (view_blocks_branch_type_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDs Hl Hm Hh Hl' Hvw HBt i' Mi' v Mv c gs' Hi' Hri' Hv Hmv).
  destruct (view_blocks_facts _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' HΓ HUl HUs) as (HD & Hc & HD' & Hc' & HIl & HIs).
  set (Is' := List.map (fun I => I[sb_of_list Id Us0]) Is) in *.
  pose proof (view_blocks_motives_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt _ _ Hi' Hri') as HA.
  rewrite (view_wrap_motive_nth _ _ _ _ _ _ _ _ _ _ _ _ _ (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD')) Hi' Hri' Hv Hb
             ltac:(eauto)) in HA.
  assert (HM : forall j Mj, ind_member D' j = Some Mj -> ⊢ elim_mctx qc D' j Mj Is' ++ Γ0)
    by (intros j Mj Hj; exact (elim_mctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl' Hj HΓ HIl HIs)).
  pose proof (wf_branch_type_sub _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl' Hi' Hri' HΓ HIl HIs HM
                (view_blocks_motives_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt)
                (blocks_typed_kind _ _ _ _ _ _ _ _ _ HBt) Hcon') as Hρc.
  rewrite (view_blocks_branch_nn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDs Hl Hm Hh Hl' Hvw HBt i' Mi' v Mv Hi' Hri' Hv Hmv) in Hρc.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA HS Hρc) as Hty; cbn [exp_sub] in Hty.
  set (n' := im_nn Mv + List.length gs' + cargs_nrec D' gs') in *.
  set (nvars := vars_from (cargs_nrec D' gs' + List.length gs') (im_nn Mv)) in *.
  set (avars := vars_from (cargs_nrec D' gs') (List.length gs')) in *.
  destruct (im_head Mi') as [pm | q'' k'' Is'' vm'' | q'' Is'' fl''] eqn:Hhi;
    [| | exfalso; unfold im_is_rview in Hri'; rewrite Hhi in Hri'; discriminate Hri' ].
  - (** A declared member of the container: the same constructor. *)
    destruct (decl_typed_view_decl _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hl' Hi' Hhi Hv) as (Mv0 & vm' & Hmv0 & Hhv).
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
    pose proof (view_blocks_branch_con_conv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt i' Mi' v Mv c gs' gs
                  Hi' Hri' Hv Hmv Hcon' Hcon Hcorr _ _ _ _ Hhi) as Hcv; cbv zeta in Hcv; destruct Hcv as [HcV Hcc].
    set (conV := apps_exp (a_con (fst (im_ref p v Mv)) (snd (im_ref p v Mv)) c)
                   (im_pre Mv (List.map (fun U => U[wk_shiftn n']ʷ) Us0) ++ nvars ++ avars)) in *.
    set (conC := apps_exp (a_con (fst (im_ref qc i' Mi')) (snd (im_ref qc i' Mi')) c)
                   (im_pre Mi' (List.map (fun U => U[wk_shiftn n']ʷ) Is') ++ nvars ++ avars)) in *.
    assert (HNl : List.length nvars = im_nn Mi')
      by (unfold nvars; rewrite length_vars_from, (view_blocks_branch_nn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDs Hl Hm Hh Hl' Hvw HBt i' Mi' v Mv Hi' Hri' Hv Hmv);
          reflexivity).
    assert (Hlen : forall x, List.length (nvars ++ x :: nil) = List.length (elim_mctx qc D' i' Mi' Is'))
      by (intros; rewrite List.length_app, length_elim_mctx, HNl; cbn; lia).
    pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_mctx_ass _ _ _ _ Is' Hc' Hi') (Hlen conC) Hρc) as HMs.
    pose proof (fun x => elim_mctx_insts qc D' i' Mi' Is' (ι wk_shiftn n') nvars x Hc' Hi' HIl HNl) as E.
    assert (Hl2 : List.length (tele_insts (im_nparams Mi') (sb_of_list Id Is' ⨟ ι wk_shiftn n') nvars) = im_nn Mi')
      by (rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption); rewrite HNl; unfold im_nn; lia).
    assert (Hσ : elim_bctx r qc D' Mi' gs' (blocks_motives (view_wrap r p qc D D' vm Us0 Is' Bks0)) Is' ++ Γ0
                   ⊢ˢ sb_of_list (ι wk_shiftn n') (nvars ++ conC :: nil) ≈ sb_of_list (ι wk_shiftn n') (nvars ++ conV :: nil)
                   : elim_mctx qc D' i' Mi' Is' ++ Γ0).
    { eapply wf_sub_eq_of_list_left;
        [ exact (elim_mctx_ass _ _ _ _ _ Hc' Hi') | exact (HM _ _ Hi')
        | apply wf_sub_eq_refl; exact (view_blocks_branch_wk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hm Hh Hl' Hvw HΓ HUl HUs HBt i' Mi' v Mv c gs'
                                         Hi' Hri' Hv Hmv Hcon')
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
    pose proof (sub_eq_preserves_sort _ _ _ _ _ _ _ _ HA HS Hσ) as Heq; cbn [exp_sub] in Heq.
    apply wf_exp_eq_sym; exact Heq.
Qed.

(** ** Weakenings and Substitutions of a View's Branch *)

(** Past a telescope [E], by [⇑^|E|]. *)
Lemma kripke_shiftn_app : forall E Δ, ⊢ E ++ Δ -> E ++ Δ ⊢ᵏ wk_shiftn (List.length E) : Δ.
Proof.
  assert (Hr : forall Γ0 Δ0 φ φ', wk_eq φ φ' -> Γ0 ⊢ᵏ φ : Δ0 -> Γ0 ⊢ᵏ φ' : Δ0).
  { intros * Ee Hk; destruct Hk.
    - eapply wk_kripke_id; [ eassumption | rewrite <- Ee; assumption ].
    - eapply wk_kripke_shift; [ eassumption | eassumption | rewrite <- Ee; assumption ]. }
  induction E as [| e E IH]; intros Δ H; cbn [List.app List.length] in *.
  - eapply wk_kripke_id; [ apply ctx_sub_refl; exact H | apply wk_shiftn_zero ].
  - pose proof (ctx_app_wf_tail _ _ (e :: nil) _ H) as H'; cbn [List.app] in H'.
    assert (Hs : e :: E ++ Δ ⊢ᵏ ↑ : E ++ Δ)
      by (eapply wk_kripke_shift; [ apply kripke_id; exact H | apply ctx_sub_refl; exact H' | symmetry; apply wk_compose_id_right ]).
    exact (Hr _ _ _ _ (wk_shiftn_succ _) (kripke_compose _ _ _ _ _ Hs (IH Δ H'))).
Qed.

(** The substitution of the non-recursive arguments before a position,
    after a list. *)
Lemma cargs_sub_of_list : forall gs σ L As, cargs_sub (sb_of_list σ L) gs As = sb_of_list σ (L ++ nonrec_exps gs As).
Proof.
  induction gs as [| [B | t] gs IH]; intros σ L [| N As]; cbn [cargs_sub nonrec_exps]; rewrite ?List.app_nil_r; try reflexivity.
  - assert (E : sb_of_list σ (L ++ N :: nil) = (sb_of_list σ L ,, N)) by (rewrite sb_of_list_app; reflexivity).
    rewrite <- E, IH, <- List.app_assoc; reflexivity.
  - apply IH.
Qed.

(** A substitution of a list of terms into a closed telescope is glued
    whatever it sends the variables past the telescope to. *)
Lemma glu_sub_closed_rebase : forall C Sb Δ τ τ' Ms ρ, all_assumptions C -> EG C ∈ glu_ctx_env ↘ Sb -> List.length Ms = List.length C ->
    Δ ⊢ˢ sb_of_list τ Ms ® ρ ∈ Sb -> Δ ⊢ˢ sb_of_list τ' Ms ® ρ ∈ Sb.
Proof.
  intros * Hass HC Hl Hσ.
  pose proof (glu_ctx_env_wf_ctx HC) as HwC.
  pose proof (glu_ctx_env_sub_escape HC _ _ _ Hσ) as Ht.
  assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
  rewrite <- (List.app_nil_r C) in Ht, HwC.
  pose proof (wf_sub_of_list_inv _ _ _ _ _ _ _ Hass Hl Ht) as HMs.
  assert (H0 : Δ ⊢ˢ τ ≈ τ' : ⋅)
    by (constructor; try (apply wf_sub_nil'; exact HΔ); intros * Hx; inversion Hx).
  pose proof (wf_sub_eq_of_list_left _ _ C Δ nil τ τ' Ms Ms Hass HwC H0 Hl Hl HMs HMs
                (fun k N N' T HN HN' HT => ltac:(rewrite HN in HN'; injection HN' as <-; exact (wf_exp_eq_refl (HMs _ _ _ HN HT))))) as E.
  rewrite List.app_nil_r in E.
  exact (glu_ctx_env_sub_resp_sub_eq HC Hσ E).
Qed.

Lemma nonrec_exps_firstn_len : forall gs As, nonrec_exps gs (List.firstn (List.length gs) As) = nonrec_exps gs As.
Proof. induction gs as [| [] gs IH]; intros [| A As]; cbn; rewrite ?IH; reflexivity. Qed.

(** A variable is glued at its type, of a value other than [LevelSort],
    to the fresh variable of its level at any type related to the type's
    value. *)
(** The type of a variable is glued at no gluing of [LevelSort], which is
    of no sort ([level_sort_untyped]). *)
Lemma glu_var_typ_not_level_sort : forall (i : universe_index) a P El Δ T x,
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ T ® P -> Δ ⊢ #x : T -> not_level_sort a.
Proof.
  intros * Hg HT Hx Ha; subst a.
  basic_invert_glu_univ_elem Hg; try discriminate.
  match goal with H : _ <∙> level_sort_glu_typ_pred |- _ => apply H in HT; destruct HT as [-> _] end.
  destruct (presup_exp_typ_not_level Hx ltac:(intro Hl0; inversion Hl0)) as (S & _ & HS).
  exact (level_sort_untyped HS).
Qed.

Lemma var_glu_elem_per : forall (i : universe_index) a b (n : nat) P El Δ T x, DG a ∈ glu_univ_elem i ↘ P ↘ El -> not_level_sort a ->
    Δ ⊢ T ® P -> Δ ⊢ #x : T -> x < List.length Δ -> Dom a ≈ b ∈ per_univ n -> Δ ⊢ #x : T ® ⇑! b (List.length Δ - 1 - x) ∈ El.
Proof.
  intros * Hg Hn HT Hx Hlt [R' HR'].
  pose proof (var_glu_elem_at _ _ _ _ _ _ _ Hg Hn HT Hx Hlt) as Hv.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [Ra HRa].
  eapply glu_univ_elem_trm_resp_per_elem; [ exact Hg | exact HRa | exact Hv |].
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR' HRa); exact (var_per_elem _ HR' Hn).
Qed.

(** The readback of the fresh variable of a variable's level, at every
    weakening, is the variable. *)
Lemma var_readback_wk : forall Δ T x, Δ ⊢ #x : T -> x < List.length Δ ->
    forall Δ' φ M', Δ' ⊢ᵏ φ : Δ -> Rne d_var (List.length Δ - 1 - x) in gc_deps ⍮ gc_stack ⍮ length Δ' ↘ M' ->
    Δ' ⊢ #x[φ]ʷ ≈ M' : T[φ]ʷ.
Proof.
  intros * Hx Hlt Δ' φ M' Hφ HR.
  inversion HR; subst.
  destruct (kripke_shiftn _ _ _ Hφ) as [Hle _].
  pose proof (wk_var_kripke _ _ _ x Hφ) as Hφx.
  change (#x[φ]ʷ) with (a_var (φ x)); rewrite Hφx.
  cbn [ne_to_exp].
  replace (List.length Δ' - (List.length Δ - 1 - x) - 1) with (x + (List.length Δ' - List.length Δ)) by lia.
  apply wf_exp_eq_refl.
  rewrite <- Hφx; change (a_var (φ x)) with (#x[φ]ʷ).
  exact (kripke_preserves_exp _ _ _ _ _ Hx Hφ).
Qed.

(** ** The Families of a Group, at its Sort

    The types of the telescopes of a valid group at uniform parameters
    [ups] are glued at the index of the sort at [ups], at the canonical
    gluings of their values: those [per_univ_glu_univ_elem] gives, read
    through the values the types evaluate to. *)
Lemma group_fams_glu : forall D, valid_ind_decl D -> decl_closed D -> ind_sort_univ (ind_sort D) ->
    forall ups bu, per_tele_args (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
    ⟦ ind_sort D ⟧ decl_env D ups ↘ bu ->
    exists NP NEl AP AEl DP DEl, ind_fams_glu D ups (Completeness.Inductives.Decl.univ_idx bu) NP NEl AP AEl DP DEl.
Proof.
  intros D HD Hc Hsu ups bu Hgd Hu Hbu.
  set (i := Completeness.Inductives.Decl.univ_idx bu).
  pose proof (Completeness.Inductives.Model.canon_hn D HD Hc Hsu ups bu Hu Hbu ups Hgd) as Hn.
  pose proof (Completeness.Inductives.Model.canon_ha D HD Hc Hsu ups bu Hu Hbu ups Hgd) as Ha.
  pose proof (Completeness.Inductives.Model.canon_hd D HD Hc Hsu ups bu Hu Hbu ups Hgd) as Hd.
  assert (Hcan : forall b P El (E : domain -> Prop), (forall b', E b' -> b' = b) -> E b -> glu_univ_elem i P El b ->
             glu_univ_elem i (fun Γ T => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> P' Γ T)
                             (fun Γ T M m => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> El' Γ T M m) b).
  { intros * HE Eb Hg.
    eapply simple_glu_univ_elem_morphism_iff; [ | | reflexivity | exact Hg ].
    - intros Γ T; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
      intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
      destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [HPP _]; apply HPP; exact HP.
    - intros Γ T M' m; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
      intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
      destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [_ HEE]; apply HEE; exact HP. }
  exists (fun m j vs Γ T => forall b P El,
              ⟦ nth_ctyp (List.rev (member_nparams D m)) j ⟧ components_env D ups (List.rev (member_nparams D m)) vs ↘ b ->
              glu_univ_elem i P El b -> P Γ T),
    (fun m j vs Γ T M m0 => forall b P El,
         ⟦ nth_ctyp (List.rev (member_nparams D m)) j ⟧ components_env D ups (List.rev (member_nparams D m)) vs ↘ b ->
         glu_univ_elem i P El b -> El Γ T M m0),
    (fun m ms c j vs Γ T => forall b P El,
         ⟦ nth_atyp D m c j ⟧ components_env D ups (List.rev (member_nparams D m) ++ member_con_tele D m c) (ms ++ vs) ↘ b ->
         glu_univ_elem i P El b -> P Γ T),
    (fun m ms c j vs Γ T M m0 => forall b P El,
         ⟦ nth_atyp D m c j ⟧ components_env D ups (List.rev (member_nparams D m) ++ member_con_tele D m c) (ms ++ vs) ↘ b ->
         glu_univ_elem i P El b -> El Γ T M m0),
    (fun (m : nat) pre Ts B Γ T => forall b P El, ⟦ B ⟧ components_env D ups Ts pre ↘ b -> glu_univ_elem i P El b -> P Γ T),
    (fun (m : nat) pre Ts B Γ T M m0 => forall b P El, ⟦ B ⟧ components_env D ups Ts pre ↘ b ->
                       glu_univ_elem i P El b -> El Γ T M m0).
  constructor.
  - intros m Mm j κ A vs HM HA Hp; destruct (Hn _ _ _ _ _ _ _ HM HA Hp) as (a & a' & Ea & _); eauto.
  - intros m Mm j κ A vs b HM HA Hp Eb.
    destruct (Hn _ _ _ _ _ _ _ HM HA Hp) as (a & a' & Ea & Ea' & Hpa & _).
    assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (Pb & Elb & Hgb).
    rewrite (nth_ctyp_eq _ _ _ _ _ _ HM HA), (member_nparams_eq _ _ _ HM).
    eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ].
  - intros m Mm ms c gs j A vs HM Hm Hcn HA Hp; destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm Hcn HA Hp) as (a & a' & Ea & _); eauto.
  - intros m Mm ms c gs j A vs b HM Hm Hcn HA Hp Eb.
    destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm Hcn HA Hp) as (a & a' & Ea & Ea' & Hpa & _).
    assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (Pb & Elb & Hgb).
    rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hcn HA), (member_nparams_eq _ _ _ HM), (member_con_tele_eq _ _ _ _ _ HM Hcn).
    eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ].
  - intros m Mm ms c gs gs1 t gs2 ws j B ys HM Hm Hcn Heq Hw HB Hy.
    destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hcn Heq Hw HB Hy) as (a & a' & Ea & _); eauto.
  - intros m Mm ms c gs gs1 t gs2 ws j B ys b HM Hm Hcn Heq Hw HB Hy Eb.
    destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hcn Heq Hw HB Hy) as (a & a' & Ea & Ea' & [Hpa _ _]).
    assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (Pb & Elb & Hgb).
    pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & _).
    pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Hlw & _).
    pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _).
    assert (Hj : j < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
    rewrite List.length_rev in Hlm.
    rewrite <- Hly, <- components_env_shape_prefix by lia.
    eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ].
Qed.

(** A branch at a position, looked up by its name, the names distinct. *)
Lemma brs_lookup_of_nth : forall (Bs : list (String.string * nat * exp)) idx c n B,
    List.NoDup (List.map (fun b => fst (fst b)) Bs) -> List.nth_error Bs idx = Some (c, n, B) -> brs_lookup Bs c = Some (n, B).
Proof.
  induction Bs as [| [[c' n'] B'] Bs IH]; intros [| idx] * Hnd H; cbn in H |- *; try discriminate.
  - injection H as <- <- <-; rewrite String.eqb_refl; reflexivity.
  - inversion Hnd as [| ? ? Hn Hnd']; subst.
    destruct (String.eqb_spec c c') as [-> | Hne]; [| exact (IH _ _ _ _ Hnd' H) ].
    exfalso; apply Hn; exact (List.in_map (fun b => fst (fst b)) _ (c', n, B) (List.nth_error_In _ _ H)).
Qed.

(** A branch of a block's readback, as [read_brs] reads it: the
    constructor, its kinds in the group read and in the branch's group,
    and the branch read back under the fresh variables at the motive's
    instance at the constructor. *)
#[warnings="-cannot-define-projection"]
Record read_branch_at (p : qname) (D Dc : ind_decl) (ups : list domain) (Bks : list eblock) (ρ : env) (s : nat)
    (Mi : imember) (r : (qname * nat * list domain)%type) (Mv : imember) (A : exp)
    (Bs : list (String.string * nat * exp)%type) (cs : list (String.string * list carg)%type) (idx : nat) (c : String.string)
    (n : nat) (B' : nf) : Prop :=
  mk_read_branch_at
  { (** The constructor's kinds in the group read *)
    rba_kinds_read : list carg
    (** Its kinds in the branch's group *)
  ; rba_kinds : list carg
    (** The branch's stored count *)
  ; rba_count : nat
    (** The branch *)
  ; rba_body : exp
    (** The fresh non-uniform parameters *)
  ; rba_ns : list domain
    (** The fresh arguments *)
  ; rba_vs : list domain
    (** The fresh recursive results *)
  ; rba_ihs : list domain
    (** The recursive results the branch is read under *)
  ; rba_wrapped_ihs : list domain
    (** The branch's value *)
  ; rba_val : domain
    (** The motive's value at the constructor *)
  ; rba_motive : domain
    (** The branch read back *)
  ; rba_nf : nf
    (** The branch at [idx] *)
  ; rba_branch : List.nth_error Bs idx = Some (c, rba_count, rba_body)
    (** The constructor at [idx] in the group read *)
  ; rba_con_read : List.nth_error cs idx = Some (c, rba_kinds_read)
    (** The constructor in the branch's group *)
  ; rba_con : ind_con Mv c = Some rba_kinds
    (** The stored count *)
  ; rba_count_eq : rba_count = (im_nn Mi + List.length rba_kinds_read + cargs_nrec D rba_kinds)%nat
    (** The count read back *)
  ; rba_count_read : n = (im_nn Mi + List.length rba_kinds_read + cargs_nrec Dc rba_kinds_read)%nat
    (** The recursive arguments' parameter counts *)
  ; rba_params_length : cargs_params_length D rba_kinds
    (** The leaf paths of the group's that are the group read's, one per
        recursive result the branch read binds *)
  ; rba_container_count : cargs_container_count D Dc rba_kinds_read rba_kinds = cargs_nrec Dc rba_kinds_read
    (** The fresh non-uniform parameters *)
  ; rba_Fn : Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ rba_ns
    (** The fresh arguments *)
  ; rba_Fc : Fcargs rba_kinds of p ups in gc_deps ⍮ gc_stack ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) rba_ns
      ⍮ (s + im_nn Mi) ↘ rba_vs
    (** The fresh recursive results *)
  ; rba_Fi : Fihs rba_vs at rba_kinds_read rba_kinds of Dc under ρ (blocks_motives Bks) at p ups in gc_deps ⍮ gc_stack
      ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) rba_ns ⍮ (s + im_nn Mi + List.length rba_kinds_read) ↘ rba_ihs
    (** The recursive results the branch is read under *)
  ; rba_Wi : ⟦wihs rba_vs of rba_kinds_read rba_kinds of Dc with rba_ihs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rba_wrapped_ihs
    (** The branch's value *)
  ; rba_Eb : ⟦ rba_body ⟧ env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ rba_kinds rba_ns rba_vs rba_wrapped_ihs)
      ↘ rba_val
    (** The motive's value at the constructor *)
  ; rba_Et : ⟦ A ⟧ env_extend_typed ρ (motive_entries D Mv ups rba_ns (d_ind (fst (fst r)) (snd (fst r)) (snd r ++ rba_ns))
                                        (d_con (fst (fst r)) (snd (fst r)) c (snd r ++ rba_ns ++ rba_vs))) ↘ rba_motive
    (** The branch read back *)
  ; rba_Rn : Rnf ⇓ rba_motive rba_val in gc_deps ⍮ gc_stack ⍮ (s + n) ↘ rba_nf
    (** It is the branch the readback has *)
  ; rba_exp : B' = rba_nf }.

(** The branches of a block's readback, one by one. *)
Lemma read_brs_nth : forall p D Dc ups Bks ρ s Mi r Mv A cs Bs Bs', ind_lookup gc_deps gc_stack p = Some D ->
    Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Bs' ->
    List.length Bs' = List.length cs /\ List.length Bs = List.length cs /\
    forall idx br, List.nth_error Bs' idx = Some br ->
      read_branch_at p D Dc ups Bks ρ s Mi r Mv A Bs cs idx (branch_constructor br) (branch_arity br) (branch_body br).
Proof.
  intros * Hl HR; induction HR.
  - split; [ reflexivity | split; [ reflexivity | intros [] *; discriminate ] ].
  - destruct (IHHR Hl) as (L1 & L2 & IH').
    match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end.
    split; [ cbn; f_equal; exact L1 | split; [ cbn; f_equal; exact L2 |] ].
    intros [| idx] br Hn; cbn in Hn.
    + injection Hn as <-; cbn [branch_constructor branch_arity branch_body].
      econstructor; first [ reflexivity | eassumption ].
    + destruct (IH' idx br Hn) as [x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 HB Hcs Hc0 En0 En1 Hpl0 Hcc0 Fn0 Fc0 Fi0 Wi0 Eb0 Et0 Rn0 EB0].
      econstructor; [ exact HB | exact Hcs | exact Hc0 | exact En0 | exact En1 | exact Hpl0 | exact Hcc0 | exact Fn0 | exact Fc0 | exact Fi0
                    | exact Wi0 | exact Eb0 | exact Et0 | exact Rn0 | exact EB0 ].
Qed.

(** The recursive results along paths all flagged as fresh variables' are
    the fresh variables. *)
Lemma wrap_leaf_vals_all : forall {X : Type} (ls : list X) rs ihs ihs' out,
    wrap_leaf_vals (List.map (fun _ => true) ls) rs ihs ihs' out -> ihs = out ++ ihs'.
Proof.
  intros X; induction ls as [| x ls IH]; intros * H; cbn in H; inversion H; subst; [ reflexivity |].
  cbn; f_equal; eauto.
Qed.

(** The members a shape's leaf paths end in do not depend on the binders
    its components are over. *)
Lemma shape_leaves_mem_offset : forall tbl t m m', List.map leaf_mem (shape_leaves tbl m t) = List.map leaf_mem (shape_leaves tbl m' t).
Proof.
  intros tbl; induction t as [j Ps | B t IH]; intros m m'; cbn [shape_leaves].
  - destruct (tbl j) as [ls |]; [| reflexivity ].
    rewrite !List.map_map; apply List.map_ext; intros l; rewrite !leaf_mem_wk; reflexivity.
  - rewrite !List.map_map; exact (IH (S m) (S m')).
Qed.

(** The recursive results along the leaf paths [ls] of an argument
    recursive in both, at the path [idx]: the container's next variable
    at a path of the container's, the group's result at one nested
    through. *)
Lemma wrap_leaves_nth : forall D' t' ls ihs r' nr' idx l, List.length ihs = List.length ls -> List.nth_error ls idx = Some l ->
    List.nth_error (wrap_leaves D' t' ls ihs r' nr') idx
    = Some (if leaf_in D' t' l then a_var (nr' - 1 - (r' + leaves_in_count D' t' (List.firstn idx ls)))
            else List.nth idx ihs a_prop).
Proof.
  intros D' t'; induction ls as [| l0 ls IH]; intros [| ih ihs] r' nr' idx l Hl Hn; cbn in Hl; try discriminate;
    [ destruct idx; discriminate |].
  injection Hl as Hl.
  destruct idx as [| idx]; cbn in Hn.
  - injection Hn as ->; cbn [wrap_leaves List.firstn]; unfold leaves_in_count; cbn.
    destruct (leaf_in D' t' l); cbn; [ rewrite Nat.add_0_r |]; reflexivity.
  - cbn [wrap_leaves List.firstn]; unfold leaves_in_count; cbn [List.filter].
    destruct (leaf_in D' t' l0); cbn [List.nth_error List.length List.nth].
    + rewrite (IH ihs (S r') nr' idx l Hl Hn); unfold leaves_in_count; destruct (leaf_in D' t' l); [| reflexivity ].
      do 3 f_equal; lia.
    + exact (IH ihs r' nr' idx l Hl Hn).
Qed.

(** The recursive results of a wrapped branch ([wrap_ihs]) at the leaf
    path [idx] of the recursive argument after [gs1]: the container's
    variable at a path of the container's argument [g'], the group's
    result [ihs] there otherwise. *)
Lemma wrap_ihs_nth : forall D' D vm gs1' g' gs2' gs1 t gs2 ihs r' nr' idx l,
    List.length gs1' = List.length gs1 -> cargs_correspond vm (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2) ->
    List.length ihs = cargs_nrec D (gs1 ++ ca_rec t :: gs2) ->
    List.nth_error (shape_leaves (rview_leaves D) 0 t) idx = Some l ->
    List.nth_error (wrap_ihs D' D (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2) ihs r' nr') (cargs_nrec D gs1 + idx)
    = match g' with
      | ca_rec t' => if leaf_in D' t' l
                     then Some (a_var (nr' - 1 - (r' + cargs_container_count D D' gs1' gs1
                                                  + leaves_in_count D' t' (List.firstn idx (shape_leaves (rview_leaves D) 0 t)))))
                     else List.nth_error ihs (cargs_nrec D gs1 + idx)
      | ca_arg _ _ => List.nth_error ihs (cargs_nrec D gs1 + idx)
      end.
Proof.
  intros D' D vm; induction gs1' as [| g1' gs1' IH]; intros g' gs2' [| g1 gs1] t gs2 ihs r' nr' idx l Hl Hc Hih Hn;
    cbn in Hl; try discriminate.
  - pose proof (nth_error_lt_length _ _ _ Hn) as Hidx.
    cbn [cargs_nrec List.app] in Hih |- *.
    destruct g' as [ra' A' | t']; cbn in Hc |- *; [| destruct Hc as (_ & _ & Hc) ].
    + rewrite List.nth_error_app1 by (rewrite List.length_firstn; lia).
      rewrite List.nth_error_firstn; destruct (Nat.ltb_spec idx (List.length (shape_leaves (rview_leaves D) 0 t))); [ reflexivity | lia ].
    + rewrite List.nth_error_app1 by (rewrite length_wrap_leaves, List.length_firstn; lia).
      rewrite (wrap_leaves_nth D' t' (shape_leaves (rview_leaves D) 0 t) (List.firstn (List.length (shape_leaves (rview_leaves D) 0 t)) ihs)
                 r' nr' idx l ltac:(rewrite List.length_firstn; lia) Hn).
      destruct (leaf_in D' t' l); [ rewrite Nat.add_0_r; reflexivity |].
      rewrite List.nth_firstn; destruct (Nat.ltb_spec idx (List.length (shape_leaves (rview_leaves D) 0 t))); [| lia ].
      symmetry; apply List.nth_error_nth'; lia.
  - injection Hl as Hl.
    destruct g1' as [ra1' A1' | t1'], g1 as [ra1 A1 | t1]; cbn in Hc; try contradiction; cbn [List.app wrap_ihs cargs_nrec cargs_container_count] in Hih |- *.
    + exact (IH g' gs2' gs1 t gs2 ihs r' nr' idx l Hl (proj2 Hc) Hih Hn).
    + destruct Hc as [_ Hc].
      rewrite List.nth_error_app2 by (rewrite List.length_firstn; lia).
      rewrite List.length_firstn, Nat.min_l by lia.
      replace (List.length (shape_leaves (rview_leaves D) 0 t1) + cargs_nrec D gs1 + idx - List.length (shape_leaves (rview_leaves D) 0 t1))
        with (cargs_nrec D gs1 + idx) by lia.
      rewrite (IH g' gs2' gs1 t gs2 (List.skipn (List.length (shape_leaves (rview_leaves D) 0 t1)) ihs) r' nr' idx l Hl Hc
                 ltac:(rewrite List.length_skipn; lia) Hn), !List.nth_error_skipn.
      replace (List.length (shape_leaves (rview_leaves D) 0 t1) + (cargs_nrec D gs1 + idx))
        with (List.length (shape_leaves (rview_leaves D) 0 t1) + cargs_nrec D gs1 + idx) by lia.
      reflexivity.
    + destruct Hc as (_ & _ & Hc).
      rewrite List.nth_error_app2 by (rewrite length_wrap_leaves, List.length_firstn; lia).
      rewrite length_wrap_leaves, List.length_firstn, (Nat.min_l _ (List.length ihs)), Nat.min_id by lia.
      replace (List.length (shape_leaves (rview_leaves D) 0 t1) + cargs_nrec D gs1 + idx - List.length (shape_leaves (rview_leaves D) 0 t1))
        with (cargs_nrec D gs1 + idx) by lia.
      rewrite (IH g' gs2' gs1 t gs2 (List.skipn (List.length (shape_leaves (rview_leaves D) 0 t1)) ihs) _ nr' idx l Hl Hc
                 ltac:(rewrite List.length_skipn; lia) Hn), !List.nth_error_skipn.
      replace (List.length (shape_leaves (rview_leaves D) 0 t1) + (cargs_nrec D gs1 + idx))
        with (List.length (shape_leaves (rview_leaves D) 0 t1) + cargs_nrec D gs1 + idx) by lia.
      destruct g'; [ reflexivity |]; destruct (leaf_in D' _ l); [| reflexivity ].
      do 3 f_equal; lia.
Qed.

(** The fresh variables along the paths [ls] flagged by [f]: at a flagged
    path [idx], the variable after those of the flagged paths before, at
    the path's type. *)
Lemma fresh_leaf_vars_nth : forall {X : Type} (f : X -> bool) ls as' s vs, fresh_leaf_vars (List.map f ls) as' s vs ->
    List.length as' = List.length ls /\ List.length vs = List.length (List.filter f ls) /\
    forall idx x b, List.nth_error ls idx = Some x -> f x = true -> List.nth_error as' idx = Some b ->
      List.nth_error vs (List.length (List.filter f (List.firstn idx ls)))
      = Some (⇑! b (s + List.length (List.filter f (List.firstn idx ls)))).
Proof.
  intros X f; induction ls as [| x0 ls IH]; intros as' s vs H; cbn in H; inversion H; subst.
  - split; [ reflexivity | split; [ reflexivity | intros [] *; discriminate ] ].
  - match goal with H0 : fresh_leaf_vars (List.map f ls) _ (S s) _ |- _ => destruct (IH _ _ _ H0) as (L1 & L2 & Hn) end.
    match goal with E : true = f x0 |- _ => rename E into Ef end.
    split; [ cbn; f_equal; exact L1 |]; split; [ cbn; rewrite <- Ef; cbn; f_equal; exact L2 |].
    intros [| idx] x b Hx Hf Hb; cbn in Hx, Hb |- *.
    + injection Hb as ->; rewrite Nat.add_0_r; reflexivity.
    + rewrite <- Ef; cbn.
      rewrite (Hn idx x b Hx Hf Hb); do 3 f_equal; lia.
  - match goal with H0 : fresh_leaf_vars (List.map f ls) _ s _ |- _ => destruct (IH _ _ _ H0) as (L1 & L2 & Hn) end.
    match goal with E : false = f x0 |- _ => rename E into Ef end.
    split; [ cbn; f_equal; exact L1 |]; split; [ cbn; rewrite <- Ef; exact L2 |].
    intros [| idx] x b Hx Hf Hb; cbn in Hx, Hb |- *.
    + injection Hx as ->; congruence.
    + rewrite <- Ef.
      exact (Hn idx x b Hx Hf Hb).
Qed.

(** The recursive results along the paths [ls] flagged by [f]
    ([wrap_leaf_vals]): at a flagged path [idx], the next of [ihs] after
    those of the flagged paths before; at the others, the group's [rs]
    there.  The flagged paths use up a prefix of [ihs]. *)
Lemma wrap_leaf_vals_nth : forall {X : Type} (f : X -> bool) ls rs ihs ihs' out, wrap_leaf_vals (List.map f ls) rs ihs ihs' out ->
    List.length rs = List.length ls /\ List.length out = List.length ls /\
    (exists pre, ihs = pre ++ ihs' /\ List.length pre = List.length (List.filter f ls)) /\
    forall idx x, List.nth_error ls idx = Some x ->
      List.nth_error out idx = if f x then List.nth_error ihs (List.length (List.filter f (List.firstn idx ls))) else List.nth_error rs idx.
Proof.
  intros X f; induction ls as [| x0 ls IH]; intros rs ihs ihs' out H; cbn in H; inversion H; subst.
  - split; [ reflexivity | split; [ reflexivity | split; [ exists nil; split; reflexivity | intros [] *; discriminate ] ] ].
  - match goal with H0 : wrap_leaf_vals (List.map f ls) _ _ _ _ |- _ => destruct (IH _ _ _ _ H0) as (L1 & L2 & (pre & Ep & Lp) & Hn) end.
    match goal with E : true = f x0 |- _ => rename E into Ef end.
    split; [ cbn; f_equal; exact L1 |]; split; [ cbn; f_equal; exact L2 |].
    split; [ exists (ih :: pre); split; [ rewrite Ep; reflexivity | cbn; rewrite <- Ef; cbn; f_equal; exact Lp ] |].
    intros [| idx] x Hx; cbn in Hx |- *.
    + injection Hx as ->; rewrite <- Ef; reflexivity.
    + rewrite <- Ef; cbn; exact (Hn idx x Hx).
  - match goal with H0 : wrap_leaf_vals (List.map f ls) _ _ _ _ |- _ => destruct (IH _ _ _ _ H0) as (L1 & L2 & (pre & Ep & Lp) & Hn) end.
    match goal with E : false = f x0 |- _ => rename E into Ef end.
    split; [ cbn; f_equal; exact L1 |]; split; [ cbn; f_equal; exact L2 |].
    split; [ exists pre; split; [ exact Ep | cbn; rewrite <- Ef; exact Lp ] |].
    intros [| idx] x Hx; cbn in Hx |- *.
    + injection Hx as ->; rewrite <- Ef; reflexivity.
    + rewrite <- Ef; exact (Hn idx x Hx).
Qed.

(** The recursive results a branch of a view is read under
    ([wrap_ihs_eval]), at the leaf path [idx] of the recursive argument
    after [gs1]: the container's fresh variable at a path of the
    container's argument [g'], the eliminator's result along the path
    otherwise. *)
Lemma wrapped_ihs_nth : forall ρ p ups Bks Dc D, ind_lookup gc_deps gc_stack p = Some D -> leaves_coherent D ->
    forall gs1' g' gs2' gs1 t gs2 vs ihs r, List.length gs1' = List.length gs1 ->
    ⟦wihs vs of (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2) of Dc with ihs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
    forall v idx l, List.nth_error vs (List.length gs1) = Some v -> List.nth_error (shape_leaves (rview_leaves D) 0 t) idx = Some l ->
    exists rs, ⟦ih v of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rs /\
      List.nth_error r (cargs_nrec D gs1 + idx)
      = match g' with
        | ca_rec t' => if leaf_in Dc t' l
                       then List.nth_error ihs (cargs_container_count D Dc gs1' gs1 + leaves_in_count Dc t' (List.firstn idx (shape_leaves (rview_leaves D) 0 t)))
                       else List.nth_error rs idx
        | ca_arg _ _ => List.nth_error rs idx
        end.
Proof.
  intros ρ p ups Bks Dc D Hl Hco gs1'; induction gs1' as [| g1' gs1' IH]; intros g' gs2' [| g1 gs1] t gs2 vs ihs r Hlen H v idx l Hv Hn;
    cbn in Hlen; try discriminate; cbn [List.app] in H; inversion H; subst; cbn [List.length List.nth_error] in Hv;
    repeat match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => tryif constr_eq D1 D then fail else (rewrite Hl in H1; injection H1 as <-) end;
    pose proof (nth_error_lt_length _ _ _ Hn) as Hidx.
  - injection Hv as ->.
    match goal with Hr : ⟦ih _ of _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?rs1, Hw : wrap_leaf_vals _ ?rs1 _ _ ?r1 |- _ =>
      exists rs1; split; [ exact Hr |];
      destruct (wrap_leaf_vals_nth _ _ _ _ _ _ Hw) as (_ & L2 & _ & Hw') end.
    cbn [cargs_nrec cargs_container_count Nat.add]; rewrite List.nth_error_app1 by lia.
    rewrite (Hw' idx l Hn); reflexivity.
  - injection Hv as ->.
    match goal with Hr : ⟦ih _ of _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?rs1 |- _ =>
      exists rs1; split; [ exact Hr |];
      pose proof (proj1 (proj2 (@eval_ih_length_all gc_deps gc_stack)) _ _ _ _ _ _ _ Hr _ Hl Hco) as L1 end.
    cbn [cargs_nrec Nat.add]; rewrite List.nth_error_app1 by lia; reflexivity.
  - injection Hlen as Hlen.
    match goal with Hw : wrap_leaf_vals _ _ _ _ ?r1, Hr0 : ⟦wihs _ of _ _ of _ with _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (wrap_leaf_vals_nth _ _ _ _ _ _ Hw) as (_ & L2 & (pre & Ep & Lp) & _);
      destruct (IH _ _ _ _ _ _ _ _ Hlen Hr0 v idx l Hv Hn) as (rs0 & Er0 & Hr0') end.
    exists rs0; split; [ exact Er0 |].
    cbn [cargs_nrec cargs_container_count]; rewrite List.nth_error_app2 by lia.
    replace (List.length (shape_leaves (rview_leaves D) 0 t0) + cargs_nrec D gs1 + idx - List.length r1) with (cargs_nrec D gs1 + idx) by lia.
    rewrite Hr0'; destruct g' as [? ? | t1']; [ reflexivity |]; destruct (leaf_in Dc t1' l); [| reflexivity ].
    rewrite Ep, List.nth_error_app2 by (unfold leaves_in_count in *; lia).
    unfold leaves_in_count in *; f_equal; lia.
  - injection Hlen as Hlen.
    match goal with Hr : ⟦ih _ of t0 under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?rs1, Hr0 : ⟦wihs _ of _ _ of _ with _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      pose proof (proj1 (proj2 (@eval_ih_length_all gc_deps gc_stack)) _ _ _ _ _ _ _ Hr _ Hl Hco) as L1;
      destruct (IH _ _ _ _ _ _ _ _ Hlen Hr0 v idx l Hv Hn) as (rs0 & Er0 & Hr0') end.
    exists rs0; split; [ exact Er0 |].
    cbn [cargs_nrec cargs_container_count]; rewrite List.nth_error_app2 by lia.
    replace (List.length (shape_leaves (rview_leaves D) 0 t0) + cargs_nrec D gs1 + idx - List.length rs) with (cargs_nrec D gs1 + idx) by lia.
    exact Hr0'.
  - injection Hlen as Hlen.
    match goal with Hr0 : ⟦wihs _ of _ _ of _ with _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ _ Hlen Hr0 v idx l Hv Hn) as (rs0 & Er0 & Hr0') end.
    exists rs0; split; [ exact Er0 |]; exact Hr0'.
Qed.

(** The fresh recursive results of a view's branch ([fresh_ihs]), at a
    leaf path [idx] of the container's of the argument after [gs1]
    recursive in both: the variable after those of the container's paths
    before, at the type of the result along the path. *)
Lemma fresh_ihs_nth : forall ρm As p ups Dc D, ind_lookup gc_deps gc_stack p = Some D ->
    forall gs1' t' gs2' gs1 t gs2 ρa vs s ihs, List.length gs1' = List.length gs1 ->
    Fihs vs at (gs1' ++ ca_rec t' :: gs2') (gs1 ++ ca_rec t :: gs2) of Dc under ρm As at p ups in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ ihs ->
    forall v idx l, List.nth_error vs (List.length gs1) = Some v -> List.nth_error (shape_leaves (rview_leaves D) 0 t) idx = Some l ->
    leaf_in Dc t' l = true ->
    exists as' b, ⟦ihty v of t at p ups under ρm As ⟧ gc_deps ⍮ gc_stack
                    ⍮ env_tele ρa (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ as' /\
      List.nth_error as' idx = Some b /\
      List.nth_error ihs (cargs_container_count D Dc gs1' gs1 + leaves_in_count Dc t' (List.firstn idx (shape_leaves (rview_leaves D) 0 t)))
      = Some (⇑! b (s + (cargs_container_count D Dc gs1' gs1 + leaves_in_count Dc t' (List.firstn idx (shape_leaves (rview_leaves D) 0 t))))).
Proof.
  intros ρm As p ups Dc D Hl gs1'; induction gs1' as [| g1' gs1' IH]; intros t' gs2' [| g1 gs1] t gs2 ρa vs s ihs Hlen H v idx l Hv Hn Hin;
    cbn in Hlen; try discriminate; cbn [List.app] in H; inversion H; subst; cbn [List.length List.nth_error] in Hv;
    repeat match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => tryif constr_eq D1 D then fail else (rewrite Hl in H1; injection H1 as <-) end.
  - injection Hv as ->.
    match goal with Ht : ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?as1, Hf : fresh_leaf_vars _ ?as1 _ _ |- _ =>
      destruct (fresh_leaf_vars_nth _ _ _ _ _ Hf) as (L1 & _ & Hf') end.
    pose proof (nth_error_lt_length _ _ _ Hn) as Hidx.
    destruct (nth_error_lt_some as' idx ltac:(lia)) as [b Hb].
    exists as', b; split; [ assumption | split; [ exact Hb |] ].
    cbn [cargs_container_count Nat.add]; unfold leaves_in_count.
    rewrite List.nth_error_app1 by (apply List.nth_error_Some; rewrite (Hf' idx l b Hn Hin Hb); discriminate).
    exact (Hf' idx l b Hn Hin Hb).
  - injection Hlen as Hlen.
    match goal with Hr0 : Fihs _ at _ _ of _ under _ _ at _ _ in _ ⍮ _ ⍮ _ ↦ _ ⦂ _ ⍮ _ ↘ _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ _ _ Hlen Hr0 v idx l Hv Hn Hin) as (as1 & b & Ea & Hb & Hi) end.
    exists as1, b; split; [ cbn [nonrec_arg_vals List.firstn List.length]; exact Ea | split; [ exact Hb | exact Hi ] ].
  - injection Hlen as Hlen.
    match goal with Hf : fresh_leaf_vars _ _ _ ?ihs1, Hr0 : Fihs _ at _ _ of _ under _ _ at _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (fresh_leaf_vars_nth _ _ _ _ _ Hf) as (_ & L2 & _);
      destruct (IH _ _ _ _ _ _ _ _ _ Hlen Hr0 v idx l Hv Hn Hin) as (as1 & b & Ea & Hb & Hi) end.
    exists as1, b; split; [ exact Ea | split; [ exact Hb |] ].
    cbn [cargs_container_count]; unfold leaves_in_count in *.
    rewrite <- !Nat.add_assoc, List.nth_error_app2 by lia.
    rewrite <- L2, Nat.add_comm, Nat.add_sub, Hi; do 3 f_equal; lia.
  - injection Hlen as Hlen.
    match goal with Hr0 : Fihs _ at _ _ of _ under _ _ at _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ _ _ Hlen Hr0 v idx l Hv Hn Hin) as (as1 & b & Ea & Hb & Hi) end.
    exists as1, b; split; [ exact Ea | split; [ exact Hb | exact Hi ] ].
Qed.

(** The recursive results of a branch read as its own group's, every path
    the group's own: the fresh ones. *)
Lemma wrapped_ihs_own : forall ρ p ups Bks D gs vs ihs r, ind_lookup gc_deps gc_stack p = Some D ->
    (forall gs1 t gs2 l, gs = gs1 ++ ca_rec t :: gs2 -> In l (shape_leaves (rview_leaves D) 0 t) -> leaf_in D t l = true) ->
    ⟦wihs vs of gs gs of D with ihs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r -> r = ihs.
Proof.
  intros ρ p ups Bks D gs; induction gs as [| g gs IH]; intros vs ihs r Hl Hown H; inversion H; subst; [ reflexivity | |].
  - match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end.
    match goal with Hw : wrap_leaf_vals (List.map (leaf_in D ?t0) (shape_leaves (rview_leaves D) 0 ?t0)) _ _ _ _ |- _ =>
      assert (Ebs : List.map (leaf_in D t0) (shape_leaves (rview_leaves D) 0 t0) = List.map (fun _ => true) (shape_leaves (rview_leaves D) 0 t0))
        by (apply List.map_ext_in; intros l Hin; exact (Hown nil t0 gs l eq_refl Hin));
      rewrite Ebs in Hw; pose proof (wrap_leaf_vals_all _ _ _ _ _ Hw) as -> end.
    f_equal; eapply IH; [ exact Hl | | eassumption ].
    intros gs1 t gs2 l Heq Hin; exact (Hown (ca_rec _ :: gs1) t gs2 l ltac:(rewrite Heq; reflexivity) Hin).
  - eapply IH; [ exact Hl | | eassumption ].
    intros gs1 t gs2 l Heq Hin; exact (Hown (ca_arg _ _ :: gs1) t gs2 l ltac:(rewrite Heq; reflexivity) Hin).
Qed.

(** Terms glued along a closed telescope are equal to the readback of
    their values up to proofs, at every weakening. *)
Lemma glu_args_read : forall Δ C Ms vs, all_assumptions C -> ctx_scoped 0 C -> glu_args Δ C Id nil Ms vs ->
    forall Δ' φ Rs, Δ' ⊢ᵏ φ : Δ -> Rps vs at List.rev C in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ' ↘ Rs ->
      glu_nfs_eq_at Δ' C (List.map (fun P => P[φ]ʷ) Ms) Rs.
Proof.
  intros * Hass Hs Hg; pose proof Hg as [L1 L2 H].
  intros Δ' φ Rs Hφ HRs.
  destruct (read_ps_nth _ _ _ _ _ HRs) as [HRl HRn].
  apply glu_nfs_eq_at_of_nth; [ rewrite List.length_map, HRl; congruence | |].
  - intros k X Y T HX HY HT.
    rewrite List.nth_error_map in HX.
    destruct (List.nth_error Ms k) as [M |] eqn:HM; [| discriminate ]; injection HX as <-.
    rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
    destruct (List.nth_error (tele_insts C Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
    assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as (κ & A & He).
    destruct (HRn _ _ _ _ Hv He) as (a' & V & Ha' & HV & HY').
    rewrite HY' in HY; injection HY as <-.
    destruct (H _ _ _ _ _ _ HM HT0 Hv He) as [i a P El Ha Hglu HP HMg].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (realize_glu_elem_top _ _ _ _ Hglu _ _ _ _ HMg) as [? ? _ _ _ _ Hrb].
    exact (Hrb _ _ _ Hφ HV).
  - intros k X HX.
    apply nth_error_lt_some.
    rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.length_map, length_tele_insts by first [ exact Hass | lia ].
    assert (HXk : k < List.length (List.map (fun P => P[φ]ʷ) Ms)) by (apply List.nth_error_Some; congruence).
    rewrite List.length_map in HXk; lia.
Qed.

(** The uniform parameters of a shape's components, moved by a
    substitution. *)
Lemma shape_uc_compose : forall D Us Tc σ β τ, shape_uc D Us Tc σ β -> shape_uc D Us Tc (σ ⨟ τ) (β ⨟ τ).
Proof.
  intros * H y Hy; cbn [sb_compose]; rewrite <- !sentry_exp_sub, H by exact Hy.
  cbn [sb_compose]; rewrite <- !sentry_exp_sub, exp_sub_sub; reflexivity.
Qed.

(** Substitutions with the same terms at every variable, extended by the
    same terms. *)
Lemma sb_exp_agree_of_list : forall σ σ' Ms, sb_exp_agree σ σ' -> sb_exp_agree (sb_of_list σ Ms) (sb_of_list σ' Ms).
Proof.
  intros * H y; destruct (Nat.lt_ge_cases y (List.length Ms)) as [Hy | Hy].
  - rewrite !(sb_of_list_nth Ms _ y a_prop Hy); reflexivity.
  - replace y with (List.length Ms + (y - List.length Ms)) by lia; rewrite !sb_of_list_ge; apply H.
Qed.

(** Substitutions with the same terms at every variable act alike on the
    recursive result along a leaf path whose terms have no free module
    variable, and on its type. *)
Lemma leaf_ih_exp_agree : forall r pq l Us Bks σ σ' M, Views.leaf_mvc l -> sb_exp_agree σ σ' ->
    leaf_ih r pq Us Bks σ M l = leaf_ih r pq Us Bks σ' M l.
Proof.
  intros r pq l; induction l as [j Ps | B l IH | f ns l IH]; intros * Hm Hσ; cbn [leaf_ih Views.leaf_mvc] in *; [ reflexivity | |].
  - destruct Hm as [HmB Hm]; f_equal; [ exact (exp_mvc_sub_agree _ _ _ HmB Hσ) |].
    apply IH; [ exact Hm | apply sb_exp_agree_q; exact Hσ ].
  - apply IH; [ exact Hm | apply sb_exp_agree_of_list; exact Hσ ].
Qed.

Lemma leaf_ihty_exp_agree : forall r l As β σ σ' x, Views.leaf_mvc l -> sb_exp_agree σ σ' ->
    leaf_ihty r As β σ x l = leaf_ihty r As β σ' x l.
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros * Hm Hσ; cbn [leaf_ihty Views.leaf_mvc] in *.
  - do 3 f_equal; apply List.map_ext_in; intros P HP.
    exact (exp_mvc_sub_agree _ _ _ (proj1 (List.Forall_forall _ _) Hm P HP) Hσ).
  - destruct Hm as [HmB Hm]; f_equal; [ exact (exp_mvc_sub_agree _ _ _ HmB Hσ) |].
    apply IH; [ exact Hm | apply sb_exp_agree_q; exact Hσ ].
  - apply IH; [ exact Hm | apply sb_exp_agree_of_list; exact Hσ ].
Qed.

(** The types of the recursive results of a record view's fields, at the
    recursive field after [gs1]: those of the field, its components the
    non-recursive fields before it, after those of the fields before. *)
Lemma eval_ihtys_nth : forall p D ups ρm As, ind_lookup gc_deps gc_stack p = Some D -> leaves_coherent D ->
    forall gs1 t gs2 ρ0 vs rs v, ⟦ihtys vs of gs1 ++ ca_rec t :: gs2 at p ups under ρm As ⟧ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ rs ->
    List.nth_error vs (List.length gs1) = Some v ->
    exists rf, ⟦ihty v of t at p ups under ρm As ⟧ gc_deps ⍮ gc_stack
                 ⍮ env_tele ρ0 (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ rf /\
      forall idx, idx < List.length rf -> List.nth_error rs (cargs_nrec D gs1 + idx) = List.nth_error rf idx.
Proof.
  intros p D ups ρm As Hl Hco gs1; induction gs1 as [| g gs1 IH]; intros t gs2 ρ0 vs rs v H Hv;
    inversion H; subst; cbn [List.app List.length] in *; try discriminate.
  - injection Hv as ->.
    match goal with Hr : ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?r1 |- _ => exists r1; split; [ exact Hr |] end.
    intros idx Hidx; cbn [cargs_nrec Nat.add]; rewrite List.nth_error_app1 by exact Hidx; reflexivity.
  - match goal with Hr : ⟦ihtys _ of gs1 ++ _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (IH _ _ _ _ _ _ Hr Hv) as (rf & Er & Hrs) end.
    exists rf; split; [ exact Er |].
    intros idx Hidx; cbn [cargs_nrec]; exact (Hrs idx Hidx).
  - match goal with Hr : ⟦ihtys _ of gs1 ++ _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (IH _ _ _ _ _ _ Hr Hv) as (rf & Er & Hrs) end.
    exists rf; split; [ exact Er |].
    intros idx Hidx; cbn [cargs_nrec].
    lazymatch goal with
    | |- List.nth_error (?r1 ++ _) _ = _ =>
        match goal with Hr1 : ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ r1 |- _ =>
          pose proof (proj1 (@eval_ihty_length_all gc_deps gc_stack) _ _ _ _ _ _ _ _ Hr1 _ Hl Hco) as Lr1 end
    end.
    rewrite List.nth_error_app2 by lia.
    rewrite <- Lr1, <- Nat.add_assoc, Nat.add_comm, Nat.add_sub; exact (Hrs idx Hidx).
Qed.

(** The fresh variables along paths all flagged as fresh ones: one per
    path, at the path's type, from [s] on. *)
Lemma fresh_leaf_vars_all : forall {X : Type} (ls : list X) as' s vs, fresh_leaf_vars (List.map (fun _ => true) ls) as' s vs ->
    List.length vs = List.length ls /\ List.length as' = List.length ls /\
    forall i a, List.nth_error as' i = Some a -> List.nth_error vs i = Some (⇑! a (s + i)).
Proof.
  intros X; induction ls as [| x ls IH]; intros as' s vs H; cbn in H; inversion H; subst.
  - split; [ reflexivity | split; [ reflexivity | intros [] *; discriminate ] ].
  - match goal with H0 : fresh_leaf_vars _ _ (S s) _ |- _ => destruct (IH _ _ _ H0) as (L1 & L2 & Hn) end.
    split; [ cbn; f_equal; exact L1 | split; [ cbn; f_equal; exact L2 |] ].
    intros [| i] a0 Ha; cbn in Ha |- *; [ injection Ha as ->; rewrite Nat.add_0_r; reflexivity |].
    rewrite (Hn i a0 Ha); do 3 f_equal; lia.
Qed.

(** The fresh recursive results of a constructor's arguments read as its
    own group's, every path of the group's: at the recursive argument
    after [gs1], one fresh variable per path at the path's type, after
    those of the arguments before. *)
Lemma fresh_ihs_own_nth : forall ρm As p ups D ρa gs vs s ihs, ind_lookup gc_deps gc_stack p = Some D ->
    Fihs vs at gs gs of D under ρm As at p ups in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ ihs ->
    (forall gs1 t gs2 l, gs = gs1 ++ ca_rec t :: gs2 -> In l (shape_leaves (rview_leaves D) 0 t) -> leaf_in D t l = true) ->
    forall gs1 t gs2 v, gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
    exists as', ⟦ihty v of t at p ups under ρm As ⟧ gc_deps ⍮ gc_stack
                  ⍮ env_tele ρa (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ↘ as' /\
      forall idx a, List.nth_error as' idx = Some a ->
        List.nth_error ihs (cargs_nrec D gs1 + idx) = Some (⇑! a (s + (cargs_nrec D gs1 + idx))).
Proof.
  intros ρm As p ups D ρa gs vs s ihs Hl H Hown gs1; revert ρa gs vs s ihs H Hown;
    induction gs1 as [| g gs1 IH]; intros ρa gs vs s ihs H Hown t gs2 v -> Hv;
    inversion H; subst; cbn [List.app List.length] in *; try discriminate.
  - injection Hv as ->.
    match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end.
    match goal with Hf : fresh_leaf_vars ?bs ?as1 s ?ihs1, Ht : ⟦ihty _ of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?as1 |- _ =>
      exists as1; split; [ exact Ht |];
      assert (Ebs : bs = List.map (fun _ => true) (shape_leaves (rview_leaves D) 0 t))
        by (apply List.map_ext_in; intros l Hin; exact (Hown nil t gs2 l eq_refl Hin));
      rewrite Ebs in Hf; destruct (fresh_leaf_vars_all _ _ _ _ Hf) as (_ & _ & Hn) end.
    intros idx a Ha; cbn [cargs_nrec Nat.add]; rewrite List.nth_error_app1 by (apply List.nth_error_Some; rewrite (Hn idx a Ha); discriminate).
    exact (Hn idx a Ha).
  - match goal with H1 : Fihs _ at (gs1 ++ _) _ of _ under _ _ at _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (IH _ _ _ _ _ H1 (fun gs1' t' gs2' l Heq Hin => Hown (ca_arg _ _ :: gs1') t' gs2' l ltac:(rewrite Heq; reflexivity) Hin)
                  t gs2 v eq_refl Hv) as (as1 & Ht & Hn) end.
    exists as1; split; [ exact Ht |].
    intros idx a Ha; cbn [cargs_nrec]; exact (Hn idx a Ha).
  - match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end.
    match goal with H1 : Fihs _ at (gs1 ++ _) _ of _ under _ _ at _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct (IH _ _ _ _ _ H1 (fun gs1' t' gs2' l Heq Hin => Hown (ca_rec _ :: gs1') t' gs2' l ltac:(rewrite Heq; reflexivity) Hin)
                  t gs2 v eq_refl Hv) as (as1 & Ht & Hn) end.
    exists as1; split; [ exact Ht |].
    match goal with Hf : fresh_leaf_vars (List.map (leaf_in D ?t0) (shape_leaves (rview_leaves D) 0 ?t0)) _ s ?ihs1 |- _ =>
      assert (Ebs : List.map (leaf_in D t0) (shape_leaves (rview_leaves D) 0 t0) = List.map (fun _ => true) (shape_leaves (rview_leaves D) 0 t0))
        by (apply List.map_ext_in; intros l Hin; exact (Hown nil t0 _ l eq_refl Hin));
      rewrite Ebs in Hf; destruct (fresh_leaf_vars_all _ _ _ _ Hf) as (L1 & _ & _);
      intros idx a Ha; cbn [cargs_nrec]; rewrite List.nth_error_app2 by lia;
      replace (List.length (shape_leaves (rview_leaves D) 0 t0) + cargs_nrec D gs1 + idx - List.length ihs1)
        with (cargs_nrec D gs1 + idx) by lia;
      rewrite (Hn idx a Ha); do 3 f_equal; lia end.
Qed.

(** Every path flagged as a fresh variable's. *)
Lemma leaf_flags_ok_fresh_all : forall P (ms : list nat), leaf_flags_ok P (List.map (fun _ => true) ms) ms.
Proof. intros P; induction ms as [| m ms IH]; cbn; constructor; exact IH. Qed.

(** ** The Blocks, Glued

    The gluing premises of an eliminator's blocks at uniform parameters
    [Us]: each block's motive in its member's context, and each branch at
    its type in its context. *)
#[warnings="-cannot-define-projection"]
Record glu_blocks (Γ : ctx) (p : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock) (i : nat) : Prop := mk_glu_blocks
  { (** Each motive is valid in its member's motive context *)
    glu_blocks_motive : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      elim_mctx p D k Mk Us ++ Γ ⊩ eb_motive b : Typeω@i
    (** Each branch is valid at its branch type in its context *)
  ; glu_blocks_branch : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
      elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ ⊩ B : elim_branch_type p D k Mk c gs (eb_motive b) Us }.

(** ** The Eliminator, at an Environment

    The group [D] at [p], valid; the context [Γ] of the eliminator, the
    uniform parameters [Us] and the blocks [Bks] there; an environment [ρ]
    of [Γ], at which [Us] are [ups]; and the gluings of the clause of
    [d_ind] at [ups]. *)

(** The leaf path of fields at the leaf path [idx1] of a recursive field
    [f] after the fields [fs1]: through [f]'s projection, after the paths
    of the fields before. *)
Lemma fields_leaves_at : forall D fs1 f t fs2 ns idx1 l1,
    List.nth_error (shape_leaves (rview_leaves D) (List.length (ns ++ fields_args fs1)) t) idx1 = Some l1 ->
    List.nth_error (fields_leaves (rview_leaves D) ns (fs1 ++ (f, ca_rec t) :: fs2)) (cargs_nrec D (List.map snd fs1) + idx1)
    = Some (leaf_proj f (ns ++ fields_args fs1) l1).
Proof.
  intros D; induction fs1 as [| [g [A | t0]] fs1 IH]; intros * Hl1; cbn [fields_leaves fields_args List.map snd List.app cargs_nrec] in *.
  - rewrite List.app_nil_r in *.
    rewrite Nat.add_0_l, List.nth_error_app1 by (rewrite List.length_map; apply List.nth_error_Some; congruence).
    rewrite List.nth_error_map, Hl1; reflexivity.
  - rewrite (IH f t fs2 (ns ++ g :: nil) idx1 l1); [ rewrite <- List.app_assoc; reflexivity |].
    rewrite <- List.app_assoc; exact Hl1.
  - rewrite List.nth_error_app2 by (rewrite List.length_map, (length_shape_leaves _ _ _ 0); lia).
    rewrite List.length_map, (length_shape_leaves _ t0 (List.length ns) 0).
    replace (List.length (shape_leaves (rview_leaves D) 0 t0) + cargs_nrec D (List.map snd fs1) + idx1
             - List.length (shape_leaves (rview_leaves D) 0 t0)) with (cargs_nrec D (List.map snd fs1) + idx1) by lia.
    exact (IH _ _ _ _ _ _ Hl1).
Qed.

(** The fields named [fl] of kinds [gs], at a recursive one. *)
Lemma combine_split_rec : forall (fl : list String.string) (gs gs1 : list carg) t gs2, List.length fl = List.length gs ->
    gs = gs1 ++ ca_rec t :: gs2 ->
    exists fs1 f fs2, List.combine fl gs = fs1 ++ (f, ca_rec t) :: fs2 /\ List.map snd fs1 = gs1.
Proof.
  intros fl gs gs1; revert fl gs; induction gs1 as [| g gs1 IH]; intros [| f fl] gs t gs2 Hl ->; cbn in Hl; try discriminate.
  - exists nil, f, (List.combine fl gs2); split; reflexivity.
  - injection Hl as Hl; destruct (IH fl _ t gs2 Hl eq_refl) as (fs1 & f' & fs2 & E & Es).
    exists ((f, g) :: fs1), f', fs2; cbn; rewrite E, Es; split; reflexivity.
Qed.

(** The non-recursive fields are as many as the non-recursive kinds. *)
Lemma length_fields_args : forall fs, List.length (fields_args fs) = List.length (cargs_nonrec (List.map snd fs)).
Proof. induction fs as [| [f [A | t]] fs IH]; cbn; lia. Qed.

(** At a record view, the recursive results of an element: those of its
    fields at its projections. *)
Lemma eval_ih_rview_inv : forall ρ p D ups Bks j Mj qr Is fl c gs Ps v rs, ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    ⟦ih v of pt_self j Ps under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rs ->
    exists ws, ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws /\ ⟦ihs ws of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rs.
Proof.
  intros * Hl HMj Hh Hcs Er.
  inversion Er; subst;
    match goal with H0 : ind_lookup _ _ p = Some ?D0 |- _ => rewrite Hl in H0; injection H0 as <- end;
    match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end.
  - exfalso; match goal with H3 : im_is_rview Mj = false |- _ => exact (not_rview_record _ _ _ _ H3 Hh) end.
  - match goal with H1 : im_head Mj = _ |- _ => rewrite Hh in H1; injection H1 as <- <- <- end.
    match goal with H1 : im_cons Mj = _ |- _ => rewrite Hcs in H1; injection H1 as <- <- end.
    eexists; split; eassumption.
Qed.

(** At a record view, the type along a leaf path: the field's along its
    path, at the projection. *)
Lemma leaf_type_rview_inv : forall D u ρm As Tm pre Ts j Mj qr Is fl c gs Ps v idx a,
    ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    Elim.leaf_type_at D u ρm As Tm pre Ts (pt_self j Ps) v idx a ->
    exists gs1 tf gs2 ws w idx1, gs = gs1 ++ ca_rec tf :: gs2 /\ ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws /\
      List.nth_error ws (List.length gs1) = Some w /\ idx = cargs_nrec D gs1 + idx1 /\
      idx1 < List.length (shape_leaves (rview_leaves D) 0 tf) /\
      Elim.leaf_type_at D u ρm As Tm (nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws)) (cargs_nonrec_tele gs1) tf w idx1 a.
Proof.
  intros * HMj Hh Hcs Hlt.
  inversion Hlt as [pre0 Ts0 j0 Mj0 Ps0 v0 bs b a0 i HMj0 Hrv0 Ebs Eb Hab
                   | pre0 Ts0 j0 Mj0 qr0 Is0 fl0 c0 gs0 gs1 tf gs2 Ps0 v0 ws w idx1 a0 HMj0 Hh0 Hcs0 Ews Heq Hw Hidx Hlt1 |];
    subst; rewrite HMj in HMj0; injection HMj0 as <-.
  - exfalso; exact (not_rview_record _ _ _ _ Hrv0 Hh).
  - rewrite Hh in Hh0; injection Hh0 as <- <- <-.
    rewrite Hcs in Hcs0; injection Hcs0 as <- ->.
    exists gs1, tf, gs2, ws, w, idx1; repeat split; assumption.
Qed.

Section ElimGlu.
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HGall : forall qn G, VP qn G -> glu_ind_decl G)
    (Hviewsall : forall qn G, VP qn G -> glu_views_ok qn G) (HPD : VP p D).
  Let HG := HGall _ _ HPD.
  Let Hvg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hsu := valid_group_sort _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Ua : all_assumptions (ind_uparams D) := decl_closed_ass _ Hc.
  Let Usem : ⊨ ind_uparams D := valid_ind_decl_uparams _ HD.

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
             Γ ⊩ N : T)
    (HUss : List.Forall (exp_scoped (List.length Γ)) Us).
  Let τU := sb_of_list Id Us.

  Variable (Bks : list eblock) (iA : nat).
  Hypotheses (HBt : blocks_typed gc_deps gc_stack Γ p D Us Bks ak_relevant iA) (HBv : valid_blocks p D Γ Us Bks iA)
    (HBg : glu_blocks Γ p D Us Bks iA).
  Let HBks := valid_blocks_has _ _ _ _ _ _ Hdt HBv.
  (** A member with a block is no record view. *)
  Let Hbnr : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> im_is_rview Mk = false :=
    fun k Mk b Hk Hb => block_not_rview D Bks k Mk b (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ Hdt))
                          (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt) Hk Hb.
  Let HMall := valid_blocks_mctx _ _ _ _ _ _ HBv.
  Let HAv := valid_blocks_motive _ _ _ _ _ _ HBv.

  Variable (ρ : env) (ups : list domain).
  Hypotheses (Hρ : RΓ ρ ρ) (HUv : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ups).

  Variable (bu : domain) (u : universe_index)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred).
  Hypotheses (Hbu : ⟦ ind_sort D ⟧ decl_env D ups ↘ bu)
    (Hule : universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).
  (** The contexts of the arguments of the constructors of the filed
      groups are glued ([AtType]); the gluing of global contexts gives
      it. *)
  Hypothesis (HΨall : forall q0 G0 j Mj c0 gs0, ind_lookup gc_deps gc_stack q0 = Some G0 -> ind_member G0 j = Some Mj ->
                 ind_con Mj c0 = Some gs0 -> ⊩ cargs_ctx q0 G0 Mj gs0 ++ im_params G0 Mj).
  (** A level above [u] and the sorts of the containers of the views, as
      [AtType] needs ([nb_exists] gives one). *)
  Variable (nb : nat).
  Hypothesis (Hnb : level_bound p D u nb).
  Let Hnbu := level_bound_clause _ _ _ _ Hnb.
  Let Hnbq := level_bound_views _ _ _ _ Hnb.
  Let Hnbr := level_bound_records _ _ _ _ Hnb.
  Let Hnbd := level_bound_doms _ _ _ _ Hnb.

  #[local] Abbreviation nr := (canon_nparams_rel D ups).
  #[local] Abbreviation ar := (canon_args_rel D ups).
  #[local] Abbreviation dr := (canon_doms_rel D ups).
  #[local] Abbreviation G := (grp_rel p D ups nr ar dr).
  #[local] Abbreviation GE f :=(f VP p D HVP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss).
  #[local] Abbreviation EB f := (f VP p D HVP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss ρ ups Hρ HUv).
  (** The telescope of the motive's context of the member [j], as
      [Completeness.Inductives.Elim] has it. *)
  Let mctx_tele j := match ind_member D j with Some Mj => List.rev (elim_mctx p D j Mj Us) | None => nil end.

  Lemma mctx_tele_at : forall j Mj, ind_member D j = Some Mj -> mctx_tele j = List.rev (elim_mctx p D j Mj Us).
  Proof. intros * HMj; unfold mctx_tele; rewrite HMj; reflexivity. Qed.

  (** ** What an Elimination Yields

      An element [mv] of the member [k], its type's non-uniform parameters
      [ns]: the value of the eliminator at it, the value of the motive of
      [k]'s block at it, and the elimination of a term [M'] of it, at the
      instance of the blocks by [σ'], glued at the motive there.  The
      motive is [List.nth k (blocks_motives Bks) a_prop]: every member has
      its block ([blocks_typed_len]), so the default is never taken. *)
  #[warnings="-cannot-define-projection"]
  Record elim_out (k : nat) (Mk : imember) (Δ' : ctx) (σ' : sub) (Ns' : list exp) (M' : exp)
      (mv : domain) (ns : list domain) : Prop := mk_elim_out
    { (** The eliminator's value at [mv] *)
      elim_out_val : domain
      (** The motive's value at [mv] *)
    ; elim_out_motive : domain
      (** The eliminator at [mv] evaluates to [elim_out_val] *)
    ; elim_out_eval : ⟦elim mv at k of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ elim_out_val
      (** The motive of [k]'s block at [ns] and [mv], in [ρ] extended
          along the motive's context, evaluates to [elim_out_motive] *)
    ; elim_out_eval_motive : ⟦ List.nth k (blocks_motives Bks) a_prop ⟧ env_tele ρ (List.rev (elim_mctx p D k Mk Us)) (ns ++ mv :: nil)
        ↘ elim_out_motive
      (** The motive's value is a type of the universe *)
    ; elim_out_per : Dom elim_out_motive ≈ elim_out_motive ∈ per_univ iA
      (** At any gluing of the motive's value, the elimination of [M'] is
          glued to [elim_out_val] *)
    ; elim_out_glu : forall P El, DG elim_out_motive ∈ glu_univ_elem iA ↘ P ↘ El ->
        Δ' ⊢ a_elim ak_relevant p (List.map (fun U => U[σ']) Us) k (blocks_sub Bks σ') M'
          : (List.nth k (blocks_motives Bks) a_prop)[sb_qn (S (im_nn Mk)) σ'][sb_of_list Id (Ns' ++ M' :: nil)] ® elim_out_val ∈ El }.

  (** The motive of the induction on the gluing of an element of the member
      [k] at the uniform parameters [Us'] and non-uniform ones [Ns']: at a
      substitution [σ'] glued to [ρ] that sends [Us] to [Us'], the
      elimination of the element is glued. *)
  Definition elim_prop (k : nat) (Δ' : ctx) (Us' Ns' : list exp) (M' : exp) (mv : domain) : Prop :=
    forall Mk σ' ns, ind_member D k = Some Mk -> im_is_rview Mk = false ->
      Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> Us' = List.map (fun U => U[σ']) Us -> Δ' ⊢ M' : im_ty_at p k Mk Us' Ns' ->
      glu_nparams k Mk NEl Δ' Us' Ns' ns -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns ->
      G k ups ups ns ns mv mv ->
      elim_out k Mk Δ' σ' Ns' M' mv ns.

  (** The context of the components of a recursive argument's shape: the
      first [d] domains of its shape [t0], the non-recursive arguments
      [gs1] before it and the parameters of its member [Mk]. *)
  Definition arg_shape_ctx (Mk : imember) (gs1 : list carg) (t0 : ptyp) (d : nat) : ctx :=
    doms_ctx (List.firstn d (ptyp_doms t0)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk.

  (** Where a recursive argument sits: at the constructor [c0] of the
      member [k], after the arguments [gs1], of shape [t0], past [d] of its
      domains, the values [pre] of its components related to themselves,
      eliminated at a substitution [σ'] glued to [ρ]. *)
  #[warnings="-cannot-define-projection"]
  Record elim_arg_context (k : nat) (Mk : imember) (ms : list domain) (c0 : String.string) (gs1 : list carg) (t0 : ptyp)
      (gs2 : list carg) (ws : list domain) (d : nat) (ys : list domain) (pre : list domain) (Ts : list centry) (t : ptyp)
      (σ' : sub) (Δ' : ctx) (Us' : list exp) : Prop := mk_elim_arg_context
    { (** [Mk] is the member [k] *)
      arg_ctx_member : ind_member D k = Some Mk
      (** The argument is the recursive one after [gs1] of [c0] *)
    ; arg_ctx_con : ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2)
      (** The components' values: the non-uniform parameters [ms], the
          non-recursive arguments [ws] before, the domains' [ys] *)
    ; arg_ctx_pre : pre = ms ++ ws ++ ys
      (** Their telescope: the non-uniform parameters', the non-recursive
          arguments' before, and the first [d] domains' *)
    ; arg_ctx_tele : Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn d (shape_doms_tele t0)
      (** The non-uniform parameters are related to themselves *)
    ; arg_ctx_nparams : tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms
      (** So are the non-recursive arguments before *)
    ; arg_ctx_args : tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws
      (** [t] is the rest of [t0] past [d] domains *)
    ; arg_ctx_skip : ptyp_skip d t0 = t
      (** [t0] has [d] domains at least *)
    ; arg_ctx_depth : d <= ptyp_depth t0
      (** The domains' values are related to themselves *)
    ; arg_ctx_doms : tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t0) d ys ys
      (** [σ'] is glued to [ρ] *)
    ; arg_ctx_sub : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ
      (** It sends [Us] to [Us'] *)
    ; arg_ctx_uparams : Us' = List.map (fun U => U[σ']) Us }.

  (** The motive at a recursive argument [N] of shape [t], its components
      at [σs], the values [pre] of them, in the context [elim_arg_context]
      gives: its recursive result along each leaf path whose end member
      satisfies [ok] is glued at the type of the result there, and so at
      equal substitutions and arguments.  The elimination of an element
      takes [ok] true everywhere; a neutral argument read back under fresh
      variables takes the members whose stuck eliminator reads back
      ([rec_neut_all]). *)
  Definition rec_prop (ok : nat -> Prop) (k : nat) (Δ' : ctx) (Us' : list exp) (pre : list domain) (Ts : list centry) (t : ptyp)
      (σs : sub) (N : exp) (v : domain) : Prop :=
    forall Mk ms c0 gs1 t0 gs2 ws d ys σ',
      elim_arg_context k Mk ms c0 gs1 t0 gs2 ws d ys pre Ts t σ' Δ' Us' ->
      forall σs' N' rs,
      Δ' ⊢ˢ σs : arg_shape_ctx Mk gs1 t0 d -> Δ' ⊢ˢ σs ≈ σs' : arg_shape_ctx Mk gs1 t0 d ->
      shape_uc D Us (arg_shape_ctx Mk gs1 t0 d) σs σ' ->
      Δ' ⊢ N ≈ N' : ptyp_ty_at p D Us' σs t ->
      rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k ups ups pre pre Ts t v v ->
      ⟦ih v of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rs ->
      forall idx l r a (j : nat) R P El,
      List.nth_error (shape_leaves (rview_leaves D) (im_nn Mk + List.length (cargs_nonrec gs1) + d) t) idx = Some l ->
      ok (leaf_mem l) ->
      List.nth_error rs idx = Some r ->
      Elim.leaf_type_at D ups ρ (blocks_motives Bks) mctx_tele pre Ts t v idx a ->
      DF a ≈ a ∈ per_univ_elem j ↘ R -> R r r -> iA <= j -> nb <= j ->
      DG a ∈ glu_univ_elem j ↘ P ↘ El ->
      Δ' ⊢ leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σ')) Id σs' N' l : Typeω@j ->
      Δ' ⊢ leaf_ih ak_relevant p Us' (blocks_sub Bks σ') σs' N' l
        : leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σ')) Id σs' N' l ® r ∈ El.

  (** At the record view [Mk] (the member [k]) of one constructor [c] of
      arguments [gs], the recursive results of an element [M'] whose
      projections have the values [ws]: [M'] is the constructor at fields
      typed along its telescope, whose recursive ones have [rec_prop] at
      their shapes, along the leaf paths whose end member satisfies
      [ok]. *)
  #[warnings="-cannot-define-projection"]
  Record rview_ihs_at (ok : nat -> Prop) (k : nat) (Mk : imember) (c : String.string) (gs : list carg) (Δ' : ctx)
      (Us' : list exp) (M' : exp) (ws : list domain) : Prop := mk_rview_ihs_at
    { (** The fields *)
      rview_ihs_args : list exp
      (** One per argument *)
    ; rview_ihs_len : List.length rview_ihs_args = List.length gs
      (** [M'] is the constructor at them *)
    ; rview_ihs_eq : Δ' ⊢ M' ≈ apps (a_con p k c) (Us' ++ rview_ihs_args) : im_ty_at p k Mk Us' nil
      (** Each typed along the constructor's telescope *)
    ; rview_ihs_typed : forall j N T, List.nth_error rview_ihs_args j = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Us') rview_ihs_args) j = Some T -> Δ' ⊢ N : T
      (** A recursive one has [rec_prop] at its shape, at the projections'
          values before it *)
    ; rview_ihs_rec : forall gs1 tf gs2 N A w, gs = gs1 ++ ca_rec tf :: gs2 ->
        List.nth_error rview_ihs_args (List.length gs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Us') rview_ihs_args) (List.length gs1) = Some A ->
        List.nth_error ws (List.length gs1) = Some w ->
        forall σs, A = ptyp_ty_at p D Us' σs tf ->
        rec_prop ok k Δ' Us' (nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws)) (cargs_nonrec_tele gs1) tf σs N w }.

  (** At a record view [k], the recursive results of an element [M'] of
      value [mv]: [rview_ihs_at], at [mv]'s projections. *)
  Definition rview_ihs_prop (ok : nat -> Prop) (k : nat) (Δ' : ctx) (Us' : list exp) (M' : exp) (mv : domain) : Prop :=
    forall Mk qr Is fl c gs ws, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      im_cons Mk = (c, gs) :: nil -> ⟦projs fl of mv ⟧ gc_deps ⍮ gc_stack ↘ ws ->
      rview_ihs_at ok k Mk c gs Δ' Us' M' ws.

  (** The neutral case at the member [j], which the induction on the ranks
      of the members proves. *)
  Definition neut_ok (j : nat) : Prop :=
    forall Mj hd k' as' e Δ' Us' Ns' M', ind_member D j = Some Mj -> im_ref p j Mj = (hd, k') -> Dom e ≈ e ∈ per_bot ->
      (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         glu_ne_eq Δ M'[φ]ʷ M0 (im_ty_at p j Mj Us' Ns')[φ]ʷ) ->
      elim_prop j Δ' Us' Ns' M' (⇑ (d_ind hd k' as') e).

  (** ** The Uniform Parameters *)

  Lemma ups_len : List.length ups = ind_nu D.
  Proof. rewrite (Completeness.Inductives.Model.eval_exps_length _ _ _ HUv); exact HUl. Qed.

  Lemma ups_tele_args : per_tele_args (List.rev (ind_uparams D)) nil nil ups ups.
  Proof. exact (EB Elim.u0_tele_args). Qed.

  Lemma ups_RU : RU (decl_env D ups) (decl_env D ups).
  Proof. exact (EB Elim.u0_env). Qed.

  (** The uniform parameters at a substitution glued to [ρ], glued at
      their telescope at [ups]. *)
  Lemma us_glu_args : forall Δ σ, Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
      glu_args Δ (ind_uparams D) Id nil (List.map (fun U => U[σ]) Us) ups.
  Proof.
    intros * Hσ.
    eapply params_glu_args; [ exact Ua | exact (decl_closed_uparams _ Hc) | exact Usem | exact HΓ | exact HRΓ | exact HSbΓ | exact Hσ
                            | rewrite HUl; reflexivity | exact HUs | exact (valid_ind_decl_uparams_evaluated _ HD) | exact HUss
                            | exact HUg | exact HUv ].
  Qed.

  (** ** The PER Model at [ρ]

      The canonical relations at [ups], and the family of the motives at
      [ρ] on both sides: the eliminator at related elements, and its
      recursive results, are related at it ([per_ind_elim_all]). *)
  Let Hcp := valid_group_canon p D Hvg ups ups_tele_args ups_len.
  #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
  Let Had := valid_group_adm p D Hvg ups ups ups_tele_args ups_len ups_tele_args.
  Let Hups := EB Elim.ups_ok ups ups ups_RU ups_RU ups_len ups_len.
  Let Hnm : blocks_binder_count_ok D Bks := valid_blocks_binder_count _ _ _ _ _ _ HBv.
  Let Hna := valid_blocks_names _ _ _ _ _ _ HBv.
  Let Har := valid_blocks_arity _ _ _ _ _ _ HBv.
  Let Hnd := decl_typed_nodup _ _ _ Hdt.
  (** The record views' leaf paths agree with their fields' shapes. *)
  Let Hco : leaves_coherent D := leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_record_struct _ _ _ Hdt)).
  #[local] Abbreviation Rel := (fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_prop) (List.nth j (blocks_motives Bks) a_prop)
      (env_tele ρ (mctx_tele j) (ns ++ m :: nil)) (env_tele ρ (mctx_tele j) (ns' ++ m' :: nil))).

  (** The motives at [ρ], at related indices and elements stored at any
      types they read back at ([Elim.motive_mid]). *)
  Lemma motive_rel : forall j Mj ba bb u u' ns ns' m m' ts ts', ind_member D j = Some Mj -> im_is_rview Mj = false ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> G j u u' ns ns' m m' ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts' ->
      exists a a', ⟦ eb_motive ba ⟧ env_extend_typed ρ (List.combine (ns ++ m :: nil) ts) ↘ a /\
        ⟦ eb_motive bb ⟧ env_extend_typed ρ (List.combine (ns' ++ m' :: nil) ts') ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns m ns' m' /\ not_level_sort a /\ domain_kind a <> ak_level.
  Proof.
    intros * HMj _ Hba Hbb Hm Ht Ht'; rewrite Hba in Hbb; injection Hbb as <-.
    exact (EB Elim.motive_mid ρ Hρ Bks iA HMall j Mj ba (eb_motive ba) HMj Hba (HAv _ _ _ HMj Hba) _ _ _ _ _ _ _ _ Hm Ht Ht').
  Qed.

  (** Related indices and elements read back at some types ([Elim.mctx_idx_readable]). *)
  Lemma motive_idx_readable : forall j Mj u u' ns ns' m m', ind_member D j = Some Mj -> im_is_rview Mj = false -> G j u u' ns ns' m m' ->
      (exists ts, List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts) /\
      (exists ts', List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts').
  Proof. intros * HMj _ Hm; exact (EB Elim.mctx_idx_readable HMall j Mj _ _ _ _ _ _ HMj Hm). Qed.

  (** The branches at [ρ] ([Elim.branch_mid]). *)
  Lemma branch_rel : forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k' ts ts', ind_member D j = Some Mj ->
      im_is_rview Mj = false ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> ind_con Mj c = Some gs ->
      brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
      G j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
      rec_results_rel D dr Rel j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (List.rev (im_nparams Mj)) gs
        vs vs' ihs ihs' ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts' ->
      exists r r', ⟦ Ba ⟧ env_extend_typed ρ (List.combine (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts) ↘ r /\
        ⟦ Bb ⟧ env_extend_typed ρ (List.combine (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts') ↘ r' /\
        Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs)) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r'.
  Proof.
    refine (EB Elim.branch_mid ρ Hρ Bks iA HBks HMall HAv (valid_blocks_bctx _ _ _ _ _ _ HBv) Bks _).
    intros * HMj Hb Hb' Hcon HlB HlB'; rewrite Hb in Hb'; injection Hb' as <-.
    rewrite HlB in HlB'; injection HlB' as <-.
    exact (valid_blocks_branch _ _ _ _ _ _ HBv _ _ _ _ _ _ _ HMj Hb Hcon (brs_lookup_in _ _ _ _ HlB)).
  Qed.

  #[local] Abbreviation ER f := (f p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had (ul iA) ρ ρ Bks Bks ups ups Hups Rel
     HBks HBks Hnm Hnm Hna Hna Har Har Hnd motive_rel motive_idx_readable (EB Elim.rneut_rel ups ups ups_RU ups_RU ups_len ups_len)
     branch_rel).
  (** The eliminator's PER facts at [ρ] and [ups] ([per_ind_elim_all]); a
      definition, so that its statement stays out of proof contexts. *)
  Definition per_elim_at_ups := ER per_ind_elim_all.

  (** ** Instances of Closed Telescopes at [ρ]

      A type of a closed telescope over the uniform parameters, at its
      instance at [τU] in [ρ] extended by values related at the telescope
      at [ups], against the type at [ups] and those values. *)
  Lemma inst_link : forall Pre X Srt zs, type_sort Srt -> all_assumptions (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
      ⊨ tele_sub Pre τU ++ Γ -> Pre ++ ind_uparams D ⊨ X : Srt ->
      per_tele_args (List.rev Pre) (decl_env D ups) (decl_env D ups) zs zs -> List.length zs = List.length Pre ->
      exists a b (j' : nat), ⟦ X[sb_qn (List.length Pre) τU] ⟧ env_tele ρ (List.rev (tele_sub Pre τU)) zs ↘ a /\
        ⟦ X ⟧ components_env D ups (List.rev Pre) zs ↘ b /\ Dom a ≈ b ∈ per_univ j'.
  Proof.
    intros * HSrt HKa HK HS HX Hg Hlz.
    pose proof (EB Elim.canonical_gen Pre HKa HK HS ρ ρ ups ups Hρ HUv HUv ups_RU ups_RU zs zs Hg Hlz) as Hg'.
    destruct (rel_ctx_wf_per_ctx_env HS) as [RS HRS].
    pose proof (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS HS Hρ ltac:(rewrite length_tele_sub; exact Hlz) Hg') as HE.
    rewrite env_tele_extend_typed in HE.
    destruct (rel_ctx_wf_per_ctx_env HK) as [RK HRK].
    destruct (per_tele_args_entries_readable _ _ _ _ _ Hg') as [Hrd _].
    pose proof (EB Elim.closed_pre_base Pre RK HKa HK HRK ρ ups (tele_entries ρ (List.rev (tele_sub Pre τU)) zs) zs Hρ HUv ups_RU
                  Hg Hlz (tele_entries_values _ _ _) Hrd) as HF.
    destruct (closed_typ_inst Pre (ind_uparams D) Γ X Srt τU RΓ RK RS ρ (tele_entries ρ (List.rev (tele_sub Pre τU)) zs) _
                (components_env D ups (List.rev Pre) zs) HKa HK Ua Usem HΓ HRΓ HRK HRS HSrt HX
                (Instance.gsub_valid (Elim.gsub_U VP p D HVP HPD Γ HΓ Us HUl HUs HUss)) HE
                ltac:(rewrite Decl.tele_entries_length; exact Hlz)
                (GE Elim.uniform_params_sub_eval ρ ρ ups Hρ HUv) HF) as (j' & a & b & Ea & Eb & Hab).
    rewrite <- env_tele_extend_typed in Ea.
    exists a, b, j'; split; [ exact Ea | split; [ exact Eb | exact Hab ] ].
  Qed.

  (** The type of an entry of the instance at [τU] of a closed telescope,
      against the entry's type at [ups]. *)
  Lemma inst_entry_link : forall C, all_assumptions (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D -> ⊨ tele_sub C τU ++ Γ ->
      forall zs, per_tele_args (List.rev C) (decl_env D ups) (decl_env D ups) zs zs -> List.length zs = List.length C ->
      forall k κ' A' a, List.nth_error (List.rev (tele_sub C τU)) k = Some (ce_ass κ' A') ->
        ⟦ A' ⟧ env_tele ρ (List.rev (tele_sub C τU)) (List.firstn k zs) ↘ a ->
        exists κ A b (j : nat), List.nth_error (List.rev C) k = Some (ce_ass κ A) /\
          ⟦ A ⟧ components_env D ups (List.rev C) (List.firstn k zs) ↘ b /\ Dom a ≈ b ∈ per_univ j.
  Proof.
    intros C HCa HCs HCS zs Hpg Hlz k κ' A' a HA' Ea.
    assert (HCa' : all_assumptions C) by (unfold all_assumptions in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
    assert (HeA : exists κ A, e = ce_ass κ A).
    { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
      unfold all_assumptions in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
    destruct HeA as (κ & A & ->).
    pose proof He as He0.
    destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
    rewrite <- HPl in HA'; rewrite nth_rev_tele_sub in HA'; injection HA' as <- <-.
    assert (ErC : List.rev (C1 ++ ce_ass κ A :: Pre) = List.rev Pre ++ (ce_ass κ A :: nil) ++ List.rev C1)
      by (rewrite List.rev_app_distr; cbn [List.rev]; rewrite <- !List.app_assoc; reflexivity).
    assert (ErS : List.rev (tele_sub (C1 ++ ce_ass κ A :: Pre) τU)
                  = List.rev (tele_sub Pre τU) ++ List.rev (tele_sub (C1 ++ ce_ass κ A :: nil) (sb_qn (List.length Pre) τU)))
      by (rewrite <- List.rev_app_distr, <- tele_sub_app; f_equal; rewrite <- List.app_assoc; reflexivity).
    rewrite ErS, env_tele_app_long in Ea by (rewrite List.length_firstn, List.length_rev, length_tele_sub; lia).
    rewrite <- List.app_assoc in HCa, HCs; cbn [List.app] in HCa, HCs.
    assert (HKa : all_assumptions (Pre ++ ind_uparams D))
      by (unfold all_assumptions in HCa; apply List.Forall_app in HCa as [_ H]; inversion H; assumption).
    pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCs) as HK1.
    destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HK1) as (Srt & HSk & HX).
    pose proof (rel_ctx_wf_tail HK1) as HK.
    rewrite tele_sub_app, <- List.app_assoc in HCS; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCS) as HS1.
    cbn [tele_sub List.app] in HS1; pose proof (rel_ctx_wf_tail HS1) as HS.
    rewrite ErC in Hpg; rewrite <- (List.firstn_skipn k zs) in Hpg.
    rewrite !List.length_app in Hlz; cbn in Hlz.
    assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_firstn, List.length_rev; lia).
    destruct (Decl.per_tele_args_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
      as [Hg1 _].
    destruct (inst_link Pre A Srt (List.firstn k zs) (sort_kind_type_sort _ _ HSk) HKa HK HS HX Hg1
                ltac:(rewrite List.length_firstn; lia)) as (a1 & b & j & Ea1 & Eb & Hab).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    exists κ, A, b, j; split; [ exact He0 | split; [| exact Hab ] ].
    unfold components_env; rewrite ErC, env_tele_app_long by (rewrite List.length_firstn, List.length_rev; lia); exact Eb.
  Qed.

  (** Glued arguments of a closed telescope over the uniform parameters,
      at its types at [ups], are glued arguments of its instance at [τU],
      over a substitution glued to [ρ]. *)
  Lemma tele_inst_args : forall C, all_assumptions (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D ->
      ⊨ tele_sub C τU ++ Γ -> ctx_scoped (ind_nu D) C ->
      forall Δ' σ' Ms zs, glu_args Δ' C (sb_of_list Id (List.map (fun U => U[σ']) Us)) (decl_env D ups) Ms zs ->
        per_tele_args (List.rev C) (decl_env D ups) (decl_env D ups) zs zs ->
        glu_args Δ' (tele_sub C τU) σ' ρ Ms zs.
  Proof.
    intros C HCa HCs HCS HCsc Δ' σ' Ms zs Hg Hpg.
    assert (HCa' : all_assumptions C) by (unfold all_assumptions in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [LM Lz].
    apply (glu_args_link Δ' C (tele_sub C τU) (sb_of_list Id (List.map (fun U => U[σ']) Us)) σ' (decl_env D ups) ρ Ms zs);
      [ rewrite length_tele_sub; reflexivity | | exact Hg | |].
    - rewrite tele_insts_tele_sub; symmetry; apply (tele_insts_base_agree _ (ind_nu D)); [ exact HCa' | exact HCsc |].
      intros x Hx; cbn [sb_compose]; unfold τU; apply sb_of_list_lt_compose; lia.
    - intros k κ A κ' A' a HA HA' Hk Ea.
      destruct (ctx_rev_split C k _ HA) as (C1 & Pre & -> & HPl).
      rewrite <- HPl in HA'; rewrite nth_rev_tele_sub in HA'; injection HA' as <- <-.
      assert (ErC : List.rev (C1 ++ ce_ass κ A :: Pre) = List.rev Pre ++ (ce_ass κ A :: nil) ++ List.rev C1)
        by (rewrite List.rev_app_distr; cbn [List.rev]; rewrite <- !List.app_assoc; reflexivity).
      assert (ErS : List.rev (tele_sub (C1 ++ ce_ass κ A :: Pre) τU)
                    = List.rev (tele_sub Pre τU) ++ List.rev (tele_sub (C1 ++ ce_ass κ A :: nil) (sb_qn (List.length Pre) τU)))
        by (rewrite <- List.rev_app_distr, <- tele_sub_app; f_equal; rewrite <- List.app_assoc; reflexivity).
      rewrite <- List.app_assoc in HCa, HCs; cbn [List.app] in HCa, HCs.
      assert (HKa : all_assumptions (Pre ++ ind_uparams D))
        by (unfold all_assumptions in HCa; apply List.Forall_app in HCa as [_ H]; inversion H; assumption).
      pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCs) as HK1.
      destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HK1) as (Srt & HSk & HX).
      pose proof (rel_ctx_wf_tail HK1) as HK.
      rewrite tele_sub_app, <- List.app_assoc in HCS; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCS) as HS1.
      cbn [tele_sub List.app] in HS1; pose proof (rel_ctx_wf_tail HS1) as HS.
      rewrite ErC in Hpg; rewrite <- (List.firstn_skipn k zs) in Hpg.
      assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_rev, List.length_firstn; lia).
      destruct (Decl.per_tele_args_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
        as [Hg1 _].
      destruct (inst_link Pre A Srt (List.firstn k zs) (sort_kind_type_sort _ _ HSk) HKa HK HS HX Hg1
                  ltac:(rewrite List.length_firstn; lia)) as (a1 & b & j & Ea1 & Eb & Hab).
      rewrite ErC, env_tele_app_long in Ea by (rewrite List.length_firstn, List.length_rev; lia).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      rewrite ErS, env_tele_app_long by (rewrite List.length_firstn, List.length_rev, length_tele_sub; lia).
      exists a1, j; split; assumption.
    - intros k e' He'.
      assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
      assert (HeA : exists κ A, e = ce_ass κ A).
      { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
        unfold all_assumptions in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
      destruct HeA as (κ & A & ->).
      destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
      rewrite <- HPl in He'; rewrite nth_rev_tele_sub in He'; injection He' as <-.
      exists κ, A; split; [ exact He | do 2 eexists; reflexivity ].
  Qed.

  (** The canonical environment of a closed telescope over the uniform
      parameters, at values related at it at [ups], is in the telescope's
      PER: it is related to the environment of the instance at [τU] in [ρ]
      ([Elim.closed_pre_base]). *)
  Lemma components_env_rel : forall Pre RK, all_assumptions (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
      EF Pre ++ ind_uparams D ≈ Pre ++ ind_uparams D ∈ per_ctx_env ↘ RK -> ⊨ tele_sub Pre τU ++ Γ ->
      forall zs, per_tele_args (List.rev Pre) (decl_env D ups) (decl_env D ups) zs zs -> List.length zs = List.length Pre ->
      RK (components_env D ups (List.rev Pre) zs) (components_env D ups (List.rev Pre) zs).
  Proof.
    intros * HKa HK HRK HS zs Hg Hlz.
    pose proof (EB Elim.canonical_gen Pre HKa HK HS ρ ρ ups ups Hρ HUv HUv ups_RU ups_RU zs zs Hg Hlz) as Hg'.
    destruct (per_tele_args_entries_readable _ _ _ _ _ Hg') as [Hrd _].
    pose proof (EB Elim.closed_pre_base Pre RK HKa HK HRK ρ ups _ zs Hρ HUv ups_RU Hg Hlz (tele_entries_values _ _ _) Hrd) as HF.
    assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
    etransitivity; [ symmetry; exact HF | exact HF ].
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
      Δ' ⊢ˢ sb_of_list σ' (Ns' ++ M' :: nil) ® env_tele ρ (List.rev (elim_mctx p D j Mj Us)) (ns ++ m :: nil) ∈ SbM.
  Proof.
    intros j Mj SbM HMj HSbM * Hσ' Hgn Hns Hr Hgl.
    pose proof (HMall _ _ HMj) as HMm.
    pose proof (rel_ctx_wf_tail HMm) as HNt.
    pose proof (member_params_ass D Hc _ _ HMj) as HPa.
    pose proof (valid_ind_decl_params _ HD _ _ HMj) as HPs.
    pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf j Mj Δ' _ Ns' ns HMj Hgn Hns) as Hg0.
    pose proof (EB Completeness.Inductives.Elim.nparams_closed_of_canon j Mj HMj ns ns Hns) as Hpg.
    pose proof (tele_inst_args (im_nparams Mj) HPa HPs HNt (decl_closed_nparams_scoped D Hc j Mj HMj) Δ' σ' Ns' ns Hg0 Hpg) as Hg1.
    destruct (glu_args_length _ _ _ _ _ _ Hg1) as [LN Ln]; rewrite length_tele_sub, length_im_nparams in LN, Ln.
    assert (HassN : all_assumptions (tele_sub (im_nparams Mj) τU)) by (apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMj)).
    eapply glu_sub_of_list; [ exact (elim_mctx_ass p D j Mj Us Hc HMj) | exact HSbM | exact HSbΓ | exact Hσ' |].
    unfold elim_mctx; change (ce_ass ?k0 ?H0 :: ?R) with ((ce_ass k0 H0 :: nil) ++ R).
    apply glu_args_app; [ exact HassN | rewrite length_tele_sub, length_im_nparams; exact LN
                        | rewrite length_tele_sub, length_im_nparams; exact Ln |].
    split; [ exact Hg1 |].
    change (ce_ass ?k0 ?H0 :: nil) with (nil ++ ce_ass k0 H0 :: nil).
    apply (proj2 (glu_args_snoc _ nil _ _ _ _ _ _ _ _)); split; [| apply glu_args_nil ].
    rewrite (mty_inst j Mj σ' Ns' HMj LN).
    (** The type's value at [ρ] and [ns], against the scrutinee's. *)
    destruct (Completeness.Inductives.Elim.mty_vars_valid p D Hvg Hcv j Mj HMj) as [jx HX].
    destruct (inst_link (im_nparams Mj) _ _ ns ltac:(constructor) HPa HPs HNt HX Hpg ltac:(rewrite length_im_nparams; exact Ln))
      as (a & b & j0 & Ea & Eb & Hab).
    unfold τU in Ea; rewrite length_im_nparams, (Completeness.Inductives.Elim.mty_vars_inst p D j Mj Us Hc HUl) in Ea.
    destruct (rel_ctx_wf_per_ctx_env HPs) as [RK HRK].
    assert (HKE : RK (components_env D ups (List.rev (im_nparams Mj)) (ns ++ nil)) (components_env D ups (List.rev (im_nparams Mj)) (ns ++ nil)))
      by (rewrite List.app_nil_r; exact (components_env_rel _ _ HPa HPs HRK HNt ns Hpg ltac:(rewrite length_im_nparams; exact Ln))).
    rewrite <- (List.app_nil_r ns) in Eb.
    destruct (mty_val_rel VP HVP p D HPD ups ups_len ups_tele_args j Mj hd k' pre (im_nparams Mj) RK ns nil 0 b ns HMj Hr HPs HRK
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
    pose proof (mty_glu VP HVP HGall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_tele_args Hbu Hule Hf nb Hnbu Hnbq
                  j Mj hd k' pre Δ' _ Ns' ns i P El ltac:(unfold i; lia) HMj Hr HΔ' (us_glu_args Δ' σ' Hσ') Hgn Hns Hglu) as HTP.
    pose proof (Hgl i P El ltac:(unfold i; lia) Hglu HTP) as HMg.
    destruct (glu_transfer_per_elem i n0 _ _ P El Δ' _ M' m Hglu Hda HTP HMg) as (k1 & P1 & El1 & Hg1' & HP1 & HM1).
    exact (mk_glu_arg _ _ _ _ _ _ k1 a P1 El1 Ea Hg1' HP1 HM1).
  Qed.

  (** The motive of the member [j]'s block at glued non-uniform parameters
      and scrutinee: its value, and its instance glued at any gluing of
      it. *)
  Lemma motive_glu : forall j Mj Δ' σ' Ns' ns M' m hd k' pre, ind_member D j = Some Mj -> im_is_rview Mj = false ->
      Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      glu_nparams j Mj NEl Δ' (List.map (fun U => U[σ']) Us) Ns' ns ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      (forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
         Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
         Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® m ∈ El) ->
      exists a, ⟦ List.nth j (blocks_motives Bks) a_prop ⟧ env_tele ρ (List.rev (elim_mctx p D j Mj Us)) (ns ++ m :: nil) ↘ a /\
        Dom a ≈ a ∈ per_univ iA /\
        forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
          Δ' ⊢ (List.nth j (blocks_motives Bks) a_prop)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)] ® P.
  Proof.
    intros * HMj Hrv Hσ' Hgn Hns Hr Hgl.
    destruct (HBks _ _ HMj Hrv) as [b Hb]; rewrite (blocks_motives_nth _ _ _ Hb).
    pose proof (glu_blocks_motive _ _ _ _ _ _ HBg _ _ _ HMj Hb) as HAg.
    destruct HAg as [SbM HSbM iM HAg'].
    pose proof (mctx_glu_sub j Mj SbM HMj HSbM Δ' σ' Ns' ns M' m hd k' pre Hσ' Hgn Hns Hr Hgl) as Hτ.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM (glu_blocks_motive _ _ _ _ _ _ HBg _ _ _ HMj Hb) Hτ) as (_ & a & Ea & Hpa & HPa).
    exists a; split; [ exact Ea | split; [ exact Hpa |] ].
    intros P El Hg; pose proof (HPa P El Hg) as H.
    rewrite <- exp_sub_qn_of_list in H.
    pose proof (glu_nparams_len _ _ _ _ _ _ _ Hgn) as LN.
    replace (List.length (Ns' ++ M' :: nil)) with (S (im_nn Mj)) in H by (rewrite List.length_app, LN; cbn; lia).
    exact H.
  Qed.

  (** ** Recursive Results

      The shape of a recursive argument in its context: the member it
      ends in, and its domains and parameters typed past the domains
      before. *)
  Lemma arg_shape_facts : forall k Mk ms c0 gs1 t0 gs2 ws d ys pre Ts t σ' Δ' Us',
      elim_arg_context k Mk ms c0 gs1 t0 gs2 ws d ys pre Ts t σ' Δ' Us' ->
      exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj /\
        shape_doms_typed gc_deps gc_stack D Mk (List.firstn d (ptyp_doms t0)) (cargs_nonrec_ctx gs1) t /\
        shape_leaf_typed gc_deps gc_stack D Mk Mj (List.firstn d (ptyp_doms t0)) (cargs_nonrec_ctx gs1) t.
  Proof.
    intros * [HMk Hc0 _ _ _ _ Hsk Hdp _ _ _].
    destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ Hdt HMk (cons_lookup_in _ _ _ Hc0) eq_refl) as (Mj & HMj & HPl & HBd & HPt).
    exists Mj; subst t; rewrite ptyp_mem_skip, ptyp_ps_skip.
    split; [ exact HMj | split; [ exact HPl |] ].
    split; [ exact (shape_doms_typed_skip _ _ _ _ _ _ _ HBd) | exact (shape_leaf_typed_skip _ _ _ _ _ _ _ _ Hdp HPt) ].
  Qed.

  (** At the end of a shape, the recursive result is the eliminator at the
      argument, an element of the member the shape ends in. *)
  Lemma rec_self_case : forall ok k Δ' Us' pre Ts j0 Mj Ps A N v, ind_member D j0 = Some Mj -> im_is_rview Mj = false ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bsr -> A = im_ty_at p j0 Mj Us' Q ->
         List.length Q = im_nn Mj /\ tele_rel (nr j0) (List.rev (im_nparams Mj)) bsr bsr /\
         (forall bsr', tele_rel (nr j0) (List.rev (im_nparams Mj)) bsr bsr' ->
            glu_nparams j0 Mj NEl Δ' Us' Q bsr' /\
            forall Δ φ, Δ ⊢ᵏ φ : Δ' -> glu_params_top D Mj Δ (List.map (fun P => P[φ]ʷ) (Us' ++ Q)) (ups ++ bsr'))) ->
      (ok j0 -> forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bsr -> A = im_ty_at p j0 Mj Us' Q ->
         forall Δ φ Us'' Q', Δ ⊢ᵏ φ : Δ' -> List.length Us'' = ind_nu D ->
           exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us' ++ Q)) (Us'' ++ Q') ->
           elim_prop j0 Δ Us'' Q' N[φ]ʷ v) ->
      forall σs, A = ptyp_ty_at p D Us' σs (pt_self j0 Ps) -> rec_prop ok k Δ' Us' pre Ts (pt_self j0 Ps) σs N v.
  Proof.
    intros * HMj Hrv Hs1 IH σs HA; unfold rec_prop.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σ' Hctx σs' N' rs Hσt Hσσ Huc HN Hsh Er idx l r a j R P El Hleaf Hok Hr Hlt HR Hrr
      HiAj Hnbj Hg HIT.
    pose proof Hctx as [HMk Hc0 Hpre Hts Hms Hws Hsk Hdp Hys Hσ' HUs'].
    cbn [shape_leaves] in Hleaf; rewrite (rview_leaves_not_rview _ _ _ HMj Hrv) in Hleaf.
    destruct idx as [| idx]; [| destruct idx; discriminate ]; cbn in Hleaf; injection Hleaf as <-.
    specialize (IH Hok).
    destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs0 & Ebs & Ebs0 & _ & _ & Hir).
    pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->.
    (** The recursive result: the eliminator at the argument. *)
    assert (Er' : ⟦elim v at j0 of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r).
    { inversion Er; subst.
      - cbn in Hr; injection Hr as <-; assumption.
      - match goal with H0 : ind_lookup _ _ p = Some ?D0 |- _ => rewrite Hl in H0; injection H0 as <- end.
        match goal with H1 : ind_member D j0 = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
          rewrite HMj in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end. }
    (** Its type: related to the motive at the shape's parameters. *)
    assert (Hlt' : exists b (i0 : nat),
               ⟦ List.nth j0 (blocks_motives Bks) a_prop ⟧ env_tele ρ (List.rev (elim_mctx p D j0 Mj Us)) (bs ++ v :: nil) ↘ b /\
                     Dom a ≈ b ∈ per_univ i0).
    { inversion Hlt; subst.
      - match goal with H : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs1 |- _ => pose proof (functional_eval_exps' _ _ _ _ H Ebs) as -> end.
        match goal with H : ⟦ _ ⟧ env_tele _ (mctx_tele _) _ ↘ _ |- _ => rewrite (mctx_tele_at _ _ HMj) in H end.
        eauto.
      - match goal with H1 : ind_member D j0 = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
          rewrite HMj in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end. }
    destruct Hlt' as (b & i0 & Eb & Hab).
    set (Q := List.map (fun P0 => P0[σs]) Ps) in *.
    assert (HAQ : ptyp_ty_at p D Us' σs (pt_self j0 Ps) = im_ty_at p j0 Mj Us' Q)
      by (cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
    rewrite HAQ in HN.
    destruct (presup_exp_eq HN) as (HΔ' & HN0 & HN1 & _).
    destruct (Hs1 _ Q Ebs (eq_trans HA HAQ)) as (HQl & Hbs & Hgn).
    pose proof (kripke_id _ HΔ') as Hid.
    destruct (Hgn bs Hbs) as [Hgn' Htop].
    assert (HUl' : List.length Us' = ind_nu D) by (rewrite HUs', List.length_map; exact HUl).
    pose proof (IH _ Q Ebs (eq_trans HA HAQ) Δ' wk_id _ Q Hid HUl'
                  ltac:(pose proof (glu_params_top_refl _ _ _ _ _ (Htop _ _ Hid)) as H; rewrite map_wk_id in H; rewrite map_wk_id; exact H)) as HE.
    rewrite exp_wk_id in HE.
    destruct (HE Mj σ' bs HMj Hrv Hσ' HUs' HN0 Hgn' Hbs Hir) as [r' a' Er'' Ea'' Haa Hgl].
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Er'' Er') as ->.
    assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Haa) as (P0 & El0 & Hg0).
    pose proof (Hgl P0 El0 Hg0) as HE0; rewrite <- HUs' in HE0.
    (** The eliminator at [N], against the one at [N'], and their types. *)
    assert (Hσt' : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
    pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt') as HBt'; rewrite <- HUs' in HBt'.
    destruct (HBks _ _ HMj Hrv) as [bj Hbj].
    rewrite (blocks_motives_nth _ _ _ Hbj) in HE0.
    assert (Hbj' : List.nth_error (blocks_sub Bks σ') j0 = Some (eblock_sub bj σ')) by (rewrite nth_error_blocks_sub, Hbj; reflexivity).
    assert (HPl : List.length (Us' ++ Q) = im_np D Mj) by (rewrite List.length_app, HUl', HQl; unfold im_np; lia).
    assert (HPt : forall k0 P1 T0, List.nth_error (Us' ++ Q) k0 = Some P1 -> List.nth_error (tele_insts (im_params D Mj) Id (Us' ++ Q)) k0 = Some T0 ->
                    Δ' ⊢ P1 : T0).
    { intros k0 P1 T0 HP1 HT0; pose proof (glu_params_top_typ _ _ _ _ _ (Htop _ _ Hid)) as Ht; rewrite map_wk_id in Ht; exact (Ht _ _ _ HP1 HT0). }
    assert (Emty : forall Us0 Q0, ind_mty p D j0 Us0 Q0 = im_ty_at p j0 Mj Us0 Q0) by (intros; unfold ind_mty; rewrite HMj; reflexivity).
    assert (HNmty : Δ' ⊢ N ≈ N' : ind_mty p D j0 (List.firstn (ind_nu D) (Us' ++ Q)) (List.skipn (ind_nu D) (Us' ++ Q)))
      by (rewrite firstn_app_exact, skipn_app_exact, Emty by exact HUl'; exact HN).
    pose proof (wf_elim_scrut_eq Δ' p D j0 Mj (eblock_sub bj σ') (blocks_sub Bks σ') (Us' ++ Q) N N' ak_relevant iA Hl HMj Hbj' HPl
                  HPt ltac:(rewrite firstn_app_exact by exact HUl'; exact HBt') HNmty) as E1.
    rewrite firstn_app_exact, skipn_app_exact in E1 by exact HUl'.
    rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMj Hbj) in E1.
    set (Asj := (eb_motive bj)[sb_qn (S (im_nn Mj)) σ']) in *.
    (** The motive at [N], against the one at [N']. *)
    pose proof (blocks_typed_motive _ _ _ _ _ _ _ _ _ HBt' _ _ _ HMj Hbj') as HAt.
    rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMj Hbj) in HAt; fold Asj in HAt.
    pose proof (blocks_mctx_wf _ _ _ _ _ _ _ _ _ HBt' _ _ HMj) as HΨ.
    pose proof (wf_elim_inst_sub_eq _ _ Δ' p D j0 Mj (Us' ++ Q) N N' Hl HMj HΔ' HPl HPt
                  ltac:(rewrite firstn_app_exact, skipn_app_exact, Emty by exact HUl'; exact HN0)
                  ltac:(rewrite firstn_app_exact, skipn_app_exact, Emty by exact HUl'; exact HN1) HNmty
                  ltac:(rewrite firstn_app_exact by exact HUl'; exact HΨ)) as Esub1.
    rewrite firstn_app_exact, skipn_app_exact in Esub1 by exact HUl'.
    pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HAt Esub1) as ET1.
    (** The motive at the parameters at [σs], against those at [σs']. *)
    destruct (arg_shape_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx) as (Mj1 & HMj1 & HPsl & _ & HPst).
    cbn [ptyp_mem ptyp_ps] in HMj1, HPsl, HPst; rewrite HMj in HMj1; injection HMj1 as <-.
    assert (HN1' : Δ' ⊢ N' : ind_mty p D j0 (List.map (fun U => U[σ']) Us) (List.map (fun P1 => P1[σs]) Ps))
      by (rewrite Emty, <- HUs'; exact HN1).
    pose proof (ih_leaf_sub_eq Γ p D j0 Mj Us Δ' (arg_shape_ctx Mk gs1 t0 d) σ' σs σs' Ps N' Hdt Hc HMj HUl
                  (blocks_mctx_wf _ _ _ _ _ _ _ _ _ HBt _ _ HMj) Hσt' Hσt Hσσ Huc HPsl
                  (shape_leaf_at _ _ _ _ _ _ _ _ HPst eq_refl) HN1') as Esub2.
    pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ (blocks_typed_motive _ _ _ _ _ _ _ _ _ HBt _ _ _ HMj Hbj) Esub2) as ET2.
    assert (EL : forall L, List.length L = S (im_nn Mj) -> (eb_motive bj)[sb_of_list σ' L] = Asj[sb_of_list Id L])
      by (intros L HL; unfold Asj; rewrite <- HL, exp_sub_qn_of_list; reflexivity).
    rewrite !EL in ET2 by (rewrite List.length_app, List.length_map; cbn; lia).
    (** The gluing moved along both. *)
    pose proof (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hg0 _ _ _ _ _ HE0 E1) as HE1.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant iA Hg0 (glu_univ_elem_trm_typ _ _ _ _ Hg0 _ _ _ _ HE1)
                (presup_exp_eq_left ET1)) as [Hkb _].
    pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hg0 _ _ _ _ _ HE1
                  ltac:(rewrite Hkb; exact (wf_exp_eq_trans _ _ _ _ _ _ _ ET1 ET2))) as HE2.
    assert (Hab' : Dom b ≈ a ∈ per_univ j) by (apply per_univ_sym'; eapply per_univ_trans'; [ exists R; exact HR | exact Hab ]).
    pose proof (glu_typ_transfer _ _ _ _ _ _ _ _ _ _ _ (ul_mono _ _ HiAj) (universe_index_le_refl _) Hab' Hg0 Hg
                  (glu_univ_elem_trm_typ _ _ _ _ Hg0 _ _ _ _ HE2)) as HT2.
    cbn [leaf_ih leaf_ihty].
    rewrite (blocks_motives_sub D Bks σ' j0 Mj Hnm HMj), (blocks_motives_nth _ _ _ Hbj); fold Asj.
    exact (glu_univ_elem_exp_conv Hab' Hg0 Hg HE2 HT2).
  Qed.

  (** The recursive result of a function shape and its type, under the
      binder, at a weakening and an argument. *)
  Lemma ih_body_inst : forall σ' σs N l φ e,
      (leaf_ih ak_relevant p (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (blocks_wk (blocks_sub Bks σ') ↑)
         (q σs) (a_app N[↑]ʷ (a_var 0)) l)[sb_extend (ι φ) e]
      = leaf_ih ak_relevant p (List.map (fun U => U[sb_wk σ' φ]) Us) (blocks_sub Bks (sb_wk σ' φ))
          (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) l.
  Proof.
    intros; rewrite leaf_ih_sub
      by (first [ exact Hc | rewrite !List.length_map; exact HUl | apply blocks_binder_count_ok_wk, blocks_binder_count_ok_sub, Hnm ]).
    f_equal.
    - rewrite !List.map_map; apply List.map_ext; intros U; rewrite exp_shift_extend_wk_e, exp_wk_sub; reflexivity.
    - apply blocks_step.
    - cbn [exp_sub]; rewrite exp_shift_extend_wk_e; reflexivity.
  Qed.

  (** The type of the recursive result along a leaf path ending in the
      member [Mm], under the binder, at a weakening and an argument. *)
  Lemma ih_cod_inst : forall σ' σs N l φ e Mm, ind_member D (leaf_mem l) = Some Mm ->
      List.length (leaf_ps l) = im_nn Mm ->
      (leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σ')) (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) l)[sb_extend (ι φ) e]
      = leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks (sb_wk σ' φ))) Id (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) l.
  Proof.
    intros * HMm HPl; rewrite leaf_ihty_sub; cbn [exp_sub]; rewrite exp_shift_extend_wk_e.
    rewrite (leaf_ihty_sb_eq _ _ _ _ (ι φ ⨟ Id) _ _ _ (fun z => eq_refl) (fun z => eq_refl)).
    apply leaf_ihty_base.
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
    split; [ exact (valid_ind_decl_params_length _ HD k Mk c0 _ HMk Hc0 gs1 t0 gs2 eq_refl) |].
    destruct (decl_mvc_members _ (decl_typed_mvc _ _ _ Hdt) _ _ HMk) as (_ & _ & Hcm).
    pose proof (Hcm _ _ (cons_lookup_in _ _ _ Hc0)) as Hf0.
    apply List.Forall_app in Hf0 as [_ Hf0]; inversion Hf0 as [| ? ? Hct _]; subst; cbn in Hct; destruct Hct as [Hd Hp].
    split; [| exact Hp ].
    rewrite <- (List.firstn_skipn d (ptyp_doms t0)) in Hd; apply List.Forall_app in Hd as [_ Hd]; exact Hd.
  Qed.

  (** At a domain of a shape, the recursive result is a function of the
      domain, glued at the [Π] by the induction at the rest of the shape. *)
  Lemma rec_pi_case : forall ok k Δ' Us' pre Ts B t A N v,
      (forall IT OT, A = a_pi ak_relevant ak_relevant IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® DP k pre Ts B) ->
      (forall IT OT, A = a_pi ak_relevant ak_relevant IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> dr k pre Ts B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre Ts B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
      (forall IT OT, A = a_pi ak_relevant ak_relevant IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Δ' -> dr k pre Ts B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre Ts B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
         forall σs, OT[(ι φ),,b] = ptyp_ty_at p D (List.map (fun U => U[φ]ʷ) Us') σs t ->
         rec_prop ok k Δ (List.map (fun U => U[φ]ʷ) Us') (pre ++ c :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t σs
           (a_app N[φ]ʷ b) fc) ->
      forall σs, A = ptyp_ty_at p D Us' σs (pt_pi B t) -> rec_prop ok k Δ' Us' pre Ts (pt_pi B t) σs N v.
  Proof.
    intros * Hq1 Hq2 IH3 σs HA; unfold rec_prop.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σ' Hctx σs' N' rs Hσt Hσσ Huc HN Hsh Er idx l r a j R P El Hleaf Hok Hr Hlt HR Hrr
      HiAj Hnbj Hg HIT.
    pose proof Hctx as [HMk Hc0 Hpre Hts Hms Hws Hsk Hdp Hys Hσ' HUs'].
    subst pre Us' Ts.
    destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hsk'].
    (** The leaf path, the result and its type. *)
    cbn [shape_leaves] in Hleaf; apply nth_error_map_inv in Hleaf as (l' & Hl' & ->).
    pose proof (eval_ih_pi_inv _ _ _ _ _ _ _ _ _ Hl Er) as ->.
    rewrite List.nth_error_map in Hr.
    destruct (List.nth_error (List.seq 0 _) idx) as [i' |] eqn:Hi'; [| discriminate ]; injection Hr as <-.
    rewrite List.nth_error_seq in Hi'; destruct (Nat.ltb_spec idx (List.length (shape_leaves (rview_leaves D) 0 t))) as [Hidx |];
      [| discriminate ].
    injection Hi' as <-.
    inversion Hlt as [| | pre0 Ts0 B0 t1 v0 idx0 b0 b ρF F i1 Eb0 Hbb0 Hcl]; subst.
    set (t := ptyp_skip (S d) t0) in *.
    (** The domain, related to the shape's at the components. *)
    destruct (arg_shape_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx) as (Mt & HMt & HPlt & HBd & HPt).
    cbn [ptyp_ty_at] in Hq1, Hq2, IH3, HN.
    set (IT := B[σs]) in *.
    set (OTy := ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (q σs) t) in *.
    specialize (Hq1 _ _ eq_refl); specialize (Hq2 _ _ eq_refl); specialize (IH3 _ _ eq_refl).
    destruct (presup_exp_eq HN) as (HΔ' & HN0 & HN1 & _).
    pose proof HR as HRsave.
    basic_invert_per_univ_elem HR.
    match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
    match goal with H : _ <~> pi_elements _ _ _ _ |- _ => rename H into HRE end.
    match goal with H : domain_kind ?b1 = ak_relevant, H' : not_level_sort ?b1 |- _ => rename H into Hkb; rename H' into Hnlb end.
    destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' ltac:(constructor) Hg) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & HEleq).
    assert (Lys : List.length ys = d) by (apply tele_prefix_rel_iff in Hys; tauto).
    assert (Lms : List.length ms = List.length (im_nparams Mk))
      by (apply tele_rel_iff in Hms; destruct Hms as (Hm0 & _); rewrite List.length_rev in Hm0; exact Hm0).
    assert (Lws : List.length ws = List.length (cargs_nonrec gs1)) by (apply tele_prefix_rel_iff in Hws; tauto).
    assert (Hdl : d < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; rewrite HB; discriminate).
    assert (Eb0' : ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0)
                     (ms ++ ws ++ ys) ↘ b0)
      by (rewrite components_env_shape_prefix, Lys by lia; exact Eb0).
    pose proof (ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hms Hc0 eq_refl Hws HB Hys Eb0') as HgD.
    cbn [leaf_ihty] in HIT; destruct (wf_pi_inversion' HIT) as [HITt HOTt].
    set (IT' := B[σs']) in *.
    (** The domain at [σs], against the one at [σs'], at the level [j]. *)
    assert (HBnb : arg_shape_ctx Mk gs1 t0 d ⊢ B : Typeω@nb).
    { unfold arg_shape_ctx; apply (Hnbd k Mk c0 _ gs1 t0 gs2 _ B (List.skipn (S d) (ptyp_doms t0)) HMk Hc0 eq_refl).
      rewrite <- (skipn_nth_cons' _ _ _ HB), List.firstn_skipn; reflexivity. }
    assert (HITeq : Δ' ⊢ IT ≈ IT' : Typeω@j) by exact (lift_exp_eq_ge _ _ _ _ _ _ _ Hnbj (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HBnb Hσσ)).
    assert (Hbb0j : Dom b0 ≈ b ∈ per_univ j)
      by (apply per_univ_sym'; eapply per_univ_trans'; [ exists in_rel; exact equiv_a_a' | exact Hbb0 ]).
    assert (Huj : universe_index_le u (ul j)) by (eapply universe_index_le_trans; [ exact Hnbu | exact (ul_mono _ _ Hnbj) ]).
    assert (HIT' : forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT'[φ]ʷ ® IP).
    { intros Δ φ Hφ.
      pose proof (glu_typ_transfer _ _ _ _ _ _ _ _ _ _ _ Huj (universe_index_le_refl _) Hbb0j HgD Hgb1 (Hq1 _ _ Hφ)) as HT0.
      eapply glu_univ_elem_typ_resp_exp_eq; [ exact Hgb1 | exact HT0 | rewrite Hkb; exact (kripke_preserves_typ_eq _ _ _ _ _ _ HITeq Hφ) ]. }
    assert (HDEl : forall Δ φ b' c, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b' : IT'[φ]ʷ ® c ∈ IEl ->
                     Δ ⊢ b' : IT[φ]ʷ ® c ∈ DEl k (ms ++ ws ++ ys)
                                (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn d (shape_doms_tele t0)) B).
    { intros * Hφ Hb.
      pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgb1 _ _ _ _ _ Hb
                    ltac:(rewrite Hkb; exact (wf_exp_eq_sym _ _ _ _ _ _ (kripke_preserves_typ_eq _ _ _ _ _ _ HITeq Hφ)))) as Hb'.
      exact (glu_univ_elem_exp_conv_universe_index (per_univ_sym' _ _ _ Hbb0j) Hgb1 HgD Hb' (Hq1 _ _ Hφ)). }
    (** The leaf path's facts. *)
    set (m := S (im_nn Mk + List.length (cargs_nonrec gs1) + d)) in *.
    destruct (rec_shape_facts k Mk c0 gs1 t0 gs2 (S d) HMk Hc0) as (_ & Hmd & Hmp); fold t in Hmd, Hmp.
    assert (Hlp : List.Forall (leaf_params_length D) (shape_leaves (rview_leaves D) m t))
      by (apply shape_leaves_params_length; [ exact (rview_leaves_params_length D Hc) | exists Mt; split; [ exact HMt | exact HPlt ] ]).
    destruct (proj1 (List.Forall_forall _ _) Hlp _ (List.nth_error_In _ _ Hl')) as (Ml & HMl & HPll).
    assert (Hlm : Views.leaf_mvc l').
    { pose proof (Views.shape_leaves_mvc (rview_leaves D) t m (Views.rview_leaves_mvc D (decl_typed_mvc _ _ _ Hdt)) Hmd Hmp) as H0.
      exact (proj1 (List.Forall_forall _ _) H0 _ (List.nth_error_In _ _ Hl')). }
    (** The domain's context, one domain further. *)
    assert (Hctx' : arg_shape_ctx Mk gs1 t0 (S d) = arg_shape_ctx Mk gs1 t0 d ▹{ak_relevant} B)
      by (unfold arg_shape_ctx; rewrite (firstn_S_snoc _ _ _ HB), doms_ctx_snoc; reflexivity).
    assert (HBσ : Δ' ⊢ IT : Typeω@nb) by exact (sub_preserves_exp _ _ _ _ _ _ _ HBnb Hσt).
    assert (HBσσ : Δ' ⊢ IT ≈ IT' : Typeω@nb) by exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HBnb Hσσ).
    set (body := leaf_ih ak_relevant p (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (blocks_wk (blocks_sub Bks σ') ↑)
                   (q σs') (a_app N'[↑]ʷ (a_var 0)) l').
    set (OTi := leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σ')) (Id ⨟ sb_of_wk ↑) (q σs') (a_app N'[↑]ʷ (a_var 0)) l') in *.
    assert (Happ : forall Δ φ b' c (equiv_c : in_rel c c), Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b' : IT'[φ]ʷ ® c ∈ IEl ->
                     exists rc a2, $| d_ihfn ρ Bks p ups t idx v & c | gc_deps ⍮ gc_stack ↘ rc /\ ⟦ F ⟧ ρF ↦ c ⦂ entry_type_value b ↘ a2 /\
                       Δ ⊢ body[(ι φ),,b'] : OTi[(ι φ),,b'] ® rc ∈ OEl c equiv_c).
    { intros * Hφ Hb.
      (** The element of the domain, at the canonical relation. *)
      assert (Hdc : dr k (ms ++ ws ++ ys) (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn d (shape_doms_tele t0)) B c c).
      { destruct Hbb0j as [R1 HR1].
        assert (Hc1 : R1 c c) by (apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ equiv_a_a' HR1); exact equiv_c).
        destruct (per_univ_trans' _ _ _ _ _ (ex_intro _ R1 HR1) (per_univ_sym' _ _ _ (ex_intro _ R1 HR1))) as [R2 HR2].
        assert (Hc2 : R2 c c) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR2); exact Hc1).
        exact (rel_dr D ups k _ _ _ _ _ _ c Eb0 HR2 Hc2). }
      pose proof (HDEl _ _ _ _ Hφ Hb) as HbD.
      destruct (Hq2 _ _ _ _ Hφ Hdc HbD) as [fc Efc].
      destruct (Hcod _ _ equiv_c) as [a2 a2' Ea2 Ea2' Ha22].
      assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
      destruct (pi_elements_app _ _ _ _ _ _ (proj1 (HRE _ _) Hrr) _ _ equiv_c) as [rc rc' Erc Erc' Hrc].
      assert (rc' = rc) as -> by (eapply functional_eval_app; eassumption).
      destruct (eval_app_ihfn_inv _ _ _ _ _ _ _ _ _ _ Erc Efc) as (rs' & Ers' & Hrs').
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hdc) as (r0 & r0' & Er0 & Er0' & Hsh').
      assert (r0 = fc) as -> by (eapply functional_eval_app; eassumption).
      assert (r0' = fc) as -> by (eapply functional_eval_app; eassumption).
      pose proof (Hcl c Hdc a2 fc Ea2 Efc) as Hlt'.
      pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hb) as Hbt.
      pose proof (glu_univ_elem_trm_escape _ _ _ _ HgD _ _ _ _ HbD) as HbtD.
      assert (HUl1 : List.length (List.map (fun U => U[σ']) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
      pose proof (IH3 _ _ _ _ _ Hφ Hdc HbD Efc (q σs ⨟ ((ι φ),,b')) (shape_ty_step VP HVP p D HPD t _ σs φ b' HUl1)) as IH'.
      exists rc, a2; split; [ exact Erc | split; [ exact Ea2 |] ].
      unfold body, OTi; rewrite ih_body_inst, (ih_cod_inst _ _ _ _ _ _ Ml HMl HPll); cbn [sentry_exp].
      replace (List.map (fun U => U[sb_wk σ' φ]) Us) with (List.map (fun U => U[φ]ʷ) (List.map (fun U => U[σ']) Us))
        by (rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub).
      (** The substitution of the components, one domain further. *)
      pose proof (kripke_escape _ _ _ Hφ) as Hφs.
      assert (Hext : Δ ⊢ˢ (ι φ),,b' : Δ' ▹{ak_relevant} IT) by (eapply wf_sub_extend; [ exact Hφs | exact HBσ | constructor | rewrite exp_sub_of_wk; exact HbtD ]).
      assert (Hσt1 : Δ ⊢ˢ q σs ⨟ ((ι φ),,b') : arg_shape_ctx Mk gs1 t0 (S d))
        by (rewrite Hctx'; eapply wf_sub_compose; [ exact (wf_sub_q _ _ _ _ _ _ _ _ Hσt HBnb ltac:(constructor) HBσ) | exact Hext ]).
      assert (Hσσ1 : Δ ⊢ˢ q σs ⨟ ((ι φ),,b') ≈ q σs' ⨟ ((ι φ),,b') : arg_shape_ctx Mk gs1 t0 (S d)).
      { rewrite Hctx'; eapply wf_sub_eq_compose_left; [ eapply wf_sub_eq_q; [ exact Hσσ | exact HBnb | constructor | exact HBσσ ] | exact Hext ]. }
      assert (Huc1 : shape_uc D Us (arg_shape_ctx Mk gs1 t0 (S d)) (q σs ⨟ ((ι φ),,b')) (sb_wk σ' φ)).
      { rewrite Hctx'; eapply shape_uc_sb_eq; [| apply shape_uc_compose, shape_uc_pi; [| exact Huc ] ].
        - intros a0; rewrite <- (sb_wk_shift_extend σ' φ (se_exp b') a0); cbn [sb_compose]; f_equal.
          unfold sb_wk; cbn [sb_compose]; rewrite sentry_sub_of_wk; reflexivity.
        - unfold arg_shape_ctx; rewrite !List.length_app, length_im_params; unfold im_np; lia. }
      assert (HNb : Δ ⊢ N[φ]ʷ $ b' ≈ N'[φ]ʷ $ b' : ptyp_ty_at p D (List.map (fun U => U[φ]ʷ) (List.map (fun U => U[σ']) Us))
                                                    (q σs ⨟ ((ι φ),,b')) t).
      { rewrite <- (shape_ty_step VP HVP p D HPD t _ σs φ b' HUl1); fold OTy.
        rewrite <- exp_sub_wk_q_extend.
        eapply wf_exp_eq_app_cong'; [ exact (kripke_preserves_exp_eq _ _ _ _ _ _ HN Hφ) | mauto 3 ]. }
      assert (HIT1 : Δ ⊢ leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks (sb_wk σ' φ))) Id (q σs' ⨟ ((ι φ),,b')) (N'[φ]ʷ $ b') l'
                       : Typeω@j).
      { pose proof (ih_cod_inst σ' σs' N' l' φ (se_exp b') Ml HMl HPll) as E; cbn [sentry_exp] in E; rewrite <- E.
        exact (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ Hbt). }
      eapply (IH' Mk ms c0 gs1 t0 gs2 ws (S d) (ys ++ c :: nil) (sb_wk σ' φ) _ (q σs' ⨟ ((ι φ),,b')) (N'[φ]ʷ $ b') rs'
                Hσt1 Hσσ1 Huc1 HNb Hsh' Ers' idx l' rc a2 j _ _ _ _ Hok Hrs' Hlt' Ha22 Hrc HiAj Hnbj (Hcodg _ equiv_c _ Ea2) HIT1).
      Unshelve.
      - constructor; [ exact HMk | exact Hc0 | rewrite <- !List.app_assoc; reflexivity | | exact Hms | exact Hws | reflexivity
                     | | | exact (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ)
                     | rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub ].
        { unfold shape_doms_tele; rewrite (firstn_S_snoc _ _ _ (List.map_nth_error _ _ _ HB)), <- !List.app_assoc; reflexivity. }
        { unfold ptyp_depth; lia. }
        apply tele_prefix_rel_snoc; [ exact Hys |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB);
          first [ exact Hdc | rewrite <- Lys; exact Hdc | rewrite Lys; exact Hdc ].
      - replace (im_nn Mk + List.length (cargs_nonrec gs1) + S d) with m by (unfold m; lia); exact Hl'. }
    (** The body's type, at the generic variable. *)
    assert (HITid : Δ' ⊢ IT' ® IP) by (pose proof (HIT' Δ' wk_id (kripke_id _ HΔ')) as Hx0; rewrite exp_wk_id in Hx0; exact Hx0).
    assert (HΔIT : ⊢ Δ' ▹{ak_relevant} IT') by mauto 3.
    pose proof (var0_glu_elem Hgb1 Hnlb HITid) as Hvar; rewrite Hkb in Hvar.
    pose proof (var_per_elem (length Δ') equiv_a_a' Hnlb) as Heqv.
    destruct (Happ _ _ _ _ Heqv (kripke_shift _ _ _ HΔIT) Hvar) as (rc0 & a0 & _ & Ea0 & Hg0).
    pose proof (glu_univ_elem_trm_escape _ _ _ _ (Hcodg _ Heqv _ Ea0) _ _ _ _ Hg0) as Hbodyt.
    assert (Ebv : body[(ι ↑),,#0] = body).
    { transitivity (body[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold body; rewrite !ih_body_inst; cbn [sentry_exp].
      apply leaf_ih_exp_agree; [ exact Hlm | apply sb_exp_agree_var0 ]. }
    assert (Eov : OTi[(ι ↑),,#0] = OTi).
    { transitivity (OTi[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold OTi; rewrite !(ih_cod_inst σ' σs' N' l' ↑ _ Ml HMl HPll); cbn [sentry_exp].
      apply leaf_ihty_exp_agree; [ exact Hlm | apply sb_exp_agree_var0 ]. }
    rewrite Ebv, Eov in Hbodyt.
    cbn [leaf_ih leaf_ihty]; fold IT' body OTi.
    apply HEleq; eapply mk_pi_glu_exp_pred with (IT := IT') (OT := OTi);
      [ apply wf_fn with (Srt := Typeω@j) (κc := ak_relevant) (i := j); [ exact HITt | constructor | exact HOTt | constructor | exact Hbodyt ]
      | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRsave Hper); exact Hrr
      | apply wf_exp_eq_refl; exact HIT | exact HITt | exact HOTt | exact HIT' |].
    intros Δ φ N0 n0 Hφ Hn0 equiv_n.
    destruct (Happ _ _ _ _ equiv_n Hφ Hn0) as (rc & a2 & Erc & Ea2 & Hgl).
    exists rc; split; [ exact Erc |].
    pose proof (Hcodg _ equiv_n _ Ea2) as Hga2.
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hga2 | exact Hgl |].
    apply wf_exp_eq_sym; eapply fn_wk_beta; [ exact HITt | exact HOTt | exact Hbodyt | exact Hφ
                                          | exact (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hn0) ].
  Qed.

  (** At the end of a shape, at a record view: a leaf path goes through a
      recursive field's projection, along the field's path; the result is
      the field's ([rview_ihs_at]), at the field's components, equal to
      the projections of the argument ([rview_field_eqs]). *)
  Lemma rec_rview_case : forall ok k Δ' Us' pre Ts j0 Mj Ps A N v, ind_member D j0 = Some Mj -> im_is_rview Mj = true ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bsr -> A = im_ty_at p j0 Mj Us' Q ->
         forall Δ φ Us'' Q', Δ ⊢ᵏ φ : Δ' -> List.length Us'' = ind_nu D ->
           exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us' ++ Q)) (Us'' ++ Q') ->
           rview_ihs_prop ok j0 Δ Us'' N[φ]ʷ v) ->
      forall σs, A = ptyp_ty_at p D Us' σs (pt_self j0 Ps) -> rec_prop ok k Δ' Us' pre Ts (pt_self j0 Ps) σs N v.
  Proof.
    intros * HMj Hrv IH σs HA; unfold rec_prop.
    intros Mk ms c0 gs1' t0 gs2' ws0 d ys σ' Hctx σs' N' rs Hσt Hσσ Huc HN Hsh Er idx l r a j R P El Hleaf Hok Hr Hlt HR Hrr
      HiAj Hnbj Hg HIT.
    pose proof Hctx as [HMk Hc0 Hpre Hts Hms Hws Hsk Hdp Hys Hσ' HUs'].
    (** The record view and its one constructor. *)
    unfold im_is_rview in Hrv; destruct (im_head Mj) as [| | qr Is fl] eqn:Hh; try discriminate Hrv.
    destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [HEG Hnn].
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gs & Hcs & Hlen).
    pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as Hnp0.
    destruct (arg_shape_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx) as (Mj1 & HMj1 & HPsl & _ & _).
    cbn [ptyp_mem ptyp_ps] in HMj1, HPsl; rewrite HMj in HMj1; injection HMj1 as <-.
    destruct Ps as [| P0 Ps]; [| cbn in HPsl; lia ].
    set (m := im_nn Mk + List.length (cargs_nonrec gs1') + d) in *.
    (** The leaf path: through a field's projection. *)
    cbn [shape_leaves] in Hleaf; rewrite (Hco _ _ _ _ _ _ _ HMj Hh Hcs) in Hleaf.
    apply nth_error_map_inv in Hleaf as (l0 & Hl0 & ->).
    destruct (eval_ih_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HMj Hh Hcs Er) as (ws & Ews & Eihs).
    destruct (leaf_type_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hlt)
      as (gs1 & tf & gs2 & ws' & w & idx1 & Heq & Ews' & Hw & -> & Hidx1 & Hlt1).
    pose proof (functional_eval_projs _ _ _ _ Ews' Ews) as ->.
    destruct (combine_split_rec fl gs gs1 tf gs2 (eq_sym Hlen) Heq) as (fs1 & f & fs2 & Ec & Es1).
    destruct (nth_error_lt_some (shape_leaves (rview_leaves D) (List.length (nil ++ fields_args fs1)) tf) idx1) as [l1 Hl1].
    { rewrite (length_shape_leaves _ _ _ 0); exact Hidx1. }
    pose proof (fields_leaves_at D fs1 f tf fs2 nil idx1 l1 Hl1) as Hl0'.
    rewrite <- Ec, Es1, Hl0 in Hl0'; injection Hl0' as ->.
    (** The result: the field's along its path. *)
    destruct (eval_ihs_nth _ _ _ _ _ _ _ _ Hl Hco Eihs gs1 tf gs2 w Heq Hw) as (rsf & Erf & Hrsf).
    pose proof (proj1 (proj2 (@eval_ih_length_all gc_deps gc_stack)) _ _ _ _ _ _ _ Erf _ Hl Hco) as Lrf.
    rewrite Hrsf in Hr by lia.
    (** The relation at the field. *)
    destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs' & _ & _ & _ & _ & Hir).
    destruct (Completeness.Inductives.Elim.ind_rel_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hir)
      as (ws1 & ws1' & Ew1 & Ew1' & Hnr & Hca).
    pose proof (functional_eval_projs _ _ _ _ Ew1 Ews) as ->; pose proof (functional_eval_projs _ _ _ _ Ew1' Ews) as ->.
    destruct (Completeness.Inductives.CargsRel.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca gs1 tf gs2 Heq)
      as (x & x' & Hx & Hx' & Hshf).
    rewrite Hw in Hx, Hx'; injection Hx as <-; injection Hx' as <-.
    cbn [List.app] in Hshf.
    destruct (ER con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hca) as [Lws _].
    (** The fields of the argument. *)
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    assert (HUl' : List.length Us' = ind_nu D) by (rewrite HUs', List.length_map; exact HUl).
    pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
    pose proof (glu_args_typed _ _ _ _ _ _ Ua HUg') as HUt'.
    assert (HAm : A = im_ty_at p j0 Mj Us' nil) by (rewrite HA; cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
    assert (Heqa : exps_eq_at Δ' (im_params D Mj) (List.map (fun P => P[wk_id]ʷ) (Us' ++ nil)) (Us' ++ nil)).
    { rewrite map_wk_id, List.app_nil_r; split; [ reflexivity |].
      intros k1 X1 Y1 T1 HX1 HY1 HT1; rewrite HX1 in HY1; injection HY1 as <-.
      rewrite HEG in HT1; apply wf_exp_eq_refl; exact (HUt' _ _ _ HX1 HT1). }
    pose proof (IH nil nil ltac:(constructor) HAm Δ' wk_id Us' nil (kripke_id _ HΔ') HUl' Heqa) as Hrv'.
    rewrite exp_wk_id in Hrv'.
    destruct (Hrv' Mj qr Is fl _ gs ws HMj Hh Hcs Ews) as [As HAl HNc HAt Hrec].
    assert (Lnonrec_ctx : forall gs0, List.length (cargs_nonrec_ctx gs0) = List.length (cargs_nonrec gs0))
      by (induction gs0 as [| [] gs0 IH0]; cbn; rewrite ?List.length_app; cbn; lia).
    assert (Anonrec_ctx : forall gs0, all_assumptions (cargs_nonrec_ctx gs0)).
    { induction gs0 as [| [] gs0 IH0]; cbn; [ constructor | | exact IH0 ].
      unfold all_assumptions in *; apply List.Forall_app; split; [ exact IH0 | constructor; [ do 2 eexists; reflexivity | constructor ] ]. }
    (** The field's recursive results, at its components at the fields. *)
    assert (Hlg1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
    destruct (nth_error_lt_some As (List.length gs1)) as [Nf HNf]; [ lia |].
    destruct (nth_error_lt_some (tele_insts (cargs_ctx p D Mj gs) (sb_of_list Id Us') As) (List.length gs1)) as [Af HAf].
    { rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. }
    set (σA := cargs_sub (sb_of_list Id Us') gs1 As).
    assert (HUnp : List.length Us' = im_np D Mj) by (unfold im_np; rewrite Hnn; lia).
    assert (HAfe : Af = ptyp_ty_at p D Us' σA tf).
    { rewrite (cargs_rec_type_at p D Mj gs gs1 tf gs2 Us' As Af Heq Hc HUnp HAf), List.firstn_all2 by lia.
      apply ptyp_ty_at_sb_eq; rewrite sb_of_list_app; unfold σA; rewrite <- (cargs_sub_firstn gs1 _ As).
      apply cargs_sub_pat; rewrite List.length_firstn; lia. }
    pose proof (Hrec gs1 tf gs2 Nf Af w Heq HNf HAf Hw σA HAfe) as RP.
    (** The fields' components and the field, against [N']'s projections. *)
    assert (Eptm : ptyp_ty_at p D Us' σs (pt_self j0 nil) = im_ty_at p j0 Mj Us' nil)
      by (cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
    rewrite Eptm in HN.
    pose proof (wf_exp_eq_trans _ _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ _ _ HN) HNc) as HN'.
    assert (HNf' : List.nth_error As (List.length fs1) = Some Nf) by (rewrite <- (List.length_map snd fs1), Es1; exact HNf).
    destruct (rview_field_eqs Δ' p D j0 Mj qr Is fl _ gs Us' As N' fs1 f tf fs2 Nf Hl HMj Hh Hcs HΔ' HUl' HUt' HAl HAt HN' Ec HNf')
      as [Eσ HNfe].
    rewrite Es1 in Eσ, HNfe; fold σA in Eσ, HNfe.
    clear Hrec Hrv' IH.
    (** Their uniform parameters: the shape's at [σs'], past [m]. *)
    set (σ0 := sb_of_list Id Us') in *.
    assert (Hdl : d <= List.length (ptyp_doms t0)) by (unfold ptyp_depth in Hdp; lia).
    assert (Hlen_ctx : List.length (arg_shape_ctx Mk gs1' t0 d) = m + ind_nu D).
    { unfold arg_shape_ctx, m; rewrite !List.length_app, length_doms_ctx, List.length_firstn, length_im_params, Lnonrec_ctx.
      unfold im_np; lia. }
    assert (Hwk : arg_shape_ctx Mk gs1' t0 d ⊢ˢ ι (wk_shiftn m) : im_params D Mj).
    { rewrite HEG; apply wf_sub_of_wk.
      pose proof (wf_sub_cod _ _ _ _ _ Hσt) as HC.
      replace (arg_shape_ctx Mk gs1' t0 d) with (((doms_ctx (List.firstn d (ptyp_doms t0)) ++ cargs_nonrec_ctx gs1') ++ im_nparams Mk)
                                                   ++ ind_uparams D) in HC |- *
        by (unfold arg_shape_ctx, im_params; rewrite <- !List.app_assoc; reflexivity).
      replace m with (List.length ((doms_ctx (List.firstn d (ptyp_doms t0)) ++ cargs_nonrec_ctx gs1') ++ im_nparams Mk))
        by (rewrite !List.length_app, length_doms_ctx, List.length_firstn, Lnonrec_ctx; unfold m, im_nn; lia).
      apply wf_wk_shiftn_app'; exact HC. }
    assert (HassP : all_assumptions (im_params D Mj)) by exact (decl_closed_params_ass D j0 Mj Hc HMj).
    assert (Hσ0t : Δ' ⊢ˢ σ0 : im_params D Mj).
    { rewrite <- (List.app_nil_r (im_params D Mj)).
      eapply wf_sub_of_list; [ exact HassP | rewrite List.app_nil_r; exact (member_params_wf _ _ _ _ _ Hdt HMj)
                             | exact (wf_sub_to_nil _ _ _ HΔ') | rewrite length_im_params; unfold im_np; lia | rewrite HEG; exact HUt' ]. }
    assert (Hb1 : Δ' ⊢ˢ σ0 ≈ ι (wk_shiftn m) ⨟ σs : im_params D Mj).
    { apply wf_sub_eq_of_agree; [ exact HassP | exact Hσ0t | eapply wf_sub_compose; [ exact Hwk | exact Hσt ] |].
      intros x Hx; rewrite length_im_params in Hx; unfold im_np in Hx; rewrite Hnn in Hx.
      pose proof (Huc x ltac:(lia)) as Hux; rewrite Hlen_ctx in Hux.
      replace (x + (m + ind_nu D - ind_nu D)) with (m + x) in Hux by lia.
      cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
      replace (x + m) with (m + x) by lia; rewrite Hux; cbn [sb_compose]; unfold σ0; rewrite HUs', <- sb_of_list_lt_compose by lia;
        reflexivity. }
    assert (Hb2 : Δ' ⊢ˢ ι (wk_shiftn m) ⨟ σs ≈ ι (wk_shiftn m) ⨟ σs' : im_params D Mj)
      by exact (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ Hwk Hσσ).
    pose proof (wf_sub_eq_trans _ _ _ _ _ _ _ Hb1 Hb2) as Hb.
    pose proof (wf_sub_eq_right _ _ _ _ _ _ Eσ) as HLt.
    assert (HLl : List.length (projections_of (fields_args fs1) N') = List.length (cargs_nonrec_ctx gs1))
      by (unfold projections_of; rewrite List.length_map, length_fields_args, Es1, Lnonrec_ctx; reflexivity).
    pose proof (sb_of_list_base_eq _ _ _ _ _ _ (Anonrec_ctx gs1) (wf_sub_cod _ _ _ _ _ HLt) Hb HLt HLl) as Eσ'.
    pose proof (wf_sub_eq_trans _ _ _ _ _ _ _ Eσ Eσ') as HσAσ.
    assert (HucA : shape_uc D Us (arg_shape_ctx Mj gs1 tf 0) σA σ').
    { intros y Hy; unfold arg_shape_ctx; cbn [List.firstn doms_ctx List.rev List.map List.app].
      rewrite List.length_app, length_im_params, Lnonrec_ctx; unfold im_np; rewrite Hnn.
      assert (Lg : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      unfold σA, σ0; rewrite <- cargs_sub_firstn, cargs_sub_of_list, sb_of_list_app.
      replace (y + (List.length (cargs_nonrec gs1) + (0 + ind_nu D) - ind_nu D))
        with (List.length (nonrec_exps gs1 (List.firstn (List.length gs1) As)) + y)
        by (rewrite length_nonrec_exps by (rewrite List.length_firstn; lia); lia).
      rewrite sb_of_list_ge; cbn [sb_compose]; rewrite HUs', <- sb_of_list_lt_compose by lia; reflexivity. }
    (** The field's context. *)
    assert (Hctxf : elim_arg_context j0 Mj nil rview_con gs1 tf gs2 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws)) 0 nil
                      (nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws)) (cargs_nonrec_tele gs1) tf σ' Δ' Us').
    { constructor; [ exact HMj | rewrite <- Heq; exact (ind_con_single _ _ _ Hcs) | cbn [List.app]; rewrite List.app_nil_r; reflexivity
                   | rewrite Hnp0; cbn [List.rev List.app List.firstn]; rewrite List.app_nil_r; reflexivity
                   | rewrite Hnp0; split; [ reflexivity | cbn; exact I ]
                   | exact (nonrec_prefix_pre _ gs ws gs1 (ca_rec tf) gs2 Hnr Lws Heq) | reflexivity | lia
                   | apply tele_prefix_rel_nil | exact Hσ' | exact HUs' ]. }
    assert (Hl1' : List.nth_error (shape_leaves (rview_leaves D) (im_nn Mj + List.length (cargs_nonrec gs1) + 0) tf) idx1 = Some l1).
    { rewrite Hnn; cbn [List.app] in Hl1; rewrite length_fields_args, Es1 in Hl1.
      replace (0 + List.length (cargs_nonrec gs1) + 0) with (List.length (cargs_nonrec gs1)) by lia; exact Hl1. }
    (** The leaf path, through the projection. *)
    rewrite leaf_mem_wk in Hok; cbn [leaf_mem] in Hok.
    rewrite leaf_ihty_wk in HIT; cbn [leaf_ihty] in HIT.
    rewrite leaf_ih_wk, leaf_ihty_wk; cbn [leaf_ih leaf_ihty].
    exact (RP Mj nil rview_con gs1 tf gs2 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws)) 0 nil σ' Hctxf
             _ (a_proj f N') rsf (wf_sub_eq_left _ _ _ _ _ _ HσAσ) HσAσ HucA HNfe Hshf Erf idx1 l1 r a j R P El
             Hl1' Hok Hr Hlt1 HR Hrr HiAj Hnbj Hg HIT).
  Qed.

  (** The recursive results' telescope of a branch, at a substitution
      [σ'] past the non-uniform parameters and the arguments: the
      telescope of the eliminator at [σ']. *)
  Lemma ihs_insts_move : forall k Mk c gs σ' Ns' As L, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      List.length Ns' = im_nn Mk -> List.length As = List.length gs ->
      tele_insts (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs)
        (sb_of_list σ' (Ns' ++ As)) L
      = tele_insts (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) (blocks_motives (blocks_sub Bks σ')) (List.map (fun U => U[σ']) Us)
                      (List.length gs) nil 0 gs) (sb_of_list Id (Ns' ++ As)) L.
  Proof.
    intros * HMk Hcon HNl HAl.
    rewrite (tele_insts_sb_eq _ _ (sb_qn (0 + List.length gs + im_nn Mk) σ' ⨟ sb_of_list Id (Ns' ++ As))).
    2:{ replace (0 + List.length gs + im_nn Mk) with (List.length (Ns' ++ As)) by (rewrite List.length_app; lia).
        symmetry; etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ]. }
    rewrite <- tele_insts_tele_sub.
    rewrite (ihs_ctx_aux_sub ak_relevant D (im_nn Mk) (blocks_motives Bks) (blocks_motives (blocks_sub Bks σ')) Us (List.length gs) σ' gs nil 0
               Hc HUl eq_refl); [ reflexivity |].
    intros gs1 t gs2 Heq.
    pose proof (decl_closed_members _ Hc _ _ HMk) as HMc.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    split.
    - rewrite HUl; exact (member_closed_recs _ _ HMc _ _ _ _ _ Hin Heq).
    - intros l Hl'.
      destruct (member_closed_rec_len _ _ HMc _ _ Hin _ _ _ Heq) as (Mj & HMj & HlMj).
      assert (Hlp : List.Forall (leaf_params_length D) (shape_leaves (rview_leaves D) (pat_nargs nil + List.length (cargs_nonrec_ctx gs1) + im_nn Mk) t))
        by (apply shape_leaves_params_length; [ exact (rview_leaves_params_length D Hc) | exists Mj; split; [ exact HMj | exact HlMj ] ]).
      destruct (proj1 (List.Forall_forall _ _) Hlp _ Hl') as (Ml & HMl & HPll).
      rewrite HPll; apply (blocks_motives_sub D Bks σ' _ Ml Hnm HMl).
  Qed.

  (** The value of a branch's type at a constructor's components and
      recursive results in the group, against the motive's at the
      constructor: the branch's type is the motive at the constructor as
      the group reads it ([τb]), related to the constructor in the group. *)
  Lemma branch_type_val_rel : forall v Mv c gs b, ind_member D v = Some Mv -> ind_con Mv c = Some gs -> im_is_rview Mv = false ->
      List.nth_error Bks v = Some b ->
      forall hd k bs vs ihs ns' abt a0 vts vts0, im_ref p v Mv = (hd, k) ->
      List.length bs = (im_unu D Mv + im_nn Mv)%nat ->
      G v ups ups (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs)) (d_con hd k c (bs ++ vs)) ->
      rec_results_rel D dr Rel v ups ups (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs) (List.rev (im_nparams Mv))
        gs vs vs ihs ihs ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns' (List.skipn (im_unu D Mv) bs) ->
      List.map fst vts = List.skipn (im_unu D Mv) bs ++ vs ++ ihs ->
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
      List.map fst vts0 = ns' ++ d_con hd k c (bs ++ vs) :: nil ->
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts0 ->
      ⟦ elim_branch_type p D v Mv c gs (eb_motive b) Us ⟧ env_extend_typed ρ vts ↘ abt ->
      ⟦ eb_motive b ⟧ env_extend_typed ρ vts0 ↘ a0 ->
      Dom abt ≈ a0 ∈ per_univ iA.
  Proof.
    intros v Mv c gs b HMv Hcon Hrv Hbk hd k bs vs ihs ns' abt a0 vts vts0 Href Lbs HGX Hir HnX Hv Hr Hv0 Hr0 Eabt Ea0.
    set (X := List.skipn (im_unu D Mv) bs) in *.
    set (Y := List.firstn (im_unu D Mv) bs).
    assert (HbY : bs = Y ++ X) by (symmetry; apply List.firstn_skipn).
    assert (LY : List.length Y = im_unu D Mv) by (unfold Y; rewrite List.length_firstn; lia).
    assert (LX : List.length X = im_nn Mv) by (unfold X; rewrite List.length_skipn; lia).
    pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as HBs.
    destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
    pose proof (EB Completeness.Inductives.Elim.canonical_bctx_elem ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs Hrv ρ ρ Hρ Hρ
                  ups ups hd k bs bs vs vs ihs ihs HGX Hir RB HRB vts vts Hv Hv Hr Hr) as HZ.
    destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lih _].
    destruct (Completeness.Inductives.Elim.rec_results_rel_vs_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Hvl _].
    (** The branch's variables, split. *)
    destruct (List.map_eq_app _ _ _ _ Hv) as (vX & vr & -> & HvX & Hvr).
    destruct (List.map_eq_app _ _ _ _ Hvr) as (vvs & vih & -> & Hvvs & Hvih).
    assert (LX1 : List.length vX = im_nn Mv) by (rewrite <- (List.length_map fst), HvX; exact LX).
    assert (Lvs1 : List.length vvs = List.length gs) by (rewrite <- (List.length_map fst), Hvvs; exact Hvl).
    assert (Lih1 : List.length vih = cargs_nrec D gs) by (rewrite <- (List.length_map fst), Hvih; exact Lih).
    (** The constructor term's value, and the branch type's substitution. *)
    destruct (Completeness.Inductives.Elim.rel_exp_under_ctx_simple_at_mty _ _ _ _ _ _ _ _ _ _ HMv HRB
                (Completeness.Inductives.Elim.branch_type_con_valid VP p D HVP HPD Γ Us HUl HUs HUss Bks v Mv c gs HMv Hcon HBs Hrv)
                _ _ HZ) as (l1 & l2 & El1 & El2 & _).
    destruct (Completeness.Inductives.Elim.branch_con_fields p D Γ Us HUl HUss Bks Mv c gs Hcon ρ vX vvs vih RB HRB HZ LX1 Lvs1 Lih1)
      as (vsp & Lvsp & Ezs & Hmix).
    assert (HUb : List.length (List.map (fun U => U[wk_shiftn (im_nn Mv + List.length gs + cargs_nrec D gs)]ʷ) Us) = ind_nu D)
      by (rewrite List.length_map; exact HUl).
    assert (LNA : List.length (vars_from (cargs_nrec D gs + List.length gs) (im_nn Mv) ++ vars_from (cargs_nrec D gs) (List.length gs))
                  = (im_nn Mv + List.length gs)%nat)
      by (rewrite List.length_app, !length_vars_from; lia).
    destruct (Completeness.Inductives.Elim.con_ref_apps_value VP p D HVP HPD v Mv c gs _ _ _ _ l1 HMv Hrv Hcon HUb Ezs LNA El1)
      as (cs1 & Lcs1 & El1v).
    pose proof (Completeness.Inductives.Elim.eval_branch_type VP p D HVP HPD Γ HΓ Us HUl HUs HUss Bks HMall v Mv c gs HMv Hcon HBs Hrv
                  ρ vX vvs vih l1 RB HRB HZ LX1 Lvs1 Lih1 El1) as Hev.
    rewrite Href in El1v; cbn [fst snd] in El1v; rewrite HvX in Hev, El1v; subst l1.
    pose proof (Completeness.Inductives.Elim.gsub_branch_type VP p D HVP HPD Γ HΓ Us HUl HUs HUss Bks HMall v Mv c gs HMv Hcon HBs Hrv)
      as Hgs.
    (** The motive's context at the substitution's value, readable. *)
    destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMv)) as [RM HRM].
    assert (HPM : PER RM) by (eapply per_env_PER; exact HRM).
    pose proof (rel_sub_under_ctx_at' (Instance.gsub_valid Hgs) HRB HRM _ _ _ _ HZ Hev Hev) as L1.
    rewrite Decl.env_extend_tagged_typed in L1.
    destruct (Completeness.Inductives.Elim.mctx_rev_sem VP p D HVP HPD Γ Us HMall v Mv HMv RM HRM) as (HMr & HRMr & Hta).
    assert (Lq : List.length (List.rev (elim_mctx p D v Mv Us)) = List.length (X ++ d_con hd k c (cs1 ++ X ++ vsp) :: nil))
      by (rewrite List.length_rev, length_elim_mctx, List.length_app, LX; cbn [List.length]; lia).
    assert (Lt : List.length (Decl.tagged_entries Γ (List.rev (elim_mctx p D v Mv Us)) (ctx_retag Γ ρ) (X ++ d_con hd k c (cs1 ++ X ++ vsp) :: nil))
                 = List.length (List.rev (elim_mctx p D v Mv Us)))
      by (rewrite Decl.tagged_entries_length by exact Lq; symmetry; exact Lq).
    destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ Lt Lt L1) as [Hrd _].
    (** The constructor the branch's type has, against the stored one. *)
    assert (HG1 : G v ups ups X ns' (d_con hd k c (cs1 ++ X ++ vsp)) (d_con hd k c (bs ++ vs))).
    { pose proof HGX as H; rewrite HbY, <- List.app_assoc in H.
      pose proof (EB Completeness.Inductives.Elim.con_up_to_proofs v Mv c gs HMv Hcon Hrv hd k Y cs1 X vs vsp Href LY H
                    ltac:(lia) ltac:(lia) ltac:(intros j0 w w' Hw Hw'; rewrite <- Hvvs in Hw; exact (Hmix j0 w w' Hw Hw'))) as H'.
      pose proof (proj1 (ind_rel_sym_all p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI (admissible_index_at D ups nr))
                    _ _ _ _ _ _ _ H') as H''.
      pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
      pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HMv _ _ HnX) as HXX.
      rewrite HbY, <- List.app_assoc.
      exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ v Mv _ _ _ _ _ _ _ _ HMv H'' HXX (tsym _ _ HMv _ _ HnX)). }
    pose proof (EB Completeness.Inductives.Elim.mctx_at_typed HMall v Mv HMv _ _ (per_ctx_env_retag_left HRΓ _ _ Hρ) Hρ RM HRM
                  _ _ _ _ _ _ HG1 _ _ (Decl.tagged_entries_fst _ Γ (ctx_retag Γ ρ) _ Lq) Hv0 Hrd Hr0) as HE.
    rewrite <- Decl.env_extend_tagged_typed in HE.
    (** The two values, related. *)
    destruct (rel_type_inversion_simple_at HRM (rel_type_of_abs_kind_sort (r := ak_relevant) (HAv _ _ _ HMv Hbk)) _ _ HE)
      as (m2 & a0' & Em2 & Ea0' & Hm2).
    assert (a0' = a0) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (typ_inst_val _ _ _ _ _ _ _ _ _ _ (HAv _ _ _ HMv Hbk) HRB (Instance.gsub_valid Hgs) HZ Hev Eabt Em2) as H1.
    eapply per_univ_trans'; [ exact H1 | exact Hm2 ].
  Qed.


  (** The instance of the recursive results' telescope of a constructor's
      branch, at the substitution [σ'] extended by the non-uniform
      parameters [Ns'], the arguments [As] and some recursive results
      [L], at the leaf path [idx] of the recursive argument [N] after
      [gs1]: the type of the result along the path, at the arguments'
      instance of the shape's components. *)
  Lemma ihs_entry_syn : forall k Mk c gs σ' Ns' As L gs1 t gs2 idx l N T,
      ind_member D k = Some Mk -> ind_con Mk c = Some gs -> List.length Ns' = im_nn Mk -> List.length As = List.length gs ->
      gs = gs1 ++ ca_rec t :: gs2 -> cargs_nrec D gs1 + idx <= List.length L ->
      List.nth_error (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t) idx = Some l ->
      List.nth_error As (List.length gs1) = Some N ->
      List.nth_error (tele_insts (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs)
                        (sb_of_list σ' (Ns' ++ As)) L) (cargs_nrec D gs1 + idx) = Some T ->
      T = leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σ')) Id (cargs_sub (sb_of_list Id (List.map (fun U => U[σ']) Us ++ Ns')) gs1 As) N l.
  Proof.
    intros k Mk c gs σ' Ns' As L gs1 t gs2 idx l N T HMk Hcon HNl' HAl Heq HLj Hl0 HN HT.
    set (Us' := List.map (fun U => U[σ']) Us).
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
    set (j := cargs_nrec D gs1 + idx) in *.
    assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
    set (σg := cargs_sub (sb_of_list Id (Us' ++ Ns')) gs1 As).
    rewrite (ihs_insts_move k Mk c gs σ' Ns' As _ HMk Hcon HNl' HAl) in HT.
    destruct (tele_insts_nth _ _ _ _ _ HT) as (κ'' & B'' & HB'' & ET).
    rewrite (ihs_ctx_nth ak_relevant D _ _ _ _ gs gs1 t gs2 idx l Heq Hl0) in HB''; fold j in HB''; injection HB'' as <- <-.
    subst T; rewrite <- sb_of_list_app, <- List.app_assoc.
    set (L' := List.firstn j L).
    assert (LL' : List.length L' = j) by (unfold L'; rewrite List.length_firstn; lia).
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
    assert (Hvar : (a_var (j + List.length gs - 1 - List.length (cargs_pat gs1)))[δ] = N).
    { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ.
      rewrite (sb_of_list_nth _ _ _ N) by (rewrite !List.length_app, HNl', HAl, LL', Heq, List.length_app, length_cargs_pat; cbn; lia).
      rewrite !List.length_app, HNl', HAl, LL', length_cargs_pat.
      replace (im_nn Mk + (List.length gs + j) - 1 - (j + List.length gs - 1 - List.length gs1))
        with (im_nn Mk + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
      cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl'; replace (im_nn Mk + List.length gs1 - im_nn Mk) with (List.length gs1) by lia.
      rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact HN. }
    rewrite leaf_ihty_sub, Hvar.
    rewrite (leaf_ihty_sb_eq _ l _ _ Id _ σg N Hβδ Hθδ); reflexivity.
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
    Hypotheses (HMk : ind_member D k = Some Mk) (HrvK : im_is_rview Mk = false) (Href : im_ref p k Mk = (hd, k'))
      (Hcon : ind_con Mk c = Some gs)
      (HUl' : List.length Us' = ind_nu D) (HNl' : List.length Ns' = im_nn Mk)
      (Hbl : List.length bs = (im_unu D Mk + im_nn Mk)%nat) (Hvl : List.length vs = List.length gs)
      (HAl : List.length As = List.length gs)
      (HMeq : Δ' ⊢ M' ≈ apps (a_con p k c) (Us' ++ Ns' ++ As) : im_ty_at p k Mk Us' Ns')
      (Hb : tele_rel (nr k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs))
      (Hv : tele_rel (ar k (List.skipn (im_unu D Mk) bs) c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs))
      (Hnp : glu_nparams k Mk NEl Δ' Us' Ns' (List.skipn (im_unu D Mk) bs))
      (HAs : forall j N A, List.nth_error As j = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) j = Some A -> Δ' ⊢ N : A)
      (Harg : forall gs1 r0 A0 gs2 N A v, gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Δ' ⊢ N : A ® v ∈ AEl k (List.skipn (im_unu D Mk) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)))
      (Hrec : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec p D ups NEl AEl DP DEl k Δ' Us' (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
            (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t A N v)
      (IH : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          forall σs, A = ptyp_ty_at p D Us' σs t ->
          rec_prop (fun _ => True) k Δ' Us' (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
            (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t σs N v).
    Variables (σ' : sub) (ns : list domain).
    Hypotheses (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HUs' : Us' = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : im_ty_at p k Mk Us' Ns') (Hgn : glu_nparams k Mk NEl Δ' Us' Ns' ns)
      (Hns : tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns)
      (HGm : G k ups ups ns ns (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs ++ vs))).
    #[local] Abbreviation X := (List.skipn (im_unu D Mk) bs).

    (** The scrutinee's parameters against the stored ones, and the
        arguments related. *)
    Lemma con_case_rel : tele_rel (nr k) (List.rev (im_nparams Mk)) ns X /\
        con_args_rel p D (admissible_index_at D ups nr) nr ar dr k ups ups X X (List.rev (im_nparams Mk)) gs vs vs.
    Proof.
      unfold grp_rel in HGm; inversion HGm; subst;
        match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HMk in H1; injection H1 as <- end.
      - match goal with H1 : ind_con Mk c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
        repeat match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => apply app_split_eq in E; [| lia ]; destruct E as [-> ->] end.
        split; assumption.
      - match goal with H2 : im_head Mk = mh_record _ _ _ |- _ => exfalso; exact (not_rview_record _ _ _ _ HrvK H2) end.
    Qed.

    Lemma con_case_LX : List.length X = im_nn Mk.
    Proof. rewrite List.length_skipn; lia. Qed.

    (** The non-uniform parameters and the arguments, glued at the instance
        of their closed telescope at [τU]: at their own types ([AtType]). *)
    Lemma con_case_args : glu_args Δ' (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) σ' ρ (Ns' ++ As) (X ++ vs).
    Proof.
      destruct con_case_rel as [_ Hia].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_tele_args Hbu Hule Hf HΨall
                  nb Hnbu Hnbq Hnbr) as [_ Hrt].
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      pose proof (at_con_args_prefix VP HVP HGall p D HPD ups u NP NEl AP AEl DP DEl ups_len ups_tele_args Hf HΨall
                    k Mk c gs Us' Ns' X vs As Δ' HMk Hcon HNl' con_case_LX Hvl HAl Hb Hv Hnp HAs Harg
                    (fun gs1 t gs2 N A v H1 H2 H3 H4 => Hrt _ _ _ _ _ _ _ _ _ (Hrec gs1 t gs2 N A v H1 H2 H3 H4)) HΔ' HUg' Hia
                    (List.length gs) (le_n _)) as HgA.
      rewrite (List.firstn_all2 (n := List.length gs) gs), (List.firstn_all2 (n := List.length gs) As),
        (List.firstn_all2 (n := List.length gs) vs) in HgA by lia.
      pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf k Mk Δ' Us' Ns' X HMk Hnp Hb) as HgN.
      assert (Hg : glu_args Δ' (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list Id Us') (decl_env D ups) (Ns' ++ As) (X ++ vs)).
      { apply glu_args_app; [ exact (decl_closed_nparams_ass D Hc _ _ HMk) | rewrite length_im_nparams; exact HNl'
                            | rewrite length_im_nparams; exact con_case_LX |].
        split; [ exact HgN |].
        unfold im_params in HgA; rewrite (Decl.env_tele_uparams D (im_nparams Mk) ups X ups_len) in HgA.
        rewrite sb_of_list_app in HgA; exact HgA. }
      rewrite HUs' in Hg.
      apply tele_inst_args; [ | | | | exact Hg |].
      - rewrite <- List.app_assoc; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMk) ].
      - rewrite <- List.app_assoc; exact (valid_group_cargs_sem p D Hvg Hcv k Mk c gs HMk Hcon).
      - pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as H.
        unfold elim_bctx in H; rewrite <- List.app_assoc in H; apply Completeness.UnitCases.rel_ctx_wf_app_r in H.
        unfold con_inst_tele in H; rewrite tele_sub_app, length_im_nparams, <- List.app_assoc;
          first [ exact H | rewrite <- List.app_assoc in H; exact H ].
      - pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk (cons_lookup_in _ _ _ Hcon) (eq_sym (List.app_nil_r gs))) as H.
        unfold im_params in H; rewrite List.app_assoc in H.
        apply ctx_scoped_app in H as [H _]; rewrite Nat.add_0_r in H; exact H.
      - pose proof (EB Completeness.Inductives.Elim.closed_args_tele_args k Mk c gs HMk Hcon X X vs vs Hb Hv Hia (List.length gs) (le_n _))
          as H.
        rewrite (List.firstn_all2 (n := List.length gs) gs), (List.firstn_all2 (n := List.length gs) vs) in H by lia; exact H.
    Qed.


    Lemma con_case_Ps_typed : forall j P T, List.nth_error (Us' ++ Ns') j = Some P ->
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
    Lemma con_case_iota_sub : Δ' ⊢ˢ sb_of_list Id (Ns' ++ As ++ elim_ihs ak_relevant p D Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns'))
                                                      (im_nn Mk) gs As)
        : elim_bctx ak_relevant p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us' ++ Δ'.
    Proof.
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      assert (HΔ' : ⊢ Δ') by (gen_presups; assumption).
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      pose proof (wf_iota_sub _ _ _ p D k Mk c gs (Us' ++ Ns') As (blocks_sub Bks σ') ak_relevant iA Hl HMk Hcon HΔ'
                    ltac:(rewrite List.length_app, HUl', HNl'; unfold im_np; lia) con_case_Ps_typed HAl HAs
                    ltac:(rewrite firstn_app_exact by exact HUl'; exact HBt')) as H.
      rewrite firstn_app_exact, skipn_app_exact in H by exact HUl'; exact H.
    Qed.

    (** The components of the shape of the recursive argument after
        [gs1], at the parameters and the arguments [As]: typed in [Δ'] at
        the shape's context, their uniform parameters those of the
        eliminator at [σ']. *)
    Lemma con_case_rec_sub : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        Δ' ⊢ˢ cargs_sub (sb_of_list Id (Us' ++ Ns')) gs1 As : arg_shape_ctx Mk gs1 t 0 /\
        shape_uc D Us (arg_shape_ctx Mk gs1 t 0) (cargs_sub (sb_of_list Id (Us' ++ Ns')) gs1 As) σ'.
    Proof.
      intros * Heq.
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      pose proof (ctx_wf_gctx _ _ _ HΔ') as Hg; pose proof (decls_of_ctx _ _ _ HΔ') as HDs.
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
      assert (HPl : List.length (Us' ++ Ns') = im_np D Mk) by (rewrite List.length_app, HUl', HNl'; unfold im_np; lia).
      destruct (params_typed_split _ _ D Hc _ _ Δ' (Us' ++ Ns') HMk HPl con_case_Ps_typed) as [HUs0 _].
      rewrite firstn_app_exact in HUs0 by exact HUl'.
      pose proof (wf_sub_uparams _ _ _ Hdt Hc _ _ HΔ' HUl' HUs0) as HσU.
      destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hg HDs Hl HMk HΔ' HσU c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [Hi _].
      pose proof (wf_sub_args_inst _ _ _ _ _ _ _ _ _ _ _ Hl HMk Hcon HΔ' HPl con_case_Ps_typed HAl HAs) as Hδ.
      rewrite firstn_app_exact, skipn_app_exact in Hδ by exact HUl'.
      destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ _ _ nil Hg HDs Hl HMk HΔ' HUl' HσU Hin Heq Hi) as (_ & Hθ & Huc & _).
      pose proof (ihs_sub_iota D Mk (Us' ++ Ns') As nil gs1 gs HPl HAl ltac:(rewrite Heq, List.length_app; cbn; lia)) as Hθδ.
      rewrite firstn_app_exact, skipn_app_exact in Hθδ by exact HUl'.
      rewrite List.app_nil_r in Hθδ.
      split.
      - rewrite <- Hθδ; eapply wf_sub_compose; [ exact Hθ | exact Hδ ].
      - intros y Hy; rewrite <- (Hθδ (y + _)); cbn [sb_compose].
        change (arg_shape_ctx Mk gs1 t 0) with (doms_ctx nil ++ cargs_nonrec_ctx gs1 ++ im_params D Mk).
        cbn [List.length] in Huc |- *.
        rewrite <- sentry_exp_sub, (Huc y Hy), sentry_exp_sub; cbn [sb_compose].
        rewrite sentry_sub_sub, (sb_of_list_lt_compose Us σ' y) by lia; rewrite <- HUs'.
        rewrite (sentry_sub_sb_eq _ _ Id); [ rewrite sentry_sub_id; reflexivity |].
        intros z; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        replace (z + (0 + List.length gs + im_nn Mk)) with (List.length (Ns' ++ As) + z) by (rewrite List.length_app; lia).
        rewrite sb_of_list_ge; reflexivity.
    Qed.

    (** The recursive results of the branch, glued: each is the
        eliminator at the matching recursive argument, glued by the
        induction hypothesis [IH] at its motive. *)
    Lemma con_case_ihs_args : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel D dr Rel k ups ups X X (List.rev (im_nparams Mk)) gs vs vs ihs ihs ->
        glu_args Δ' (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs)
          (sb_of_list σ' (Ns' ++ As)) (env_tele ρ (List.rev (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)) (X ++ vs))
          (elim_ihs ak_relevant p D Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) (im_nn Mk) gs As) ihs.
    Proof.
      intros ihs Ei Hir.
      pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      destruct con_case_rel as [HnX Hia].
      pose proof con_case_LX as LX.
      destruct (eval_ihs_length _ _ _ _ _ _ _ _ Hl Hco Ei) as [_ Lih].
      set (IC := ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs).
      (** The components and the results, related at their telescopes. *)
      pose proof (EB Completeness.Inductives.Elim.canonical_args_tele Bks k Mk c gs HMk Hcon HBs
                    ρ ρ Hρ Hρ X X vs vs Hb Hv Hia) as Hci.
      pose proof (EB Completeness.Inductives.Elim.canonical_ihs ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs HrvK
                    ρ ρ Hρ Hρ X X vs vs ihs ihs Hb Hv Hia Hir Hci (List.length gs) (le_n _)) as Hpgi.
      rewrite List.firstn_all, !List.firstn_all2 in Hpgi by lia; fold IC in Hpgi.
      constructor; [ unfold IC; rewrite length_elim_ihs, length_ihs_ctx_aux by exact HAl; reflexivity
                   | unfold IC; rewrite length_ihs_ctx_aux; exact Lih |].
      intros j0 M T r κ B0 HMj0 HT Hr HB0.
      assert (Hj0 : j0 < cargs_nrec D gs) by (rewrite <- Lih; apply List.nth_error_Some; congruence).
      destruct (rec_leaf_pos_of_lt D gs j0 Hj0) as [gs1 t gs2 idx Heq Hidx ->].
      set (j := cargs_nrec D gs1 + idx) in *.
      assert (Hls : List.length (cargs_nonrec_ctx gs1) = List.length (cargs_nonrec gs1))
        by (rewrite Completeness.Inductives.Model.cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele; reflexivity).
      set (m0 := pat_nargs (cargs_pat gs1) + im_nn Mk).
      assert (Hm0 : m0 = im_nn Mk + List.length (cargs_nonrec gs1) + 0) by (unfold m0; rewrite pat_nargs_cargs_pat, Hls; lia).
      destruct (nth_error_lt_some (shape_leaves (rview_leaves D) m0 t) idx) as [l Hl0].
      { rewrite (length_shape_leaves _ _ _ 0); exact Hidx. }
      pose proof (ihs_ctx_nth ak_relevant D (im_nn Mk) (blocks_motives Bks) Us (List.length gs) gs gs1 t gs2 idx l Heq Hl0) as EB0.
      fold IC j in EB0; rewrite HB0 in EB0; injection EB0 as -> EB0.
      assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [N HN].
      assert (Hl1 : List.nth_error (shape_leaves (rview_leaves D) (im_nn Mk + List.length (cargs_nonrec gs1)) t) idx = Some l)
        by (rewrite <- (Nat.add_0_r (_ + _)), <- Hm0; exact Hl0).
      rewrite (elim_ihs_nth _ _ _ _ _ _ _ gs gs1 t gs2 As N idx l Heq HAl HN Hl1) in HMj0; injection HMj0 as <-.
      destruct (Completeness.Inductives.CargsRel.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (v & v' & Hv1 & Hv1' & Hsh).
      rewrite Hv1' in Hv1; injection Hv1 as <-.
      destruct (eval_ihs_nth _ _ _ _ _ _ _ _ Hl Hco Ei gs1 t gs2 v' Heq Hv1') as (rs & Er' & Hrs).
      assert (Lrs : List.length rs = List.length (shape_leaves (rview_leaves D) 0 t))
        by exact (proj1 (proj2 (@eval_ih_length_all gc_deps gc_stack)) _ _ _ _ _ _ _ Er' _ Hl Hco).
      pose proof Hr as Hr0; unfold j in Hr0; rewrite (Hrs idx ltac:(rewrite Lrs; exact Hidx)) in Hr0.
      set (σg := cargs_sub (sb_of_list Id (Us' ++ Ns')) gs1 As).
      (** The syntactic type of the entry. *)
      assert (ET : T = leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σ')) Id σg N l).
      { unfold σg; rewrite HUs'.
        refine (ihs_entry_syn k Mk c gs σ' Ns' As _ gs1 t gs2 idx l N T HMk Hcon HNl' HAl Heq _ Hl0 HN HT).
        rewrite (length_elim_ihs ak_relevant p D Us' (blocks_sub Bks σ') _ _ gs As HAl); unfold j; rewrite Heq, cargs_nrec_app'; cbn; lia. }
      rewrite (ihs_insts_move k Mk c gs σ' Ns' As _ HMk Hcon HNl' HAl) in HT.
      rewrite <- HUs' in HT.
      (** The entry is typed, by the typing of [ι], and so is its type. *)
      set (Ihs := elim_ihs ak_relevant p D Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) (im_nn Mk) gs As) in *.
      set (Bc := elim_bctx ak_relevant p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us').
      set (Kj := im_nn Mk + List.length gs + j).
      assert (Lei : List.length Ihs = cargs_nrec D gs) by (apply length_elim_ihs; exact HAl).
      set (Rst := tele_sub (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) (sb_of_list Id Us')) ++ tele_sub (im_nparams Mk) (sb_of_list Id Us')).
      assert (HRa : all_assumptions Rst)
        by (unfold Rst; apply List.Forall_app; split; apply all_assumptions_sub; [ apply cargs_ctx_aux_ass | apply (decl_closed_nparams_ass D Hc _ _ HMk) ]).
      assert (LRst : List.length Rst = List.length (Ns' ++ As))
        by (unfold Rst; rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams, HNl', HAl; lia).
      assert (Hlen : List.length (Ns' ++ As ++ Ihs) = List.length Bc)
        by (unfold Bc; rewrite length_elim_bctx, !List.length_app, HNl', HAl, Lei; lia).
      assert (HTi : List.nth_error (tele_insts Bc Id (Ns' ++ As ++ Ihs)) Kj = Some T).
      { unfold Bc, elim_bctx; fold Rst.
        assert (LRi : List.length (tele_insts Rst Id (Ns' ++ As)) = im_nn Mk + List.length gs)
          by (rewrite length_tele_insts by exact HRa; rewrite LRst, Nat.min_id, List.length_app, HNl', HAl; reflexivity).
        rewrite List.app_assoc, tele_insts_app by (first [ exact HRa | exact (eq_sym LRst) ]).
        rewrite List.nth_error_app2 by (unfold Kj; lia); rewrite LRi.
        replace (Kj - (im_nn Mk + List.length gs)) with j by (unfold Kj; lia).
        exact HT. }
      assert (HMt' : Δ' ⊢ leaf_ih ak_relevant p Us' (blocks_sub Bks σ') σg N l : T).
      { apply (wf_sub_of_list_inv _ _ _ Bc Δ' Id (Ns' ++ As ++ Ihs) (elim_bctx_ass ak_relevant p D k Mk gs _ Us' Hc HMk) Hlen
                  con_case_iota_sub Kj); [| exact HTi ].
        rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; unfold Kj; lia).
        rewrite List.length_app, HNl', HAl.
        replace (Kj - (im_nn Mk + List.length gs)) with j by (unfold Kj; lia).
        exact (elim_ihs_nth _ _ _ _ _ _ _ gs gs1 t gs2 As N idx l Heq HAl HN Hl1). }
      assert (HjT0 : exists jT, Δ' ⊢ T : Typeω@jT).
      { pose proof HTi as HTi'; apply tele_insts_nth in HTi' as (κ0 & A0 & HA0 & ->).
        assert (κ0 = ak_relevant) as ->.
        { unfold Bc, elim_bctx in HA0; fold Rst in HA0.
          rewrite List.rev_app_distr, List.nth_error_app2 in HA0 by (rewrite List.length_rev, LRst, List.length_app, HNl', HAl; unfold Kj; lia).
          rewrite List.length_rev, LRst, List.length_app, HNl', HAl in HA0.
          replace (Kj - (im_nn Mk + List.length gs)) with j in HA0 by (unfold Kj; lia).
          pose proof (ihs_ctx_nth ak_relevant D (im_nn Mk) (blocks_motives (blocks_sub Bks σ')) Us' (List.length gs) gs gs1 t gs2 idx l Heq Hl0)
            as E'.
          fold j in E'; rewrite E' in HA0; congruence. }
        exact (wf_sub_of_list_relevant_entry _ _ _ _ _ Hlen con_case_iota_sub Kj A0 HA0). }
      destruct HjT0 as [jT HjT].
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
      pose proof (IH gs1 t gs2 N TN v' Heq HN HTN Hv1' σg HTNeq) as IHr.
      (** The semantic type of the entry, and of the result along the
          leaf path. *)
      destruct (per_tele_args_nth_elem _ _ _ _ _ j _ _ Hpgi HB0 ltac:(rewrite Lih; unfold j; rewrite Heq, cargs_nrec_app'; cbn; lia))
        as (i0 & Rae & ae & ae' & x & x' & Eae & Eae' & HRae & Hx & Hx' & Hrr).
      assert (ae' = ae) as -> by (eapply functional_eval_exp; eassumption).
      rewrite Hr in Hx; injection Hx as <-; rewrite Hr in Hx'; injection Hx' as <-.
      set (fa := List.firstn (List.length gs1) vs) in *.
      pose proof Eae as Eae1; rewrite EB0 in Eae1.
      pose proof (EB Completeness.Inductives.Elim.ihs_entry_type ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs HrvK
                    ρ Hρ gs1 t gs2 Heq X vs ihs Hb Hv Hia Hci Lih Hpgi idx l v' ae Hl0 Hv1' Eae1) as Hlt'.
      fold fa in Hlt'.
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk; fold fa in Hpk.
      (** The level of the result, above the motives', [nb] and the
          entry's type's. *)
      set (J := max (max iA nb) (max i0 jT)).
      pose proof (per_univ_elem_cumu_ge i0 J _ _ _ ltac:(unfold J; lia) HRae) as HRaeJ.
      destruct (per_univ_glu_univ_elem J ae (ex_intro _ Rae HRaeJ)) as (Pb & Elb & Hgb).
      pose proof (lift_exp_ge _ _ _ _ jT J ltac:(unfold J; lia) HjT) as HjJ.
      assert (Hc1 : ind_con Mk c = Some (gs1 ++ ca_rec t :: gs2)) by (rewrite <- Heq; exact Hcon).
      destruct (con_case_rec_sub gs1 t gs2 Heq) as [Hσg Hucg].
      assert (Hctx : elim_arg_context k Mk X c gs1 t gs2 (nonrec_arg_vals gs1 fa) 0 nil (X ++ nonrec_arg_vals gs1 fa)
                       (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t σ' Δ' Us')
        by (constructor; first [ exact HMk | exact Hc1 | rewrite List.app_nil_r; reflexivity
                               | cbn [List.firstn]; rewrite List.app_nil_r; reflexivity | exact Hb | exact Hpk | reflexivity
                               | lia | exact (tele_prefix_rel_nil _) | exact Hσ' | exact HUs' ]).
      pose proof (HAs _ _ _ HN HTN) as HNt; rewrite HTNeq in HNt.
      pose proof (IHr Mk X c gs1 t gs2 (nonrec_arg_vals gs1 fa) 0 nil σ' Hctx σg N rs Hσg
                    (wf_sub_eq_refl _ _ _ _ _ Hσg) Hucg ltac:(apply wf_exp_eq_refl; exact HNt) Hsh Er' idx l r ae J Rae Pb Elb
                    ltac:(rewrite <- Hm0; exact Hl0) I Hr0 Hlt' HRaeJ Hrr ltac:(unfold J; lia) ltac:(unfold J; lia) Hgb
                    HjJ) as HMg.
      rewrite ET; exact (mk_glu_arg _ _ _ _ _ _ J ae Pb Elb Eae Hgb (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HMg) HMg).
    Qed.

    (** The constructor in the group at its stored parameters. *)
    Lemma con_case_GX : G k ups ups X X (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs ++ vs)).
    Proof.
      destruct con_case_rel as [HnX _].
      exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ k Mk _ _ _ _ _ _ _ _ HMk HGm HnX HnX).
    Qed.

    (** The recursive results, related at the motives. *)
    Lemma con_case_ihs : exists ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs /\
        rec_results_rel D dr Rel k ups ups X X (List.rev (im_nparams Mk)) gs vs vs ihs ihs.
    Proof.
      destruct con_case_rel as [_ Hia].
      destruct per_elim_at_ups as (_ & H2 & _).
      destruct (H2 _ _ _ _ _ _ _ _ _ Hia Had Had) as (ihs & ihs' & Ei & Ei' & Hir).
      pose proof (functional_eval_ihs _ _ _ _ _ _ _ _ Ei Ei') as <-.
      exists ihs; split; assumption.
    Qed.

    (** The branch's own environment ([eval_elim_con]): the values of the
        non-uniform parameters, the arguments and the recursive results,
        at the types the eliminator stores. *)
    Definition con_case_bentries (ihs : list domain) : list (domain * entry_type) :=
      branch_entries D Mk p ups (blocks_motives Bks) ρ gs X vs ihs.

    (** Its values, which read back at their types. *)
    Lemma con_case_bentries_ok : forall ihs, rec_results_rel D dr Rel k ups ups X X (List.rev (im_nparams Mk)) gs vs vs ihs ihs ->
        List.map fst (con_case_bentries ihs) = X ++ vs ++ ihs /\
        List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) (con_case_bentries ihs).
    Proof.
      intros ihs Hir.
      destruct con_case_rel as [_ Hia].
      destruct (ER branch_entries_readable k Mk c gs ups ups X X vs vs ihs ihs Had Had HMk Hcon Hb Hv Hia Hir) as [Hrd2 _].
      assert (Hv2 : List.map fst (con_case_bentries ihs) = X ++ vs ++ ihs)
        by exact (ER branch_entries_values Mk ups (blocks_motives Bks) ρ gs X vs ihs).
      split; [ exact Hv2 |].
      unfold con_case_bentries in *; rewrite <- Hv2 in Hrd2; pose proof (Completeness.Inductives.Elim.Forall_combine_of_Forall2 _ _ _ Hrd2) as H0.
      rewrite combine_map_fst_snd in H0; exact H0.
    Qed.

    (** The branch's context relates the environment of its telescope at
        those values to the branch's own environment. *)
    Lemma con_case_env : forall ihs, rec_results_rel D dr Rel k ups ups X X (List.rev (im_nparams Mk)) gs vs vs ihs ihs ->
        forall RB, EF elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ
                   ≈ elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ ∈ per_ctx_env ↘ RB ->
        RB (env_tele ρ (List.rev (elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us)) (X ++ vs ++ ihs))
           (env_extend_typed ρ (con_case_bentries ihs)).
    Proof.
      intros ihs Hir RB HRB.
      destruct con_case_rel as [_ Hia].
      pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      set (Bc := elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us) in *.
      pose proof (EB Completeness.Inductives.Elim.canonical_bctx ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs HrvK
                    ρ ρ Hρ Hρ X X vs vs ihs ihs Hb Hv Hia Hir RB HRB) as HEc.
      (** The telescope's entries read back. *)
      assert (HBr : ⊨ List.rev (List.rev Bc) ++ Γ) by (rewrite List.rev_involutive; exact HBs).
      assert (HRBr : EF List.rev (List.rev Bc) ++ Γ ≈ List.rev (List.rev Bc) ++ Γ ∈ per_ctx_env ↘ RB)
        by (rewrite List.rev_involutive; exact HRB).
      assert (HtaB : all_assumptions (List.rev Bc)) by (apply List.Forall_rev; exact (elim_bctx_ass ak_relevant p D k Mk gs _ Us Hc HMk)).
      destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lih _].
      assert (LB : List.length (X ++ vs ++ ihs) = List.length (List.rev Bc))
        by (unfold Bc; rewrite List.length_rev, length_elim_bctx, !List.length_app, con_case_LX, Hvl, Lih; lia).
      unfold env_tele in HEc.
      destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HBr HtaB HRBr _ _ _ _ ltac:(rewrite Decl.tele_entries_length; exact LB)
                  ltac:(rewrite Decl.tele_entries_length; exact LB) HEc) as [Hr1 _].
      (** The branch's own entries read back. *)
      destruct (con_case_bentries_ok ihs Hir) as [Hv2 Hr2].
      unfold env_tele.
      exact (EB Completeness.Inductives.Elim.canonical_bctx_elem ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs HrvK
               ρ ρ Hρ Hρ ups ups hd k' bs bs vs vs ihs ihs con_case_GX Hir RB HRB _ _ (tele_entries_values _ _ _) Hv2 Hr1 Hr2).
    Qed.

    (** The substitution [ι] at [σ'], glued to the environment of the
        branch's telescope at those values. *)
    Lemma con_case_sub_tele : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel D dr Rel k ups ups X X (List.rev (im_nparams Mk)) gs vs vs ihs ihs ->
        forall Sb, EG elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ ∈ glu_ctx_env ↘ Sb ->
        Δ' ⊢ˢ sb_of_list σ' (Ns' ++ As ++ elim_ihs ak_relevant p D Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) (im_nn Mk) gs As)
          ® env_tele ρ (List.rev (elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us)) (X ++ vs ++ ihs) ∈ Sb.
    Proof.
      intros ihs Ei Hir Sb HSb.
      pose proof (con_case_ihs_args ihs Ei Hir) as Hgi.
      pose proof con_case_args as Hga.
      destruct (glu_args_length _ _ _ _ _ _ Hga) as [L1 L2].
      assert (HCa : all_assumptions (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU))
        by (apply all_assumptions_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_nparams_ass D Hc _ _ HMk) ]).
      assert (Esp : elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us
                    = ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                      ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)
        by (rewrite tele_sub_app, length_im_nparams; unfold elim_bctx; reflexivity).
      rewrite Esp in HSb |- *; rewrite <- List.app_assoc in HSb.
      rewrite (List.app_assoc X).
      eapply glu_sub_of_list; [ | rewrite <- List.app_assoc; exact HSb | exact HSbΓ | exact Hσ' |].
      - apply List.Forall_app; split; [ apply ihs_ctx_aux_ass | exact HCa ].
      - rewrite (List.app_assoc Ns').
        apply glu_args_app; [ exact HCa | exact L1 | exact L2 |].
        split; [ exact Hga | exact Hgi ].
    Qed.

    (** So glued to the branch's own environment ([glu_sub_retype]). *)
    Lemma con_case_sub : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel D dr Rel k ups ups X X (List.rev (im_nparams Mk)) gs vs vs ihs ihs ->
        forall Sb, EG elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ ∈ glu_ctx_env ↘ Sb ->
        Δ' ⊢ˢ sb_of_list σ' (Ns' ++ As ++ elim_ihs ak_relevant p D Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) (im_nn Mk) gs As)
          ® env_extend_typed ρ (con_case_bentries ihs) ∈ Sb.
    Proof.
      intros ihs Ei Hir Sb HSb.
      pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
      destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lih _].
      pose proof (con_case_sub_tele ihs Ei Hir Sb HSb) as Hτ; unfold env_tele in Hτ.
      pose proof (con_case_env ihs Hir RB HRB) as HE; unfold env_tele in HE.
      refine (glu_sub_retype _ _ _ _ (elim_bctx_ass ak_relevant p D k Mk gs _ Us Hc HMk) HSb HRB _ _ _ _ _ _ _ HE Hτ).
      - rewrite tele_entries_values; symmetry; exact (proj1 (con_case_bentries_ok ihs Hir)).
      - rewrite Decl.tele_entries_length, length_elim_bctx, !List.length_app, con_case_LX, Hvl, Lih; lia.
    Qed.
    (** The value of the branch's type in the branch's environment, against
        the motive's at the scrutinee: the branch's type is the motive at
        the constructor as the group reads it ([τb]), related to the
        scrutinee in the group. *)
    Lemma con_case_branch_type_rel : forall b ihs abt a0, List.nth_error Bks k = Some b ->
        rec_results_rel D dr Rel k ups ups X X (List.rev (im_nparams Mk)) gs vs vs ihs ihs ->
        ⟦ elim_branch_type p D k Mk c gs (eb_motive b) Us ⟧ env_extend_typed ρ (con_case_bentries ihs) ↘ abt ->
        ⟦ eb_motive b ⟧ env_tele ρ (List.rev (elim_mctx p D k Mk Us)) (ns ++ d_con hd k' c (bs ++ vs) :: nil) ↘ a0 ->
        Dom abt ≈ a0 ∈ per_univ iA.
    Proof.
      intros b ihs abt a0 Hbk Hir Eabt Ea0.
      destruct con_case_rel as [HnX _].
      destruct (con_case_bentries_ok ihs Hir) as [Hv2 Hr2].
      destruct (EB Completeness.Inductives.Elim.mctx_readable HMall k Mk HMk ρ ρ Hρ Hρ _ _ _ _ _ _ HGm) as [Hr0 _].
      unfold env_tele in Ea0.
      exact (branch_type_val_rel k Mk c gs b HMk Hcon HrvK Hbk hd k' bs vs ihs ns abt a0 _ _ Href Hbl con_case_GX Hir HnX Hv2 Hr2
               (tele_entries_values _ _ _) Hr0 Eabt Ea0).
    Qed.

    (** The constructor applied, as the member it is at reads it
        ([im_ref], [im_pre]): itself at a declared member, the container's
        at a view. *)
    Lemma con_case_con_ref : Δ' ⊢ apps (a_con p k c) (Us' ++ Ns' ++ As) ≈ apps (a_con hd k' c) (im_pre Mk Us' ++ Ns' ++ As)
        : im_ty_at p k Mk Us' Ns'.
    Proof.
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      pose proof Href as Href'.
      unfold im_ref in Href'; destruct (im_head Mk) as [pm | qc kc Is vm | qr Is fl] eqn:Hh;
        try (exfalso; exact (not_rview_record _ _ _ _ HrvK Hh)); injection Href' as <- <-.
      - unfold im_pre; rewrite Hh; apply wf_exp_eq_refl; gen_presups; eassumption.
      - destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mq & Hq & HMq & _ & _ & _ & _ & Hfst & _).
        destruct (cons_lookup_names (im_cons Mq) c) as [gh Hgh].
        { rewrite <- Hfst; apply (List.in_map fst _ (c, gs)), cons_lookup_in; exact Hcon. }
        unfold im_pre; rewrite Hh.
        exact (view_head_con_eq p D k Mk qc kc Is vm Dq Mq Hdt Hl Hc HMk Hh Hq HMq Δ' Us' Ns' As c gs gh HΔ' HUl' HNl'
                 con_case_Ps_typed Hgh Hcon HAl HAs).
    Qed.

    (** The constructor case: the eliminator evaluates to the branch at
        [ι]'s values, glued there; the elimination of [M'] is the branch at
        [ι] by [ι] and the congruence of the scrutinee, and the type of the
        branch is the motive's at the constructor, equal to its at [M']. *)
    Lemma con_case_main : elim_out k Mk Δ' σ' Ns' M' (d_con hd k' c (bs ++ vs)) ns.
    Proof.
      destruct con_case_ihs as (ihs & Ei & Hir).
      destruct (HBks _ _ HMk HrvK) as [b Hbk].
      destruct (brs_names_lookup _ _ _ _ (Hna _ _ _ HMk Hbk) Hcon) as (n & B & HlB & HinB).
      pose proof (Har _ _ _ _ _ _ _ HMk Hbk Hcon HinB) as Hn.
      destruct (glu_blocks_branch _ _ _ _ _ _ HBg _ _ _ _ _ _ _ HMk Hbk Hcon HinB) as [Sbb HSbb lvl Hbody].
      pose proof (con_case_sub ihs Ei Hir Sbb HSbb) as Hτ.
      destruct (Hbody _ _ _ Hτ) as [abt rB Pb Elb Eabt ErB Hgb HBgl].
      destruct (ER im_ref_target k Mk hd k' HMk Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
      destruct (eval_ihs_length _ _ _ _ _ _ _ _ Hl Hco Ei) as [_ Lih].
      (** The motive's value at the scrutinee is relevant, as a type of a
          universe; so is the branch type's, related to it. *)
      destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMk)) as [RM HRM].
      pose proof (EB Completeness.Inductives.Elim.mctx_at HMall k Mk HMk ρ ρ Hρ Hρ RM HRM _ _ _ _ _ _ HGm) as HEm.
      destruct (rel_exp_of_typ_relevant_at HRM (HAv _ _ _ HMk Hbk) _ _ HEm) as (a1 & Ea1 & Hk1).
      pose proof (con_case_branch_type_rel b ihs abt a1 Hbk Hir Eabt Ea1) as Hrel1.
      assert (Hkr : domain_kind abt = ak_relevant)
        by (destruct Hrel1 as [R1 HR1]; rewrite (per_univ_elem_kind _ _ _ _ HR1); exact Hk1).
      rewrite Hkr in ErB; cbn [glu_term_value] in ErB.
      (** The eliminator's value. *)
      assert (Ee : ⟦elim d_con hd k' c (bs ++ vs) at k of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rB).
      { eapply eval_elim_con; [ exact Hl | exact HMk | exact Href | exact Hq | exact HMq | exact Hcon
                              | rewrite List.length_app; unfold im_np; lia | exact Hbk | exact HlB | rewrite Hnnq; exact Hn
                              | exact Hco | |].
        - rewrite skipn_app_exact by (unfold im_np; lia); exact Ei.
        - rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact ErB. }
      (** The motive at the scrutinee, glued in the group ([AtType]). *)
      destruct (Completeness.Inductives.ViewReadback.mref_exists VP HVP p D HPD ups ups_tele_args ups_len k Mk HMk HrvK) as [[[hd0 k0] pre] Er].
      destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D k Mk ups hd0 k0 pre Hl HMk ups_len Er) as [Href0 Lpre].
      rewrite Href in Href0; injection Href0 as E1 E2; subst hd0 k0.
      assert (HIG : ind_glu_elem p D ups NEl AEl DP DEl k Δ' Us' Ns' M' (d_con hd k' c (bs ++ vs)))
        by (eapply ind_glu_elem_con; eassumption).
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_tele_args Hbu Hule Hf HΨall
                  nb Hnbu Hnbq Hnbr) as [Hel _].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (Hgl : forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
                Δ' ⊢ im_ty_at p k Mk (List.map (fun U => U[σ']) Us) Ns' ® P ->
                Δ' ⊢ M' : im_ty_at p k Mk (List.map (fun U => U[σ']) Us) Ns' ® d_con hd k' c (bs ++ vs) ∈ El).
      { intros i P El _ Hglu HT; rewrite <- HUs' in HT |- *.
        exact (proj1 (Hel _ _ _ _ _ _ HIG) Mk ns hd k' pre i P El HMk Er HUg' HMt Hgn Hns HGm Hglu HT). }
      pose proof Hgn as Hgn'; rewrite HUs' in Hgn'.
      destruct (motive_glu k Mk Δ' σ' Ns' ns M' _ hd k' pre HMk HrvK Hσ' Hgn' Hns Er Hgl) as (a0 & Ea0 & Hpa0 & HPa0).
      exists rB a0; [ exact Ee | exact Ea0 | exact Hpa0 |].
      intros P El Hg.
      pose proof (HPa0 P El Hg) as HTP.
      rewrite (blocks_motives_nth _ _ _ Hbk) in Ea0, HTP |- *.
      assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption).
      pose proof Hrel1 as Hrel.
      (** [ι], at the blocks at [σ']. *)
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      assert (HBt2 : blocks_typed gc_deps gc_stack Δ' p D (List.firstn (ind_nu D) (Us' ++ Ns')) (blocks_sub Bks σ') ak_relevant iA)
        by (rewrite firstn_app_exact by exact HUl'; exact HBt').
      assert (HPl : List.length (Us' ++ Ns') = im_np D Mk) by (rewrite List.length_app, HUl', HNl'; unfold im_np; lia).
      assert (Hbk' : List.nth_error (blocks_sub Bks σ') k = Some (eblock_sub b σ')) by (rewrite nth_error_blocks_sub, Hbk; reflexivity).
      assert (HlB' : brs_lookup (eb_brs (eblock_sub b σ')) c = Some (n, B[sb_qn n σ']))
        by (rewrite Completeness.Inductives.Elim.eb_brs_sub, brs_lookup_sub, HlB; reflexivity).
      set (Ihs := elim_ihs ak_relevant p D Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) (im_nn Mk) gs As) in *.
      assert (LIhs : List.length Ihs = cargs_nrec D gs) by (apply length_elim_ihs; exact HAl).
      pose proof (wf_elim_iota_blocks_typed Δ' p D k Mk (eblock_sub b σ') (blocks_sub Bks σ') c gs (Us' ++ Ns') As ak_relevant iA n
                    (B[sb_qn n σ']) HΔ' Hl HMk Hbk' Hcon HPl con_case_Ps_typed HAl HAs HBt2 HlB') as E1.
      rewrite firstn_app_exact, skipn_app_exact in E1 by exact HUl'.
      fold Ihs in E1; rewrite Href in E1; cbn [fst snd] in E1.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in E1.
      set (conA := apps (a_con hd k' c) (im_pre Mk Us' ++ Ns' ++ As)) in *.
      set (A' := (eb_motive b)[sb_qn (S (im_nn Mk)) σ']) in *.
      (** The scrutinee is the constructor, as its member reads it. *)
      assert (Emt : ind_mty p D k Us' Ns' = im_ty_at p k Mk Us' Ns') by (unfold ind_mty; rewrite HMk; reflexivity).
      assert (HMM : Δ' ⊢ M' ≈ conA : ind_mty p D k (List.firstn (ind_nu D) (Us' ++ Ns')) (List.skipn (ind_nu D) (Us' ++ Ns')))
        by (rewrite firstn_app_exact, skipn_app_exact, Emt by exact HUl'; exact (wf_exp_eq_trans _ _ _ _ _ _ _ HMeq con_case_con_ref)).
      pose proof (wf_elim_scrut_eq Δ' p D k Mk (eblock_sub b σ') (blocks_sub Bks σ') (Us' ++ Ns') M' conA ak_relevant iA Hl HMk Hbk' HPl
                    con_case_Ps_typed HBt2 HMM) as E2.
      rewrite firstn_app_exact, skipn_app_exact in E2 by exact HUl'.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in E2; fold A' in E2.
      pose proof (blocks_typed_motive _ _ _ _ _ _ _ _ _ HBt' _ _ _ HMk Hbk') as HAt.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in HAt; fold A' in HAt.
      assert (HΨ : ⊢ elim_mctx p D k Mk (List.firstn (ind_nu D) (Us' ++ Ns')) ++ Δ')
        by (rewrite firstn_app_exact by exact HUl'; gen_presups; assumption).
      destruct (presup_exp_eq HMM) as (_ & HM1 & HM2 & _).
      pose proof (wf_elim_inst_sub_eq _ _ Δ' p D k Mk (Us' ++ Ns') M' conA Hl HMk HΔ' HPl con_case_Ps_typed HM1 HM2 HMM HΨ) as Esub.
      rewrite firstn_app_exact, skipn_app_exact in Esub by exact HUl'.
      pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HAt Esub) as E3.
      (** The branch's type at [ι] at [σ'] is the motive at the constructor. *)
      assert (LL : List.length (Ns' ++ As ++ Ihs) = n) by (rewrite !List.length_app, HNl', HAl, LIhs, Hn; lia).
      assert (T1 : (elim_branch_type p D k Mk c gs (eb_motive b) Us)[sb_of_list σ' (Ns' ++ As ++ Ihs)] = A'[sb_of_list Id (Ns' ++ conA :: nil)]).
      { rewrite <- exp_sub_qn_of_list, LL, Hn, (elim_branch_type_sub p D k Mk c gs (eb_motive b) Us σ' Hc HMk HUl).
        fold A'; rewrite <- HUs', (elim_branch_type_iota p D k Mk c gs A' Us' Ns' As Ihs Hc HMk HUl' HNl' HAl LIhs).
        rewrite Href; reflexivity. }
      assert (T2 : B[sb_of_list σ' (Ns' ++ As ++ Ihs)] = B[sb_qn n σ'][sb_of_list Id (Ns' ++ As ++ Ihs)])
        by (rewrite <- LL, exp_sub_qn_of_list; reflexivity).
      rewrite T1, T2 in HBgl.
      destruct (presup_exp_eq E3) as (_ & HTm & _).
      assert (Eall : Δ' ⊢ a_elim ak_relevant p Us' k (blocks_sub Bks σ') M' ≈ B[sb_qn n σ'][sb_of_list Id (Ns' ++ As ++ Ihs)]
                       : A'[sb_of_list Id (Ns' ++ M' :: nil)]).
      { eapply wf_exp_eq_trans; [ exact E2 |].
        eapply wf_exp_eq_conv; [ exact E1 | exact HTm | apply wf_exp_eq_sym; exact E3 ]. }
      (** The branch's gluing moved to the motive's. *)
      assert (HTbr : Δ' ⊢ A'[sb_of_list Id (Ns' ++ conA :: nil)] ® P)
        by (eapply glu_univ_elem_typ_resp_exp_eq; [ exact Hg | exact HTP | rewrite Hk1; exact E3 ]).
      pose proof (glu_univ_elem_exp_conv Hrel Hgb Hg HBgl HTbr) as HM3.
      pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hg _ _ _ _ _ HM3 ltac:(rewrite Hk1; exact (wf_exp_eq_sym _ _ _ _ _ _ E3))) as HM4.
      rewrite <- HUs'.
      exact (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hg _ _ _ _ _ HM4 (wf_exp_eq_sym _ _ _ _ _ _ Eall)).
    Qed.
  End ConCase.

  (** ** Fresh Variables, Glued

      The fresh variables a stuck eliminator's readback reads a block's
      motive under, at [ups], against the entries of the motive's context
      in [ρ]: each of a type related to its entry's. *)
  Lemma mctx_entry_link : forall v Mv, ind_member D v = Some Mv -> forall s ns hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ ns ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      forall kk κ X a, List.nth_error (List.rev (elim_mctx p D v Mv Us)) kk = Some (ce_ass κ X) ->
        ⟦ X ⟧ env_tele ρ (List.rev (elim_mctx p D v Mv Us)) (List.firstn kk (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv) :: nil)) ↘ a ->
        exists b (n : nat), List.nth_error (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv) :: nil) kk = Some (⇑! b (s + kk)) /\
          Dom a ≈ b ∈ per_univ n.
  Proof.
    intros v Mv HMv s ns hd k pre Fn Hns Er kk κ X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (HMall _ _ HMv) as HMm.
    pose proof (rel_ctx_wf_tail HMm) as HNt.
    pose proof (member_params_ass D Hc _ _ HMv) as HPa.
    pose proof (valid_ind_decl_params _ HD _ _ HMv) as HPs.
    pose proof (EB Completeness.Inductives.Elim.nparams_closed_of_canon v Mv HMv ns ns Hns) as Hpg.
    unfold elim_mctx in HX, Ea; cbn [List.rev] in HX, Ea.
    assert (LT : List.length (List.rev (tele_sub (im_nparams Mv) (sb_of_list Id Us))) = im_nn Mv)
      by (rewrite List.length_rev, length_tele_sub, length_im_nparams; reflexivity).
    destruct (Nat.lt_ge_cases kk (im_nn Mv)) as [Hk | Hk].
    - (** A non-uniform parameter. *)
      rewrite env_tele_app_long in Ea by (rewrite List.length_firstn, LT; lia).
      rewrite List.nth_error_app1 in HX by lia.
      rewrite firstn_app_le in Ea by lia.
      destruct (inst_entry_link (im_nparams Mv) HPa HPs HNt ns Hpg ltac:(rewrite length_im_nparams; exact Ln) kk κ X a HX Ea)
        as (κ0 & A0 & b & n & HA & Eb & Hab).
      destruct (fresh_tele_nth _ _ _ _ Fn kk κ0 A0 HA) as (b' & Eb' & Hb').
      assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
      exists b, n; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
    - (** The scrutinee: at the member's type. *)
      assert (kk = im_nn Mv) as ->.
      { match type of HX with List.nth_error ?l _ = _ =>
          assert (Hlt : kk < List.length l) by (apply List.nth_error_Some; rewrite HX; discriminate) end.
        rewrite List.length_app, LT in Hlt; cbn in Hlt; lia. }
      rewrite List.nth_error_app2 in HX by lia.
      rewrite LT, Nat.sub_diag in HX; cbn in HX; injection HX as <- <-.
      rewrite env_tele_app_long in Ea by (rewrite List.length_firstn, LT; lia).
      rewrite firstn_app_le, List.firstn_all2 in Ea by lia.
      destruct (Completeness.Inductives.Elim.mty_vars_valid p D Hvg Hcv v Mv HMv) as [jx HXv].
      destruct (inst_link (im_nparams Mv) _ _ ns (type_sort_universe jx) HPa HPs HNt HXv Hpg ltac:(rewrite length_im_nparams; exact Ln))
        as (a1 & b & j1 & Ea1 & Eb & Hab).
      unfold τU in Ea1; rewrite length_im_nparams, (Completeness.Inductives.Elim.mty_vars_inst p D v Mv Us Hc HUl) in Ea1.
      assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (rel_ctx_wf_per_ctx_env HPs) as [RK HRK].
      assert (HKE : RK (components_env D ups (List.rev (im_nparams Mv)) (ns ++ nil)) (components_env D ups (List.rev (im_nparams Mv)) (ns ++ nil))).
      { rewrite List.app_nil_r; unfold components_env, im_params in *.
        exact (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRU HRK HPs ups_RU ltac:(rewrite length_im_nparams; exact Ln) Hpg). }
      replace ns with (ns ++ nil) in Eb at 1 by (rewrite List.app_nil_r; reflexivity).
      destruct (mty_val_rel VP HVP p D HPD ups ups_len ups_tele_args v Mv hd k pre (im_nparams Mv) RK ns nil 0 b ns HMv Er HPs HRK
                  ltac:(rewrite List.app_nil_r, length_im_nparams; exact Ln) Ln eq_refl HKE Eb Hns) as (i0 & R0 & H0).
      destruct (Decl.per_univ_elem_to_nat _ _ _ _ H0) as [n0 Hn0].
      exists (d_ind hd k (pre ++ ns)), n0; split.
      + rewrite List.nth_error_app2, Ln, Nat.sub_diag by lia; reflexivity.
      + apply per_univ_sym'; eapply per_univ_trans'; [ exists R0; exact Hn0 | apply per_univ_sym'; exact Hab ].
  Qed.

  (** The motive's context relates its telescope's environment at fresh
      non-uniform parameters [ns] and a fresh scrutinee to the motive's own
      environment there ([motive_entries], as readback evaluates the
      motive). *)
  Lemma fresh_motive_env : forall v Mv, ind_member D v = Some Mv -> im_is_rview Mv = false -> forall s ns hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ ns ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      forall RM, EF elim_mctx p D v Mv Us ++ Γ ≈ elim_mctx p D v Mv Us ++ Γ ∈ per_ctx_env ↘ RM ->
      RM (env_tele ρ (List.rev (elim_mctx p D v Mv Us)) (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv) :: nil))
         (env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) (⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv)))).
  Proof.
    intros v Mv HMv Hrv s ns hd k pre Fn Hns Er RM HRM.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D v Mv ups hd k pre Hl HMv ups_len Er) as [Href Lpre].
    set (x := ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv)).
    (** The fresh scrutinee is an element of the member. *)
    assert (HGx : G v ups ups ns ns x x).
    { eapply ind_rel_neut; [ exact HMv | exact Hrv | exact Href | exact Hns | | | | | exact var_per_bot ];
        try (rewrite List.length_app; lia); rewrite skipn_app_exact by exact Lpre; exact Hns. }
    (** Both sides' entries read back. *)
    destruct (EB Completeness.Inductives.Elim.mctx_readable HMall v Mv HMv ρ ρ Hρ Hρ _ _ _ _ _ _ HGx) as [Hr1 _].
    assert (Hv2 : List.map fst (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) x) = ns ++ x :: nil)
      by (unfold motive_entries; rewrite List.map_app, tele_entries_values; reflexivity).
    assert (Hr2 : List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) x)).
    { unfold motive_entries; apply List.Forall_app; split.
      - pose proof (nparams_entries_readable_at_admissible_base D ups nr ar dr ups v Mv ns ns Hass Had HMv Hns) as H0.
        rewrite <- (tele_entries_values ns (decl_env D ups) (List.rev (im_nparams Mv))) in H0 at 1.
        pose proof (Completeness.Inductives.Elim.Forall_combine_of_Forall2 _ _ _ H0) as H1.
        rewrite combine_map_fst_snd in H1; exact H1.
      - constructor; [| constructor ].
        exact (elim_ups_ok_member_elements_readable_at_ua _ _ _ _ _ _ _ _ Hups v Mv hd k pre ups ups ns ns ns x x HMv Hrv Had Had Er HGx Hns). }
    unfold env_tele.
    exact (EB Completeness.Inductives.Elim.mctx_at_typed HMall v Mv HMv ρ ρ Hρ Hρ RM HRM _ _ _ _ _ _ HGx _ _
             (tele_entries_values _ _ _) Hv2 Hr1 Hr2).
  Qed.

  (** The readback of the motive of the block of the member [v] under the
      fresh variables, against the motive at [σ''] past its context. *)
  Lemma readback_motive : forall v Mv b, ind_member D v = Some Mv -> List.nth_error Bks v = Some b ->
      forall Δ σ'' hd k pre ns a A', Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ length Δ ↘ ns ->
      ⟦ eb_motive b ⟧ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns))
                                          (⇑! (d_ind hd k (pre ++ ns)) (length Δ + im_nn Mv))) ↘ a ->
      Rtyp a in gc_deps ⍮ gc_stack ⍮ S (length Δ + im_nn Mv) ↘ A' ->
      glu_nf_eq (elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ) (eb_motive b)[sb_qn (S (im_nn Mv)) σ''] A' Typeω@iA.
  Proof.
    intros v Mv b HMv Hb Δ σ'' hd k pre ns a A' Hσ'' Er Fn Ea HRA.
    destruct (Completeness.Inductives.ViewReadback.fresh_nparams_exist p D Hvg ups ups_tele_args ups_len v Mv (List.length Δ) HMv)
      as (ns' & Fn' & Hns).
    pose proof (functional_fresh_tele' _ _ _ _ _ Fn' Fn) as <-.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (glu_blocks_motive _ _ _ _ _ _ HBg _ _ _ HMv Hb) as HAg.
    destruct HAg as [SbM HSbM iM HAg'].
    assert (HMl : List.length (elim_mctx p D v Mv Us) = S (im_nn Mv)) by (rewrite length_elim_mctx; reflexivity).
    assert (Lx : List.length (ns' ++ ⇑! (d_ind hd k (pre ++ ns')) (List.length Δ + im_nn Mv) :: nil) = List.length (elim_mctx p D v Mv Us))
      by (rewrite HMl, List.length_app, Ln; cbn; lia).
    pose proof (glu_sub_fresh _ Γ SbΓ (elim_mctx_ass p D v Mv Us Hc HMv) HSbΓ SbM HSbM Δ σ'' ρ _ Hσ'' Lx
                  (mctx_entry_link v Mv HMv (List.length Δ) ns' hd k pre Fn Hns Er)) as Hτ.
    rewrite (elim_mctx_sub p D v Mv Us σ'' Hc HMv HUl), HMl in Hτ.
    (** At the motive's own environment ([glu_sub_retype]). *)
    destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMv)) as [RM HRM].
    pose proof (fresh_motive_env v Mv HMv (Hbnr _ _ _ HMv Hb) (List.length Δ) ns' hd k pre Fn Hns Er RM HRM) as HE.
    unfold env_tele in Hτ, HE.
    set (x := ⇑! (d_ind hd k (pre ++ ns')) (List.length Δ + im_nn Mv)) in *.
    assert (Hv1 : List.map fst (tele_entries ρ (List.rev (elim_mctx p D v Mv Us)) (ns' ++ x :: nil))
                  = List.map fst (motive_entries D Mv ups ns' (d_ind hd k (pre ++ ns')) x))
      by (rewrite tele_entries_values; unfold motive_entries; rewrite List.map_app, tele_entries_values; reflexivity).
    assert (Lv1 : List.length (tele_entries ρ (List.rev (elim_mctx p D v Mv Us)) (ns' ++ x :: nil)) = List.length (elim_mctx p D v Mv Us))
      by (rewrite Decl.tele_entries_length; exact Lx).
    pose proof (glu_sub_retype _ _ _ _ (elim_mctx_ass p D v Mv Us Hc HMv) HSbM HRM _ _ _ _ _ Hv1 Lv1 HE Hτ) as Hτ'.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM (glu_blocks_motive _ _ _ _ _ _ HBg _ _ _ HMv Hb) Hτ') as (HAτ & a0 & Ea0 & Hpa & HPa).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (P & El & Hg).
    pose proof (HPa P El Hg) as HP.
    assert (HPM : PER RM) by (eapply per_env_PER; exact HRM).
    assert (HE2 : RM (env_extend_typed ρ (motive_entries D Mv ups ns' (d_ind hd k (pre ++ ns')) x))
                     (env_extend_typed ρ (motive_entries D Mv ups ns' (d_ind hd k (pre ++ ns')) x)))
      by (etransitivity; [ symmetry; exact HE | exact HE ]).
    pose proof (rel_type_value_not_level_sort _ _ _ _ _ _ _ _ (rel_type_of_abs_kind_sort (r := ak_relevant) (HAv _ _ _ HMv Hb))
                  HRM HE2 Ea) as Hnl.
    destruct (realize_glu_typ_top _ _ _ _ Hg Hnl _ _ HP) as [_ _ Hrbt].
    assert (HΔm : ⊢ elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ) by (gen_presups; assumption).
    assert (Hlen : List.length (elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ) = S (List.length Δ + im_nn Mv))
      by (rewrite List.length_app, length_elim_mctx; lia).
    rewrite <- Hlen in HRA.
    pose proof (Hrbt _ wk_id _ (kripke_id _ HΔm) HRA) as H.
    destruct (rel_exp_of_typ_relevant_at HRM (HAv _ _ _ HMv Hb) _ _ HE2) as (a2 & Ea2 & Hk2).
    assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
    rewrite exp_wk_id, Hk2 in H; exact H.
  Qed.

  (** The domains of the shape of a recursive argument after [gs1],
      defined after the non-recursive arguments before it. *)
  Lemma cargs_doms_ok_at : forall X Y k pre pre' Ts gs vs vs', cargs_doms_ok D ups nr dr X Y k pre pre' Ts gs vs vs' ->
      forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      shape_doms_ok D ups nr dr X Y k (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) (Ts ++ cargs_nonrec_tele gs1) t.
  Proof.
    intros X Y k pre pre' Ts gs vs vs' H gs1; revert pre pre' Ts gs vs vs' H; induction gs1 as [| g gs1 IH];
      intros pre pre' Ts gs vs vs' H t gs2 ->; inversion H; subst; cbn [List.app List.length List.firstn nonrec_arg_vals cargs_nonrec_tele] in *.
    - rewrite !List.app_nil_r; assumption.
    - match goal with H0 : cargs_doms_ok _ _ _ _ _ _ _ _ _ _ (gs1 ++ _) _ _ |- _ => pose proof (IH _ _ _ _ _ _ H0 t gs2 eq_refl) as H1 end.
      rewrite <- !List.app_assoc in H1; exact H1.
    - match goal with H0 : cargs_doms_ok _ _ _ _ _ _ _ _ _ _ (gs1 ++ _) _ _ |- _ => exact (IH _ _ _ _ _ _ H0 t gs2 eq_refl) end.
  Qed.

  (** The domains of the shapes of a constructor's arguments, all related
      to themselves: defined at [ups] ([cargs_doms_adm]). *)
  Corollary con_fields_doms : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      forall ns vs, tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns -> List.length vs = List.length gs ->
        tele_rel (ar k ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs) ->
        cargs_doms_ok D ups nr dr ups ups k ns ns (List.rev (im_nparams Mk)) gs vs vs.
  Proof.
    intros * HM Hcn ns vs Hns L [_ Hr].
    pose proof (cargs_doms_adm p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had ups ups Had Had k Mk c gs ns ns HM Hcn Hns
                  gs nil nil nil vs vs eq_refl L L (tele_prefix_rel_nil _) Hr) as H.
    rewrite !List.app_nil_r in H; exact H.
  Qed.

  (** Every leaf path of a recursive argument of a constructor of the
      group is the group's own ([leaf_in]). *)
  Lemma own_cargs_leaves : forall v Mv c gs, ind_member D v = Some Mv -> ind_con Mv c = Some gs ->
      forall gs1 t gs2 l, gs = gs1 ++ ca_rec t :: gs2 -> In l (shape_leaves (rview_leaves D) 0 t) -> leaf_in D t l = true.
  Proof.
    intros v Mv c gs HMv Hcon gs1 t gs2 l Heq Hin.
    destruct (rec_shape_facts v Mv c gs1 t gs2 0 HMv ltac:(rewrite <- Heq; exact Hcon)) as ((Mt & HMt & _) & _ & _).
    exact (own_leaves p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had t 0 l (ex_intro _ Mt HMt) Hin).
  Qed.

  (** An entry [kk] of a branch's context of the member [v] among its
      recursive results, the result along the leaf path [idx] of the
      recursive argument after [gs1]: the entry's value [a] is the type of
      the result along the path ([Elim.leaf_type_at]), and the result
      [ihs] has there is an element of it. *)
  #[warnings="-cannot-define-projection"]
  Record bctx_ih_entry (v : nat) (Mv : imember) (gs : list carg) (ns vs ihs : list domain) (kk : nat) (a : domain) : Prop :=
    mk_bctx_ih_entry
    { (** The arguments before the recursive one *)
      bie_before : list carg
      (** The recursive argument's shape *)
    ; bie_shape : ptyp
      (** The arguments after it *)
    ; bie_after : list carg
      (** The leaf path's index among the shape's *)
    ; bie_index : nat
      (** The recursive argument's value *)
    ; bie_arg : domain
      (** The level of the entry's type *)
    ; bie_lvl : nat
      (** The relation of the entry's type *)
    ; bie_rel : relation domain
      (** The result at the entry *)
    ; bie_val : domain
      (** The kinds, split at the recursive argument *)
    ; bie_split : gs = bie_before ++ ca_rec bie_shape :: bie_after
      (** The index is a leaf path's *)
    ; bie_bound : bie_index < List.length (shape_leaves (rview_leaves D) 0 bie_shape)
      (** The entry's position, past the parameters, the arguments and
          the results before *)
    ; bie_pos : kk = (im_nn Mv + List.length gs + (cargs_nrec D bie_before + bie_index))%nat
      (** The recursive argument *)
    ; bie_arg_at : List.nth_error vs (List.length bie_before) = Some bie_arg
      (** The recursive argument is related to itself by its shape *)
    ; bie_rec : rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr v ups ups
        (ns ++ nonrec_arg_vals bie_before (List.firstn (List.length bie_before) vs))
        (ns ++ nonrec_arg_vals bie_before (List.firstn (List.length bie_before) vs))
        (List.rev (im_nparams Mv) ++ cargs_nonrec_tele bie_before) bie_shape bie_arg bie_arg
      (** Its shape's domains are defined *)
    ; bie_doms : shape_doms_ok D ups nr dr ups ups v
        (ns ++ nonrec_arg_vals bie_before (List.firstn (List.length bie_before) vs))
        (ns ++ nonrec_arg_vals bie_before (List.firstn (List.length bie_before) vs))
        (List.rev (im_nparams Mv) ++ cargs_nonrec_tele bie_before) bie_shape
      (** The entry's value is the type of the result along the path *)
    ; bie_type : Elim.leaf_type_at D ups ρ (blocks_motives Bks) mctx_tele
        (ns ++ nonrec_arg_vals bie_before (List.firstn (List.length bie_before) vs))
        (List.rev (im_nparams Mv) ++ cargs_nonrec_tele bie_before) bie_shape bie_arg bie_index a
      (** The result at the entry *)
    ; bie_val_at : List.nth_error ihs (cargs_nrec D bie_before + bie_index) = Some bie_val
      (** The entry's type is a type *)
    ; bie_per : DF a ≈ a ∈ per_univ_elem bie_lvl ↘ bie_rel
      (** The result is an element of it *)
    ; bie_elem : bie_rel bie_val bie_val }.

  (** The fresh variables a stuck eliminator's readback reads a branch of
      the member [v] under, at [ups] (the non-uniform parameters, the
      arguments and the recursive results), against the entries of the
      branch's context in [ρ]: a parameter or an argument is a fresh
      variable of a type related to its entry's; a recursive result is
      described by [bctx_ih_entry]. *)
  Lemma bctx_link_gen : forall v Mv c gs, ind_member D v = Some Mv -> ind_con Mv c = Some gs -> im_is_rview Mv = false ->
      forall s ns vs ihs hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mv) ↘ vs ->
      List.length pre = im_unu D Mv ->
      G v ups ups ns ns (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)) ->
      rec_results_rel D dr Rel v ups ups ns ns (List.rev (im_nparams Mv)) gs vs vs ihs ihs ->
      forall kk κ X a, List.nth_error (List.rev (elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us)) kk = Some (ce_ass κ X) ->
        ⟦ X ⟧ env_tele ρ (List.rev (elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us)) (List.firstn kk (ns ++ vs ++ ihs)) ↘ a ->
        (kk < im_nn Mv + List.length gs /\
           exists b (n : nat), List.nth_error (ns ++ vs ++ ihs) kk = Some (⇑! b (s + kk)) /\ Dom a ≈ b ∈ per_univ n) \/
        bctx_ih_entry v Mv gs ns vs ihs kk a.
  Proof.
    intros v Mv c gs HMv Hcon Hrv s ns vs ihs hd k pre Fn Fc Lpre Hm Hir kk κ X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    assert (Hns : tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns /\
                  con_args_rel p D (admissible_index_at D ups nr) nr ar dr v ups ups ns ns (List.rev (im_nparams Mv)) gs vs vs /\
                  tele_rel (ar v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs)).
    { unfold grp_rel in Hm; inversion Hm; subst;
        match goal with H1 : ind_member D v = Some ?M1 |- _ => rewrite HMv in H1; injection H1 as <- end;
        [| match goal with H2 : im_head Mv = mh_record _ _ _ |- _ => exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end ].
      match goal with H1 : ind_con Mv c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app; lia ]; destruct E as [-> ->] end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app in *; lia ]; destruct E as [-> ->] end.
      rewrite skipn_app_exact in * by exact Lpre.
      split; [ assumption | split; assumption ]. }
    destruct Hns as (Hns & Hia & Hav).
    destruct (ER con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
    destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
    assert (Hbe : elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us
                  = ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                    ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)
      by (unfold elim_bctx; rewrite tele_sub_app, length_im_nparams; reflexivity).
    rewrite Hbe, List.rev_app_distr in HX, Ea.
    assert (LC : List.length (List.rev (tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)) = (im_nn Mv + List.length gs)%nat)
      by (rewrite List.length_rev, length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams; lia).
    assert (Ldecl : List.length (List.rev (im_nparams Mv)) = List.length ns) by (rewrite List.length_rev, length_im_nparams; lia).
    destruct (Nat.lt_ge_cases kk (im_nn Mv + List.length gs)) as [Hk | Hk].
    - (** The non-uniform parameters and the arguments: entries of the
          instance at [τU] of a closed telescope. *)
      left; split; [ exact Hk |].
      rewrite List.nth_error_app1 in HX by lia.
      rewrite env_tele_app_long in Ea by (rewrite List.length_firstn, LC; lia).
      assert (Hfk : List.firstn kk (ns ++ vs ++ ihs) = List.firstn kk (ns ++ vs))
        by (rewrite List.app_assoc, firstn_app_le by (rewrite List.length_app; lia); reflexivity).
      rewrite Hfk in Ea.
      pose proof (EB Completeness.Inductives.Elim.closed_args_tele_args v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                    (List.length gs) (le_n _)) as Hpg.
      rewrite List.firstn_all2, List.firstn_all2 in Hpg by lia.
      assert (HCa : all_assumptions ((cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D))
        by (rewrite <- List.app_assoc; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMv) ]).
      assert (HCs : ⊨ (cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; exact (valid_group_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon)).
      assert (HCS : ⊨ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU ++ Γ).
      { pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as H.
        rewrite Hbe, <- List.app_assoc in H; exact (Completeness.UnitCases.rel_ctx_wf_app_r _ _ H). }
      destruct (inst_entry_link _ HCa HCs HCS (ns ++ vs) Hpg
                  ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia) kk κ X a HX Ea)
        as (κ0 & A0 & b & n & HA0 & Eb & Hab).
      unfold components_env in Eb.
      rewrite List.rev_app_distr in HA0, Eb.
      destruct (Nat.lt_ge_cases kk (im_nn Mv)) as [Hk1 | Hk1].
      + rewrite List.nth_error_app1 in HA0 by lia.
        destruct (fresh_tele_nth _ _ _ _ Fn kk κ0 A0 HA0) as (b' & Eb' & Hb').
        rewrite firstn_app_le in Eb by lia.
        rewrite env_tele_app_long in Eb by (rewrite List.length_firstn; lia).
        assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
        exists b, n; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
      + rewrite List.nth_error_app2 in HA0 by lia.
        rewrite Ldecl in HA0.
        destruct (nth_error_lt_some gs (kk - im_nn Mv) ltac:(lia)) as [g Hg].
        destruct (List.nth_error_split _ _ Hg) as (gs1 & gs2 & Heq & Hl1).
        rewrite Ln, <- Hl1 in HA0.
        rewrite firstn_app_ge in Eb by lia; rewrite Ln in Eb; rewrite <- Hl1 in Eb.
        (** The environment of the entry's type: the closed telescope of
            the arguments before. *)
        set (fa := List.firstn (List.length gs1) vs) in *.
        assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn; lia).
        assert (HEenv : env_tele (decl_env D ups) (List.rev (im_nparams Mv) ++ List.rev (cargs_ctx p D Mv gs)) (ns ++ fa)
                        = env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa)).
        { rewrite Heq at 1; rewrite cargs_ctx_app, List.rev_app_distr, List.app_assoc.
          rewrite env_tele_app_long by (rewrite !List.length_app, !List.length_rev, length_cargs_ctx, length_im_nparams, Lfa; lia).
          unfold im_params, decl_env; rewrite !List.rev_app_distr, <- !List.app_assoc.
          rewrite (env_tele_app nil (List.rev (ind_uparams D)) _ ups (ns ++ fa)) by (rewrite List.length_rev, ups_len; reflexivity).
          reflexivity. }
        rewrite HEenv in Eb.
        assert (Hnthw : forall x, List.nth_error vs (List.length gs1) = Some x -> List.nth_error (ns ++ vs ++ ihs) kk = Some x).
        { intros x Hx; rewrite List.nth_error_app2 by lia; rewrite Ln, <- Hl1; rewrite List.nth_error_app1 by lia; exact Hx. }
        destruct (fresh_cargs_nth _ _ _ _ _ _ Fc gs1 g gs2 Heq) as [Fa Fr].
        assert (HEenv2 : env_tele (env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns) (cargs_nonrec_tele gs1) (nonrec_arg_vals gs1 fa)
                         = components_env D ups (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) (ns ++ nonrec_arg_vals gs1 fa))
          by (unfold components_env; rewrite env_tele_app by exact (eq_sym Ldecl); reflexivity).
        pose proof (EB Completeness.Inductives.Elim.closed_args_tele_args v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                      (List.length gs1) ltac:(lia)) as Hpg1.
        replace (List.firstn (List.length gs1) gs) with gs1 in Hpg1 by (rewrite Heq; symmetry; apply firstn_app_len; reflexivity).
        assert (Hpg2 : per_tele_args (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
        { unfold im_params; rewrite List.app_assoc, List.rev_app_distr.
          apply Decl.per_tele_args_app_intro; [ rewrite List.length_rev; exact ups_len | exact ups_tele_args | exact Hpg1 ]. }
        destruct g as [r0 B0 | t].
        * (** A non-recursive argument: its type at the non-recursive
              values. *)
          pose proof (cargs_rev_nth_arg p D Mv gs gs1 r0 B0 gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as -> ->.
          destruct (Fa r0 B0 eq_refl) as (a' & Ea' & Hv).
          fold fa in Ea', Hv; rewrite HEenv2 in Ea'.
          destruct (valid_group_arg_types p D Hvg Hcv v Mv c gs gs1 r0 B0 gs2 ups ns fa HMv Hcon Heq ups_len Ln Lfa Hpg2)
            as (i & R & a1 & a1' & Ea1 & Ea1' & HR).
          assert (a1 = b) as -> by (eapply functional_eval_exp; eassumption).
          assert (a1' = a') as -> by (eapply functional_eval_exp; eassumption).
          exists a', n; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia |].
          eapply per_univ_trans'; [ exact Hab | exists R; exact HR ].
        * (** A recursive argument: the type of its shape ([shape_type_link]). *)
          pose proof (cargs_rev_nth_rec p D Mv gs gs1 t gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as -> ->.
          destruct (Fr t eq_refl) as (a' & Ea' & Hv).
          fold fa in Ea', Hv; rewrite HEenv2 in Ea'.
          pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hav Lv Heq) as Hpk; fold fa in Hpk.
          destruct (valid_group_cargs_sem_all p D Hvg Hcv v Mv c gs HMv Hcon gs1 (ca_rec t :: gs2) Heq) as [HW0 _].
          destruct (rel_ctx_wf_per_ctx_env HW0) as [R0 HR0].
          assert (HE0 : R0 (env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa))
                           (env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa))).
          { apply (Completeness.Inductives.Model.tele_args_env_rel _ _ _ _ _ _ HR0 HW0);
              [ rewrite !List.length_app, length_cargs_ctx, length_im_params, Ln, Lfa, ups_len; unfold im_np, ind_nu in *; lia |].
            exact Hpg2. }
          assert (Hpre_env : forall R, EF cargs_ctx p D Mv gs1 ++ im_params D Mv ≈ cargs_ctx p D Mv gs1 ++ im_params D Mv
                                          ∈ per_ctx_env ↘ R ->
                               R (env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa))
                                 (env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa))).
          { intros R HR; apply (per_ctx_env_right_irrel _ _ _ _ _ HR0 HR); exact HE0. }
          pose proof (fun Mj qc kc Is vm Dq cups cs bs0 bs0' =>
                        ViewReadback.view_end_type VP HVP p D HPD ups ups_tele_args ups_len (ptyp_mem t) Mj qc kc Is vm Dq cups cs bs0 bs0') as Hend.
          assert (Hbb : Dom b ≈ b ∈ per_univ n) by (eapply per_univ_trans'; [ apply per_univ_sym'; exact Hab | exact Hab ]).
          destruct Hbb as [Rb HRb].
          destruct (shape_type_link p D Hvg Hcv v Mv c gs HMv Hcon (valid_group_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon) gs1 t gs2 Heq
                      ups ns fa ups_len Ln Lfa ups_tele_args Hns Hpk Hpre_env Hend
                      (List.length (ptyp_doms t)) 0 nil b n Rb ltac:(lia) (tele_prefix_rel_nil _) ltac:(cbn; apply per_tele_args_nil)
                      ltac:(cbn [List.repeat List.app ptyp_skip List.firstn shape_domains_ctx List.rev];
                            change (env_tele ?E0 nil nil) with E0; exact Eb) HRb)
            as (bsh & Ebsh & Hbs).
          cbn [ptyp_skip] in Ebsh; rewrite List.app_nil_r in Ebsh.
          unfold components_env in Ebsh, Ea'; rewrite List.app_assoc, env_tele_app_long in Ebsh
            by (rewrite !List.length_app, List.length_rev, length_im_nparams, length_cargs_nonrec_tele, length_nonrec_arg_vals by exact Lfa; lia).
          pose proof (functional_eval_shape_type _ _ _ _ _ _ Ebsh Ea') as <-.
          exists bsh, n; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia |].
          eapply per_univ_trans'; [ exact Hab | exact Hbs ].
    - (** A recursive result: the type of the result along its leaf
          path ([ihs_entry_type]), the result an element of it. *)
      right.
      rewrite List.nth_error_app2 in HX by lia; rewrite LC in HX.
      set (j := kk - (im_nn Mv + List.length gs)) in *.
      assert (Hj : j < cargs_nrec D gs).
      { assert (Hs : j < List.length (List.rev (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs)))
          by (apply List.nth_error_Some; congruence).
        rewrite List.length_rev, length_ihs_ctx_aux in Hs; exact Hs. }
      destruct (rec_leaf_pos_of_lt D gs j Hj) as [gs1 t gs2 idx Heq Hidx Hjat].
      destruct (nth_error_lt_some (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mv) t) idx) as [l Hl0].
      { rewrite (length_shape_leaves _ _ _ 0); exact Hidx. }
      pose proof (ihs_ctx_nth ak_relevant D (im_nn Mv) (blocks_motives Bks) Us (List.length gs) gs gs1 t gs2 idx l Heq Hl0) as EX.
      rewrite <- Hjat, HX in EX; injection EX as -> ->.
      set (TB := List.rev (tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)) in *.
      set (IC := ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs) in *.
      assert (Hfk : List.firstn kk (ns ++ vs ++ ihs) = (ns ++ vs) ++ List.firstn j ihs)
        by (rewrite List.app_assoc, firstn_app_ge by (rewrite List.length_app; lia); rewrite List.length_app, Ln, Lv; reflexivity).
      rewrite Hfk, env_tele_app in Ea by (unfold TB; rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_im_nparams; lia).
      destruct (Completeness.Inductives.CargsRel.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & v' & Hx & Hv1' & Hsh).
      rewrite Hv1' in Hx; injection Hx as <-.
      pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as HBs.
      (** The components and the results, related at their telescopes. *)
      pose proof (EB Completeness.Inductives.Elim.canonical_args_tele Bks v Mv c gs HMv Hcon HBs
                    ρ ρ Hρ Hρ ns ns vs vs Hns Hav Hia) as Hci.
      pose proof (EB Completeness.Inductives.Elim.canonical_ihs ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs Hrv
                    ρ ρ Hρ Hρ ns ns vs vs ihs ihs Hns Hav Hia Hir Hci (List.length gs) (le_n _)) as Hpgi.
      rewrite List.firstn_all, !List.firstn_all2 in Hpgi by lia; fold IC in Hpgi.
      (** The entry's value: the type of the result along the path. *)
      assert (Ea' := Ea); rewrite Hjat in Ea'.
      pose proof (EB Completeness.Inductives.Elim.ihs_entry_type ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs Hrv
                    ρ Hρ gs1 t gs2 Heq ns vs ihs Hns Hav Hia Hci Li Hpgi idx l v' a Hl0 Hv1' Ea') as Hlt.
      (** The result at the entry, an element of it. *)
      destruct (per_tele_args_nth_elem _ _ _ _ _ j _ _ Hpgi HX ltac:(rewrite Li; exact Hj))
        as (i0 & Rae & ae & ae' & x0 & x0' & Eae & Eae' & HRae & Hx0 & Hx0' & Hrr).
      rewrite Hx0 in Hx0'; injection Hx0' as <-.
      assert (ae = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (ae' = a) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (cargs_doms_ok_at _ _ _ _ _ _ _ _ _ (con_fields_doms v Mv c gs HMv Hcon ns vs Hns Lv Hav) gs1 t gs2 Heq) as Hdoms.
      exact (mk_bctx_ih_entry v Mv gs ns vs ihs kk a gs1 t gs2 idx v' i0 Rae x0 Heq Hidx ltac:(unfold j in Hjat; lia) Hv1' Hsh Hdoms
               Hlt ltac:(rewrite <- Hjat; exact Hx0) HRae Hrr).
  Qed.

  (** The type of the recursive result along a leaf path of a neutral
      recursive argument, after [pre], against its type as readback reads
      it ([eval_ihty]): related at the level of the former. *)
  Lemma leaf_ihty_link : forall pre Ts t v idx a,
      Elim.leaf_type_at D ups ρ (blocks_motives Bks) mctx_tele pre Ts t v idx a ->
      forall k, List.length pre = List.length Ts -> idx < List.length (shape_leaves (rview_leaves D) 0 t) ->
      rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k ups ups pre pre Ts t v v -> is_neut v ->
      shape_doms_ok D ups nr dr ups ups k pre pre Ts t ->
      forall (i : nat) R, DF a ≈ a ∈ per_univ_elem i ↘ R ->
      forall bs, ⟦ihty v of t at p ups under ρ (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bs ->
      exists b, List.nth_error bs idx = Some b /\ Dom a ≈ b ∈ per_univ i.
  Proof.
    induction 1 as [pre Ts j Mj Ps v bs b a i0 HMj Hrv Ebs Eb Hab
                   | pre Ts j Mj qr Is fl c gs gs1 tf gs2 Ps v ws w idx a HMj Hh Hcs Ew Heq Hw Hidx0 Hlt IH
                   | pre Ts B t v idx b0 b ρF F i1 Eb0 Hbb0 Hcl IH];
      intros k Lp Hidx Hsh Hn Hd i R HR bs0 Ety.
    - (** At the end: the motive at the shape's parameters, at the
          entries readback stores them at ([motive_rel]). *)
      inversion Ety; subst;
        match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H; injection H as <- end.
      + match goal with H : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs1 |- _ => pose proof (functional_eval_exps' _ _ _ _ H Ebs) as -> end.
        match goal with H : ⟦ List.nth j (blocks_motives Bks) a_prop ⟧ env_extend_typed ρ _ ↘ _ |- _ => rename H into Ea2 end.
        match goal with H : ind_member D j = Some ?M0 |- _ =>
          tryif constr_eq M0 Mj then fail else (rewrite HMj in H; injection H as <-) end.
        destruct (HBks _ _ HMj Hrv) as [bj Hbj].
        rewrite (blocks_motives_nth _ _ _ Hbj) in Eb, Ea2.
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (b1 & b2 & Eb1 & Eb2 & _ & _ & HGv).
        pose proof (functional_eval_exps' _ _ _ _ Eb1 Ebs) as ->.
        pose proof (functional_eval_exps' _ _ _ _ Eb2 Ebs) as ->.
        pose proof (ind_rel_ns p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ j Mj _ _ _ _ _ _ HMj HGv) as Hbb.
        destruct (Completeness.Inductives.ViewReadback.mref_exists VP HVP p D HPD ups ups_tele_args ups_len j Mj HMj Hrv)
          as [[[hd k'] pa] Er].
        destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D j Mj ups hd k' pa Hl HMj ups_len Er) as [Href _].
        (** Both environments' entries read back. *)
        destruct (EB Completeness.Inductives.Elim.mctx_readable HMall j Mj HMj ρ ρ Hρ Hρ _ _ _ _ _ _ HGv) as [Hr1 _].
        apply (Completeness.Inductives.Elim.Forall2_of_Forall_pairs (fun v t => entry_readable (de_term v t))) in Hr1.
        rewrite tele_entries_values in Hr1.
        pose proof (ER motive_self_entries_readable ups (components_env D ups Ts pre) j Mj Ps bs bs hd k' v Had
                      (elim_ups_ok_mref_a _ _ _ _ _ _ _ _ Hups)
                      (fun pa0 Er0 => elim_ups_ok_member_elements_readable_at_ua _ _ _ _ _ _ _ _ Hups j Mj hd k' pa0 ups ups bs bs bs v v
                                        HMj Hrv Had Had Er0 HGv Hbb)
                      HMj Hrv Href Ebs Hbb) as Hr2.
        destruct (motive_rel j Mj bj bj ups ups bs bs v v _ _ HMj Hrv Hbj Hbj HGv Hr1 Hr2) as (a1 & a2 & Ea1 & Ea2' & Ha12 & _).
        rewrite <- (tele_entries_values (bs ++ v :: nil) ρ (List.rev (elim_mctx p D j Mj Us))) in Ea1 at 1.
        rewrite combine_map_fst_snd in Ea1.
        assert (Hv2 : List.map fst (tele_entries (decl_env D ups) (List.rev (im_nparams Mj)) bs
                                    ++ (v, entry_type_shape p ups (components_env D ups Ts pre) (pt_self j Ps)) :: nil) = bs ++ v :: nil)
          by (rewrite List.map_app, tele_entries_values; reflexivity).
        rewrite <- Hv2 in Ea2' at 1; rewrite combine_map_fst_snd in Ea2'.
        lazymatch type of Ea2 with ⟦ _ ⟧ _ ↘ ?a3 => exists a3 end.
        split; [ reflexivity |].
        unfold env_tele in Eb; rewrite (mctx_tele_at _ _ HMj) in Eb.
        assert (a1 = b) as -> by (eapply functional_eval_exp; eassumption).
        match goal with |- Dom _ ≈ ?a3 ∈ _ => assert (a2 = a3) as -> by (eapply functional_eval_exp; eassumption) end.
        eapply per_univ_trans'; [ exists R; exact HR |].
        eapply per_univ_trans'; [ exact Hab | exists (Rel j bs v bs v); exact Ha12 ].
      + match goal with H1 : ind_member D _ = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
          rewrite HMj in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end.
    - (** At a record view: the field's, at its projection. *)
      inversion Ety; subst;
        match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H; injection H as <- end;
        match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end.
      { exfalso; match goal with H3 : im_is_rview Mj = false |- _ => exact (not_rview_record _ _ _ _ H3 Hh) end. }
      match goal with H1 : im_head Mj = _ |- _ => rewrite Hh in H1; injection H1 as <- <- <- end.
      match goal with H1 : im_cons Mj = _ |- _ => rewrite Hcs in H1; injection H1 as <- <- end.
      match goal with H1 : ⟦projs fl of v ⟧ _ ⍮ _ ↘ ?ws1 |- _ => pose proof (functional_eval_projs _ _ _ _ H1 Ew) as -> end.
      match goal with H1 : ⟦ihtys ws of _ at _ _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ bs0 |- _ =>
        destruct (eval_ihtys_nth p D ups ρ (blocks_motives Bks) Hl Hco gs1 tf gs2 _ ws bs0 w H1 Hw) as (rf & Erf & Hrs) end.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bsx & bsx' & _ & _ & _ & _ & Hi).
      inversion Hi; subst;
        match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end;
        try (exfalso; match goal with H3 : im_is_rview Mj = false |- _ => exact (not_rview_record _ _ _ _ H3 Hh) end).
      match goal with H1 : im_head Mj = _ |- _ => rewrite Hh in H1; injection H1 as <- <- <- end.
      match goal with H1 : im_cons Mj = _ |- _ => rewrite Hcs in H1; injection H1 as <- <- end.
      repeat match goal with H1 : ⟦projs fl of v ⟧ _ ⍮ _ ↘ ?ws1 |- _ =>
        tryif constr_eq ws1 ws then fail else pose proof (functional_eval_projs _ _ _ _ H1 Ew) as -> end.
      match goal with H6 : con_args_rel _ _ _ _ _ _ j ups ups nil nil _ _ ws ws,
                      H5 : tele_rel (ar j nil c) _ _ _ |- _ => rename H6 into Hca, H5 into Hnr end.
      destruct (Completeness.Inductives.CargsRel.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca gs1 tf gs2 eq_refl)
        as (x & x' & Hx & Hx' & Hshf).
      rewrite Hw in Hx, Hx'; injection Hx as <-; injection Hx' as <-.
      assert (Hnw : is_neut w)
        by exact (proj1 (List.Forall_forall _ _) (is_neut_projs _ _ _ Ew Hn) w (List.nth_error_In _ _ Hw)).
      destruct (ER con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hca) as [Lws _].
      pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as Enp.
      destruct Hnr as [_ Hnr'].
      pose proof (rview_cargs_doms p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had ups ups Had Had j Mj qr Is fl c _ HMj Hh Hcs
                    _ nil nil nil ws ws eq_refl Lws Lws (tele_prefix_rel_nil _) Hnr') as Hdf.
      rewrite Enp in Hdf; cbn [List.rev List.app cargs_nonrec_tele] in Hdf.
      try (rewrite Enp in Hshf); cbn [List.rev List.app cargs_nonrec_tele] in Hshf.
      pose proof (cargs_doms_ok_at _ _ _ _ _ _ _ _ _ Hdf gs1 tf gs2 eq_refl) as Hdf1.
      cbn [List.app] in Hshf, Hdf1.
      assert (Lp1 : List.length (nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws)) = List.length (cargs_nonrec_tele gs1))
        by (rewrite length_cargs_nonrec_tele; apply length_nonrec_arg_vals; rewrite List.length_firstn, Lws, List.length_app; lia).
      destruct (IH j Lp1 Hidx0 Hshf Hnw Hdf1 i R HR rf Erf) as (b & Hb & Hab).
      exists b; split; [| exact Hab ].
      rewrite Hrs by (apply List.nth_error_Some; congruence); exact Hb.
    - (** At a domain: a [Π], its codomains at related arguments by the
          induction at the function's values there. *)
      inversion Ety; subst;
        match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H; injection H as <- end.
      match goal with H : ⟦ B ⟧ _ ↘ ?b1 |- _ => tryif constr_eq b1 b0 then fail else
        (assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption)) end.
      assert (Hidx' : idx < List.length (shape_leaves (rview_leaves D) 0 t))
        by (cbn [shape_leaves] in Hidx; rewrite List.length_map, (length_shape_leaves _ _ 1 0) in Hidx; exact Hidx).
      eexists; split.
      { rewrite List.nth_error_map, List.nth_error_seq; destruct (Nat.ltb_spec idx (List.length (shape_leaves (rview_leaves D) 0 t)));
          [ reflexivity | lia ]. }
      basic_invert_per_univ_elem HR.
      match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
      cbn [Nat.add].
      destruct Hbb0 as [Rb HRb].
      destruct (Instance.per_univ_elem_trans_any _ _ _ _ _ _ _ equiv_a_a' HRb) as (Rd & HRd & ERd).
      eexists; apply (per_univ_elem_pi_canonical HRd).
      intros c c' Hcc.
      assert (Hin : in_rel c c') by (apply ERd; exact Hcc).
      assert (Hin0 : in_rel c' c') by (etransitivity; [ symmetry; exact Hin | exact Hin ]).
      destruct (Hcod _ _ Hin) as [xc x2 Exc Ex2 Hxx].
      destruct (Hcod _ _ Hin0) as [x' x'' Ex' Ex'' Hx'x'].
      assert (x2 = x') as -> by (eapply functional_eval_exp; eassumption).
      assert (x'' = x') as -> by (eapply functional_eval_exp; eassumption).
      (** The argument, at the domain's canonical relation. *)
      destruct (per_univ_trans' _ _ _ _ _ (per_univ_sym' _ _ _ (ex_intro _ Rd HRd)) (ex_intro _ Rd HRd)) as [R2 HR2].
      assert (Hc2 : R2 c' c') by (apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRd HR2); apply ERd; exact Hin0).
      pose proof (rel_dr D ups k pre Ts B b0 i R2 c' Eb0 HR2 Hc2) as Hdc'.
      (** The function's value there, and the types of its results
          ([ih_leaves_all]). *)
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c' c' Hdc') as (fc & fc0 & Efc & Efc0 & Hshc).
      assert (fc0 = fc) as -> by (eapply functional_eval_app; eassumption).
      inversion Hd as [| ? ? ? ? ? bd bd' Ebd Ebd' _ Hdcl _ _ _ _]; subst.
      pose proof (Hdcl c' c' Hdc') as Hdc''.
      pose proof (is_neut_app _ _ _ Efc Hn) as Hnfc.
      assert (Lp' : List.length (pre ++ c' :: nil) = List.length (Ts ++ ce_ass ak_relevant B :: nil))
        by (rewrite !List.length_app, Lp; reflexivity).
      destruct (proj1 (proj2 (proj2 (ER ih_leaves_all))) k ups ups (pre ++ c' :: nil) (pre ++ c' :: nil)
                  (Ts ++ ce_ass ak_relevant B :: nil) t fc fc Hshc eq_refl eq_refl Lp' Lp' Hnfc Hnfc Hdc'' _ (leaf_flags_ok_fresh_all _ _))
        as [tya tyb resa resb Ta _ _ _ _ _ _ _ _].
      destruct (IH c' Hdc' x' fc Ex' Efc k Lp' Hidx' Hshc Hnfc Hdc'' i _ Hx'x' tya Ta) as (y & Hy & Hx'y).
      destruct (per_univ_trans' _ _ _ _ _ (ex_intro _ (out_rel c c' Hin) Hxx) Hx'y) as [R0 HR0].
      exists xc, y, R0; split; [ exact Exc | split; [| exact HR0 ] ].
      unfold components_env in Ta; rewrite env_tele_snoc in Ta by exact Lp.
      eapply eval_fam_cod_ihfam; [ exact Efc | exact Ta | exact Hy ].
      (** The kinds and the sorts of the [Π]. *)
      all: first [ intros ? ? Hc0; match goal with Hk : forall c c', ?ir c c' -> rel_typ_kind _ _ _ |- _ =>
                                     eapply Hk; apply (proj2 (ERd _ _)); exact Hc0 end
                 | intros ? ? Hc0; match goal with Hk : forall c c', ?ir c c' -> value_not_level_sort _ _ |- _ =>
                                     eapply Hk; apply (proj2 (ERd _ _)); exact Hc0 end
                 | assumption
                 | constructor
                 | rewrite <- (per_univ_elem_kind _ _ _ _ HRd); assumption ].
  Qed.

  (** At fresh recursive results, every entry is a fresh variable of a
      type related to its entry's. *)
  Lemma bctx_entry_link : forall v Mv c gs, ind_member D v = Some Mv -> ind_con Mv c = Some gs -> im_is_rview Mv = false ->
      forall s ns vs ihs hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mv) ↘ vs ->
      Fihs vs at gs gs of D under ρ (blocks_motives Bks) at p ups in gc_deps ⍮ gc_stack
        ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mv + List.length gs) ↘ ihs ->
      List.length pre = im_unu D Mv ->
      G v ups ups ns ns (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)) ->
      rec_results_rel D dr Rel v ups ups ns ns (List.rev (im_nparams Mv)) gs vs vs ihs ihs ->
      forall kk κ X a, List.nth_error (List.rev (elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us)) kk = Some (ce_ass κ X) ->
        ⟦ X ⟧ env_tele ρ (List.rev (elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us)) (List.firstn kk (ns ++ vs ++ ihs)) ↘ a ->
        exists b (n : nat), List.nth_error (ns ++ vs ++ ihs) kk = Some (⇑! b (s + kk)) /\ Dom a ≈ b ∈ per_univ n.
  Proof.
    intros v Mv c gs HMv Hcon Hrv s ns vs ihs hd k pre Fn Fc Fi Lpre Hm Hir kk κ X a HX Ea.
    destruct (bctx_link_gen v Mv c gs HMv Hcon Hrv s ns vs ihs hd k pre Fn Fc Lpre Hm Hir kk κ X a HX Ea)
      as [[_ H] | [gs1 t gs2 idx v' lv Rv x Heq Hidx -> Hv' Hshv Hdv Hlt Hx HRa Hxx]]; [ exact H |].
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
    (** The fresh variable at the entry, at the type readback reads it at. *)
    assert (Hown : forall gs1' t' gs2' l, gs = gs1' ++ ca_rec t' :: gs2' -> In l (shape_leaves (rview_leaves D) 0 t') ->
                     leaf_in D t' l = true).
    { intros gs1' t' gs2' l Heq' Hin.
      destruct (rec_shape_facts v Mv c gs1' t' gs2' 0 HMv ltac:(rewrite <- Heq'; exact Hcon)) as ((Mt & HMt & _) & _ & _).
      exact (own_leaves p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had t' 0 l (ex_intro _ Mt HMt) Hin). }
    destruct (fresh_ihs_own_nth _ _ _ _ _ _ _ _ _ _ Hl Fi Hown gs1 t gs2 v' Heq Hv') as (as' & Eas & Hih).
    assert (Ldecl : List.length ns = List.length (List.rev (im_nparams Mv))) by (rewrite List.length_rev, length_im_nparams; lia).
    rewrite <- env_tele_app in Eas by exact Ldecl; fold (components_env D ups (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1)
                                                      (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))) in Eas.
    assert (Hnv : is_neut v').
    { destruct (fresh_cargs_nth _ _ _ _ _ _ Fc gs1 (ca_rec t) gs2 Heq) as [_ Fr].
      destruct (Fr t eq_refl) as (a0 & _ & Hv0); rewrite Hv' in Hv0; injection Hv0 as ->.
      exists a0, (d_var (s + im_nn Mv + List.length gs1)); reflexivity. }
    assert (Lp : List.length (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                 = List.length (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1)).
    { rewrite !List.length_app, <- Ldecl, length_cargs_nonrec_tele, length_nonrec_arg_vals; [ reflexivity |].
      rewrite List.length_firstn, Lv, Heq, List.length_app; cbn; lia. }
    destruct (leaf_ihty_link _ _ _ _ _ _ Hlt v Lp Hidx Hshv Hnv Hdv lv Rv HRa as' Eas) as (b & Hb & Hab).
    exists b, lv; split; [| exact Hab ].
    rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
    rewrite List.length_app, Ln, Lv.
    replace (im_nn Mv + List.length gs + (cargs_nrec D gs1 + idx) - (im_nn Mv + List.length gs)) with (cargs_nrec D gs1 + idx) by lia.
    rewrite (Hih idx b Hb); do 3 f_equal; lia.
  Qed.

  (** The readback of a branch of the block of the member [v] under the
      fresh variables, recursive results included, against the branch at
      [σ''] past its context, up to proofs: the branch is glued at the
      fresh substitution, retyped at the branch's own environment
      ([glu_sub_retype]), at the motive's value at the constructor. *)
  Lemma readback_branch : forall v Mv b c gs n B, ind_member D v = Some Mv -> im_is_rview Mv = false -> List.nth_error Bks v = Some b ->
      ind_con Mv c = Some gs -> In (c, n, B) (eb_brs b) ->
      forall Δ σ'' hd k pre ns vs ihs bv t0 Bn, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ length Δ ↘ ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (length Δ + im_nn Mv) ↘ vs ->
      Fihs vs at gs gs of D under ρ (blocks_motives Bks) at p ups in gc_deps ⍮ gc_stack
        ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (length Δ + im_nn Mv + List.length gs) ↘ ihs ->
      G v ups ups ns ns (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)) ->
      rec_results_rel D dr Rel v ups ups ns ns (List.rev (im_nparams Mv)) gs vs vs ihs ihs ->
      ⟦ B ⟧ env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs ihs) ↘ bv ->
      ⟦ eb_motive b ⟧ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) (d_con hd k c (pre ++ ns ++ vs))) ↘ t0 ->
      Rnf ⇓ t0 bv in gc_deps ⍮ gc_stack ⍮ (length Δ + n) ↘ Bn ->
      glu_nf_eq (elim_bctx ak_relevant p D Mv gs (blocks_motives (blocks_sub Bks σ'')) (List.map (fun U => U[σ'']) Us) ++ Δ)
        B[sb_qn n σ''] Bn (elim_branch_type p D v Mv c gs (eb_motive b)[sb_qn (S (im_nn Mv)) σ''] (List.map (fun U => U[σ'']) Us)).
  Proof.
    intros v Mv b c gs n B HMv Hrv Hb Hcon HinB Δ σ'' hd k pre ns vs ihs bv t0 Bn Hσ'' Er Fn Fc Fi Hm Hir Ebv Et0 HRn.
    destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D v Mv ups hd k pre Hl HMv ups_len Er) as [Href Lpre].
    pose proof (Har _ _ _ _ _ _ _ HMv Hb Hcon HinB) as Hn.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
    destruct (Completeness.Inductives.Elim.rec_results_rel_vs_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lv _].
    destruct (glu_blocks_branch _ _ _ _ _ _ HBg _ _ _ _ _ _ _ HMv Hb Hcon HinB) as [SbB HSbB lvl Hbody].
    set (Bc := elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us) in *.
    assert (Lb : List.length Bc = (im_nn Mv + List.length gs + cargs_nrec D gs)%nat)
      by (unfold Bc; rewrite length_elim_bctx; lia).
    assert (Lx : List.length (ns ++ vs ++ ihs) = List.length Bc)
      by (rewrite Lb, !List.length_app, Ln, Lv, Li; lia).
    pose proof (glu_sub_fresh _ Γ SbΓ (elim_bctx_ass ak_relevant p D v Mv gs _ Us Hc HMv) HSbΓ SbB HSbB Δ σ'' ρ _ Hσ'' Lx
                  (bctx_entry_link v Mv c gs HMv Hcon Hrv (List.length Δ) ns vs ihs hd k pre Fn Fc Fi Lpre Hm Hir)) as Hτ0.
    (** The constructor's components, related ([ind_rel_con_inv]). *)
    destruct (ind_rel_con_inv p D ups _ _ _ Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMv Hrv
                ltac:(rewrite List.length_app; lia)) as (gs0 & bs' & vs' & Ez & _ & Hnns & Hc0 & Hbl' & _ & _ & Hav & Hca).
    rewrite Hcon in Hc0; injection Hc0 as <-.
    injection Ez as Ez; apply app_split_eq in Ez as [<- <-]; [| rewrite !List.length_app, Hbl'; lia ].
    rewrite skipn_app_exact in Hav, Hca by exact Lpre.
    (** The telescope's entries and the branch's own read back. *)
    pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as HBs.
    destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
    pose proof (EB Completeness.Inductives.Elim.canonical_bctx ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs Hrv
                  ρ ρ Hρ Hρ ns ns vs vs ihs ihs Hnns Hav Hca Hir RB HRB) as HEc.
    assert (HBr : ⊨ List.rev (List.rev Bc) ++ Γ) by (rewrite List.rev_involutive; exact HBs).
    assert (HRBr : EF List.rev (List.rev Bc) ++ Γ ≈ List.rev (List.rev Bc) ++ Γ ∈ per_ctx_env ↘ RB)
      by (rewrite List.rev_involutive; exact HRB).
    assert (HtaB : all_assumptions (List.rev Bc)) by (apply List.Forall_rev; exact (elim_bctx_ass ak_relevant p D v Mv gs _ Us Hc HMv)).
    assert (LB : List.length (ns ++ vs ++ ihs) = List.length (List.rev Bc)) by (rewrite List.length_rev; exact Lx).
    unfold env_tele in HEc.
    destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HBr HtaB HRBr _ _ _ _ ltac:(rewrite Decl.tele_entries_length; exact LB)
                ltac:(rewrite Decl.tele_entries_length; exact LB) HEc) as [Hr1 _].
    set (bes := branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs ihs) in *.
    destruct (ER branch_entries_readable v Mv c gs ups ups ns ns vs vs ihs ihs Had Had HMv Hcon Hnns Hav Hca Hir) as [Hrd2 _].
    assert (Hv2 : List.map fst bes = ns ++ vs ++ ihs) by exact (ER branch_entries_values Mv ups (blocks_motives Bks) ρ gs ns vs ihs).
    assert (Hr2 : List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) bes).
    { rewrite <- Hv2 in Hrd2; pose proof (Completeness.Inductives.Elim.Forall_combine_of_Forall2 _ _ _ Hrd2) as H0.
      rewrite combine_map_fst_snd in H0; exact H0. }
    pose proof (EB Completeness.Inductives.Elim.canonical_bctx_elem ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs Hrv
                  ρ ρ Hρ Hρ ups ups hd k (pre ++ ns) (pre ++ ns) vs vs ihs ihs
                  ltac:(rewrite skipn_app_exact by exact Lpre; exact Hm) ltac:(rewrite skipn_app_exact by exact Lpre; exact Hir)
                  RB HRB _ _ ltac:(rewrite tele_entries_values, skipn_app_exact by exact Lpre; reflexivity)
                  ltac:(rewrite skipn_app_exact by exact Lpre; exact Hv2) Hr1 Hr2) as HE.
    (** The fresh substitution, at the branch's own environment. *)
    assert (Hv1 : List.map fst (tele_entries ρ (List.rev Bc) (ns ++ vs ++ ihs)) = List.map fst bes)
      by (rewrite tele_entries_values; symmetry; exact Hv2).
    assert (Lv1 : List.length (tele_entries ρ (List.rev Bc) (ns ++ vs ++ ihs)) = List.length Bc)
      by (rewrite Decl.tele_entries_length; exact Lx).
    unfold env_tele in Hτ0.
    pose proof (glu_sub_retype _ _ _ _ (elim_bctx_ass ak_relevant p D v Mv gs _ Us Hc HMv) HSbB HRB _ _ _ _ _ Hv1 Lv1 HE Hτ0) as Hτ.
    destruct (Hbody _ _ _ Hτ) as [eb rb Pb Elb Eeb Erb Hgb HBgl].
    (** The branch type's value, against the motive's at the constructor. *)
    assert (Lbs : List.length (pre ++ ns) = (im_unu D Mv + im_nn Mv)%nat) by (rewrite List.length_app; lia).
    assert (HG' : G v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                    (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)))
      by (rewrite skipn_app_exact by exact Lpre; exact Hm).
    assert (Hir' : rec_results_rel D dr Rel v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                     (List.rev (im_nparams Mv)) gs vs vs ihs ihs)
      by (rewrite skipn_app_exact by exact Lpre; exact Hir).
    assert (Hnn : tele_rel (nr v) (List.rev (im_nparams Mv)) ns (List.skipn (im_unu D Mv) (pre ++ ns)))
      by (rewrite skipn_app_exact by exact Lpre; exact Hnns).
    (** The motive's entries read back. *)
    rewrite List.app_assoc in Et0.
    set (xc := d_con hd k c ((pre ++ ns) ++ vs)) in *.
    set (mes := motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) xc) in *.
    assert (Hv0 : List.map fst mes = ns ++ xc :: nil) by exact (motive_entries_values D Mv ups ns (d_ind hd k (pre ++ ns)) xc).
    assert (Hr0 : List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) mes).
    { unfold mes, motive_entries; apply List.Forall_app; split.
      - pose proof (nparams_entries_readable_at_admissible_base D ups nr ar dr ups v Mv ns ns Hass Had HMv Hnns) as H0.
        rewrite <- (tele_entries_values ns (decl_env D ups) (List.rev (im_nparams Mv))) in H0 at 1.
        pose proof (Completeness.Inductives.Elim.Forall_combine_of_Forall2 _ _ _ H0) as H1.
        rewrite combine_map_fst_snd in H1; exact H1.
      - constructor; [| constructor ].
        exact (elim_ups_ok_member_elements_readable_at_ua _ _ _ _ _ _ _ _ Hups v Mv hd k pre ups ups ns ns ns xc xc HMv Hrv Had Had Er Hm Hnns). }
    assert (Hv2' : List.map fst bes = List.skipn (im_unu D Mv) (pre ++ ns) ++ vs ++ ihs)
      by (rewrite skipn_app_exact by exact Lpre; exact Hv2).
    pose proof (branch_type_val_rel v Mv c gs b HMv Hcon Hrv Hb hd k (pre ++ ns) vs ihs ns eb t0 bes mes Href Lbs HG' Hir' Hnn
                  Hv2' Hr2 Hv0 Hr0 Eeb Et0) as Hrel.
    (** The motive's value at the constructor is relevant, as a type of a
        universe; so is the branch type's, related to it. *)
    destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMv)) as [RM HRM].
    pose proof (EB Completeness.Inductives.Elim.mctx_at_typed HMall v Mv HMv ρ ρ Hρ Hρ RM HRM _ _ _ _ _ _ Hm _ _
                  Hv0 Hv0 Hr0 Hr0) as HEm.
    destruct (rel_exp_of_typ_relevant_at HRM (HAv _ _ _ HMv Hb) _ _ HEm) as (a1 & Ea1 & Hk1).
    assert (a1 = t0) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hkr : domain_kind eb = ak_relevant)
      by (destruct Hrel as [R1 HR1]; rewrite (per_univ_elem_kind _ _ _ _ HR1); exact Hk1).
    rewrite Hkr in Erb; cbn [glu_term_value] in Erb.
    assert (rb = bv) as -> by (eapply functional_eval_exp; eassumption).
    (** The branch glued at the motive's value, read back. *)
    pose proof (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HBgl) as HTP.
    destruct (glu_transfer_per lvl iA eb t0 Pb Elb _ _ _ bv Hgb Hrel HTP HBgl) as (k' & P' & El' & Hg' & HP' & HM').
    destruct (realize_glu_elem_top _ _ _ _ Hg' _ _ _ _ HM') as [? ? _ _ _ _ Hrbs].
    assert (HΔb : ⊢ tele_sub Bc σ'' ++ Δ)
      by (pose proof (glu_ctx_env_sub_escape HSbB _ _ _ Hτ); gen_presups; assumption).
    assert (Hlen : List.length (tele_sub Bc σ'' ++ Δ) = (List.length Δ + n)%nat)
      by (rewrite List.length_app, length_tele_sub, Lb, Hn; lia).
    rewrite <- Hlen in HRn.
    pose proof (Hrbs _ wk_id _ (kripke_id _ HΔb) HRn) as H.
    rewrite !exp_wk_id in H.
    unfold Bc in H, Lb.
    rewrite (elim_bctx_sub ak_relevant p D v Mv c gs (blocks_motives Bks) (blocks_motives (blocks_sub Bks σ'')) Us σ'' Hc HMv
               (cons_lookup_in _ _ _ Hcon) HUl (fun j0 Mj0 HMj0 => blocks_motives_sub D Bks σ'' j0 Mj0 Hnm HMj0)) in H.
    rewrite Lb, (elim_branch_type_sub p D v Mv c gs (eb_motive b) Us σ'' Hc HMv HUl) in H.
    rewrite Hn; exact H.
  Qed.

  (** The readback of a stuck eliminator's blocks, block by block. *)
  Lemma read_blocks_nth : forall s sel Dc Ms i NBks, Rblks i Ms of Dc from p ups Bks sel in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ NBks ->
      List.length NBks = List.length Ms /\
      forall n b', List.nth_error NBks n = Some b' ->
        exists Mi Mv b hd k pre ns Z' a A' Bs', List.nth_error Ms n = Some Mi /\
          ind_member D (elim_src sel (i + n)) = Some Mv /\ List.nth_error Bks (elim_src sel (i + n)) = Some b /\
          eb_binder_count b = S (im_nn Mi) /\ ⟦mref elim_src sel (i + n) of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) /\
          Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ ns /\
          Rtyp d_ind hd k (pre ++ ns) in gc_deps ⍮ gc_stack ⍮ (s + im_nn Mi) ↘ Z' /\
          ⟦ eb_motive b ⟧ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns))
                                              (⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mi))) ↘ a /\
          Rtyp a in gc_deps ⍮ gc_stack ⍮ S (s + im_nn Mi) ↘ A' /\
          Rbrs (eb_brs b) at (im_cons Mi) of Mi (hd, k, pre) of Dc from p ups Bks Mv (eb_motive b) in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Bs' /\
          b' = mk_normal_block (S (im_nn Mi)) Z' A' Bs'.
  Proof.
    intros s sel Dc Ms; induction Ms as [| Mi Ms IH]; intros i NBks HR; inversion HR; subst.
    - split; [ reflexivity | intros [] *; discriminate ].
    - match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H; injection H as <- end.
      match goal with H : Rblks (S i) Ms of _ from _ _ _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => destruct (IH _ _ H) as [L1 HN1] end.
      split; [ cbn; f_equal; exact L1 |].
      intros [| n] b' Hn; cbn in Hn.
      + injection Hn as <-; rewrite Nat.add_0_r.
        do 11 eexists; split; [ reflexivity | repeat split; eassumption ].
      + destruct (HN1 n b' Hn) as (Mi' & Mv' & b0 & hd0 & k0 & pre0 & ns0 & Z0 & a0 & A0 & Bs0 & HN2).
        replace (i + S n) with (S i + n) by lia.
        exists Mi', Mv', b0, hd0, k0, pre0, ns0, Z0, a0, A0, Bs0; exact HN2.
  Qed.

  (** What the PER model gives of the fresh variables of a block of the
      group read as its own ([member_pair], at [ups] on both sides): no
      argument nests through a view. *)
  Lemma own_member_pair : forall s i Mi, ind_member D i = Some Mi -> im_is_rview Mi = false ->
      member_pair p D ups nr ar dr ρ ρ Bks Bks ups ups Rel s D None i Mi.
  Proof.
    intros s i Mi HMi Hrv.
    pose proof (adm_fresh_of_uparams p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups (elim_ups_ok_adm_a _ _ _ _ _ _ _ _ Hups)) as Ha.
    destruct (group_structure_rank _ Hass) as [rk Hrk].
    refine (ER member_pair_of s D None i Mi Mi rk 0 Ha Ha ups_len ups_len (elim_ups_ok_mref_a _ _ _ _ _ _ _ _ Hups)
              (elim_ups_ok_mref_a _ _ _ _ _ _ _ _ Hups) HMi Hrv eq_refl eq_refl _ Hrk _).
    - intros c gs' gs Hin Hcn.
      assert (gs = gs') as -> by (pose proof (cons_lookup_nodup_in _ _ _ (Hnd _ _ HMi) Hin) as Hc0; unfold ind_con in Hcn; congruence).
      constructor; [ apply cargs_same_kinds_refl
                   | exact (cargs_container_count_own_of_ass D Hass gs' (group_structure_params_length _ Hass _ _ _ _ HMi (cons_lookup_in _ _ _ Hcn)))
                   | exact (cargs_nest_ok_own p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had rk 0 i Mi c gs' HMi Hcn) ].
    - intros j0 Hj; lia.
  Qed.

  (** The same at a view [vm] of the container's member [i']: the
      positions the view nests through are stuck eliminators, related at
      every member ([per_bot_elim]). *)
  Lemma view_member_pair : forall s m Mm qc kc Is vm D' i' Mi', ind_member D m = Some Mm -> im_head Mm = mh_view qc kc Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      member_pair p D ups nr ar dr ρ ρ Bks Bks ups ups Rel s D' (Some vm) i' Mi'.
  Proof.
    intros s m Mm qc kc Is vm D' i' Mi' HMm Hh Hq Hi' Hrv'.
    pose proof (adm_fresh_of_uparams p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups (elim_ups_ok_adm_a _ _ _ _ _ _ _ _ Hups)) as Ha.
    destruct (group_structure_vm _ Hass m Mm qc kc Is vm D' i' Mi' HMm Hh Hq Hi') as [v Mv Hvm HMv Hnn Himg].
    (** The view's member is no record view, as [Mi'] is not. *)
    assert (Hrv : im_is_rview Mv = false).
    { unfold im_is_rview in *; destruct (im_head Mi') as [pm | qv kv Is'' vm'' | qr Is'' fl] eqn:Hh'; try discriminate.
      - destruct Himg as [vm' Hv']; rewrite Hv'; reflexivity.
      - destruct Himg as (Is' & vm' & Hv' & _); rewrite Hv'; reflexivity. }
    destruct (group_structure_view_wrap _ Hass m Mm qc kc Is vm HMm Hh) as (D'' & Hq' & Hvw).
    rewrite Hq in Hq'; injection Hq' as <-.
    destruct (view_wrap_ok_members _ _ _ Hvw i' Mi' v Hi' Hvm) as (Mv' & HMv' & _ & Hnames & Hcorr).
    rewrite HMv in HMv'; injection HMv' as <-.
    assert (Hsrc : elim_src (Some vm) i' = v) by (cbn; apply List.nth_error_nth; exact Hvm).
    pose proof (valid_group_typed _ _ (Hcv m Mm qc kc Is vm D' HMm Hh Hq)) as HdtQ.
    destruct (group_structure_rank _ Hass) as [rk Hrk].
    refine (ER member_pair_of s D' (Some vm) i' Mi' Mv rk (rk m) Ha Ha ups_len ups_len (elim_ups_ok_mref_a _ _ _ _ _ _ _ _ Hups)
              (elim_ups_ok_mref_a _ _ _ _ _ _ _ _ Hups) ltac:(rewrite Hsrc; exact HMv) Hrv Hnn (eq_sym Hnames) _ Hrk _).
    - intros c gs' gs Hin Hcn.
      constructor; [ exact (cargs_same_kinds_of_correspond _ _ _ (Hcorr c gs' gs Hin Hcn)) | |].
      + (** the group's paths the container has, as many as its branch binds *)
        pose proof (decl_typed_record_struct _ _ _ HdtQ) as HrsQ.
        exact (cargs_container_count_view p qc D D' vm (leaves_coherent_of_order D (rview_struct_order _ _ _ (group_structure_record_struct _ Hass)))
                 (leaves_coherent_of_order D' (rview_struct_order _ _ _ HrsQ)) (group_structure_record_struct _ Hass) HrsQ
                 (view_members_of_ass p D m Mm qc kc Is vm D' Hass HMm Hh Hq) gs' gs (Hcorr c gs' gs Hin Hcn)).
      + exact (view_rank_ok_nest _ _ _ _ Hrk m Mm qc kc Is vm D' i' Mi' v Mv c gs' gs HMm Hh Hq Hi' Hvm HMv
                 (cons_lookup_nodup_in _ _ _ (decl_typed_nodup _ _ _ HdtQ _ _ Hi') Hin) Hcn).
    - intros j _; exact (ER per_bot_elim j).
  Qed.

  (** Fresh variables of the non-uniform parameters of the member [v],
      variables of a context at their types, are glued at the gluings of
      the parameters' types ([NEl]). *)
  Lemma glu_fresh_nparams : forall v Mv Δx Usx j0 s ns, ind_member D v = Some Mv -> ⊢ Δx ->
      glu_args Δx (ind_uparams D) Id nil Usx ups -> (s + j0 + im_nn Mv = length Δx)%nat ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ ns ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      (forall j N T, List.nth_error (vars_from j0 (im_nn Mv)) j = Some N ->
         List.nth_error (tele_insts (im_nparams Mv) (sb_of_list Id Usx) (vars_from j0 (im_nn Mv))) j = Some T -> Δx ⊢ N : T) ->
      glu_nparams v Mv NEl Δx Usx (vars_from j0 (im_nn Mv)) ns.
  Proof.
    intros v Mv Δx Usx j0 s ns HMv HΔx HUsx Hlen Fn Hns HNt.
    pose proof (components_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl ups_len Hbu Hule Hf Δx Usx HΔx HUsx)
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
    destruct (nparams_lt_ass D v Mv n Hass HMv Hk') as (κ & A & HA).
    destruct (fresh_tele_nth _ _ _ _ Fn n κ A HA) as (b & Eb & Hb).
    rewrite Hw in Hb; injection Hb as ->.
    assert (Hpm : tele_prefix_rel (nr v) n (List.firstn n ns) (List.firstn n ns))
      by (eapply tele_prefix_rel_of_full; [ exact Hns | rewrite List.length_rev, length_im_nparams; lia ]).
    fold (components_env D ups (List.rev (im_nparams Mv)) (List.firstn n ns)) in Eb.
    pose proof (ind_fams_glu_nparams_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ HMv HA Hpm Eb) as Hgu.
    (** A parameter's type is not [LevelSort] ([nparams_related]). *)
    assert (Hnl : not_level_sort b).
    { destruct (Completeness.Inductives.Model.canon_hn D HD Hc Hsu ups bu ups_len Hbu ups ups_tele_args
                  v Mv n κ A _ _ HMv HA Hpm) as (a0 & a0' & Ea0 & _ & _ & Hnl0).
      assert (a0 = b) as <- by (eapply functional_eval_exp; eassumption); exact Hnl0. }
    assert (HTP : Δx ⊢ T ® NP v n (List.firstn n ns)).
    { eapply (HCN v Mv n _ (List.firstn n ns) T HMv); [ rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
      intros j' N' T' w' Hj' HN' HT' Hw'.
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hw'; destruct (Nat.ltb_spec j' n); [| discriminate ].
      eapply IH; eauto; lia. }
    pose proof (HNt n N T HN HT) as HNtn.
    apply vars_from_nth_error in HN as [Hnn ->].
    pose proof (var_glu_elem_at u b _ _ Δx T _ Hgu Hnl HTP HNtn ltac:(lia)) as Hv.
    replace (List.length Δx - 1 - (j0 + (im_nn Mv - 1 - n))) with (s + n) in Hv by lia.
    exact Hv.
  Qed.

  (** The member's type at fresh non-uniform parameters is a type
      ([mty_val_rel]). *)
  Lemma fresh_mty_per : forall v Mv, ind_member D v = Some Mv -> forall s ns hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ s ↘ ns ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      exists n : nat, Dom d_ind hd k (pre ++ ns) ≈ d_ind hd k (pre ++ ns) ∈ per_univ n.
  Proof.
    intros v Mv HMv s ns hd k pre Fn Hns Er.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (HMall _ _ HMv) as HMm.
    pose proof (rel_ctx_wf_tail HMm) as HNt.
    pose proof (member_params_ass D Hc _ _ HMv) as HPa.
    pose proof (valid_ind_decl_params _ HD _ _ HMv) as HPs.
    pose proof (EB Completeness.Inductives.Elim.nparams_closed_of_canon v Mv HMv ns ns Hns) as Hpg.
    destruct (Completeness.Inductives.Elim.mty_vars_valid p D Hvg Hcv v Mv HMv) as [jx HXv].
    destruct (inst_link (im_nparams Mv) _ _ ns (type_sort_universe jx) HPa HPs HNt HXv Hpg ltac:(rewrite length_im_nparams; exact Ln))
      as (a1 & b & j1 & _ & Eb & _).
    destruct (rel_ctx_wf_per_ctx_env HPs) as [RK HRK].
    assert (HKE : RK (components_env D ups (List.rev (im_nparams Mv)) (ns ++ nil)) (components_env D ups (List.rev (im_nparams Mv)) (ns ++ nil))).
    { rewrite List.app_nil_r; unfold components_env, im_params in *.
      exact (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRU HRK HPs ups_RU ltac:(rewrite length_im_nparams; exact Ln) Hpg). }
    replace ns with (ns ++ nil) in Eb at 1 by (rewrite List.app_nil_r; reflexivity).
    destruct (mty_val_rel VP HVP p D HPD ups ups_len ups_tele_args v Mv hd k pre (im_nparams Mv) RK ns nil 0 b ns HMv Er HPs HRK
                ltac:(rewrite List.app_nil_r, length_im_nparams; exact Ln) Ln eq_refl HKE Eb Hns) as (i0 & R0 & H0).
    destruct (Decl.per_univ_elem_to_nat _ _ _ _ H0) as [n0 Hn0].
    exists n0; eapply per_univ_trans'; [ exists R0; exact Hn0 | apply per_univ_sym'; exists R0; exact Hn0 ].
  Qed.

  (** The readback of the scrutinee's type of the block of the member [v]
      under the fresh non-uniform parameters, against the member's type at
      [σ''] past them, up to proofs: the type is glued there at fresh
      variables glued at the parameters' types ([mty_glu]). *)
  Lemma readback_scrutinee_type : forall v Mv, ind_member D v = Some Mv ->
      forall Δ σ'' hd k pre ns Z', Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ length Δ ↘ ns ->
      Rtyp d_ind hd k (pre ++ ns) in gc_deps ⍮ gc_stack ⍮ (length Δ + im_nn Mv) ↘ Z' ->
      exists j : nat, glu_nf_eq (tele_sub (im_nparams Mv) (sb_of_list Id (List.map (fun U => U[σ'']) Us)) ++ Δ)
        (ind_mty p D v (List.map (fun U => U[wk_shiftn (im_nn Mv)]ʷ) (List.map (fun U => U[σ'']) Us)) (vars_from 0 (im_nn Mv)))
        Z' Typeω@j.
  Proof.
    intros v Mv HMv Δ σ'' hd k pre ns Z' Hσ'' Er Fn HRZ.
    destruct (Completeness.Inductives.ViewReadback.fresh_nparams_exist p D Hvg ups ups_tele_args ups_len v Mv (List.length Δ) HMv)
      as (ns' & Fn' & Hns).
    pose proof (functional_fresh_tele' _ _ _ _ _ Fn' Fn) as ->.
    set (Us' := List.map (fun U => U[σ'']) Us).
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
    set (Δx := tele_sub (im_nparams Mv) (sb_of_list Id Us') ++ Δ).
    assert (Lx : List.length (tele_sub (im_nparams Mv) (sb_of_list Id Us')) = im_nn Mv)
      by (rewrite length_tele_sub, length_im_nparams; reflexivity).
    (** The context past the non-uniform parameters. *)
    assert (Hσt : Δ ⊢ˢ σ'' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'').
    pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; fold Us' in HBt'.
    pose proof (blocks_typed_mctx _ _ _ _ _ _ _ _ _ HBt' v Mv HMv) as HMe.
    unfold elim_mctx in HMe; apply ext_eq_cons_inv in HMe.
    assert (HΔx : ⊢ Δx) by exact (ext_eq_ctx_left _ _ _ _ _ HMe).
    (** The uniform parameters past them, and the fresh variables, glued. *)
    pose proof (glu_args_wk Δ Δx (wk_shiftn (im_nn Mv)) (ind_uparams D) nil Us' ups Ua (decl_closed_uparams _ Hc)
                  ltac:(rewrite <- Lx; exact (kripke_shiftn_app _ _ HΔx)) (us_glu_args Δ σ'' Hσ'')) as HUx.
    assert (Hlen : (List.length Δ + 0 + im_nn Mv = length Δx)%nat) by (unfold Δx; rewrite List.length_app, Lx; lia).
    pose proof (mctx_vars_typed _ _ Δ D v Mv Us' Hdt Hc HMv HUl' HΔx) as HNt.
    pose proof (glu_fresh_nparams v Mv Δx _ 0 (List.length Δ) ns HMv HΔx HUx Hlen Fn Hns HNt) as Hgn.
    (** The member's type, glued at a gluing of its value above [nb]. *)
    destruct (fresh_mty_per v Mv HMv (List.length Δ) ns hd k pre Fn Hns Er) as [n0 [Rd HRd]].
    set (i := Nat.max n0 nb).
    pose proof (per_univ_elem_cumu_ge n0 i _ _ _ ltac:(unfold i; lia) HRd) as HRdi.
    destruct (per_univ_glu_univ_elem i _ (ex_intro _ Rd HRdi)) as (P & El & Hglu).
    pose proof (mty_glu VP HVP HGall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_tele_args Hbu Hule Hf nb Hnbu Hnbq
                  v Mv hd k pre Δx _ _ ns i P El ltac:(unfold i; lia) HMv Er HΔx HUx Hgn Hns Hglu) as HTP.
    (** Read back. *)
    assert (Hnl : not_level_sort (d_ind hd k (pre ++ ns))) by discriminate.
    destruct (realize_glu_typ_top _ _ _ _ Hglu Hnl _ _ HTP) as [_ _ Hrd].
    assert (Hlx : List.length Δx = (List.length Δ + im_nn Mv)%nat) by (unfold Δx; rewrite List.length_app, Lx; lia).
    rewrite <- Hlx in HRZ.
    pose proof (Hrd _ wk_id _ (kripke_id _ HΔx) HRZ) as H.
    rewrite !exp_wk_id in H; cbn [domain_kind abs_kind_sort] in H.
    exists (large_level i); unfold ind_mty; rewrite HMv; exact H.
  Qed.

  (** A block of the readback of a stuck eliminator at a declared member,
      against the group's own block at [σ'']: the same count and names,
      and, up to proofs, the scrutinee's type against the member's type,
      and the motive and the branches against the block's at [σ'']. *)
  Lemma own_block_rb : forall Δ σ'' NBks, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      Rblks 0 (ind_block_members D) of D from p ups Bks None in gc_deps ⍮ gc_stack ⍮ ρ ⍮ length Δ ↘ NBks ->
      forall k Mk b nbk, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error NBks k = Some nbk ->
        block_arity nbk = S (im_nn Mk) /\
        (exists j : nat, glu_nf_eq (tele_sub (im_nparams Mk) (sb_of_list Id (List.map (fun U => U[σ'']) Us)) ++ Δ)
           (ind_mty p D k (List.map (fun U => U[wk_shiftn (im_nn Mk)]ʷ) (List.map (fun U => U[σ'']) Us)) (vars_from 0 (im_nn Mk)))
           (block_scrutinee_type nbk) Typeω@j) /\
        glu_nf_eq (elim_mctx p D k Mk (List.map (fun U => U[σ'']) Us) ++ Δ) (eb_motive b)[sb_qn (S (im_nn Mk)) σ''] (block_motive nbk)
          Typeω@iA /\
        List.map fst (brs_sub (eb_brs b) σ'') = List.map (fun br => (branch_constructor br, branch_arity br)) (block_branches nbk) /\
        forall i c n B br gs, List.nth_error (eb_brs b) i = Some (c, n, B) -> List.nth_error (block_branches nbk) i = Some br ->
          ind_con Mk c = Some gs ->
          glu_nf_eq (elim_bctx ak_relevant p D Mk gs (blocks_motives (blocks_sub Bks σ'')) (List.map (fun U => U[σ'']) Us) ++ Δ)
            B[sb_qn n σ''] (branch_body br)
            (elim_branch_type p D k Mk c gs (eb_motive b)[sb_qn (S (im_nn Mk)) σ''] (List.map (fun U => U[σ'']) Us)).
  Proof.
    intros Δ σ'' NBks Hσ'' HR k Mk b nbk HMk Hb Hnbk.
    pose proof (Hbnr k Mk b HMk Hb) as Hrv.
    destruct (read_blocks_nth _ _ _ _ _ _ HR) as [_ HRn].
    destruct (HRn k nbk Hnbk) as (Mi & Mv & b0 & hd & k0 & pre & ns & Z' & a & A' & Bs' & HMi & HMv & Hb0 & Hnm0 & Er & Fn & HRZ & Ea
                                & HRA & HRB & ->).
    cbn [Nat.add elim_src] in *.
    destruct (ind_block_members_member _ _ _ HMi) as [HMi' _].
    assert (Mi = Mk) as -> by congruence.
    rewrite HMk in HMv; injection HMv as <-.
    rewrite Hb in Hb0; injection Hb0 as <-.
    cbn [block_arity block_scrutinee_type block_motive block_branches].
    destruct (read_brs_nth _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HRB) as (LB1 & LB2 & HBn).
    assert (Hgs : forall c gs' gs, List.In (c, gs') (im_cons Mk) -> ind_con Mk c = Some gs -> gs = gs')
      by (intros c gs' gs Hin Hcn; pose proof (cons_lookup_nodup_in _ _ _ (Hnd _ _ HMk) Hin) as Hc0; unfold ind_con in Hcn; congruence).
    split; [ reflexivity | split; [ exact (readback_scrutinee_type k Mk HMk Δ σ'' hd k0 pre ns Z' Hσ'' Er Fn HRZ) | split ] ].
    - exact (readback_motive k Mk b HMk Hb Δ σ'' hd k0 pre ns a A' Hσ'' Er Fn Ea HRA).
    - split.
      + (** The names and counts. *)
        assert (Efst : List.map fst (brs_sub (eb_brs b) σ'') = List.map fst (eb_brs b))
          by (unfold brs_sub; rewrite List.map_map; apply List.map_ext; intros [[c0 n0] B0]; reflexivity).
        rewrite Efst; apply List.nth_error_ext; intros idx; rewrite !List.nth_error_map.
        destruct (List.nth_error Bs' idx) as [br |] eqn:E1.
        * destruct (HBn idx br E1) as [gs' gs n0 B0 ns' vs ihs wihs bv t Bn HB0 Hcs Hcn En0 En _ _ _ _ _ _ _ _ _ _].
          rewrite HB0; cbn.
          pose proof (Hgs _ _ _ (List.nth_error_In _ _ Hcs) Hcn) as ->.
          rewrite En0, En; reflexivity.
        * rewrite (proj2 (List.nth_error_None (eb_brs b) idx)); [ reflexivity |].
          apply List.nth_error_None in E1; lia.
      + (** A branch, by the fresh variables the PER model has. *)
        intros i c n B br gs HBi HBi' Hcn.
        destruct (HBn i br HBi') as [gs' gs0 n0 B0 ns' vs ihs wihs bv t Bn HB0 Hcs Hcn0 En0 En
                                     Hpl Hcc Fn' Fc Fi Wi Ebv Et Rn EBn].
        rewrite HBi in HB0; injection HB0 as Ec <- <-.
        rewrite <- Ec in Hcs, Hcn0, Et.
        rewrite Hcn in Hcn0; injection Hcn0 as <-.
        pose proof (Hgs _ _ _ (List.nth_error_In _ _ Hcs) Hcn) as <-.
        assert (Ear : branch_arity br = n) by (rewrite En, En0; reflexivity).
        rewrite Ear in Rn; rewrite EBn.
        cbn [fst snd] in Et.
        pose proof (own_cargs_leaves k Mk c gs HMk Hcn) as Hown.
        pose proof (wrapped_ihs_own _ _ _ _ _ _ _ _ _ Hl Hown Wi) as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fn Fn') as <-.
        destruct (own_member_pair (List.length Δ) k Mk HMk Hrv) as [Mv HMv _ Hnn hd1 k1 pre1 pre2 R1 R2 Lp1 Lp2 nsa nsb Fa Fb Hneut Hnames Hbrs].
        cbn [elim_src] in HMv, R1, R2; rewrite HMk in HMv; injection HMv as <-.
        pose proof (functional_eval_mref _ _ _ _ _ R1 Er) as E1; injection E1 as -> -> ->.
        pose proof (functional_eval_mref _ _ _ _ _ R2 Er) as E2; injection E2 as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fa Fn) as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fb Fn) as ->.
        destruct (Hbrs c gs (List.nth_error_In _ _ Hcs)) as (gs1 & Hcn1 & _ & _ & _ & BP).
        rewrite Hcn in Hcn1; injection Hcn1 as <-.
        destruct BP as [vsa vsb ihsa ihsb wa wb Fa' Fb' Ia Ib Wa Wb Hrel Hrecs].
        pose proof (functional_fresh_cargs _ _ _ _ _ _ Fa' _ Fc) as ->.
        pose proof (functional_fresh_cargs _ _ _ _ _ _ Fb' _ Fc) as ->.
        pose proof (functional_fresh_ihs _ _ _ _ _ _ _ _ _ _ _ Ia _ Fi) as ->.
        pose proof (functional_fresh_ihs _ _ _ _ _ _ _ _ _ _ _ Ib _ Fi) as ->.
        pose proof (wrapped_ihs_own _ _ _ _ _ _ _ _ _ Hl Hown Wa) as ->.
        pose proof (wrapped_ihs_own _ _ _ _ _ _ _ _ _ Hl Hown Wb) as ->.
        cbn [elim_src] in Hrel, Hrecs.
        rewrite !List.app_assoc in Hrel.
        exact (readback_branch k Mk b c gs n B HMk Hrv Hb Hcn (List.nth_error_In _ _ HBi) Δ σ'' hd k0 pre ns vs ihs bv t Bn Hσ'' Er
                 Fn Fc Fi Hrel Hrecs Ebv Et Rn).
  Qed.

  (** Witnesses up to proofs of the bodies of a list of branches, chosen
      position by position. *)
  Lemma branches_witness : forall (Pb : nat -> nf -> Prop) Bs,
      (forall i br, List.nth_error Bs i = Some br -> exists W, nf_eq_upto_proofs (branch_body br) W /\ Pb i W) ->
      exists Bs', branches_eq_upto_proofs Bs Bs' /\
        List.map (fun br => (branch_constructor br, branch_arity br)) Bs'
          = List.map (fun br => (branch_constructor br, branch_arity br)) Bs /\
        forall i br', List.nth_error Bs' i = Some br' -> Pb i (branch_body br').
  Proof.
    intros Pb Bs; revert Pb; induction Bs as [| [c n W] Bs IH]; intros Pb H.
    - exists nil; split; [ apply branches_eq_upto_proofs_nil | split; [ reflexivity | intros [] *; discriminate ] ].
    - destruct (H 0 _ eq_refl) as (W' & HW & HP).
      destruct (IH (fun i => Pb (S i)) (fun i br Hi => H (S i) br Hi)) as (Bs' & HB & Hn & HP').
      exists (mk_normal_branch c n W' :: Bs'); split; [ apply branches_eq_upto_proofs_cons; assumption |].
      split; [ cbn; f_equal; exact Hn |].
      intros [| i] br' Hi; cbn in Hi; [ injection Hi as <-; exact HP | exact (HP' i br' Hi) ].
  Qed.

  (** The same for the scrutinee types, the motives and the branches of a
      list of blocks. *)
  Lemma blocks_witness : forall (Pz Pa : nat -> nf -> Prop) (Pb : nat -> nat -> nf -> Prop) NBks,
      (forall k b, List.nth_error NBks k = Some b ->
         (exists Z, nf_eq_upto_proofs (block_scrutinee_type b) Z /\ Pz k Z) /\
         (exists A, nf_eq_upto_proofs (block_motive b) A /\ Pa k A) /\
         (forall i br, List.nth_error (block_branches b) i = Some br -> exists W, nf_eq_upto_proofs (branch_body br) W /\ Pb k i W)) ->
      exists NBks', blocks_eq_upto_proofs NBks NBks' /\ List.length NBks' = List.length NBks /\
        forall k b', List.nth_error NBks' k = Some b' -> exists b, List.nth_error NBks k = Some b /\
          block_arity b' = block_arity b /\ Pz k (block_scrutinee_type b') /\ Pa k (block_motive b') /\
          List.map (fun br => (branch_constructor br, branch_arity br)) (block_branches b')
            = List.map (fun br => (branch_constructor br, branch_arity br)) (block_branches b) /\
          forall i br', List.nth_error (block_branches b') i = Some br' -> Pb k i (branch_body br').
  Proof.
    intros Pz Pa Pb NBks; revert Pz Pa Pb; induction NBks as [| [n Z A Bs] NBks IH]; intros Pz Pa Pb H.
    - exists nil; split; [ apply blocks_eq_upto_proofs_nil | split; [ reflexivity | intros [] *; discriminate ] ].
    - destruct (H 0 _ eq_refl) as ((Z' & HZ & PZ) & (A' & HA & PA) & HBs); cbn in HZ, HA, HBs.
      destruct (branches_witness (Pb 0) Bs HBs) as (Bs' & HB & Hn & PB).
      destruct (IH (fun k => Pz (S k)) (fun k => Pa (S k)) (fun k => Pb (S k)) (fun k b Hk => H (S k) b Hk))
        as (NBks' & HK & Lk & HP).
      exists (mk_normal_block n Z' A' Bs' :: NBks'); split; [ apply blocks_eq_upto_proofs_cons; assumption |].
      split; [ cbn; f_equal; exact Lk |].
      intros [| k] b' Hk; cbn in Hk.
      + injection Hk as <-; exists (mk_normal_block n Z A Bs); cbn; repeat split; first [ reflexivity | assumption ].
      + exact (HP k b' Hk).
  Qed.

  (** A block with its scrutinee type, motive and branches annotated, as
      [ne_annotate_proofs] annotates the blocks of a stuck eliminator. *)
  Definition block_annotate (b : normal_block) : normal_block :=
    mk_normal_block (block_arity b) (nf_annotate_proofs (block_scrutinee_type b)) (nf_annotate_proofs (block_motive b))
      (List.map (fun br => mk_normal_branch (branch_constructor br) (branch_arity br) (nf_annotate_proofs (branch_body br)))
         (block_branches b)).

  (** The readback of a stuck eliminator at a declared member is the
      elimination's at [σ''], up to proofs: by the congruence, at the
      witnesses of the uniform parameters read back ([glu_args_read]),
      of the blocks read back ([own_block_rb]), and of the scrutinee read
      back. *)
  Lemma elim_readback_decl : forall j Mj pm, ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      forall as' e Δ σ'' Ns M (M0 : ne), Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> List.length Ns = im_nn Mj ->
      (forall i P T, List.nth_error (List.map (fun U => U[σ'']) Us ++ Ns) i = Some P ->
         List.nth_error (tele_insts (im_params D Mj) Id (List.map (fun U => U[σ'']) Us ++ Ns)) i = Some T -> Δ ⊢ P : T) ->
      (forall Mr, Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ Mr -> glu_ne_eq Δ M Mr (im_ty_at p j Mj (List.map (fun U => U[σ'']) Us) Ns)) ->
      Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
      glu_ne_eq Δ (a_elim ak_relevant p (List.map (fun U => U[σ'']) Us) j (blocks_sub Bks σ'') M) M0
        ((List.nth j (blocks_motives Bks) a_prop)[sb_qn (S (im_nn Mj)) σ''][sb_of_list Id (Ns ++ M :: nil)]).
  Proof.
    intros j Mj pm HMj Hh as' e Δ σ'' Ns M M0 Hσ'' HNl HPs HMr HR.
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
    match goal with H1 : Rblks _ _ of _ from _ _ _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRB end.
    match goal with H1 : Rne e in _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRM end.
    set (Us' := List.map (fun U => U[σ'']) Us) in *.
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
    destruct (HBks _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity)) as [b Hb].
    assert (Hσt : Δ ⊢ˢ σ'' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'').
    pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; fold Us' in HBt'.
    assert (Hbk' : List.nth_error (blocks_sub Bks σ'') j = Some (eblock_sub b σ'')) by (rewrite nth_error_blocks_sub, Hb; reflexivity).
    assert (HPl : List.length (Us' ++ Ns) = im_np D Mj) by (rewrite List.length_app, HUl', HNl; unfold im_np; lia).
    destruct (read_blocks_nth _ _ _ _ _ _ HRB) as [LNB HRBn].
    rewrite (blocks_motives_nth _ _ _ Hb).
    rewrite <- (Hnm _ _ _ HMj Hb), <- Completeness.Inductives.Elim.eb_motive_sub.
    assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
    pose proof (own_block_rb Δ σ'' NBks Hσ'' HRB) as Hown.
    (** The witnesses up to proofs: of the uniform parameters, of the
        scrutinee, and of the blocks. *)
    destruct (glu_args_read Δ (ind_uparams D) Us' ups Ua (decl_closed_uparams _ Hc) (us_glu_args Δ σ'' Hσ'') Δ wk_id Us0
                (kripke_id Δ HΔ) HRU0) as (Uw & HUw & Hu).
    rewrite map_wk_id in Hu.
    destruct (HMr M1 HRM) as (M1w & HMw & HMeq).
    set (Pz := fun k Z => forall Mk, ind_member D k = Some Mk -> exists jj : nat,
               tele_sub (im_nparams Mk) (sb_of_list Id Us') ++ Δ
                 ⊢ ind_mty p D k (List.map (fun U => U[wk_shiftn (im_nn Mk)]ʷ) Us') (vars_from 0 (im_nn Mk)) ≈ nf_annotate_proofs Z
                 : Typeω@jj).
    set (Pa := fun k A => forall Mk b0, ind_member D k = Some Mk -> List.nth_error Bks k = Some b0 ->
               elim_mctx p D k Mk Us' ++ Δ ⊢ (eb_motive b0)[sb_qn (S (im_nn Mk)) σ''] ≈ nf_annotate_proofs A : Typeω@iA).
    set (Pb := fun k i W => forall Mk b0 c n B gs, ind_member D k = Some Mk -> List.nth_error Bks k = Some b0 ->
               List.nth_error (eb_brs b0) i = Some (c, n, B) -> ind_con Mk c = Some gs ->
               elim_bctx ak_relevant p D Mk gs (blocks_motives (blocks_sub Bks σ'')) Us' ++ Δ ⊢ B[sb_qn n σ''] ≈ nf_annotate_proofs W
                 : elim_branch_type p D k Mk c gs (eb_motive b0)[sb_qn (S (im_nn Mk)) σ''] Us').
    destruct (blocks_witness Pz Pa Pb NBks) as (NBw & HNBw & LNBw & HPw).
    { intros k nbk Hk.
      destruct (HRBn k nbk Hk) as (Mi & Mk & b0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMk & Hb0 & _).
      cbn [elim_src Nat.add] in HMk, Hb0.
      destruct (Hown k Mk b0 nbk HMk Hb0 Hk) as (_ & (jj & Zw & HZ & HZe) & (Aw & HA & HAe) & _ & HB).
      split; [| split ].
      - exists Zw; split; [ exact HZ |]; intros Mk' HMk'; rewrite HMk in HMk'; injection HMk' as <-; exists jj; exact HZe.
      - exists Aw; split; [ exact HA |]; intros Mk' b' HMk' Hb'; rewrite HMk in HMk'; injection HMk' as <-;
          rewrite Hb0 in Hb'; injection Hb' as <-; exact HAe.
      - intros i br Hbr.
        destruct (List.nth_error (eb_brs b0) i) as [[[c n] B] |] eqn:HBi.
        + destruct (ind_con Mk c) as [gs |] eqn:Hcn.
          * destruct (HB i c n B br gs HBi Hbr Hcn) as (W & HW & HWe).
            exists W; split; [ exact HW |].
            intros Mk' b' c' n' B' gs' HMk' Hb' HBi' Hcn'; rewrite HMk in HMk'; injection HMk' as <-.
            rewrite Hb0 in Hb'; injection Hb' as <-; rewrite HBi in HBi'; injection HBi' as <- <- <-.
            rewrite Hcn in Hcn'; injection Hcn' as <-; exact HWe.
          * exists (branch_body br); split; [ exact (proj1 nf_ne_eqb_upto_proofs_refl _) |].
            intros Mk' b' c' n' B' gs' HMk' Hb' HBi' Hcn'; rewrite HMk in HMk'; injection HMk' as <-.
            rewrite Hb0 in Hb'; injection Hb' as <-; rewrite HBi in HBi'; injection HBi' as <- <- <-; congruence.
        + exists (branch_body br); split; [ exact (proj1 nf_ne_eqb_upto_proofs_refl _) |].
          intros Mk' b' c' n' B' gs' HMk' Hb' HBi'; rewrite Hb0 in Hb'; injection Hb' as <-; congruence. }
    set (Uw' := List.map nf_to_exp (List.map nf_annotate_proofs Uw)) in *.
    assert (LUw' : List.length Uw' = ind_nu D) by (destruct Hu as [Lu _]; rewrite <- Lu; exact HUl').
    set (Bks' := List.map block_exp (List.map block_annotate NBw)).
    (** A block of the witness. *)
    assert (HBk' : forall k b', List.nth_error Bks' k = Some b' -> exists nbw nbk Mk b0,
              List.nth_error NBw k = Some nbw /\ b' = block_exp (block_annotate nbw) /\ List.nth_error NBks k = Some nbk /\
              ind_member D k = Some Mk /\ List.nth_error Bks k = Some b0 /\
              block_arity nbw = block_arity nbk /\ Pz k (block_scrutinee_type nbw) /\ Pa k (block_motive nbw) /\
              List.map (fun br => (branch_constructor br, branch_arity br)) (block_branches nbw)
                = List.map (fun br => (branch_constructor br, branch_arity br)) (block_branches nbk) /\
              (forall i br', List.nth_error (block_branches nbw) i = Some br' -> Pb k i (branch_body br'))).
    { intros k b' Hk; unfold Bks' in Hk; rewrite !List.nth_error_map in Hk.
      destruct (List.nth_error NBw k) as [nbw |] eqn:Hw; cbn in Hk; [| discriminate ]; injection Hk as <-.
      destruct (HPw k nbw Hw) as (nbk & Hnbk & Har' & HPz & HPa & Hnm' & HPb).
      destruct (HRBn k nbk Hnbk) as (Mi & Mk & b0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMk & Hb0 & _).
      cbn [elim_src Nat.add] in HMk, Hb0.
      exists nbw, nbk, Mk, b0; repeat split; first [ reflexivity | assumption ]. }
    assert (E : Δ ⊢ a_elim ak_relevant p (List.firstn (ind_nu D) (Us' ++ Ns)) j (blocks_sub Bks σ'') M
              ≈ a_elim ak_relevant p (List.firstn (ind_nu D) (Uw' ++ Ns)) j Bks' (ne_to_exp (ne_annotate_proofs M1w))
              : (eb_motive (eblock_sub b σ''))[sb_of_list Id (List.skipn (ind_nu D) (Us' ++ Ns) ++ M :: nil)]).
    { eapply wf_exp_eq_elim_cong with (Ps' := Uw' ++ Ns) (Bks' := Bks').
      - exact Hl.
      - exact HMj.
      - exact Hbk'.
      - exact (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt').
      - unfold Bks'; rewrite !List.length_map, LNBw, LNB, length_ind_block_members; reflexivity.
      - exact HPl.
      - exact HPs.
      - rewrite List.length_app, LUw', HNl; unfold im_np; lia.
      - (** The parameters, against their witnesses. *)
        rewrite <- (firstn_app_exact Us' Ns (ind_nu D) HUl') in Hu.
        pose proof (exps_eq_at_params_of_uparams D Mj Δ (Us' ++ Ns) Uw' Hc HPl HPs Hu) as [_ Hu'].
        rewrite skipn_app_exact in Hu' by exact HUl'.
        exact Hu'.
      - (** The scrutinee, against its witness. *)
        rewrite firstn_app_exact, skipn_app_exact by exact HUl'.
        assert (Emt : ind_mty p D j Us' Ns = im_ty_at p j Mj Us' Ns) by (unfold ind_mty; rewrite HMj; reflexivity).
        rewrite Emt; exact HMeq.
      - reflexivity.
      - reflexivity.
      - exact (blocks_typed_binder_count _ _ _ _ _ _ _ _ _ HBt').
      - intros k Mk b' HMk Hb'.
        destruct (HBk' k b' Hb') as (nbw & nbk & Mk' & b0 & _ & -> & Hnbk & HMk' & Hb0 & Har' & _).
        rewrite HMk in HMk'; injection HMk' as <-.
        cbn [block_exp block_annotate eb_binder_count block_arity]; rewrite Har'.
        exact (proj1 (Hown k Mk b0 nbk HMk Hb0 Hnbk)).
      - rewrite firstn_app_exact by exact HUl'; exact (blocks_typed_scrutinee_type _ _ _ _ _ _ _ _ _ HBt').
      - (** The scrutinee types of the witness, by their readback. *)
        rewrite firstn_app_exact by exact HUl'.
        intros k Mk b' HMk Hb'.
        destruct (HBk' k b' Hb') as (nbw & nbk & Mk' & b0 & _ & -> & Hnbk & HMk' & Hb0 & _ & HPz & _).
        rewrite HMk in HMk'; injection HMk' as <-.
        destruct (HPz Mk HMk) as [jj HZe].
        cbn [block_exp block_annotate eb_scrutinee_type block_scrutinee_type].
        pose proof (blocks_typed_mctx _ _ _ _ _ _ _ _ _ HBt' k Mk HMk) as HMe.
        unfold elim_mctx in HMe |- *.
        pose proof (ext_eq_cons_inv _ _ _ _ _ _ _ HMe) as HTe.
        eapply wf_ext_eq_ass_eq; [ exact HTe | exact (presup_exp_eq_right HZe) | exact (sort_kind_abs_kind_sort ak_relevant jj)
                                 | apply wf_exp_eq_sym; exact HZe | exact (presup_exp_eq_left HZe) | exact (presup_exp_eq_left HZe) ].
      - rewrite firstn_app_exact by exact HUl'; exact (blocks_typed_motive _ _ _ _ _ _ _ _ _ HBt').
      - (** The motives, by their readback. *)
        rewrite firstn_app_exact by exact HUl'.
        intros k Mk ba b' HMk Hba Hb'.
        destruct (Completeness.Inductives.Elim.nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        destruct (HBk' k b' Hb') as (nbw & nbk & Mk' & b0' & _ & -> & Hnbk & HMk' & Hb0' & _ & _ & HPa & _).
        rewrite HMk in HMk'; injection HMk' as <-; rewrite Hb0 in Hb0'; injection Hb0' as <-.
        rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hb0).
        cbn [block_exp block_annotate eb_motive block_motive].
        exact (HPa Mk b0 HMk Hb0).
      - rewrite firstn_app_exact by exact HUl'; exact (blocks_typed_mctx _ _ _ _ _ _ _ _ _ HBt').
      - exact (blocks_typed_names _ _ _ _ _ _ _ _ _ HBt').
      - (** The names and counts. *)
        intros k ba b' Hba Hb'.
        destruct (Completeness.Inductives.Elim.nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        destruct (HBk' k b' Hb') as (nbw & nbk & Mk & b0' & _ & -> & Hnbk & HMk & Hb0' & _ & _ & _ & Hnmw & _).
        rewrite Hb0 in Hb0'; injection Hb0' as <-.
        rewrite Completeness.Inductives.Elim.eb_brs_sub.
        rewrite (proj1 (proj2 (proj2 (proj2 (Hown k Mk b0 nbk HMk Hb0 Hnbk))))), <- Hnmw.
        cbn [block_exp block_annotate eb_brs block_branches]; rewrite !List.map_map; apply List.map_ext; intros br; reflexivity.
      - rewrite firstn_app_exact by exact HUl'; exact (blocks_typed_bctx _ _ _ _ _ _ _ _ _ HBt').
      - exact (blocks_typed_counts _ _ _ _ _ _ _ _ _ HBt').
      - (** The branches, by their readback. *)
        rewrite firstn_app_exact by exact HUl'.
        intros k Mk ba b' i c gs n B B' HMk Hba Hb' HB HB' Hcn.
        destruct (Completeness.Inductives.Elim.nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        rewrite Completeness.Inductives.Elim.eb_brs_sub in HB; unfold brs_sub in HB; rewrite List.nth_error_map in HB.
        destruct (List.nth_error (eb_brs b0) i) as [[[c0 n0] B0] |] eqn:HB0; cbn in HB; [| discriminate ].
        injection HB as -> -> <-.
        destruct (HBk' k b' Hb') as (nbw & nbk & Mk' & b0' & _ & -> & _ & HMk' & Hb0' & _ & _ & _ & _ & HPb).
        rewrite HMk in HMk'; injection HMk' as <-; rewrite Hb0 in Hb0'; injection Hb0' as <-.
        cbn [block_exp block_annotate eb_brs block_branches] in HB'; rewrite !List.nth_error_map in HB'.
        destruct (List.nth_error (block_branches nbw) i) as [br' |] eqn:Hbr'; cbn in HB'; [| discriminate ].
        injection HB' as _ _ <-.
        rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hb0).
        exact (HPb i br' Hbr' Mk b0 c n B0 gs HMk Hb0 HB0 Hcn).
      - exact motive_kind_relevant. }
    rewrite !firstn_app_exact, skipn_app_exact in E by first [ exact HUl' | exact LUw' ].
    exists (ne_elim p Uw j NBw M1w); split; [ exact (ne_elim_upto_proofs _ _ _ _ _ _ _ _ HUw HNBw HMw) |].
    exact E.
  Qed.

  (** The readback of a stuck eliminator at the member [j] is the
      elimination's at every substitution glued to [ρ]: at a declared
      member by [elim_readback_decl], at a view by the readback at the members
      of lower rank. *)
  Definition elim_readback_ok (j : nat) : Prop :=
    forall Mj as' e Δ σ'' Ns M (M0 : ne), ind_member D j = Some Mj -> Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      List.length Ns = im_nn Mj ->
      (forall i P T, List.nth_error (List.map (fun U => U[σ'']) Us ++ Ns) i = Some P ->
         List.nth_error (tele_insts (im_params D Mj) Id (List.map (fun U => U[σ'']) Us ++ Ns)) i = Some T -> Δ ⊢ P : T) ->
      (forall Mr, Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ Mr -> glu_ne_eq Δ M Mr (im_ty_at p j Mj (List.map (fun U => U[σ'']) Us) Ns)) ->
      Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
      glu_ne_eq Δ (a_elim ak_relevant p (List.map (fun U => U[σ'']) Us) j (blocks_sub Bks σ'') M) M0
        ((List.nth j (blocks_motives Bks) a_prop)[sb_qn (S (im_nn Mj)) σ''][sb_of_list Id (Ns ++ M :: nil)]).

  Lemma elim_readback_decl_ok : forall j Mj pm, ind_member D j = Some Mj -> im_head Mj = mh_decl pm -> elim_readback_ok j.
  Proof.
    intros j Mj pm HMj Hh Mj' as' e Δ σ'' Ns M M0 HMj'; rewrite HMj in HMj'; injection HMj' as <-.
    exact (elim_readback_decl j Mj pm HMj Hh as' e Δ σ'' Ns M M0).
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
  Lemma elim_readback_wk : forall j, elim_readback_ok j ->
      forall Mj as' e Δ' σ' Ns' M', ind_member D j = Some Mj -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      List.length Ns' = im_nn Mj ->
      (forall i P T, List.nth_error (List.map (fun U => U[σ']) Us ++ Ns') i = Some P ->
         List.nth_error (tele_insts (im_params D Mj) Id (List.map (fun U => U[σ']) Us ++ Ns')) i = Some T -> Δ' ⊢ P : T) ->
      (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         glu_ne_eq Δ M'[φ]ʷ M0 (im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns')[φ]ʷ) ->
      forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
        glu_ne_eq Δ (a_elim ak_relevant p (List.map (fun U => U[σ']) Us) j (blocks_sub Bks σ') M')[φ]ʷ M0
          ((List.nth j (blocks_motives Bks) a_prop)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)])[φ]ʷ.
  Proof.
    intros j Hok Mj as' e Δ' σ' Ns' M' HMj Hσ' HNl HPs HMr Δ φ M0 Hφ HR.
    pose proof (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) as Hσ2.
    assert (EU : List.map (fun U0 => U0[φ]ʷ) (List.map (fun U => U[σ']) Us) = List.map (fun U => U[sb_wk σ' φ]) Us)
      by (rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub).
    assert (EB : blocks_wk (blocks_sub Bks σ') φ = blocks_sub Bks (sb_wk σ' φ))
      by (rewrite <- blocks_sub_of_wk, blocks_sub_sub; apply blocks_sub_sb_eq; symmetry; apply sb_wk_compose).
    rewrite exp_wk_elim, EU, EB.
    rewrite (motive_inst_wk _ (S (im_nn Mj)) σ' (Ns' ++ M' :: nil) φ) by (rewrite List.length_app, HNl; cbn; lia).
    rewrite List.map_app; cbn [List.map].
    apply (Hok Mj as' e Δ (sb_wk σ' φ) (List.map (fun N => N[φ]ʷ) Ns') M'[φ]ʷ M0 HMj Hσ2);
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

  (** Fresh variables of the non-recursive arguments of a constructor, at
      their types, are glued at the gluings of the arguments' types
      ([AEl]). *)
  Lemma glu_fresh_args : forall v Mv c gs Δx Usx Ns j1 s ns vs, ind_member D v = Some Mv -> ind_con Mv c = Some gs -> ⊢ Δx ->
      glu_args Δx (ind_uparams D) Id nil Usx ups -> (s + im_nn Mv + j1 + List.length gs = length Δx)%nat ->
      glu_nparams v Mv NEl Δx Usx Ns ns -> tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mv) ↘ vs ->
      tele_rel (ar v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs) ->
      (forall j N T, List.nth_error (vars_from j1 (List.length gs)) j = Some N ->
         List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Usx ++ Ns)) (vars_from j1 (List.length gs))) j = Some T ->
         Δx ⊢ N : T) ->
      forall hs1 rB B hs2 N T w, gs = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error (vars_from j1 (List.length gs)) (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Usx ++ Ns)) (vars_from j1 (List.length gs))) (List.length hs1) = Some T ->
        List.nth_error vs (List.length hs1) = Some w ->
        Δx ⊢ N : T ® w ∈ AEl v ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)).
  Proof.
    intros v Mv c gs Δx Usx Ns j1 s ns vs HMv Hcon HΔx HUsx Hlen Hgn Hns Fc Hav HAt.
    pose proof (components_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl ups_len Hbu Hule Hf Δx Usx HΔx HUsx)
      as [_ HCA _].
    pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
    enough (H : forall n hs1 rB B hs2 N T w, List.length hs1 < n -> gs = hs1 ++ ca_arg rB B :: hs2 ->
              List.nth_error (vars_from j1 (List.length gs)) (List.length hs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Usx ++ Ns)) (vars_from j1 (List.length gs))) (List.length hs1) = Some T ->
              List.nth_error vs (List.length hs1) = Some w ->
              Δx ⊢ N : T ® w ∈ AEl v ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
    { intros hs1 rB B hs2 N T w Heq HN HT Hw; exact (H (S (List.length hs1)) hs1 rB B hs2 N T w ltac:(lia) Heq HN HT Hw). }
    induction n as [| n IH]; intros hs1 rB B hs2 N T w Hn Heq HN HT Hw; [ lia |].
    assert (Hlt : List.length hs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
    pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hav Lv Heq) as Hpre.
    assert (HTP : Δx ⊢ T ® AP v ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
    { eapply (HCA v Mv c gs hs1 rB B hs2 Ns ns (vars_from j1 (List.length gs)) (List.firstn (List.length hs1) vs) T HMv Hcon Heq Hgn Hns);
        [ rewrite List.length_firstn; lia | exact HT | | exact Hpre ].
      intros hs1' rB' B' hs2' N' T' w' Heq1 HN' HT' Hw'.
      subst hs1.
      rewrite List.nth_error_firstn in Hw'; destruct (Nat.ltb_spec (List.length hs1') (List.length (hs1' ++ ca_arg rB' B' :: hs2'))); [| discriminate ].
      rewrite List.firstn_firstn, Nat.min_l by lia.
      eapply (IH hs1' rB' B' (hs2' ++ ca_arg rB B :: hs2)); [ rewrite List.length_app in Hn; cbn in Hn; lia
                                                   | rewrite Heq, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hw' ]. }
    destruct (fresh_cargs_nth _ _ _ _ _ _ Fc hs1 (ca_arg rB B) hs2 Heq) as [Fa _].
    destruct (Fa rB B eq_refl) as (a' & Ea' & Hv).
    rewrite Hw in Hv; injection Hv as ->.
    (** The argument's type, at the components before it. *)
    pose proof (glu_nparams_vals_len _ _ _ _ _ _ _ Hgn) as Lns.
    assert (Ldecl : List.length ns = List.length (List.rev (im_nparams Mv))) by (rewrite List.length_rev, length_im_nparams; exact Lns).
    assert (Lpre : List.length (ns ++ nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))
                   = List.length (List.rev (im_nparams Mv) ++ cargs_nonrec_tele hs1)).
    { rewrite !List.length_app, <- Ldecl, length_cargs_nonrec_tele, length_nonrec_arg_vals; [ reflexivity |].
      rewrite List.length_firstn; lia. }
    assert (HTs : List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs
                  = (List.rev (im_nparams Mv) ++ cargs_nonrec_tele hs1) ++ cargs_nonrec_tele (ca_arg rB B :: hs2))
      by (rewrite Heq, cargs_nonrec_tele_app, List.app_assoc; reflexivity).
    assert (Ea'' : ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs)
                     (ns ++ nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)) ↘ a').
    { rewrite HTs, components_env_prefix by exact Lpre; unfold components_env; rewrite env_tele_app by exact Ldecl; exact Ea'. }
    assert (HnB : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec hs1)) = Some B)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    pose proof (ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ HMv Hns Hcon HnB Hpre Ea'') as Hgu.
    (** An argument's type is not [LevelSort] ([args_related]). *)
    assert (Hnl : not_level_sort a').
    { destruct (Completeness.Inductives.Model.canon_ha D HD Hc Hsu ups bu ups_len Hbu ups ups_tele_args
                  v Mv ns ns c gs _ B _ _ HMv Hns Hcon HnB Hpre) as (a0 & a0' & Ea0 & _ & _ & Hnl0).
      assert (a0 = a') as <- by (eapply functional_eval_exp; eassumption); exact Hnl0. }
    pose proof (HAt _ _ _ HN HT) as HNt.
    apply vars_from_nth_error in HN as [Hnn ->].
    pose proof (var_glu_elem_at u a' _ _ Δx T _ Hgu Hnl HTP HNt ltac:(lia)) as Hvv.
    replace (List.length Δx - 1 - (j1 + (List.length gs - 1 - List.length hs1))) with (s + im_nn Mv + List.length hs1) in Hvv by lia.
    exact Hvv.
  Qed.

  (** ** On a Neutral

      A neutral of the member [j], glued in the group, at a substitution
      [σ'] glued to [ρ]: the eliminator is stuck, at the motive's value at
      the scrutinee; it is glued there when its readback is the
      elimination's ([neut_case_out]), which the readback of its blocks under
      fresh variables gives. *)
  Section NeutCase.
    Variables (j : nat) (Mj : imember) (hd : qname) (k' : nat) (as' : list domain) (e : domain_ne)
      (Δ' : ctx) (Us' Ns' : list exp) (M' : exp).
    Hypotheses (HMj : ind_member D j = Some Mj) (Hrv : im_is_rview Mj = false) (Href : im_ref p j Mj = (hd, k'))
      (He : Dom e ≈ e ∈ per_bot)
      (Hrb : forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         glu_ne_eq Δ M'[φ]ʷ M0 (im_ty_at p j Mj Us' Ns')[φ]ʷ).
    Variables (σ' : sub) (ns : list domain).
    Hypotheses (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HUs' : Us' = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : im_ty_at p j Mj Us' Ns') (Hgn : glu_nparams j Mj NEl Δ' Us' Ns' ns)
      (Hns : tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns)
      (HGm : G j ups ups ns ns (⇑ (d_ind hd k' as') e) (⇑ (d_ind hd k' as') e)).

    Lemma neut_case_inv : List.length as' = (im_unu D Mj + im_nn Mj)%nat /\
        tele_rel (nr j) (List.rev (im_nparams Mj)) ns (List.skipn (im_unu D Mj) as').
    Proof.
      unfold grp_rel in HGm; inversion HGm; subst;
        match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end;
        [ split; assumption
        | match goal with H2 : im_head Mj = mh_record _ _ _ |- _ => exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end ].
    Qed.

    Lemma neut_case_Ps_typed : forall i P T, List.nth_error (Us' ++ Ns') i = Some P ->
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
    Lemma neut_case_out :
        (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
           glu_ne_eq Δ (a_elim ak_relevant p (List.map (fun U => U[σ']) Us) j (blocks_sub Bks σ') M')[φ]ʷ M0
             ((List.nth j (blocks_motives Bks) a_prop)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)])[φ]ʷ) ->
        elim_out j Mj Δ' σ' Ns' M' (⇑ (d_ind hd k' as') e) ns.
    Proof.
      intros Hrbe.
      destruct neut_case_inv as [La Hsn].
      destruct (ER im_ref_target j Mj hd k' HMj Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
      destruct (HBks _ _ HMj Hrv) as [b Hb].
      destruct (Completeness.Inductives.ViewReadback.mref_exists VP HVP p D HPD ups ups_tele_args ups_len j Mj HMj Hrv) as [[[hd0 k0] pre] Er].
      destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D j Mj ups hd0 k0 pre Hl HMj ups_len Er) as [Href0 Lpre].
      rewrite Href in Href0; injection Href0 as E1 E2; subst hd0 k0.
      set (X := List.skipn (im_unu D Mj) as') in *.
      set (m := ⇑ (d_ind hd k' as') e) in *.
      pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ j Mj _ _ _ _ _ _ _ _ HMj HGm Hsn Hns) as HG2.
      (** The motive's entries at the stored parameters, and at [ns], read back. *)
      assert (HXX : tele_rel (nr j) (List.rev (im_nparams Mj)) X X)
        by exact (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ Mj HMj _ _ Hsn).
      set (mes := motive_entries D Mj ups X (d_ind hd k' (pre ++ X)) m).
      assert (Ht : List.Forall2 (fun v t => entry_readable (de_term v t)) (X ++ m :: nil) (List.map snd mes)).
      { unfold mes, motive_entries; rewrite List.map_app; apply List.Forall2_app;
          [ exact (nparams_entries_readable_at_admissible_base D ups nr ar dr ups j Mj X X Hass Had HMj HXX)
          | constructor; [| constructor ] ].
        exact (elim_ups_ok_member_elements_readable_at_ua _ _ _ _ _ _ _ _ Hups j Mj hd k' pre ups ups X ns X m m HMj Hrv Had Had Er HG2 HXX). }
      destruct (EB Completeness.Inductives.Elim.mctx_readable HMall j Mj HMj ρ ρ Hρ Hρ _ _ _ _ _ _ HGm) as [Hr0 _].
      pose proof (Completeness.Inductives.Elim.Forall2_of_Forall_pairs (fun v t => entry_readable (de_term v t)) _ Hr0) as Ht'.
      rewrite tele_entries_values in Ht'.
      destruct (motive_rel j Mj b b ups ups X ns m m _ _ HMj Hrv Hb Hb HG2 Ht Ht') as (a1 & a2 & Ea1 & Ea2 & Hr12 & Hnl1 & Hkl1).
      rewrite <- (motive_entries_values D Mj ups X (d_ind hd k' (pre ++ X)) m), combine_map_fst_snd in Ea1.
      rewrite <- (tele_entries_values (ns ++ m :: nil) ρ (List.rev (elim_mctx p D j Mj Us))), combine_map_fst_snd in Ea2 at 1.
      fold (env_tele ρ (List.rev (elim_mctx p D j Mj Us)) (ns ++ m :: nil)) in Ea2.
      assert (Ee : ⟦elim m at j of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ⇑ a1 (d_elim ρ Bks p ups j as' e)).
      { eapply eval_elim_neut; [ exact Hl | exact HMj | exact Href | exact Hq | exact HMq | unfold im_np; lia | exact Hb
                               | rewrite (Hnm _ _ _ HMj Hb), Hnnq; reflexivity | exact Er | rewrite Hnuq; exact Ea1 ]. }
      (** The motive at the scrutinee, glued in the group ([AtType]). *)
      assert (HIG : ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' Ns' M' (⇑ (d_ind hd k' as') e))
        by (eapply ind_glu_elem_neut; eassumption).
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_tele_args Hbu Hule Hf HΨall
                  nb Hnbu Hnbq Hnbr) as [Hel _].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (Hgl : forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
                Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
                Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® ⇑ (d_ind hd k' as') e ∈ El).
      { intros i P El _ Hglu HT; rewrite <- HUs' in HT |- *.
        exact (proj1 (Hel _ _ _ _ _ _ HIG) Mj ns hd k' pre i P El HMj Er HUg' HMt Hgn Hns HGm Hglu HT). }
      pose proof Hgn as Hgn'; rewrite HUs' in Hgn'.
      destruct (motive_glu j Mj Δ' σ' Ns' ns M' _ hd k' pre HMj Hrv Hσ' Hgn' Hns Er Hgl) as (a0 & Ea0 & Hpa0 & HPa0).
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
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      pose proof (glu_nparams_len _ _ _ _ _ _ _ Hgn) as HNl'.
      assert (HUl' : List.length Us' = ind_nu D) by (rewrite HUs', List.length_map; exact HUl).
      assert (HBt2 : blocks_typed gc_deps gc_stack Δ' p D (List.firstn (ind_nu D) (Us' ++ Ns')) (blocks_sub Bks σ') ak_relevant iA)
        by (rewrite firstn_app_exact by exact HUl'; exact HBt').
      assert (HPl : List.length (Us' ++ Ns') = im_np D Mj) by (rewrite List.length_app, HUl', HNl'; unfold im_np; lia).
      assert (Hbk' : List.nth_error (blocks_sub Bks σ') j = Some (eblock_sub b σ')) by (rewrite nth_error_blocks_sub, Hb; reflexivity).
      assert (Emt : ind_mty p D j Us' Ns' = im_ty_at p j Mj Us' Ns') by (unfold ind_mty; rewrite HMj; reflexivity).
      assert (HMM : Δ' ⊢ M' ≈ M' : ind_mty p D j (List.firstn (ind_nu D) (Us' ++ Ns')) (List.skipn (ind_nu D) (Us' ++ Ns')))
        by (rewrite firstn_app_exact, skipn_app_exact, Emt by exact HUl'; apply wf_exp_eq_refl; exact HMt).
      pose proof (wf_elim_scrut_eq Δ' p D j Mj (eblock_sub b σ') (blocks_sub Bks σ') (Us' ++ Ns') M' M' ak_relevant iA Hl HMj Hbk' HPl
                    neut_case_Ps_typed HBt2 HMM) as E2.
      rewrite firstn_app_exact, skipn_app_exact in E2 by exact HUl'.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMj Hb) in E2.
      destruct (presup_exp_eq E2) as (_ & Hty & _).
      rewrite (blocks_motives_nth _ _ _ Hb) in HTP, Hrbe |- *.
      rewrite <- HUs' in Hrbe |- *.
      eapply realize_glu_elem_bot; [ exact Hg1 |].
      econstructor; [ exact Hty | exact Hg1 | exact HTP | |].
      - (** A neutral of the motive's value: not [LevelSort], nor of a
            type of levels ([motive_rel]). *)
        split; [ exact Hnl1 | split; [ exact (ER per_bot_elim j Mj hd k' as' as' e e ups ups ns ns HMj Hrv HGm) |] ].
        intros Hk; exfalso; exact (Hkl1 Hk).
      - exact Hrbe.
    Qed.
  End NeutCase.

  (** The neutral case at a member whose stuck eliminator reads back as
      the elimination ([elim_readback_ok]). *)
  Lemma neut_ok_of_rb : forall j, elim_readback_ok j -> neut_ok j.
  Proof.
    intros j Hok Mj hd k' as' e Δ' Us' Ns' M' HMj Href He Hrb Mk σ' ns HMk Hrv Hσ' HUs' HMt Hgn Hns HGm.
    rewrite HMj in HMk; injection HMk as <-.
    apply (neut_case_out j Mj hd k' as' e Δ' Us' Ns' M' HMj Hrv Href He Hrb σ' ns Hσ' HUs' HMt Hgn Hns HGm).
    intros Δ φ M0 Hφ HR.
    pose proof (neut_case_Ps_typed j Mj Δ' Us' Ns' HMj σ' ns Hσ' HUs' Hgn Hns) as HPs.
    subst Us'.
    exact (elim_readback_wk j Hok Mj as' e Δ' σ' Ns' M' HMj Hσ' (glu_nparams_len _ _ _ _ _ _ _ Hgn) HPs Hrb Δ φ M0 Hφ HR).
  Qed.

  (** ** Recursive Results of Neutrals

      By induction on the gluing of the group, at neutral values: along a
      leaf path that ends in a member whose stuck eliminator reads back
      ([elim_readback_ok]), the recursive result of a neutral recursive argument
      is glued ([rec_prop] at [elim_readback_ok]), and so are those of the
      fields of a neutral of a record view ([rview_ihs_prop]).  The end of
      a path is a neutral of the member it ends in ([neut_ok_of_rb]);
      neutrals stay neutral through applications ([is_neut_app]) and
      projections ([is_neut_projs]).  A constructor is no neutral.  The
      induction is on the gluing alone: no rank is involved, the
      readbacks at the ends are premises. *)
  Theorem rec_neut_all :
    (forall k Γ' Us' Ns' M' mv, ind_glu_elem p D ups NEl AEl DP DEl k Γ' Us' Ns' M' mv ->
       is_neut mv -> rview_ihs_prop elim_readback_ok k Γ' Us' M' mv) /\
    (forall k Γ' Us' pre Ts t A N v, glu_rec p D ups NEl AEl DP DEl k Γ' Us' pre Ts t A N v ->
       is_neut v -> forall σs, A = ptyp_ty_at p D Us' σs t -> rec_prop elim_readback_ok k Γ' Us' pre Ts t σs N v).
  Proof.
    apply (ind_glu_elem_mut_ind_all p D ups NEl AEl DP DEl
             (fun k Γ' Us' Ns' M' mv _ => is_neut mv -> rview_ihs_prop elim_readback_ok k Γ' Us' M' mv)
             (fun k Γ' Us' pre Ts t A N v _ => is_neut v -> forall σs, A = ptyp_ty_at p D Us' σs t ->
                                              rec_prop elim_readback_ok k Γ' Us' pre Ts t σs N v)).
    - (** A constructor: no neutral. *)
      intros *; repeat intro;
        match goal with H : _ |- _ => solve [ destruct H as (?a0 & ?e0 & ?E0); discriminate ] end.
    - (** A neutral of a member that is no record view. *)
      intros k Mk hd k' m Γ' Us' Ns' M' as' HMk Hrv _ _ _ _ Mk0 qr Is fl c gs ws HMk0 Hh.
      rewrite HMk in HMk0; injection HMk0 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv Hh).
    - (** An element of a record view: its fields. *)
      intros k Mk qr Is fl c gs Us' Ns' As m vs Γ' M HMk Hh Hcs HUl' HNl HAl Hps HMeq Hv HAs Harg Hrec IH Hn
        Mk0 qr0 Is0 fl0 c0 gs0 ws0 HMk0 Hh0 Hcs0 Hws0.
      rewrite HMk in HMk0; injection HMk0 as <-.
      rewrite Hh in Hh0; injection Hh0 as <- <- <-; rewrite Hcs in Hcs0; injection Hcs0 as <- <-.
      pose proof (functional_eval_projs _ _ _ _ Hws0 Hps) as ->.
      destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMk Hh) as [_ Hnn].
      destruct Ns' as [| N0 Ns']; [| cbn in HNl; lia ].
      cbn [List.app] in HMeq.
      rewrite List.app_nil_r in HAs.
      apply (mk_rview_ihs_at elim_readback_ok k Mk c gs Γ' Us' M vs As HAl HMeq HAs).
      intros gs1 tf gs2 N A w Heq HN HA Hw σs HAeq.
      rewrite <- (List.app_nil_r Us') in HA.
      assert (Hnw : is_neut w)
        by exact (proj1 (List.Forall_forall _ _) (is_neut_projs _ _ _ Hps Hn) w (List.nth_error_In _ _ Hw)).
      exact (IH gs1 tf gs2 N A w Heq HN HA Hw Hnw σs HAeq).
    - (** At the end of a shape. *)
      intros j Mj Ps Ts pre A Us' Γ' N v k HMj Hs1 Hs2 IH Hn σs HA.
      destruct (im_is_rview Mj) eqn:Hrv.
      + (** A record view: through its fields. *)
        apply (rec_rview_case elim_readback_ok k Γ' Us' pre Ts j Mj Ps A N v HMj Hrv); [| exact HA ].
        intros bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq; exact (IH bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq Hn).
      + (** A member with a block: the stuck eliminator. *)
        apply (rec_self_case elim_readback_ok k Γ' Us' pre Ts j Mj Ps A N v HMj Hrv Hs1); [| exact HA ].
        intros Hok bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq.
        pose proof (Hs2 bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq) as Hg0.
        destruct Hn as (a0 & e0 & ->).
        inversion Hg0; subst;
          match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end;
          [| match goal with H2 : im_head Mj = mh_record _ _ _ |- _ => exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end ].
        eapply neut_ok_of_rb; eassumption.
    - (** At a domain: a function, by the rest at its applications. *)
      intros A Γ' k pre Ts B v Us' t N Hq1 Hq2 _ IH Hn σs HA.
      apply (rec_pi_case elim_readback_ok k Γ' Us' pre Ts B t A N v Hq1 Hq2); [| exact HA ].
      intros IT OT HAp Δ φ b c fc Hφ Hdc Hb Efc σs' HOT.
      exact (IH IT OT HAp Δ φ b c fc Hφ Hdc Hb Efc (is_neut_app _ _ _ Efc Hn) σs' HOT).
  Qed.

  (** ** A Branch of a View's Block, Read Back

      The block of the container's member [i'] the view [vm] of the member
      [m] wraps, at the instance of the blocks by [σ''] glued to [ρ]: the
      branch of the container's constructor [c] is the view's branch at the
      container's variables and the recursive results of the view
      ([wrap_branch]); it is glued at the environment the readback reads it in,
      so equal to its readback, at the container's branch type
      ([view_branch_type_conv]). *)
  Section ViewBranch.
    Variables (m : nat) (Mm : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (D' : ind_decl).
    Hypotheses (Hm : ind_member D m = Some Mm) (Hh : im_head Mm = mh_view qc kc Is vm)
      (Hq : ind_lookup gc_deps gc_stack qc = Some D') (Hvw : view_wrap_ok D D' vm).
    Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember) (b : eblock) (c : String.string) (gs' gs : list carg).
    Hypotheses (Hi' : ind_member D' i' = Some Mi') (Hri' : im_is_rview Mi' = false) (Hv : List.nth_error vm i' = Some v)
      (HMv : ind_member D v = Some Mv)
      (Hb : List.nth_error Bks v = Some b) (Hcon' : ind_con Mi' c = Some gs') (Hcon : ind_con Mv c = Some gs)
      (Hcorr : cargs_correspond vm gs' gs).
    Variables (Δ : ctx) (σ'' : sub).
    Hypothesis (Hσ'' : Δ ⊢ˢ σ'' ® ρ ∈ SbΓ).

    #[local] Abbreviation n' := (im_nn Mv + List.length gs' + cargs_nrec D' gs')%nat.
    #[local] Abbreviation Us'' := (List.map (fun U => U[σ'']) Us).
    #[local] Abbreviation Bks'' := (blocks_sub Bks σ'').
    #[local] Abbreviation Is'' := (List.map (fun I => I[sb_of_list Id Us'']) Is).
    #[local] Abbreviation Δc := (elim_bctx ak_relevant qc D' Mi' gs' (blocks_motives (view_wrap ak_relevant p qc D D' vm Us'' Is'' Bks'')) Is'' ++ Δ).
    #[local] Abbreviation σw := (sb_wk σ'' (wk_shiftn n')).
    #[local] Abbreviation nvars := (vars_from (cargs_nrec D' gs' + List.length gs') (im_nn Mv)).
    #[local] Abbreviation avars := (vars_from (cargs_nrec D' gs') (List.length gs')).
    #[local] Abbreviation Usw := (List.map (fun U => U[wk_shiftn n']ʷ) Us'').
    #[local] Abbreviation σ0 := (sb_of_list (ι (wk_shiftn n')) (Usw ++ nvars)).
    #[local] Abbreviation Ihs := (elim_ihs ak_relevant p D Usw (blocks_wk Bks'' (wk_shiftn n')) σ0 (im_nn Mv) gs avars).
    #[local] Abbreviation W := (wrap_ihs D' D gs' gs Ihs 0 (cargs_nrec D' gs')).
    #[local] Abbreviation Ms := (nvars ++ avars ++ W).
    #[local] Abbreviation C := (elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us).

    Lemma view_branch_Δ : ⊢ Δ.
    Proof. pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ''); gen_presups; assumption. Qed.

    Lemma view_branch_HUl : List.length Us'' = ind_nu D.
    Proof. rewrite List.length_map; exact HUl. Qed.

    Lemma view_branch_HUs : forall k U T, List.nth_error Us'' k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us'') k = Some T ->
        Δ ⊢ U : T.
    Proof. exact (glu_args_typed _ _ _ _ _ _ Ua (us_glu_args Δ σ'' Hσ'')). Qed.

    Lemma view_branch_HBt : blocks_typed gc_deps gc_stack Δ p D Us'' Bks'' ak_relevant iA.
    Proof. exact (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ _ Hl HUl HBt (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'')). Qed.

    Lemma view_branch_nn : im_nn Mv = im_nn Mi'.
    Proof.
      destruct (view_wrap_ok_members _ _ _ Hvw i' Mi' v Hi' Hv) as (Mv' & HMv' & Hnn & _).
      rewrite HMv in HMv'; injection HMv' as <-; exact Hnn.
    Qed.

    Lemma view_branch_na : List.length gs' = List.length gs.
    Proof. exact (cargs_correspond_length _ _ _ Hcorr). Qed.

    Lemma view_branch_ctx : ⊢ Δc.
    Proof.
      exact (view_blocks_branch_ctx gc_deps gc_stack Δ p D m Mm qc kc Is vm D' Us'' Bks'' ak_relevant iA (ctx_wf_gctx _ _ _ view_branch_Δ) (decls_of_ctx _ _ _ view_branch_Δ)
               Hl Hm Hh Hq Hvw view_branch_Δ view_branch_HUl view_branch_HUs view_branch_HBt i' Mi' c gs' Hi' Hcon').
    Qed.

    Lemma view_branch_sub_typed : Δc ⊢ˢ sb_of_list (ι (wk_shiftn n')) Ms : elim_bctx ak_relevant p D Mv gs (blocks_motives Bks'') Us'' ++ Δ.
    Proof.
      exact (view_blocks_branch_sub gc_deps gc_stack Δ p D m Mm qc kc Is vm D' Us'' Bks'' ak_relevant iA (ctx_wf_gctx _ _ _ view_branch_Δ) (decls_of_ctx _ _ _ view_branch_Δ)
               Hl Hm Hh Hq Hvw view_branch_Δ view_branch_HUl view_branch_HUs view_branch_HBt i' Mi' v Mv c gs' gs Hi' Hri' Hv HMv Hcon' Hcon Hcorr).
    Qed.

    Lemma view_branch_len : List.length Ms = List.length C.
    Proof.
      rewrite length_elim_bctx, !List.length_app, !length_vars_from, (length_wrap_ihs _ _ _ _ _ _ _ _ Hcorr), view_branch_na;
        [ lia | apply length_elim_ihs; rewrite length_vars_from; exact view_branch_na ].
    Qed.

    Lemma view_branch_lenc : List.length Δc = (List.length Δ + n')%nat.
    Proof. rewrite List.length_app, length_elim_bctx, view_branch_nn; lia. Qed.

    Lemma view_branch_kripke : Δc ⊢ᵏ wk_shiftn n' : Δ.
    Proof.
      pose proof (kripke_shiftn_app _ Δ view_branch_ctx) as H.
      rewrite length_elim_bctx, <- view_branch_nn in H.
      replace (cargs_nrec D' gs' + List.length gs' + im_nn Mv)%nat with n' in H by lia; exact H.
    Qed.

    Lemma view_branch_σw : Δc ⊢ˢ σw ® ρ ∈ SbΓ.
    Proof. exact (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ'' view_branch_kripke). Qed.

    (** The instance of the group's branch context by [σ''] is the
        group's branch context at the instance of the blocks. *)
    Lemma view_branch_C_sub : tele_sub C σ'' = elim_bctx ak_relevant p D Mv gs (blocks_motives Bks'') Us''.
    Proof.
      exact (elim_bctx_sub ak_relevant p D v Mv c gs (blocks_motives Bks) (blocks_motives Bks'') Us σ'' Hc HMv (cons_lookup_in _ _ _ Hcon) HUl
               (fun j0 Mj0 HMj0 => blocks_motives_sub D Bks σ'' j0 Mj0 Hnm HMj0)).
    Qed.

    (** The entries of the substitution, typed. *)
    Lemma view_branch_typed : forall k M T, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C σw Ms) k = Some T -> Δc ⊢ M : T.
    Proof.
      intros k M T HM HT.
      assert (E : tele_insts C σw Ms = tele_insts (elim_bctx ak_relevant p D Mv gs (blocks_motives Bks'') Us'') (ι (wk_shiftn n')) Ms)
        by (rewrite <- view_branch_C_sub, tele_insts_tele_sub; apply tele_insts_sb_eq, sb_wk_compose).
      rewrite E in HT.
      refine (wf_sub_of_list_inv _ _ _ _ _ _ _ (elim_bctx_ass ak_relevant p D v Mv gs _ Us'' Hc HMv) _ view_branch_sub_typed k M T HM HT).
      rewrite view_branch_len, !length_elim_bctx; reflexivity.
    Qed.

    (** The uniform parameters, the blocks and the substitutions of the
        shapes' components of the wrapped branch, at [σw]. *)
    Lemma view_branch_EUs : Usw = List.map (fun U => U[σw]) Us.
    Proof. rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub. Qed.

    Lemma view_branch_EUs' : List.map (fun U => U[ι (wk_shiftn n')]) Us'' = List.map (fun U => U[σw]) Us.
    Proof.
      rewrite List.map_map; apply List.map_ext; intros U.
      rewrite exp_sub_sub; apply exp_sub_sb_eq; symmetry; apply sb_wk_compose.
    Qed.

    Lemma view_branch_EB : blocks_wk Bks'' (wk_shiftn n') = blocks_sub Bks σw.
    Proof. rewrite <- blocks_sub_of_wk, blocks_sub_sub; apply blocks_sub_sb_eq; symmetry; apply sb_wk_compose. Qed.

    Lemma view_branch_σs : forall gs1, cargs_sub σ0 gs1 avars
        = sb_of_list (ι (wk_shiftn n')) (List.map (fun U => U[σw]) Us ++ nvars ++ nonrec_exps gs1 (List.firstn (List.length gs1) avars)).
    Proof. intros; rewrite cargs_sub_of_list, nonrec_exps_firstn_len, view_branch_EUs, List.app_assoc; reflexivity. Qed.

    Variables (ns vs ihs wihs : list domain) (hd : qname) (k0 : nat) (pre : list domain).
    Hypotheses (Lpre : List.length pre = im_unu D Mv)
      (Fn : Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ups ⍮ length Δ ↘ ns)
      (Fc : Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns
              ⍮ (length Δ + im_nn Mv) ↘ vs)
      (Fi : Fihs vs at gs' gs of D' under ρ (blocks_motives Bks) at p ups in gc_deps ⍮ gc_stack
              ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (length Δ + im_nn Mv + List.length gs') ↘ ihs)
      (Wi : ⟦wihs vs of gs' gs of D' with ihs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ wihs)
      (HGm : G v ups ups ns ns (d_con hd k0 c ((pre ++ ns) ++ vs)) (d_con hd k0 c ((pre ++ ns) ++ vs)))
      (Hir : rec_results_rel D dr Rel v ups ups ns ns (List.rev (im_nparams Mv)) gs vs vs wihs wihs)
      (** The stuck eliminator reads back at the end of every leaf path the
          view nests through: of an argument non-recursive in the
          container, or not the container's *)
      (Hok : forall gs1' g' gs2' gs1 t gs2 l, gs' = gs1' ++ g' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
               List.length gs1' = List.length gs1 -> In l (shape_leaves (rview_leaves D) 0 t) ->
               (forall t', g' = ca_rec t' -> leaf_in D' t' l = false) -> elim_readback_ok (leaf_mem l)).

    (** The view's member is no record view, as the container's is not. *)
    Lemma view_branch_rv : im_is_rview Mv = false.
    Proof.
      destruct (group_structure_vm _ Hass m Mm qc kc Is vm D' i' Mi' Hm Hh Hq Hi') as [v1 Mv1 Hvm HMv1 _ Himg].
      rewrite Hv in Hvm; injection Hvm as <-; rewrite HMv in HMv1; injection HMv1 as <-.
      unfold im_is_rview in *; destruct (im_head Mi') as [pm | qv kv Is'' vm'' | qr Is'' fl] eqn:Hh'; try discriminate.
      - destruct Himg as [vm' Hv']; rewrite Hv'; reflexivity.
      - destruct Himg as (Is' & vm' & Hv' & _); rewrite Hv'; reflexivity.
    Qed.

    Lemma view_branch_rel : tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns /\
        con_args_rel p D (admissible_index_at D ups nr) nr ar dr v ups ups ns ns (List.rev (im_nparams Mv)) gs vs vs /\
        tele_rel (ar v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs).
    Proof.
      pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
      unfold grp_rel in HGm; inversion HGm; subst;
        match goal with H1 : ind_member D v = Some ?M1 |- _ => rewrite HMv in H1; injection H1 as <- end;
        [| match goal with H2 : im_head Mv = mh_record _ _ _ |- _ => exfalso; exact (not_rview_record _ _ _ _ view_branch_rv H2) end ].
      match goal with H1 : ind_con Mv c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app; lia ]; destruct E as [-> ->] end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app in *; lia ]; destruct E as [-> ->] end.
      rewrite skipn_app_exact in * by exact Lpre.
      split; [ assumption | split; assumption ].
    Qed.

    (** A recursive result along a leaf path the view nests through (of
        an argument non-recursive in the container, or a path that is not
        the container's): the eliminator along the path at the argument.
        The argument is a fresh variable glued at its type ([glu_args] of
        the parameters and the arguments), so glued at its shape
        ([con_rec_glu]); it is neutral, so its result along the path is
        glued ([rec_neut_all]), as the stuck eliminator at the path's end
        member reads back ([Hok]). *)
    Lemma view_branch_nested : forall gs1' g' gs2' gs1 t gs2 idx l l' v' rs r a (lv : nat) Rv (i : nat) P El T,
        gs' = gs1' ++ g' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
        List.nth_error (shape_leaves (rview_leaves D) 0 t) idx = Some l -> (forall t', g' = ca_rec t' -> leaf_in D' t' l = false) ->
        List.nth_error (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mv) t) idx = Some l' ->
        List.nth_error vs (List.length gs1) = Some v' -> ⟦ih v' of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rs ->
        List.nth_error rs idx = Some r ->
        Elim.leaf_type_at D ups ρ (blocks_motives Bks) mctx_tele (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
          (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) t v' idx a ->
        DF a ≈ a ∈ per_univ_elem lv ↘ Rv -> Rv r r ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δc ⊢ T ® P ->
        glu_args Δc (tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) (sb_of_list Id Us)) σw ρ (nvars ++ avars) (ns ++ vs) ->
        Δc ⊢ leaf_ih ak_relevant p Usw (blocks_wk Bks'' (wk_shiftn n')) (cargs_sub σ0 gs1 avars)
               (a_var (cargs_nrec D' gs' + (List.length gs' - 1 - List.length gs1))) l' : T ® r ∈ El.
    Proof.
      intros gs1' g' gs2' gs1 t gs2 idx l l' v' rs r a lv Rv i P El T Heq' Heq Hlen Hln Hnin Hl' Hv' Ers Hr Hlty HRa Hrr Hg HTP Hpre.
      destruct view_branch_rel as (Hns & Hia & Hav).
      pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
      pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
      pose proof view_branch_na as Xna.
      assert (Hlt : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      (** The argument: a fresh variable, its shape's value. *)
      destruct (Completeness.Inductives.CargsRel.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (y & y' & Hy & Hy' & Hsh).
      rewrite Hv' in Hy; injection Hy as <-; rewrite Hv' in Hy'; injection Hy' as <-.
      destruct (fresh_cargs_nth _ _ _ _ _ _ Fc gs1 (ca_rec t) gs2 Heq) as [_ Fr].
      destruct (Fr t eq_refl) as (a_sh & Esh & Hy).
      rewrite Hv' in Hy; injection Hy as Ev'.
      pose proof view_branch_ctx as HΔc.
      pose proof view_branch_σw as Hσw.
      pose proof (us_glu_args Δc _ Hσw) as XUg.
      set (nv := nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) in *.
      (** The container's variables, typed and glued. *)
      assert (Xg : ⊢ᵍ gc_deps ⍮ gc_stack) by exact (ctx_wf_gctx _ _ _ view_branch_Δ).
      pose proof (view_blocks_branch_base gc_deps gc_stack Δ p D m Mm qc kc Is vm D' Us'' Bks'' ak_relevant iA Xg (decls_of_ctx _ _ _ view_branch_Δ) Hl Hm Hh Hq Hvw view_branch_Δ
                    view_branch_HUl view_branch_HUs view_branch_HBt i' Mi' v Mv c gs' gs Hi' Hri' Hv HMv Hcon' Hcon) as Xbase.
      destruct (con_inst_tele_args_typed _ _ Δc Δ p D v Mv Us'' c gs (wk_shiftn n') nvars avars Hc HMv (cons_lookup_in _ _ _ Hcon) view_branch_HUl
                  (length_vars_from _ _) ltac:(rewrite length_vars_from; exact Xna) Xbase) as [XNt XAt].
      rewrite view_branch_EUs in XNt, XAt.
      pose proof (glu_fresh_nparams v Mv Δc (List.map (fun U => U[σw]) Us) (cargs_nrec D' gs' + List.length gs') (length Δ) ns HMv HΔc XUg
                    ltac:(rewrite view_branch_lenc; lia) Fn Hns XNt) as Xgn.
      replace (vars_from (cargs_nrec D' gs') (List.length gs')) with (vars_from (cargs_nrec D' gs') (List.length gs)) in XAt
        by (rewrite Xna; reflexivity).
      pose proof (glu_fresh_args v Mv c gs Δc (List.map (fun U => U[σw]) Us) nvars (cargs_nrec D' gs') (length Δ) ns vs HMv Hcon HΔc XUg
                    ltac:(rewrite view_branch_lenc; lia) Xgn Hns Fc Hav XAt) as XAEl.
      (** The substitution of the shape's components, glued. *)
      destruct (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ 0 HMv Hcon Heq ltac:(lia)) as [SbC HSbC].
      pose proof HSbC as HSbC0; cbn [List.firstn doms_ctx List.app] in HSbC0.
      assert (XHpre : forall hs1 rB B hs2 N T' w, gs1 = hs1 ++ ca_arg rB B :: hs2 ->
                 List.nth_error (vars_from (cargs_nrec D' gs') (List.length gs)) (List.length hs1) = Some N ->
                 List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (List.map (fun U => U[σw]) Us ++ nvars))
                                   (vars_from (cargs_nrec D' gs') (List.length gs))) (List.length hs1) = Some T' ->
                 List.nth_error (List.firstn (List.length gs1) vs) (List.length hs1) = Some w ->
                 Δc ⊢ N : T' ® w ∈ AEl v ns c (List.length (cargs_nonrec hs1))
                                     (nonrec_arg_vals hs1 (List.firstn (List.length hs1) (List.firstn (List.length gs1) vs)))).
      { intros hs1 rB B hs2 N T' w E1 HN HT' Hw.
        assert (Lh : List.length hs1 < List.length gs1) by (rewrite E1, List.length_app; cbn; lia).
        rewrite List.firstn_firstn, Nat.min_l by lia.
        rewrite List.nth_error_firstn in Hw; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| discriminate ].
        apply (XAEl hs1 rB B (hs2 ++ ca_rec t :: gs2)); [ rewrite Heq, E1, <- List.app_assoc; reflexivity | exact HN | exact HT' | exact Hw ]. }
      pose proof (nonrec_prefix_pre _ gs vs gs1 (ca_rec t) gs2 Hav Lv Heq) as Xpfx.
      pose proof (nonrec_args_prefix_glu_sub p D Hc Hass ups u NP NEl AP AEl DP DEl ups_len Hf Δc (List.map (fun U => U[σw]) Us) HΔc XUg
                    v Mv c gs gs1 (ca_rec t) gs2 nvars ns (vars_from (cargs_nrec D' gs') (List.length gs)) (List.firstn (List.length gs1) vs) SbC
                    HMv Hcon Heq Xgn Hns ltac:(rewrite List.length_firstn; lia) ltac:(rewrite length_vars_from; lia) XHpre Xpfx HSbC0) as Xσ0.
      replace (vars_from (cargs_nrec D' gs') (List.length gs)) with (vars_from (cargs_nrec D' gs') (List.length gs')) in Xσ0
        by (rewrite Xna; reflexivity).
      replace (doms_ctx nil) with (@nil centry) in HSbC0 by reflexivity; cbn [List.app] in HSbC0.
      set (Ys := nvars ++ nonrec_exps gs1 (List.firstn (List.length gs1) avars)).
      assert (XYl : List.length Ys = (0 + List.length (cargs_nonrec gs1) + im_nn Mv)%nat).
      { unfold Ys; rewrite List.length_app, length_vars_from, length_nonrec_exps
          by (rewrite List.length_firstn, length_vars_from; lia); lia. }
      assert (Xσs : Δc ⊢ˢ sb_of_list (ι (wk_shiftn n')) (List.map (fun U => U[σw]) Us ++ Ys)
                    ® components_env D ups (List.rev (doms_ctx (List.firstn 0 (ptyp_doms t))
                                                       ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mv))
                        (ns ++ nv ++ nil) ∈ SbC).
      { cbn [List.firstn doms_ctx List.app]; rewrite List.app_nil_r.
        unfold Ys; rewrite List.app_assoc.
        refine (glu_sub_closed_rebase _ SbC Δc Id _ _ _ _ HSbC0 _ Xσ0).
        - unfold all_assumptions; apply List.Forall_app; split; [ apply nonrec_args_prefix_ass | exact (member_params_ass D Hc _ _ HMv) ].
        - rewrite !List.length_app, List.length_map, length_vars_from, length_im_params.
          rewrite length_nonrec_exps by (rewrite List.length_firstn, length_vars_from; lia).
          rewrite length_nonrec_args_prefix by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
          unfold im_np, ind_nu in *; lia. }
      set (σs := sb_of_list (ι (wk_shiftn n')) (List.map (fun U => U[σw]) Us ++ Ys)) in *.
      assert (Eσ : cargs_sub σ0 gs1 avars = σs) by (unfold σs, Ys; apply view_branch_σs).
      set (N := a_var (cargs_nrec D' gs' + (List.length gs' - 1 - List.length gs1))).
      set (fa := List.firstn (List.length gs1) vs) in *.
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn; lia).
      (** The argument, glued at its type ([Hpre]), and at the type's value
          at [ups] ([inst_entry_link]). *)
      set (ka := (im_nn Mv + List.length gs1)%nat).
      set (con_inst_tele := tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) (sb_of_list Id Us)) in *.
      assert (HassT : all_assumptions con_inst_tele)
        by (apply all_assumptions_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_nparams_ass D Hc _ _ HMv) ]).
      assert (Lctel : List.length con_inst_tele = (im_nn Mv + List.length gs)%nat)
        by (unfold con_inst_tele; rewrite length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams; lia).
      assert (HNk : List.nth_error (nvars ++ avars) ka = Some N).
      { unfold ka, N; rewrite List.nth_error_app2 by (rewrite length_vars_from; lia).
        rewrite length_vars_from, Nat.add_comm, Nat.add_sub.
        rewrite <- (vars_from_nth (cargs_nrec D' gs') (List.length gs') (List.length gs' - 1 - List.length gs1) (a_var 0)) by lia.
        replace (List.length gs' - 1 - (List.length gs' - 1 - List.length gs1)) with (List.length gs1) by lia.
        apply List.nth_error_nth'; rewrite length_vars_from; lia. }
      assert (Hvk : List.nth_error (ns ++ vs) ka = Some v')
        by (unfold ka; rewrite List.nth_error_app2, Ln, Nat.add_comm, Nat.add_sub by lia; exact Hv').
      destruct (nth_error_lt_some (List.rev con_inst_tele) ka ltac:(rewrite List.length_rev; unfold ka; lia)) as [e He].
      assert (HeA : exists κA A0', e = ce_ass κA A0').
      { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
        unfold all_assumptions in HassT; rewrite List.Forall_forall in HassT; exact (HassT _ Hin). }
      destruct HeA as (κA & A0' & ->).
      destruct (nth_error_lt_some (tele_insts con_inst_tele σw (nvars ++ avars)) ka) as [TA HTA].
      { rewrite length_tele_insts by exact HassT; rewrite List.length_app, !length_vars_from; unfold ka; lia. }
      destruct (glu_args_glu _ _ _ _ _ _ Hpre ka N TA v' κA A0' HNk HTA Hvk He) as [ia aA PA ElA EaA HgA HTA' HNA].
      pose proof (EB Completeness.Inductives.Elim.closed_args_tele_args v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                    (List.length gs) (le_n _)) as Hpg.
      rewrite List.firstn_all2, List.firstn_all2 in Hpg by lia.
      assert (HCa : all_assumptions ((cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D))
        by (rewrite <- List.app_assoc; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMv) ]).
      assert (HCs : ⊨ (cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; exact (valid_group_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon)).
      assert (HCS : ⊨ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU ++ Γ).
      { pose proof (valid_blocks_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as H.
        assert (Esp : elim_bctx ak_relevant p D Mv gs (blocks_motives Bks) Us
                      = ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                        ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)
          by (rewrite tele_sub_app, length_im_nparams; unfold elim_bctx; reflexivity).
        rewrite Esp, <- List.app_assoc in H; exact (Completeness.UnitCases.rel_ctx_wf_app_r _ _ H). }
      destruct (inst_entry_link _ HCa HCs HCS (ns ++ vs) Hpg
                  ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia) ka κA A0' aA He EaA)
        as (κ0 & A0 & bA & j0 & HA0 & Eb & Hab).
      rewrite List.rev_app_distr, List.nth_error_app2 in HA0 by (rewrite List.length_rev, length_im_nparams; unfold ka; lia).
      rewrite List.length_rev, length_im_nparams in HA0; unfold ka in HA0; rewrite Nat.add_comm, Nat.add_sub in HA0.
      pose proof (cargs_rev_nth_rec p D Mv gs gs1 t gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as -> ->.
      assert (Efk : List.firstn ka (ns ++ vs) = ns ++ fa)
        by (unfold ka, fa; rewrite firstn_app_ge by lia; rewrite Ln, Nat.add_comm, Nat.add_sub; reflexivity).
      rewrite Efk in Eb.
      destruct (glu_transfer_per_elem ia j0 aA bA PA ElA Δc TA N v' HgA Hab HTA' HNA) as (ib & Pb & Elb & Hgb & _ & HNb).
      (** The arguments before, related at their telescope. *)
      pose proof (EB Completeness.Inductives.Elim.closed_args_tele_args v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                    (List.length gs1) ltac:(lia)) as Hpg1.
      replace (List.firstn (List.length gs1) gs) with gs1 in Hpg1 by (rewrite Heq; symmetry; apply firstn_app_len; reflexivity).
      assert (Hpg2 : per_tele_args (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
      { unfold im_params; rewrite List.app_assoc, List.rev_app_distr.
        apply Decl.per_tele_args_app_intro; [ rewrite List.length_rev; exact ups_len | exact ups_tele_args | exact Hpg1 ]. }
      (** The argument's type's value, at the components before it. *)
      assert (Eb' : ⟦ ptyp_ty p D (im_nn Mv) (List.repeat false 0 ++ cargs_pat gs1) t ⟧
                      env_tele (env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa))
                        (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn 0 (ptyp_doms t)))) nil ↘ bA).
      { change (env_tele (env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa))
                  (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn 0 (ptyp_doms t)))) nil)
          with (env_tele nil (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) (ups ++ ns ++ fa)).
        cbn [List.repeat List.app].
        unfold im_params; rewrite List.app_assoc, Completeness.Inductives.Decl.env_tele_uparams by exact ups_len.
        assert (Ectx : List.rev (cargs_ctx p D Mv gs ++ im_nparams Mv)
                       = List.rev (cargs_ctx p D Mv gs1 ++ im_nparams Mv)
                         ++ List.rev (cargs_ctx_aux p D (im_nn Mv) (cargs_pat gs1) (ca_rec t :: gs2)))
          by (rewrite Heq, cargs_ctx_app, <- List.app_assoc, (List.rev_app_distr (cargs_ctx_aux _ _ _ _ _)); reflexivity).
        rewrite Ectx, components_env_prefix in Eb
          by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_nparams, Ln, Lfa; lia).
        exact Eb. }
      (** The argument at its shape ([con_rec_glu]), neutral. *)
      pose proof (con_rec_glu VP p D HVP HPD HG v Mv c gs HMv Hcon ups bu u NP NEl AP AEl DP DEl ups_len ups_tele_args Hbu Hule Hf
                    gs1 t gs2 ns fa Heq Ln Lfa Hns Xpfx Hpg2
                    (Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_tele_args Hbu Hule Hf (ptyp_mem t))
                    t 0 nil Δc (ι (wk_shiftn n')) (List.map (fun U => U[σw]) Us) Ys SbC TA N v' bA ib Pb Elb
                    eq_refl (Nat.le_0_l _) (tele_prefix_rel_nil _) ltac:(constructor) HΔc XUg XYl HSbC Xσs Eb' Hgb HNb) as Hrg.
      fold σs in Hrg; cbn [List.firstn] in Hrg; rewrite !List.app_nil_r in Hrg.
      assert (Hnv : is_neut v') by (rewrite Ev'; do 2 eexists; reflexivity).
      pose proof (proj2 rec_neut_all _ _ _ _ _ _ _ _ _ Hrg Hnv σs eq_refl) as Hrp.
      (** The result along the path, typed ([view_blocks_branch_argrec], [view_blocks_branch_rec_arg]). *)
      assert (Xδ : Δc ⊢ˢ sb_of_list (ι (wk_shiftn n')) (nvars ++ avars ++ nil) : nil ++ con_inst_ctx Δ p D Mv Us'' gs)
        by (rewrite List.app_nil_r, con_inst_ctx_con_inst_tele; exact Xbase).
      pose proof (wf_sub_cod _ _ _ _ _ Xδ) as XΨ.
      pose proof (view_blocks_branch_argrec gc_deps gc_stack Δ p D m Mm qc kc Is vm D' Us'' Bks'' ak_relevant iA Xg (decls_of_ctx _ _ _ view_branch_Δ) Hl Hm Hh Hq Hvw view_branch_Δ
                    view_branch_HUl view_branch_HUs view_branch_HBt i' Mi' v Mv c gs' gs Hi' Hri' Hv HMv Hcon' Hcon Hcorr gs1 t gs2 nil nil l' Heq eq_refl
                    (List.nth_error_In _ _ Hl') XΨ Xδ) as XIH.
      destruct (view_blocks_branch_rec_arg gc_deps gc_stack Δ p D m Mm qc kc Is vm D' Us'' Bks'' ak_relevant Xg (decls_of_ctx _ _ _ view_branch_Δ) Hl Hm Hh Hq view_branch_Δ
                  view_branch_HUl view_branch_HUs Mi' v Mv c gs' gs HMv Hcon Hcorr gs1 t gs2 nil nil Heq eq_refl XΨ Xδ) as (Xσt & Xuc & XN).
      rewrite Eσ in XIH, Xσt, Xuc.
      rewrite view_branch_EUs', Eσ in XN.
      fold N in XIH, XN.
      (** The motives at the path's end, at [σw]. *)
      assert (Eβ : leaf_ihty ak_relevant (blocks_motives Bks'') (ι (wk_shiftn n')) σs N l'
                   = leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σw)) Id σs N l').
      { rewrite (leaf_ihty_sb_eq ak_relevant l' _ _ (ι (wk_shiftn n') ⨟ Id) _ _ N (fun z => eq_refl) (fun z => eq_refl)).
        apply leaf_ihty_base.
        pose proof (decl_closed_members _ Hc _ _ HMv) as HMc.
        pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
        destruct (member_closed_rec_len _ _ HMc _ _ Hin _ _ _ Heq) as (Mj & HMj & HlMj).
        assert (Hlp : List.Forall (leaf_params_length D) (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mv) t)).
        { rewrite pat_nargs_cargs_pat.
          replace (List.length (cargs_nonrec_ctx gs1) + im_nn Mv) with (pat_nargs nil + List.length (cargs_nonrec_ctx gs1) + im_nn Mv) by reflexivity.
          apply shape_leaves_params_length; [ exact (rview_leaves_params_length D Hc) | exists Mj; split; [ exact HMj | exact HlMj ] ]. }
        destruct (proj1 (List.Forall_forall _ _) Hlp _ (List.nth_error_In _ _ Hl')) as (Ml & HMl & HPll).
        rewrite HPll, !(blocks_motives_sub D Bks _ _ Ml Hnm HMl).
        symmetry; apply exp_sub_sub_ext, sb_qn_compose_ext; symmetry; apply sb_wk_compose. }
      rewrite Eβ in XIH.
      (** The type of the result is a type of a universe: so it is in the
          branch's context ([rec_ih_typed]), moved by the container's
          variables ([view_blocks_branch_ihty_view]). *)
      assert (HjT0 : exists jT, Δc ⊢ leaf_ihty ak_relevant (blocks_motives (blocks_sub Bks σw)) Id σs N l' : Typeω@jT).
      { pose proof (wf_sub_uparams _ _ _ Hdt Hc _ _ view_branch_Δ view_branch_HUl view_branch_HUs) as HσU.
        assert (HMe : forall j0 Mj0, ind_member D j0 = Some Mj0 -> ⊢ elim_mctx p D j0 Mj0 Us'' ++ Δ)
          by (intros jm Mjm Hjm; exact (ext_eq_ctx_left _ _ _ _ _ (blocks_typed_mctx _ _ _ _ _ _ _ _ _ view_branch_HBt jm Mjm Hjm))).
        pose proof (blocks_motives_typed _ _ _ _ _ _ _ _ _
                      (rview_struct_suffix gc_deps gc_stack D (decl_typed_record_struct gc_deps gc_stack D Hdt)) view_branch_HBt) as HAm.
        destruct (rec_ih_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nil l' Xg (decls_of_ctx _ _ _ view_branch_Δ) Hl HMv view_branch_Δ
                    view_branch_HUl HσU HMe HAm HAm (fun j0 Mj0 Hj0 Hr0 => wf_exp_eq_refl (HAm j0 Mj0 Hj0 Hr0)) motive_kind_relevant
                    (cons_lookup_in _ _ _ Hcon) Heq (List.nth_error_In _ _ Hl') XΨ) as (jT & HT0 & _).
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ HT0 Xδ) as H.
        pose proof (view_blocks_branch_ihty_view D vm D' Us'' ak_relevant view_branch_HUl Mv gs' gs Hcorr (blocks_motives Bks'')
                      gs1 t gs2 nil nil l' Heq eq_refl) as E1.
        cbv beta in E1, H; rewrite E1, Eσ in H; fold N in H; rewrite Eβ in H.
        exists jT; exact H. }
      destruct HjT0 as [jT HjT].
      (** The level of the result, above the motives', [nb] and the type's. *)
      set (J := Nat.max (Nat.max iA nb) (Nat.max lv jT)).
      pose proof (per_univ_elem_cumu_ge lv J _ _ _ ltac:(unfold J; lia) HRa) as HRaJ.
      destruct (per_univ_glu_univ_elem J a (ex_intro _ Rv HRaJ)) as (PJ & ElJ & HgJ).
      pose proof (lift_exp_ge _ _ _ _ jT J ltac:(unfold J; lia) HjT) as HjJ.
      (** The path, at the offset of the components. *)
      assert (Hls : List.length (cargs_nonrec_ctx gs1) = List.length (cargs_nonrec gs1))
        by (rewrite Completeness.Inductives.Model.cargs_nonrec_ctx_rev_tele, List.length_rev, ?List.length_map, ?length_cargs_nonrec_tele;
            reflexivity).
      assert (Hl'' : List.nth_error (shape_leaves (rview_leaves D) (im_nn Mv + List.length (cargs_nonrec gs1) + 0) t) idx = Some l')
        by (rewrite <- Hls, Nat.add_0_r, Nat.add_comm, <- pat_nargs_cargs_pat; exact Hl').
      assert (Hok' : elim_readback_ok (leaf_mem l')).
      { pose proof (shape_leaves_mem_offset (rview_leaves D) t 0 (pat_nargs (cargs_pat gs1) + im_nn Mv)) as Em.
        assert (E1 : List.nth_error (List.map leaf_mem (shape_leaves (rview_leaves D) 0 t)) idx = Some (leaf_mem l))
          by (rewrite List.nth_error_map, Hln; reflexivity).
        rewrite Em, List.nth_error_map, Hl' in E1; injection E1 as ->.
        exact (Hok gs1' g' gs2' gs1 t gs2 l Heq' Heq Hlen (List.nth_error_In _ _ Hln) Hnin). }
      assert (Hctx : elim_arg_context v Mv ns c gs1 t gs2 nv 0 nil (ns ++ nv) (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1)
                       t σw Δc (List.map (fun U => U[σw]) Us))
        by (constructor; first [ exact HMv | rewrite <- Heq; exact Hcon | rewrite List.app_nil_r; reflexivity
                               | cbn [List.firstn]; rewrite !List.app_nil_r; reflexivity | exact Hns | exact Xpfx
                               | reflexivity | lia | exact (tele_prefix_rel_nil _) | exact Hσw ]).
      assert (Xuc' : shape_uc D Us (arg_shape_ctx Mv gs1 t 0) σs σw).
      { intros y Hy; unfold arg_shape_ctx; cbn [List.firstn]; rewrite (Xuc y Hy); cbn [sb_compose].
        rewrite <- !sentry_exp_sub.
        destruct (nth_error_lt_some Us y ltac:(lia)) as [U HU].
        rewrite !(sb_of_list_nth _ _ y a_prop) by (rewrite ?List.length_map; lia).
        cbn [sentry_exp]; rewrite List.length_map.
        pose proof (nth_error_lt_length _ _ _ HU) as Hy'.
        rewrite (List.nth_indep _ a_prop (a_prop[σ''])) by (rewrite List.length_map; lia).
        rewrite (List.map_nth (fun U0 => U0[σ''])), exp_sub_sub; apply exp_sub_sb_eq; symmetry; apply sb_wk_compose. }
      pose proof (Hrp Mv ns c gs1 t gs2 nv 0 nil σw Hctx σs N rs Xσt (wf_sub_eq_refl _ _ _ _ _ Xσt) Xuc'
                    ltac:(apply wf_exp_eq_refl; exact XN) Hsh Ers idx l' r a J Rv PJ ElJ Hl'' Hok' Hr Hlty HRaJ Hrr
                    ltac:(unfold J; lia) ltac:(unfold J; lia) HgJ HjJ) as HMg.
      (** At the entry's type. *)
      rewrite Eσ, view_branch_EUs, view_branch_EB.
      exact (glu_elem_retype _ _ _ _ _ _ _ _ _ _ _ _ HgJ Hg (glu_univ_elem_trm_typ _ _ _ _ HgJ _ _ _ _ HMg) HMg HTP).
    Qed.

    (** The container's recursive results of the constructor's arguments
        are the paths of the group's of them that are the container's. *)
    Lemma view_branch_container_count : cargs_container_count D D' gs' gs = cargs_nrec D' gs'.
    Proof.
      pose proof (valid_groups_containers VP HVP p D m Mm qc kc Is vm D' HPD Hm Hh Hq) as HPq.
      pose proof (valid_group_typed _ _ (valid_groups_valid VP HVP qc D' HPq)) as HdtQ.
      assert (Hvm : forall j' j, List.nth_error vm j' = Some j ->
                exists Mj' Mj, ind_member D' j' = Some Mj' /\ Semantic.Inductives.ViewCoherence.view_member p D qc D' vm j' Mj' j Mj).
      { intros j' j Hvj.
        assert (Hj : j' < List.length (ind_members D')) by (rewrite <- (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; congruence).
        destruct (nth_error_lt_some' _ _ Hj) as [Mj' HMj'].
        destruct (Semantic.Inductives.ViewCount.view_agree_members p D m Mm qc kc Is vm D' Hass Hm Hh Hq j' Mj' HMj')
          as (v1 & Mv1 & Hvm1).
        pose proof (Semantic.Inductives.ViewCoherence.view_member_v _ _ _ _ _ _ _ _ _ Hvm1) as Hv1; rewrite Hvj in Hv1; injection Hv1 as <-.
        exists Mj', Mv1; split; [ exact HMj' | exact Hvm1 ]. }
      exact (Semantic.Inductives.ViewCount.cargs_container_count_view p qc D D' vm Hco
               (leaves_coherent_of_order D' (rview_struct_order _ _ D' (decl_typed_record_struct _ _ _ HdtQ)))
               (group_structure_record_struct _ Hass) (decl_typed_record_struct _ _ _ HdtQ) Hvm gs' gs Hcorr).
    Qed.

    (** A parameter or an argument of the branch's context: its fresh
        variable, glued at a type related to the entry's. *)
    Lemma view_branch_prefix_entry : forall kk M T w κ A a (i : nat) P El, kk < im_nn Mv + List.length gs ->
        List.nth_error Ms kk = Some M -> List.nth_error (tele_insts C σw Ms) kk = Some T ->
        List.nth_error (ns ++ vs ++ wihs) kk = Some w -> List.nth_error (List.rev C) kk = Some (ce_ass κ A) ->
        ⟦ A ⟧ env_tele ρ (List.rev C) (List.firstn kk (ns ++ vs ++ wihs)) ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δc ⊢ T ® P ->
        Δc ⊢ M : T ® w ∈ El.
    Proof.
      intros kk M T w κ A a i P El Hk HMk HT Hw HA Ea Hg HTP.
      pose proof view_branch_na as Xna.
      pose proof view_branch_lenc as Xlc.
      pose proof (view_branch_typed kk M T HMk HT) as HMt.
      destruct (bctx_link_gen v Mv c gs HMv Hcon view_branch_rv (length Δ) ns vs wihs hd k0 pre Fn Fc Lpre HGm Hir kk κ A a HA Ea)
        as [(_ & b' & n0 & Hw' & Hab) | E]; [| exfalso; destruct E; lia ].
      rewrite Hw in Hw'; injection Hw' as ->.
      assert (EM : M = a_var (n' - 1 - kk)).
      { destruct (Nat.lt_ge_cases kk (im_nn Mv)) as [Hlt | Hge].
        - rewrite List.nth_error_app1 in HMk by (rewrite length_vars_from; lia).
          apply vars_from_nth_error in HMk as [_ ->]; f_equal; lia.
        - rewrite List.nth_error_app2, List.nth_error_app1 in HMk by (rewrite !length_vars_from; lia).
          apply vars_from_nth_error in HMk as [_ ->]; rewrite length_vars_from; f_equal; lia. }
      subst M.
      pose proof (var_glu_elem_per i a b' n0 P El Δc T _ Hg (glu_var_typ_not_level_sort _ _ _ _ _ _ _ Hg HTP HMt) HTP HMt
                    ltac:(rewrite Xlc; lia) Hab) as H.
      replace (length Δc - 1 - (n' - 1 - kk)) with (length Δ + kk) in H by (rewrite Xlc; lia).
      exact H.
    Qed.

    (** The parameters and the arguments, glued along their telescope
        ([glu_args]): what the recursive results nested through use of
        the argument they are at. *)
    Lemma view_branch_prefix_args : forall SbB, EG C ++ Γ ∈ glu_ctx_env ↘ SbB ->
        glu_args Δc (tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) (sb_of_list Id Us)) σw ρ (nvars ++ avars) (ns ++ vs).
    Proof.
      intros SbB HSbB.
      pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
      pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
      pose proof view_branch_na as Xna.
      set (IC := ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs).
      set (con_inst_tele := tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) (sb_of_list Id Us)).
      assert (EC : C = IC ++ con_inst_tele) by (unfold IC, con_inst_tele, elim_bctx; rewrite tele_sub_app, length_im_nparams; reflexivity).
      assert (HassT : all_assumptions con_inst_tele)
        by (apply all_assumptions_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_nparams_ass D Hc _ _ HMv) ]).
      assert (Lctel : List.length con_inst_tele = (im_nn Mv + List.length gs)%nat)
        by (unfold con_inst_tele; rewrite length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams; lia).
      assert (LNA : List.length (nvars ++ avars) = List.length con_inst_tele) by (rewrite List.length_app, !length_vars_from, Lctel; lia).
      pose proof HSbB as HSbB'; rewrite EC, <- List.app_assoc in HSbB'.
      destruct (glu_ctx_env_suffix IC _ _ (ihs_ctx_aux_ass _ _ _ _ _ _ _ _ _) HSbB') as [Sb' HSb'].
      eapply glu_args_by; [ exact HassT | exact HSb' | exact HSbΓ | exact view_branch_σw | exact LNA | rewrite List.length_app; lia |].
      intros kk M T w κ A a i P El HMk HT Hw HA Ea Hg HTP.
      assert (Hk : kk < im_nn Mv + List.length gs)
        by (rewrite <- Lctel, <- List.length_rev; apply List.nth_error_Some; congruence).
      apply (view_branch_prefix_entry kk M T w κ A a i P El Hk); [ | | | | | exact Hg | exact HTP ].
      - rewrite List.app_assoc, List.nth_error_app1 by lia; exact HMk.
      - rewrite EC, List.app_assoc, tele_insts_app by first [ exact HassT | exact LNA ].
        rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact HassT; lia); exact HT.
      - rewrite List.app_assoc, List.nth_error_app1 by (rewrite List.length_app; lia); exact Hw.
      - rewrite EC, List.rev_app_distr, List.nth_error_app1 by (rewrite List.length_rev; lia); exact HA.
      - rewrite EC, List.rev_app_distr, env_tele_app_long
          by (rewrite List.length_firstn, List.length_rev, !List.length_app; lia).
        rewrite List.app_assoc, firstn_app_le by (rewrite List.length_app; lia); exact Ea.
    Qed.
    Check TEMP_STOP_PORT.

    (** The substitution of the wrapped branch, glued at the environment the
        readback evaluates the view's branch in: the parameters and the
        arguments are the fresh variables, the recursive results the
        container's variables or the eliminator at the argument
        ([view_branch_nested]). *)
    Lemma view_branch_glu_sub : forall SbB, EG C ++ Γ ∈ glu_ctx_env ↘ SbB ->
        Δc ⊢ˢ sb_of_list σw Ms ® env_args ρ (ns ++ vs ++ wihs) ∈ SbB.
    Proof.
      intros SbB HSbB.
      pose proof (view_branch_prefix_args SbB HSbB) as Hpre.
      pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
      pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
      destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
      pose proof view_branch_na as Xna.
      pose proof view_branch_lenc as Xlc.
      eapply glu_sub_of_list_by; [ exact (elim_bctx_ass p D v Mv gs (blocks_motives Bks) Us Hc HMv) | exact HSbB | exact HSbΓ | exact view_branch_σw
                                 | exact view_branch_len | rewrite length_elim_bctx, !List.length_app; lia |].
      intros kk M T w A a i P El HMk HT Hw HA Ea Hg HTP.
      destruct (Nat.lt_ge_cases kk (im_nn Mv + List.length gs)) as [Hk | Hk];
        [ exact (view_branch_prefix_entry kk M T w A a i P El Hk HMk HT Hw HA Ea Hg HTP) |].
      pose proof (view_branch_typed kk M T HMk HT) as HMt.
      destruct (bctx_link_gen v Mv c gs HMv Hcon view_branch_rv (length Δ) ns vs wihs hd k0 pre Fn Fc Lpre HGm Hir kk A a HA Ea)
        as [[Hk' _] | [gs1 t gs2 idx v' lv Rv x Heq Hidx -> Hv' Hshv Hdv Hlty Hx HRa Hxx]]; [ lia |].
      (** A recursive result: the one along the leaf path [idx] of the
          recursive argument after [gs1]. *)
      set (j := (cargs_nrec D gs1 + idx)%nat) in *.
      assert (Lg1 : List.length gs1 < List.length gs') by (rewrite Xna, Heq, List.length_app; cbn; lia).
      rewrite List.app_assoc, List.nth_error_app2 in Hw by (rewrite List.length_app; lia).
      rewrite List.length_app, Ln, Lv, Nat.add_comm, Nat.add_sub in Hw.
      rewrite Hx in Hw; injection Hw as <-.
      rewrite List.app_assoc, List.nth_error_app2 in HMk by (rewrite List.length_app, !length_vars_from; lia).
      rewrite List.length_app, !length_vars_from in HMk.
      replace (im_nn Mv + List.length gs + j - (im_nn Mv + List.length gs')) with j in HMk by lia.
      destruct (nth_error_lt_some gs' (List.length gs1) Lg1) as [g' Hg'].
      destruct (List.nth_error_split gs' (List.length gs1) Hg') as (gs1' & gs2' & Egs' & Hl1).
      assert (Hcorr' : cargs_correspond vm (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2)) by (rewrite <- Egs', <- Heq; exact Hcorr).
      (** The leaf path, at the components' offset too. *)
      destruct (nth_error_lt_some (shape_leaves (rview_leaves D) 0 t) idx Hidx) as [l Hln].
      destruct (nth_error_lt_some (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mv) t) idx) as [l' Hl'].
      { rewrite (length_shape_leaves _ _ _ 0); exact Hidx. }
      assert (Hls : List.length (cargs_nonrec_ctx gs1) = List.length (cargs_nonrec gs1))
        by (rewrite Completeness.Inductives.Model.cargs_nonrec_ctx_rev_tele, List.length_rev, ?List.length_map, ?length_cargs_nonrec_tele;
            reflexivity).
      assert (Hl'' : List.nth_error (shape_leaves (rview_leaves D) (im_nn Mv + List.length (cargs_nonrec gs1)) t) idx = Some l')
        by (rewrite <- Hls, Nat.add_comm, <- pat_nargs_cargs_pat; exact Hl').
      (** The term and the value at the entry. *)
      assert (LIhs : List.length Ihs = cargs_nrec D (gs1 ++ ca_rec t :: gs2))
        by (rewrite <- Heq; apply length_elim_ihs; rewrite length_vars_from; exact Xna).
      pose proof (wrap_ihs_nth D' D vm gs1' g' gs2' gs1 t gs2 Ihs 0 (cargs_nrec D' gs') idx l Hl1 Hcorr' LIhs Hln) as EW.
      rewrite <- Egs', <- Heq in EW; fold j in EW.
      rewrite EW in HMk.
      assert (Wi' : ⟦wihs vs of (gs1' ++ g' :: gs2') (gs1 ++ ca_rec t :: gs2) of D' with ihs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ wihs)
        by (rewrite <- Egs', <- Heq; exact Wi).
      destruct (wrapped_ihs_nth ρ p ups Bks D' D Hl Hco gs1' g' gs2' gs1 t gs2 vs ihs wihs Hl1 Wi' v' idx l Hv' Hln) as (rs & Ers & Hwj).
      fold j in Hwj; rewrite Hx in Hwj.
      assert (HN : List.nth_error avars (List.length gs1) = Some (a_var (cargs_nrec D' gs' + (List.length gs' - 1 - List.length gs1)))).
      { rewrite <- (vars_from_nth (cargs_nrec D' gs') (List.length gs') (List.length gs' - 1 - List.length gs1) (a_var 0)) by lia.
        replace (List.length gs' - 1 - (List.length gs' - 1 - List.length gs1)) with (List.length gs1) by lia.
        apply List.nth_error_nth'; rewrite length_vars_from; lia. }
      pose proof (elim_ihs_nth p D (Some p) Usw (blocks_wk Bks'' (wk_shiftn n')) σ0 (im_nn Mv) gs gs1 t gs2 avars _ idx l' Heq
                    ltac:(rewrite length_vars_from; exact Xna) HN Hl'') as EI.
      fold j in EI.
      destruct g' as [A' | t'].
      - (** Recursive in the view only: nested through. *)
        rewrite EI in HMk; injection HMk as <-.
        exact (view_branch_nested gs1' (ca_arg A') gs2' gs1 t gs2 idx l l' v' rs x a lv Rv i P El T Egs' Heq Hl1 Hln
                 (fun t1 E => ltac:(discriminate E)) Hl' Hv' Ers (eq_sym Hwj) Hlty HRa Hxx Hg HTP Hpre).
      - destruct (leaf_in D' t' l) eqn:Hin.
        + (** A path of the container's: its variable. *)
          injection HMk as <-.
          assert (Fi' : Fihs vs at (gs1' ++ ca_rec t' :: gs2') (gs1 ++ ca_rec t :: gs2) of D' under ρ (blocks_motives Bks) at p ups
                          in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns) ⍮ (length Δ + im_nn Mv + List.length gs') ↘ ihs)
            by (rewrite <- Egs', <- Heq; exact Fi).
          destruct (fresh_ihs_nth ρ (blocks_motives Bks) p ups D' D Hl gs1' t' gs2' gs1 t gs2 _ vs _ ihs Hl1 Fi' v' idx l Hv' Hln Hin)
            as (as' & b0 & Eas & Hb0 & Hih).
          rewrite Hih in Hwj; injection Hwj as ->.
          rewrite <- env_args_app, <- List.app_assoc in Eas.
          assert (Hnv : is_neut v').
          { destruct (fresh_cargs_nth _ _ _ _ _ _ Fc gs1 (ca_rec t) gs2 Heq) as [_ Fr].
            destruct (Fr t eq_refl) as (a0 & _ & Hv0); rewrite Hv' in Hv0; injection Hv0 as ->.
            exists a0, (d_var (length Δ + im_nn Mv + List.length gs1)); reflexivity. }
          destruct (leaf_ihty_link _ _ _ _ _ Hlty v (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                      ltac:(rewrite List.app_assoc; reflexivity) Hidx Hshv Hnv Hdv lv Rv HRa as' Eas) as (b1 & Hb1 & Hab).
          rewrite Hb0 in Hb1; injection Hb1 as <-.
          (** The variable's position, below the container's recursive
              results. *)
          pose proof (fresh_ihs_length _ _ _ _ _ _ _ _ _ _ _ _ Hl Fi) as LFi.
          rewrite view_branch_container_count in LFi.
          pose proof (nth_error_lt_length _ _ _ Hih) as Hpos; rewrite LFi in Hpos.
          pose proof (var_glu_elem_per i a b0 lv P El Δc T _ Hg HTP HMt ltac:(rewrite Xlc; lia) Hab) as H.
          replace (length Δc - 1 - (cargs_nrec D' gs' - 1 - (cargs_container_count D D' gs1' gs1
                                     + leaves_in_count D' t' (List.firstn idx (shape_leaves (rview_leaves D) 0 t)))))
            with (length Δ + im_nn Mv + List.length gs' + (cargs_container_count D D' gs1' gs1
                                     + leaves_in_count D' t' (List.firstn idx (shape_leaves (rview_leaves D) 0 t)))) in H
            by (rewrite Xlc; lia).
          exact H.
        + (** A path not the container's: nested through. *)
          rewrite EI in HMk; injection HMk as <-.
          exact (view_branch_nested gs1' (ca_rec t') gs2' gs1 t gs2 idx l l' v' rs x a lv Rv i P El T Egs' Heq Hl1 Hln
                   (fun t1 E => ltac:(injection E as <-; exact Hin)) Hl' Hv' Ers (eq_sym Hwj) Hlty HRa Hxx Hg HTP Hpre).
    Qed.

    (** The wrapped branch, against its readback: glued at its type's value
        at the substitution's environment ([view_branch_glu_sub]), read back there,
        at the container's branch type ([view_branch_type_conv]). *)
    Lemma readback_branch_view : forall n B bv t0 Bn, brs_lookup (eb_brs b) c = Some (n, B) -> im_ref p v Mv = (hd, k0) ->
        ⟦ B ⟧ env_args ρ (ns ++ vs ++ wihs) ↘ bv ->
        ⟦ eb_motive b ⟧ env_args ρ (ns ++ d_con hd k0 c (pre ++ ns ++ vs) :: nil) ↘ t0 ->
        Rnf ⇓ t0 bv in gc_deps ⍮ gc_stack ⍮ (length Δ + (im_nn Mi' + List.length gs' + cargs_nrec D' gs')) ↘ Bn ->
        Δc ⊢ snd (wrap_branch p D D' Us'' Bks'' Mv (eb_brs (eblock_sub b σ'')) c gs') ≈ Bn
          : elim_branch_type qc D' i' Mi' c gs' (eb_motive (eblock_sub b σ'')) Is''.
    Proof.
      intros n B bv t0 Bn Hlk Href Ebv Et0 HRn.
      pose proof (brs_lookup_in _ _ _ _ Hlk) as HinB.
      pose proof (Har _ _ _ _ _ _ _ HMv Hb Hcon HinB) as Hn.
      pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
      pose proof (fresh_cargs_length _ _ _ _ _ _ Fc) as Lv.
      destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
      pose proof view_branch_na as Xna.
      assert (XLM : List.length Ms = (im_nn Mv + List.length gs + cargs_nrec D gs)%nat)
        by (pose proof view_branch_len as XL; rewrite length_elim_bctx in XL; lia).
      (** The branch, glued and read back. *)
      destruct (glu_blocks_branch _ _ _ _ _ _ HBg _ _ _ _ _ _ _ HMv Hb Hcon HinB) as [SbB HSbB lvl Hbody].
      destruct (Hbody _ _ _ (view_branch_glu_sub SbB HSbB)) as [eb rb Pb Elb Eeb Erb Hgb HBgl].
      assert (rb = bv) as -> by (eapply functional_eval_exp; eassumption).
      destruct view_branch_rel as (Hns & _ & _).
      assert (Lbs : List.length (pre ++ ns) = (im_unu D Mv + im_nn Mv)%nat) by (rewrite List.length_app; lia).
      assert (HG' : G v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                      (d_con hd k0 c ((pre ++ ns) ++ vs)) (d_con hd k0 c ((pre ++ ns) ++ vs)))
        by (rewrite skipn_app_exact by exact Lpre; exact HGm).
      assert (Hir' : rec_results_rel D dr Rel v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                       gs vs vs wihs wihs)
        by (rewrite skipn_app_exact by exact Lpre; exact Hir).
      assert (Eeb' : ⟦ elim_branch_type p D v Mv c gs (eb_motive b) Us ⟧ env_args ρ (List.skipn (im_unu D Mv) (pre ++ ns) ++ vs ++ wihs) ↘ eb)
        by (rewrite skipn_app_exact by exact Lpre; exact Eeb).
      rewrite List.app_assoc in Et0.
      assert (Hns' : tele_rel (nr v) (List.rev (im_nparams Mv)) ns (List.skipn (im_unu D Mv) (pre ++ ns)))
        by (rewrite skipn_app_exact by exact Lpre; exact Hns).
      pose proof (branch_type_val_rel v Mv c gs b HMv Hcon view_branch_rv Hb hd k0 (pre ++ ns) vs wihs ns eb t0 Href Lbs HG' Hir' Hns' Eeb' Et0) as Hrel.
      pose proof (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HBgl) as HTP.
      destruct (glu_transfer_per lvl iA eb t0 Pb Elb _ _ _ bv Hgb Hrel HTP HBgl) as (k' & P' & El' & Hg' & HP' & HM').
      destruct (realize_glu_elem_top _ _ _ _ Hg' _ _ _ _ HM') as [? ? _ _ _ _ Hrbs].
      rewrite <- view_branch_nn in HRn.
      replace (length Δ + n')%nat with (length Δc) in HRn by exact view_branch_lenc.
      pose proof (Hrbs _ wk_id _ (kripke_id _ view_branch_ctx) HRn) as H.
      rewrite !exp_wk_id in H.
      (** The substitution of the wrapped branch. *)
      assert (Esb : sb_eq (sb_qn (List.length Ms) σ'' ⨟ sb_of_list (ι (wk_shiftn n')) Ms) (sb_of_list σw Ms))
        by (etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong; symmetry; apply sb_wk_compose ]).
      assert (ELHS : snd (wrap_branch p D D' Us'' Bks'' Mv (eb_brs (eblock_sub b σ'')) c gs') = B[sb_of_list σw Ms]).
      { unfold wrap_branch; cbv zeta; rewrite Hcon, Completeness.Inductives.Elim.eb_brs_sub, brs_lookup_sub, Hlk; cbn [option_map fst snd].
        rewrite exp_sub_sub, Hn, <- XLM; apply exp_sub_sb_eq; exact Esb. }
      (** Its type, the container's. *)
      assert (Hb'' : List.nth_error Bks'' v = Some (eblock_sub b σ'')) by (rewrite nth_error_blocks_sub, Hb; reflexivity).
      pose proof (view_branch_type_conv Δ p D m Mm qc kc Is vm D' Us'' Bks'' iA (ctx_wf_gctx _ _ _ view_branch_Δ) (decls_of_ctx _ _ _ view_branch_Δ)
                    Hl Hm Hh Hq Hvw view_branch_Δ view_branch_HUl view_branch_HUs view_branch_HBt i' Mi' v Mv c gs' gs (eblock_sub b σ'') W
                    Hi' Hri' Hv HMv Hcon' Hcon Hcorr Hb''
                    (length_wrap_ihs _ _ _ _ _ _ _ _ Hcorr ltac:(apply length_elim_ihs; rewrite length_vars_from; exact Xna))) as Hty.
      assert (ETy : (elim_branch_type p D v Mv c gs (eb_motive (eblock_sub b σ'')) Us'')[sb_of_list (ι (wk_shiftn n')) Ms]
                    = (elim_branch_type p D v Mv c gs (eb_motive b) Us)[sb_of_list σw Ms]).
      { rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMv Hb).
        rewrite <- (elim_branch_type_sub p D v Mv c gs (eb_motive b) Us σ'' Hc HMv HUl).
        rewrite exp_sub_sub, <- XLM; apply exp_sub_sb_eq; exact Esb. }
      rewrite ETy in Hty.
      destruct (presup_exp_eq Hty) as (_ & _ & HT2 & _).
      rewrite ELHS; exact (wf_exp_eq_conv _ _ _ _ _ _ _ _ H HT2 Hty).
    Qed.
  End ViewBranch.

  (** A block of the readback of a stuck eliminator at a view [vm] of the
      container's group [D'], against the container's block of the
      wrapped blocks at [σ''] ([view_wrap]): the same count and names, and
      equal motives and branches. *)
  Lemma view_block_rb : forall m Mm qc kc Is vm D', ind_member D m = Some Mm -> im_head Mm = mh_view qc kc Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> view_wrap_ok D D' vm ->
      (forall i' Mi' v Mv c gs' gs gs1' g' gs2' gs1 t gs2 l, ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v ->
         ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
         gs' = gs1' ++ g' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
         In l (shape_leaves (rview_leaves D) 0 t) -> (forall t', g' = ca_rec t' -> leaf_in D' t' l = false) ->
         elim_readback_ok (leaf_mem l)) ->
      forall Δ σ'' NBks, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      Rblks 0 (ind_block_members D') of D' from p ups Bks (Some vm) in gc_deps ⍮ gc_stack ⍮ ρ ⍮ length Δ ↘ NBks ->
      forall k Mk b b', ind_member D' k = Some Mk ->
        List.nth_error (view_wrap p D D' vm (List.map (fun U => U[σ'']) Us) (blocks_sub Bks σ'')) k = Some b ->
        List.nth_error (List.map block_exp NBks) k = Some b' ->
        eb_binder_count b' = S (im_nn Mk) /\ eb_ann b' = None /\
        elim_mctx qc D' k Mk (List.map (fun I => I[sb_of_list Id (List.map (fun U => U[σ'']) Us)]) Is) ++ Δ
          ⊢ eb_motive b ≈ eb_motive b' : Typeω@iA /\
        List.map fst (eb_brs b) = List.map fst (eb_brs b') /\
        forall i c n B B' gs, List.nth_error (eb_brs b) i = Some (c, n, B) -> List.nth_error (eb_brs b') i = Some (c, n, B') ->
          ind_con Mk c = Some gs ->
          elim_bctx qc D' Mk gs (blocks_motives (view_wrap p D D' vm (List.map (fun U => U[σ'']) Us) (blocks_sub Bks σ'')))
                    (List.map (fun I => I[sb_of_list Id (List.map (fun U => U[σ'']) Us)]) Is) ++ Δ
            ⊢ B ≈ B' : elim_branch_type qc D' k Mk c gs (eb_motive b) (List.map (fun I => I[sb_of_list Id (List.map (fun U => U[σ'']) Us)]) Is).
  Proof.
    intros m Mm qc kc Is vm D' HMm Hh Hq Hvw Hok Δ σ'' NBks Hσ'' HR k Mk b b' HMk Hb Hb'.
    destruct (read_blocks_nth _ _ _ _ _ _ HR) as [_ HRn].
    destruct (HRn k b' Hb') as (Mi & Mv & b0 & hd & k0 & pre & ns & a & A' & Bs' & HMi & HMv & Hb0 & Hnm0 & Er & Fn & Ea & HRA & HRB & ->).
    cbn [Nat.add] in *.
    destruct (ind_block_members_member _ _ _ HMi) as [HMi' Hkb].
    assert (Mi = Mk) as -> by congruence.
    (** The container's member has a block: it is no record view. *)
    pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ (decls_of_ctx _ _ _ (view_branch_Δ Δ σ'' Hσ'') _ _ Hq))) as Hsuf.
    assert (Hrk : im_is_rview Mk = false).
    { destruct (im_is_rview Mk) eqn:Er0; [| reflexivity ].
      apply (Hsuf _ _ HMk) in Er0; lia. }
    destruct (nth_error_lt_some vm k) as [v Hv]; [ rewrite (view_wrap_ok_length _ _ _ Hvw); exact (ind_member_lt _ _ _ HMk) |].
    assert (Hsrc : elim_src (Some vm) k = v) by (cbn; apply List.nth_error_nth; exact Hv).
    rewrite Hsrc in HMv, Hb0, Er.
    destruct (view_wrap_ok_members _ _ _ Hvw k Mk v HMk Hv) as (Mv' & HMv' & Hnn & Hnames & Hcorr).
    rewrite HMv in HMv'; injection HMv' as <-.
    assert (Hb0'' : List.nth_error (blocks_sub Bks σ'') v = Some (eblock_sub b0 σ'')) by (rewrite nth_error_blocks_sub, Hb0; reflexivity).
    rewrite (nth_error_view_wrap _ _ _ _ _ _ _ _ Hsuf HMk Hrk) in Hb; injection Hb as <-.
    rewrite (view_wrap_block_eq _ _ _ _ _ _ _ _ _ _ _ Hv Hb0'' HMv).
    cbn [eb_binder_count eb_ann eb_motive eb_brs].
    rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMv Hb0).
    destruct (read_brs_nth _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl HRB) as (LB1 & LB2 & HBn).
    pose proof (decls_of_ctx _ _ _ (view_branch_Δ Δ σ'' Hσ'')) as XDs.
    pose proof (decl_typed_nodup _ _ _ (XDs _ _ Hq)) as Hnd'.
    split; [ reflexivity | split; [ reflexivity | split ] ].
    - (** The motives, in the container's member's context. *)
      rewrite <- Hnn in Ea, HRA.
      pose proof (readback_motive v Mv b0 HMv Hb0 Δ σ'' hd k0 pre ns a A' Hσ'' Er Fn Ea HRA) as H.
      pose proof (view_mctx_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ (view_branch_Δ Δ σ'' Hσ'')) XDs Hl HMm Hh Hq HMk Hrk Hv HMv
                    (view_branch_Δ Δ σ'' Hσ'') (view_branch_HUl σ'') (view_branch_HUs Δ σ'' Hσ'')) as Hx.
      pose proof (ctxsub_ext _ _ _ _ _ Hx (elim_mctx_ass _ _ _ _ _ Hc HMv)) as Hs.
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H Hs) as H'.
      rewrite !exp_sub_id in H'; exact H'.
    - split.
      + (** The names and counts. *)
        apply List.nth_error_ext; intros idx; rewrite !List.nth_error_map, <- (List.nth_error_map branch_exp).
        destruct (List.nth_error (List.map branch_exp Bs') idx) as [[[c1 n1] B1] |] eqn:E1.
        * destruct (HBn idx c1 n1 B1 E1) as [gs' gs n0 B0 ns' vs ihs wihs bv t Bn HB0 Hcs _ _ En _ _ _ _ _ _ _ _ _].
          rewrite Hcs; cbn; rewrite En, Hnn; reflexivity.
        * rewrite (proj2 (List.nth_error_None (im_cons Mk) idx)); [ reflexivity |].
          apply List.nth_error_None in E1; lia.
      + (** A branch, by the fresh variables the PER model has. *)
        intros i c n B B' gs HBi HBi' Hcn.
        rewrite List.nth_error_map in HBi.
        destruct (List.nth_error (im_cons Mk) i) as [[c0 gs0] |] eqn:Hci; cbn in HBi; [| discriminate ].
        destruct (HBn i c n B' HBi') as [gs' gsv n0 B0 ns' vs ihs wihs bv t Bn HB0 Hcs Hcnv En0 En
                                         Hpl Fn' Fc Fi Wi Ebv Et Rn ->].
        rewrite Hci in Hcs; injection Hcs as <- <-.
        assert (Hcn' : ind_con Mk c0 = Some gs0) by (exact (cons_lookup_nodup_in _ _ _ (Hnd' _ _ HMk) (List.nth_error_In _ _ Hci))).
        assert (Ewb : wrap_branch p D D' (List.map (fun U => U[σ'']) Us) (blocks_sub Bks σ'') Mv (eb_brs (eblock_sub b0 σ'')) c0 gs0
                      = (c0, (im_nn Mv + List.length gs0 + cargs_nrec D' gs0)%nat,
                         snd (wrap_branch p D D' (List.map (fun U => U[σ'']) Us) (blocks_sub Bks σ'') Mv (eb_brs (eblock_sub b0 σ'')) c0 gs0)))
          by reflexivity.
        rewrite Ewb in HBi; injection HBi as <- <-.
        rewrite Hcn in Hcn'; injection Hcn' as <-.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fn Fn') as <-.
        (** The PER model's fresh variables are the readback's. *)
        destruct (view_member_pair (length Δ) m Mm qc kc Is vm D' k Mk HMm Hh Hq HMk Hrk)
          as [Mv2 HMv2 _ Hnn2 hd1 k1 pre1 pre2 R1 R2 Lp1 Lp2 nsa nsb Fa Fb Hneut Hnames2 Hbrs].
        rewrite Hsrc in HMv2, R1, R2; rewrite HMv in HMv2; injection HMv2 as <-.
        pose proof (functional_eval_mref _ _ _ _ _ R1 Er) as E1; injection E1 as -> -> ->.
        pose proof (functional_eval_mref _ _ _ _ _ R2 Er) as E2; injection E2 as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fa Fn) as ->.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fb Fn) as ->.
        destruct (Hbrs c0 gs (List.nth_error_In _ _ Hci)) as (gs1 & Hcn1 & _ & _ & _ & BP).
        rewrite Hsrc in BP; rewrite Hcnv in Hcn1; injection Hcn1 as <-.
        destruct BP as [vsa vsb ihsa ihsb wa wb Fa' Fb' Ia Ib Wa Wb Hrel Hrecs].
        pose proof (functional_fresh_cargs _ _ _ _ _ _ Fa' _ Fc) as ->.
        pose proof (functional_fresh_cargs _ _ _ _ _ _ Fb' _ Fc) as ->.
        pose proof (functional_fresh_ihs _ _ _ _ _ _ _ _ _ _ _ Ia _ Fi) as ->.
        pose proof (functional_fresh_ihs _ _ _ _ _ _ _ _ _ _ _ Ib _ Fi) as ->.
        pose proof (functional_wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ Wa _ Wi) as ->.
        pose proof (functional_wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ Wb _ Wi) as ->.
        rewrite !List.app_assoc in Hrel.
        destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D v Mv ups hd k0 pre Hl HMv ups_len Er) as [Href Lpre].
        rewrite <- Hnn in Fc, Fi.
        (** The view's branch, looked up by name. *)
        assert (HndB : List.NoDup (List.map (fun b1 => fst (fst b1)) (eb_brs b0)))
          by (rewrite <- (Hna _ _ _ HMv Hb0); exact (Hnd _ _ HMv)).
        pose proof (brs_lookup_of_nth _ _ _ _ _ HndB HB0) as Hlk.
        pose proof (Hcorr c0 gs gsv (List.nth_error_In _ _ Hci) Hcnv) as Hcr.
        rewrite Hnn in Rn.
        rewrite <- (Hnm _ _ _ HMv Hb0), <- Completeness.Inductives.Elim.eb_motive_sub.
        exact (readback_branch_view m Mm qc kc Is vm D' HMm Hh Hq Hvw k Mk v Mv b0 c0 gs gsv HMk Hrk Hv HMv Hb0 Hcn Hcnv Hcr Δ σ'' Hσ''
                 ns vs ihs wihs hd k0 pre Lpre Fn Fc Fi Wi Hrel Hrecs
                 (fun gs1' g' gs2' gs1 t gs2 l E1 E2 E3 E4 E5 =>
                    Hok k Mk v Mv c0 gs gsv gs1' g' gs2' gs1 t gs2 l HMk Hv HMv Hcn Hcnv E1 E2 E3 E4 E5)
                 n0 B0 bv t Bn Hlk Href Ebv Et Rn).
  Qed.

  (** The readback of a stuck eliminator at a view is the elimination's,
      when the readbacks at the members of lower rank are: the eliminator
      at the view is the container's at the wrapped blocks (E1′), whose
      readback is the stuck one's, by the congruence. *)
  Lemma elim_readback_view : forall m Mm qc kc Is vm, ind_member D m = Some Mm -> im_head Mm = mh_view qc kc Is vm ->
      forall rk, view_rank_ok gc_deps gc_stack D rk -> (forall j, rk j < rk m -> elim_readback_ok j) -> elim_readback_ok m.
  Proof.
    intros m Mm qc kc Is vm HMm Hh rk Hrk IH.
    intros Mj as' e Δ σ'' Ns M oq M0 HMj Hgrp Hσ'' HNl HPs HMr HR.
    rewrite HMm in HMj; injection HMj as <-.
    inversion HR; subst.
    repeat match goal with
      | H1 : ind_lookup gc_deps gc_stack p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <-
      | H1 : ind_member D m = Some ?M1 |- _ => rewrite HMm in H1; injection H1 as <-
      end.
    match goal with H1 : im_ref p m Mm = _ |- _ => unfold im_ref in H1; rewrite Hh in H1; injection H1 as <- <- end.
    match goal with H1 : ind_lookup gc_deps gc_stack qc = Some ?D1 |- _ => rename D1 into D'; rename H1 into Hq end.
    match goal with H1 : ind_member D' kc = Some ?M1 |- _ => rename M1 into Mk; rename H1 into HMk end.
    match goal with H1 : ⟦mref m of p ups ⟧ gc_deps ⍮ gc_stack ↘ _ |- _ =>
      destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMm Hh H1) as (py & E & Epy); inversion E; subst py end.
    assert (Hsel : im_sel Mm = Some vm) by (unfold im_sel; rewrite Hh; reflexivity).
    rewrite Hsel in *.
    match goal with H1 : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRU0 end.
    match goal with H1 : Rblks _ _ of _ from _ _ _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRB end.
    match goal with H1 : Rne e in _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H1 into HRM end.
    set (Us' := List.map (fun U => U[σ'']) Us) in *.
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
    assert (HUs' : forall k U T, List.nth_error Us' k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us') k = Some T ->
                     Δ ⊢ U : T) by exact (glu_args_typed _ _ _ _ _ _ Ua (us_glu_args Δ σ'' Hσ'')).
    assert (Hσt : Δ ⊢ˢ σ'' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'').
    assert (HΔ : ⊢ Δ) by exact (view_branch_Δ Δ σ'' Hσ'').
    pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; fold Us' in HBt'.
    pose proof (ctx_wf_gctx _ _ _ HΔ) as Xg.
    pose proof (decls_of_ctx _ _ _ HΔ) as XDs.
    (** The container. *)
    destruct (group_structure_view_wrap _ Hass m Mm qc kc Is vm HMm Hh) as (D'' & Hq' & Hvw).
    rewrite Hq in Hq'; injection Hq' as <-.
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMm Hh) as (D0 & Mk' & Hl0 & Hk' & Hlt' & HIl & _ & Hself & _).
    rewrite Hq in Hl0; injection Hl0 as <-; rewrite HMk in Hk'; injection Hk' as <-.
    pose proof (valid_groups_containers VP HVP p D m Mm qc kc Is vm D' HPD HMm Hh Hq) as HPq.
    pose proof (valid_groups_valid VP HVP qc D' HPq) as HgQ.
    pose proof (valid_group_closed _ _ HgQ) as Hc'.
    pose proof (XDs _ _ Hq) as HD'.
    set (Is' := List.map (fun I => I[sb_of_list Id Us']) Is) in *.
    assert (HIl' : List.length Is' = ind_nu D') by (unfold Is'; rewrite List.length_map; exact HIl).
    pose proof (view_blocks_typed gc_deps gc_stack Δ p D m Mm qc kc Is vm D' Us' (blocks_sub Bks σ'') iA Xg XDs Hl HMm Hh Hq Hvw HΔ
                  HUl' HUs' HBt') as HBtv.
    fold Is' in HBtv.
    (** The scrutinee, typed. *)
    pose proof (HMr M1 HRM) as HMM1.
    destruct (presup_exp_eq HMM1) as (_ & HMt & _).
    assert (Emt : ind_mty p D m Us' Ns = im_ty_at p m Mm Us' Ns) by (unfold ind_mty; rewrite HMm; reflexivity).
    assert (Emt' : ind_mty qc D' kc Is' Ns = im_ty_at p m Mm Us' Ns).
    { destruct (member_lt_decl _ _ _ _ _ HD' HMk Hlt') as [pm Hpm].
      unfold ind_mty; rewrite HMk; unfold im_ty_at, im_ref, im_pre; rewrite Hh, Hpm; reflexivity. }
    assert (Hrvm : im_is_rview Mm = false) by (unfold im_is_rview; rewrite Hh; reflexivity).
    destruct (HBks _ _ HMm Hrvm) as [b Hb].
    assert (Hbk' : List.nth_error (blocks_sub Bks σ'') m = Some (eblock_sub b σ'')) by (rewrite nth_error_blocks_sub, Hb; reflexivity).
    assert (HPl : List.length (Us' ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl', HNl; unfold im_np; lia).
    (** E1′: the eliminator at the view is the container's at the wrapped blocks. *)
    assert (E1 : Δ ⊢ a_elim oq (List.firstn (ind_nu D) (Us' ++ Ns)) m (blocks_sub Bks σ'') M
               ≈ a_elim (Some qc) (im_pre Mm (List.firstn (ind_nu D) (Us' ++ Ns))) kc
                   (view_wrap p D D' vm (List.firstn (ind_nu D) (Us' ++ Ns)) (blocks_sub Bks σ'')) M
               : (eb_motive (eblock_sub b σ''))[sb_of_list Id (List.skipn (ind_nu D) (Us' ++ Ns) ++ M :: nil)]).
    { eapply wf_exp_eq_elim_view;
        first [ exact Hl | exact Hgrp | exact HMm | exact Hh | exact Hq | exact Hvw | exact Hbk' | exact HPl | exact HPs
              | exact (blocks_typed_len _ _ _ _ _ _ _ _ HBt') | reflexivity | idtac ];
        rewrite ?firstn_app_exact, ?skipn_app_exact by exact HUl';
        first [ exact (blocks_typed_binder_count _ _ _ _ _ _ _ _ HBt') | exact (blocks_typed_ann _ _ _ _ _ _ _ _ HBt') | exact (blocks_typed_motive _ _ _ _ _ _ _ _ HBt')
              | exact (blocks_typed_mctx _ _ _ _ _ _ _ _ HBt') | exact (blocks_typed_names _ _ _ _ _ _ _ _ HBt') | exact (blocks_typed_bctx _ _ _ _ _ _ _ _ HBt')
              | exact (blocks_typed_counts _ _ _ _ _ _ _ _ HBt') | exact (blocks_typed_brs _ _ _ _ _ _ _ _ HBt') | rewrite Emt; exact HMt ]. }
    rewrite firstn_app_exact, skipn_app_exact in E1 by exact HUl'.
    replace (im_pre Mm Us') with Is' in E1 by (unfold im_pre; rewrite Hh; reflexivity).
    (** The container's parameters. *)
    destruct (params_typed_split _ _ D Hc _ _ Δ (Us' ++ Ns) HMm HPl HPs) as [_ HNs].
    rewrite firstn_app_exact, skipn_app_exact in HNs by exact HUl'.
    destruct (view_params_typed gc_deps gc_stack Δ p D m Mm qc kc Is vm D' Mk Us' Ns Xg Hl XDs Hdt Hc Hc' HMm Hh Hq HMk Hself HIl
                HΔ HUl' HUs' HNl HNs) as [HNl' HPs'].
    fold Is' in HPs'.
    assert (HPl' : List.length (Is' ++ Ns) = im_np D' Mk) by (rewrite List.length_app, HIl', HNl'; unfold im_np; lia).
    pose proof (view_uparams_glu VP p D HVP HPD HG m Mm qc kc Is vm D' HMm Hh Hq Δ Us' ups pre HΔ (us_glu_args Δ σ'' Hσ'') Epy) as HUc.
    fold Is' in HUc.
    pose proof (glu_args_read Δ (ind_uparams D') Is' pre (decl_closed_ass _ Hc') (decl_closed_uparams _ Hc') HUc Δ wk_id Us0 (kripke_id Δ HΔ) HRU0) as Hu.
    rewrite map_wk_id in Hu.
    rewrite <- (firstn_app_exact Is' Ns (ind_nu D') HIl') in Hu.
    pose proof (exps_eq_at_params_of_uparams D' Mk Δ (Is' ++ Ns) (List.map nf_to_exp Us0) Hc' HPl' HPs' Hu) as [_ Hu'].
    rewrite skipn_app_exact in Hu' by exact HIl'.
    destruct (read_ps_nth _ _ _ _ _ HRU0) as [LUr _].
    assert (LUr' : List.length (List.map nf_to_exp Us0) = ind_nu D').
    { rewrite LUr, (Completeness.Inductives.Model.eval_exps_length _ _ _ Epy); exact HIl. }
    (** The blocks, read back. *)
    (** The leaf paths the view nests through end in members of lower rank:
        of a whole argument non-recursive in the container, below the
        argument's member ([leaf_mem_rank]); of one recursive in both, by
        the leaf-wise condition ([cargs_nest_ok_leaf_at]). *)
    assert (Hok : forall i' Mi' v Mv c gs' gs gs1' g' gs2' gs1 t gs2 l, ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v ->
                    ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                    gs' = gs1' ++ g' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
                    In l (shape_leaves (rview_leaves D) 0 t) -> (forall t', g' = ca_rec t' -> leaf_in D' t' l = false) ->
                    elim_readback_ok (leaf_mem l)).
    { intros i' Mi' v Mv c gs' gs gs1' g' gs2' gs1 t gs2 l Hi' Hv HMv Hcon' Hcon E3 E4 E5 Hin Hnin; apply IH.
      pose proof (view_rank_ok_nest _ _ _ _ Hrk m Mm qc kc Is vm D' i' Mi' v Mv c gs' gs HMm Hh Hq Hi' Hv HMv Hcon' Hcon) as Hno.
      rewrite E3, E4 in Hno.
      destruct g' as [A' | t'].
      - pose proof (cargs_nest_ok_at _ _ _ _ _ _ _ _ _ _ E5 Hno) as Ht.
        pose proof (leaf_mem_rank p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had rk Hrk t 0 l Hin) as Hle; lia.
      - exact (cargs_nest_ok_leaf_at _ _ _ _ _ _ _ _ _ _ _ E5 Hno Hin (Hnin t' eq_refl)). }
    pose proof (view_block_rb m Mm qc kc Is vm D' HMm Hh Hq Hvw Hok Δ σ'' NBks Hσ'' HRB) as Hown.
    fold Us' Is' in Hown.
    destruct (read_blocks_nth _ _ _ _ _ _ HRB) as [LNB _].
    pose proof (blocks_typed_len _ _ _ _ _ _ _ _ HBtv) as LBv.
    pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD')) as Hsuf'.
    (** The container's member is a declared one: no record view. *)
    assert (HrvK : im_is_rview Mk = false).
    { destruct (member_lt_decl _ _ _ _ _ HD' HMk Hlt') as [pm Hpm]; unfold im_is_rview; rewrite Hpm; reflexivity. }
    assert (Lsame : List.length (List.map block_exp NBks) = List.length (view_wrap p D D' vm Us' (blocks_sub Bks σ'')))
      by (rewrite LNB, length_ind_block_members; exact (eq_sym LBv)).
    assert (Hbv : List.nth_error (view_wrap p D D' vm Us' (blocks_sub Bks σ'')) kc
                  = Some (eb_mk (eb_binder_count (eblock_sub b σ'')) None (eb_motive (eblock_sub b σ''))
                            (List.map (fun cg => wrap_branch p D D' Us' (blocks_sub Bks σ'') Mm (eb_brs (eblock_sub b σ'')) (fst cg) (snd cg))
                                      (im_cons Mk))))
      by (rewrite (nth_error_view_wrap _ _ _ _ _ _ _ _ Hsuf' HMk HrvK), (view_wrap_block_eq _ _ _ _ _ _ _ _ _ _ _ Hself Hbk' HMm); reflexivity).
    assert (HMt' : Δ ⊢ M ≈ ne_to_exp M1 : ind_mty qc D' kc (List.firstn (ind_nu D') (Is' ++ Ns)) (List.skipn (ind_nu D') (Is' ++ Ns)))
      by (rewrite firstn_app_exact, skipn_app_exact, Emt' by exact HIl'; exact HMM1).
    assert (E2 : Δ ⊢ a_elim (Some qc) (List.firstn (ind_nu D') (Is' ++ Ns)) kc (view_wrap p D D' vm Us' (blocks_sub Bks σ'')) M
               ≈ a_elim (Some qc) (List.firstn (ind_nu D') (List.map nf_to_exp Us0 ++ Ns)) kc (List.map block_exp NBks) (ne_to_exp M1)
               : (eb_motive (eblock_sub b σ''))[sb_of_list Id (List.skipn (ind_nu D') (Is' ++ Ns) ++ M :: nil)]).
    { eapply wf_exp_eq_elim_cong with (Ps' := List.map nf_to_exp Us0 ++ Ns) (Bks' := List.map block_exp NBks) (bm := eb_mk _ _ _ _);
        first [ exact Hq | left; reflexivity | exact HMk | exact Hbv | exact HPl' | exact HPs' | reflexivity | exact LNB
              | exact LBv | exact HMt' | idtac ];
        rewrite ?firstn_app_exact, ?skipn_app_exact by first [ exact HIl' | exact LUr' ];
        first [ exact (blocks_typed_binder_count _ _ _ _ _ _ _ _ HBtv) | exact (blocks_typed_ann _ _ _ _ _ _ _ _ HBtv) | exact (blocks_typed_motive _ _ _ _ _ _ _ _ HBtv)
              | exact (blocks_typed_mctx _ _ _ _ _ _ _ _ HBtv) | exact (blocks_typed_names _ _ _ _ _ _ _ _ HBtv) | exact (blocks_typed_bctx _ _ _ _ _ _ _ _ HBtv)
              | exact (blocks_typed_counts _ _ _ _ _ _ _ _ HBtv) | idtac ].
      - rewrite LNB, length_ind_block_members; reflexivity.
      - rewrite List.length_app, LUr', HNl'; unfold im_np; lia.
      - exact Hu'.
      - intros k Mk0 b' HMk0 Hb'.
        destruct (blocks_nth_same _ _ k b' Lsame Hb') as [b0 Hb0].
        exact (proj1 (Hown k Mk0 b0 b' HMk0 Hb0 Hb')).
      - intros k Mk0 b' Z HMk0 Hb' HZ.
        destruct (blocks_nth_same _ _ k b' Lsame Hb') as [b0 Hb0].
        rewrite (proj1 (proj2 (Hown k Mk0 b0 b' HMk0 Hb0 Hb'))) in HZ; discriminate.
      - intros k Mk0 ba b' HMk0 Hba Hb'; exact (proj1 (proj2 (proj2 (Hown k Mk0 ba b' HMk0 Hba Hb')))).
      - intros k ba b' Hba Hb'.
        destruct (ind_member D' k) as [Mk0 |] eqn:HMk0.
        2: { exfalso; unfold ind_member in HMk0; apply List.nth_error_None in HMk0.
             assert (k < List.length (view_wrap p D D' vm Us' (blocks_sub Bks σ''))) by (apply List.nth_error_Some; congruence).
             pose proof (ind_nblk_le D'); lia. }
        exact (proj1 (proj2 (proj2 (proj2 (Hown k Mk0 ba b' HMk0 Hba Hb'))))).
      - intros k Mk0 ba b' i c gs n B B' HMk0 Hba Hb' HB HB' Hcn.
        exact (proj2 (proj2 (proj2 (proj2 (Hown k Mk0 ba b' HMk0 Hba Hb')))) i c n B B' gs HB HB' Hcn). }
    rewrite !firstn_app_exact, skipn_app_exact in E2 by first [ exact HIl' | exact LUr' ].
    rewrite (blocks_motives_nth _ _ _ Hb).
    change (ne_to_exp (ne_elim qc Us0 kc NBks M1)) with (a_elim (Some qc) (List.map nf_to_exp Us0) kc (List.map block_exp NBks) (ne_to_exp M1)).
    rewrite <- (Hnm _ _ _ HMm Hb), <- Completeness.Inductives.Elim.eb_motive_sub.
    eapply wf_exp_eq_trans; [ exact E1 | exact E2 ].
  Qed.


  (** ** The Readback of the Stuck Eliminator, at Every Member

      By strong induction on the rank: at a declared member directly, at a
      view by the readbacks at the members of lower rank. *)
  Lemma elim_readback_all : forall j, elim_readback_ok j.
  Proof.
    destruct (group_structure_rank _ Hass) as [rk Hrk].
    assert (H : forall r j, rk j < r -> elim_readback_ok j).
    { induction r as [| r IH]; intros j Hj; [ lia |].
      intros Mj as' e Δ σ'' Ns M oq M0 HMj.
      destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
      - exact (elim_readback_decl j Mj pm HMj Hh as' e Δ σ'' Ns M oq M0).
      - exact (elim_readback_view j Mj qc kc Is vm HMj Hh rk Hrk (fun j' Hj' => IH j' ltac:(lia)) Mj as' e Δ σ'' Ns M oq M0 HMj).
      - (** A record view has no stuck eliminator: its reference is
            undefined. *)
        intros _ _ _ _ _ HR; exfalso; inversion HR; subst.
        match goal with H2 : ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ _ |- _ => inversion H2; subst end;
          repeat match goal with H : ind_lookup _ _ p = Some ?D' |- _ => tryif constr_eq D' D then fail else (rewrite Hl in H; injection H as <-) end;
          congruence. }
    intros j; exact (H (S (rk j)) j ltac:(lia)).
  Qed.

  (** The neutral case, at every member. *)
  Lemma neut_ok_all : forall j, neut_ok j.
  Proof. intros j; exact (neut_ok_of_rb j (elim_readback_all j)). Qed.

  (** ** The Eliminator, Glued

      By induction on the gluing of the group: a constructor by its branch
      ([con_case_main]), a neutral by the readback of the stuck eliminator
      ([neut_ok_all]), the recursive arguments by the shapes, and an
      element of a record view by its fields ([rview_ihs_prop]), which a
      shape ending in the record view uses ([rec_rview_case]).  Every leaf
      path is taken ([fun _ => True]). *)
  Theorem elim_glu_all :
    (forall k Γ' Us' Ns' M' mv, ind_glu_elem p D ups NEl AEl DP DEl k Γ' Us' Ns' M' mv ->
       elim_prop k Γ' Us' Ns' M' mv /\ rview_ihs_prop (fun _ => True) k Γ' Us' M' mv) /\
    (forall k Γ' Us' pre t A N v, glu_rec p D ups NEl AEl DP DEl k Γ' Us' pre t A N v ->
       forall σs, A = ptyp_ty_at p D Us' σs t -> rec_prop (fun _ => True) k Γ' Us' pre t σs N v).
  Proof.
    apply (ind_glu_elem_mut_ind_all p D ups NEl AEl DP DEl
             (fun k Γ' Us' Ns' M' mv _ => elim_prop k Γ' Us' Ns' M' mv /\ rview_ihs_prop (fun _ => True) k Γ' Us' M' mv)
             (fun k Γ' Us' pre t A N v _ => forall σs, A = ptyp_ty_at p D Us' σs t -> rec_prop (fun _ => True) k Γ' Us' pre t σs N v)).
    - (** A constructor: its branch. *)
      intros k Mk hd k' c gs Us' Ns' bs vs As Δ' M' HMk Hrv Href Hcon HUl' HNl' Hbl Hvl HAl HMeq Hb Hv Hnp HAs Harg Hrec IH.
      split.
      + intros Mk0 σ' oq' ns HMk0 _ Hgrp Hσ' HUs' HMt Hgn Hns HGm.
        rewrite HMk in HMk0; injection HMk0 as <-.
        exact (con_case_main k Mk hd k' c gs Us' Ns' bs vs As Δ' M' HMk Hrv Href Hcon HUl' HNl' Hbl Hvl HAl HMeq Hb Hv Hnp HAs Harg Hrec IH
                 σ' oq' ns Hgrp Hσ' HUs' HMt Hgn Hns HGm).
      + intros Mk0 qr0 Is0 fl0 c0 gs0 ws0 HMk0 Hh0; rewrite HMk in HMk0; injection HMk0 as <-.
        exfalso; exact (not_rview_record _ _ _ _ Hrv Hh0).
    - (** A neutral: the readback of the stuck eliminator. *)
      intros k Mk hd k' m Γ' Us' Ns' M' as' HMk Hrv Href Hm Hrb.
      split; [ exact (neut_ok_all k Mk hd k' as' m Γ' Us' Ns' M' HMk Href Hm Hrb) |].
      intros Mk0 qr0 Is0 fl0 c0 gs0 ws0 HMk0 Hh0; rewrite HMk in HMk0; injection HMk0 as <-.
      exfalso; exact (not_rview_record _ _ _ _ Hrv Hh0).
    - (** An element of a record view: no eliminator; its fields. *)
      intros k Mk qr Is fl c gs Us' Ns' As m vs Γ' M HMk Hh Hcs HUl' HNl' HAl Hps HMeq Hv HAs Harg Hrec IH.
      split.
      + intros Mk0 σ' oq' ns HMk0 Hrv0; rewrite HMk in HMk0; injection HMk0 as <-.
        unfold im_is_rview in Hrv0; rewrite Hh in Hrv0; discriminate.
      + intros Mk0 qr0 Is0 fl0 c0 gs0 ws0 HMk0 Hh0 Hcs0 Hws0.
        rewrite HMk in HMk0; injection HMk0 as <-.
        rewrite Hh in Hh0; injection Hh0 as <- <- <-; rewrite Hcs in Hcs0; injection Hcs0 as <- <-.
        pose proof (functional_eval_projs _ _ _ _ Hws0 Hps) as ->.
        destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMk Hh) as [_ Hnn].
        destruct Ns' as [| N0 Ns']; [| cbn in HNl'; lia ].
        cbn [List.app] in HMeq.
        rewrite List.app_nil_r in HAs.
        apply (mk_rview_ihs_at (fun _ => True) k Mk c gs Γ' Us' M vs As HAl HMeq HAs).
        intros gs1 tf gs2 N A w Heq HN HA Hw σs HAeq.
        rewrite <- (List.app_nil_r Us') in HA.
        exact (IH gs1 tf gs2 N A w Heq HN HA Hw σs HAeq).
    - (** At the end of a shape. *)
      intros j Mj Ps pre A Us' Γ' N v k HMj Hs1 _ IH σs HA.
      destruct (im_is_rview Mj) eqn:Hrv.
      + (** A record view: through its fields. *)
        apply (rec_rview_case (fun _ => True) k Γ' Us' pre j Mj Ps A N v HMj Hrv); [| exact HA ].
        intros bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq; exact (proj2 (IH bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq)).
      + (** A member with a block: the eliminator at the member. *)
        apply (rec_self_case (fun _ => True) k Γ' Us' pre j Mj Ps A N v HMj Hrv Hs1); [| exact HA ].
        intros _ bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq; exact (proj1 (IH bsr Q Ebs HAQ Δ φ Us'' Q' Hφ HUl'' Heq)).
    - (** At a domain: a function, by the rest at its applications. *)
      intros A Γ' k pre B v Us' t N Hq1 Hq2 _ IH σs HA.
      apply (rec_pi_case (fun _ => True) k Γ' Us' pre B t A N v Hq1 Hq2); [| exact HA ].
      intros IT OT HAp Δ φ b c fc Hφ Hdc Hb Efc σs' HOT.
      exact (IH IT OT HAp Δ φ b c fc Hφ Hdc Hb Efc σs' HOT).
  Qed.

End ElimGlu.

(** ** The Eliminator Is Glued

    At a substitution glued to [ρ]: the scrutinee is an element of the
    group at its member ([ind_glu_elem]), at the gluings of the clause of
    the member's type at a declared member, of the group's families at its
    sort at a view (where the scrutinee is glued at the container's type,
    [glu_view_end_at]); its relation is the group's ([scrut_rel]).  The
    elimination is then glued ([elim_glu_all]) at the motive's value,
    related to the value of the rule's type. *)
Theorem glu_rel_exp_elim : forall VP p D, valid_groups VP -> (forall qn G, VP qn G -> glu_ind_decl G) -> VP p D ->
    forall Γ m Mm bm Bks Ps M (i : nat),
    ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D -> List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊩ P : T) ->
    Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Γ ⊩ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹{ak_relevant} eb_scrutinee_type b
         ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊩ eb_motive b : Typeω@i) ->
    (forall k Mk, ind_member D k = Some Mk ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
            ≈ elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊩ a_elim ak_relevant p (List.firstn (ind_nu D) Ps) m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros VP p D HVP HGall HPD Γ m Mm bm Bks Ps M i HMm Hbm HLb HPl HPt HPg HMt HMg Hnm Hann HAt HAg HMx Hna HBx Har HBt HBg.
  pose proof (fun qn G H => glu_views_ok_all VP qn G HVP H (HGall _ _ H)) as Hviewsall.
  pose proof (HGall _ _ HPD) as HG.
  pose proof (valid_groups_valid VP HVP p D HPD) as Hvg.
  pose proof (valid_group_lookup _ _ Hvg) as Hl; pose proof (valid_group_valid _ _ Hvg) as HD; pose proof (valid_group_closed _ _ Hvg) as Hc.
  pose proof (valid_group_sort _ _ Hvg) as Hsu; pose proof (valid_group_ass _ _ Hvg) as Hass; pose proof (valid_group_typed _ _ Hvg) as Hdt.
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  destruct (params_typed_split _ _ D Hc _ _ Γ Ps HMm HPl HPt) as [HUt HNt]; fold Us Ns in HUt, HNt.
  pose proof (presup_exp_ctx HMt) as HΓw.
  pose proof (completeness_fundamental_ctx _ HΓw) as HΓs.
  destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
  destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
  assert (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ N : T)
    by (intros; eapply completeness_fundamental_exp; eauto).
  assert (HNs : forall k N T, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
             Γ ⊨ N : T) by (intros; eapply completeness_fundamental_exp; eauto).
  assert (HUg : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊩ N : T).
  { assert (Hti : tele_insts (im_params D Mm) Id Ps
                  = tele_insts (ind_uparams D) Id Us ++ tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns).
    { unfold Us, Ns; rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
        [ exact (decl_uparams_ass D Hc) | fold Us; rewrite HUl; reflexivity ]. }
    intros k N T HN HT; apply (HPg k).
    - unfold Us in HN; rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HN.
    - rewrite Hti, List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HT. }
  (** The blocks. *)
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ Hdt)) as Hsuf.
  (** The eliminated member has a block: it is no record view. *)
  pose proof (block_not_rview D Bks m Mm bm Hsuf HLb HMm Hbm) as Hrvm.
  assert (HBt' : blocks_typed gc_deps gc_stack Γ p D Us Bks i) by (constructor; assumption).
  assert (HBv : valid_blocks p D Γ Us Bks i).
  { constructor; try assumption.
    - intros j Mj HMj; exact (completeness_fundamental_ctx _ (ext_eq_ctx_left _ _ _ _ _ (HMx _ _ HMj))).
    - intros j Mj b HMj Hb; exact (completeness_fundamental_exp _ _ _ (HAt _ _ _ HMj Hb)).
    - intros j Mj c gs HMj Hcon; exact (completeness_fundamental_ctx _ (ext_eq_ctx_left _ _ _ _ _ (HBx _ _ _ _ HMj Hcon))).
    - intros * HMj Hb Hcon Hin; exact (completeness_fundamental_exp _ _ _ (HBt _ _ _ _ _ _ _ HMj Hb Hcon Hin)). }
  assert (HBg' : glu_blocks Γ p D Us Bks i) by (constructor; assumption).
  (** The substitution and the scrutinee. *)
  pose proof HMg as [SbΓ HSbΓ _ _].
  destruct (glu_rel_exp_clean_inversion1 HSbΓ HMg) as [iM HiM].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HSbΓ |]; intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_per_env HSbΓ HRΓ Hσ) as Hρ.
  assert (HΔ : ⊢ Δ) by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ); gen_presups; assumption).
  assert (Hσt : Δ ⊢ˢ σ : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ).
  destruct (Completeness.Inductives.Model.eval_exps_each Us ρ) as [ups HUv].
  { intros k N HN.
    destruct (nth_error_lt_some' (tele_insts (ind_uparams D) Id Us) k) as [T HT].
    { rewrite length_tele_insts by exact (decl_uparams_ass D Hc).
      assert (k < List.length Us) by (apply List.nth_error_Some; congruence); unfold ind_nu in *; lia. }
    destruct (rel_exp_under_ctx_simple_at HRΓ (HUs _ _ _ HN HT) _ _ Hρ) as (v1 & v2 & E1 & _); eauto. }
  pose proof (Completeness.Inductives.Elim.u0_tele_args VP p D HVP HPD Γ RΓ HRΓ HΓs RU HRU Us HUl HUs ρ ups Hρ HUv) as Hgu.
  assert (Hu : List.length ups = ind_nu D) by (rewrite (Completeness.Inductives.Model.eval_exps_length _ _ _ HUv); exact HUl).
  destruct (HiM _ _ _ Hσ) as [aM mv PM ElM EaM Em HgM HMσ].
  destruct (eval_mty_inv p D m Mm Us Ns ρ aM HMm Hrvm EaM) as (cs & ns0 & Ecs & Ens & EaMd).
  destruct (glu_univ_elem_per_univ _ _ _ _ HgM) as [RM HRM].
  assert (HMa : ⊨ elim_mctx p D m Mm Us ++ Γ) by exact (valid_blocks_mctx _ _ _ _ _ _ HBv m Mm HMm).
  pose proof (Completeness.Inductives.Elim.gsub_ns VP p D HVP HPD Γ HΓs Us m Mm HMm HMa Ns HNl HNs) as HgN.
  destruct (Completeness.Inductives.Elim.scrut_rel VP p D HVP HPD Γ RΓ HRΓ HΓs RU HRU Us HUl HUs ρ ups Hρ HUv m Mm HMm HMa Ns HNl HgN
              ρ Hρ ns0 ns0 Ens Ens aM aM iM RM EaM EaM HRM) as [Hns0 ERM].
  pose proof (glu_univ_elem_per_elem _ _ _ _ HgM _ _ _ _ _ HMσ HRM) as Hmv.
  assert (HGm : grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) m ups ups ns0 ns0 mv mv)
    by (apply ERM; exact Hmv).
  (** The parameters, glued. *)
  assert (EPs : ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ups ++ ns0)
    by (rewrite <- (List.firstn_skipn (ind_nu D) Ps); fold Us Ns; apply eval_exps_app; assumption).
  pose proof (decl_closed_params_ass D m Mm Hc HMm) as HassP.
  pose proof (decl_closed_params D m Mm Hc HMm) as HsP.
  pose proof (params_glu_args (im_params D Mm) Γ RΓ SbΓ Δ σ ρ Ps (ups ++ ns0) HassP HsP (valid_ind_decl_params _ HD _ _ HMm) HΓs HRΓ HSbΓ Hσ
                ltac:(rewrite length_im_params; exact HPl)
                ltac:(intros; eapply completeness_fundamental_exp; eauto) HPg EPs) as Hpa.
  assert (EPσ : List.map (fun P => P[σ]) Ps = List.map (fun U => U[σ]) Us ++ List.map (fun N => N[σ]) Ns)
    by (rewrite <- List.map_app; unfold Us, Ns; rewrite List.firstn_skipn; reflexivity).
  pose proof Hpa as Hpa'; rewrite EPσ in Hpa'; unfold im_params in Hpa'.
  apply glu_args_app in Hpa' as [HUga HNga];
    [| exact (decl_uparams_ass D Hc) | rewrite List.length_map; exact HUl | rewrite Hu; reflexivity ].
  destruct (Completeness.Inductives.Model.sort_value D HD ups Hgu Hu) as [bu Hbu].
  (** The families of the group, and the scrutinee glued as an element. *)
  assert (Hfam : exists (u : universe_index) NP NEl AP AEl DP DEl, universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u /\
            ind_fams_glu D ups u NP NEl AP AEl DP DEl /\
            ind_glu_elem p D ups NEl AEl DP DEl m Δ (List.map (fun U => U[σ]) Us) (List.map (fun N => N[σ]) Ns) M[σ] mv).
  { destruct (im_head Mm) as [pm | qc kc Is vm | qr Is fl] eqn:Hh;
      [| | exfalso; unfold im_is_rview in Hrvm; rewrite Hh in Hrvm; discriminate ].
    - (** A declared member: the gluings of the clause of its type. *)
      assert (Href : im_ref p m Mm = (p, m)) by (unfold im_ref; rewrite Hh; reflexivity).
      rewrite Href in EaMd; cbn [fst snd] in EaMd.
      assert (cs = ups) as -> by (unfold im_pre in Ecs; rewrite Hh in Ecs; eapply functional_eval_exps'; eassumption).
      subst aM.
      destruct (sort_bound_of D Hsu) as [n0 Hn0].
      set (J := Nat.max iM n0).
      destruct (glu_univ_elem_cumu_ge (i := iM) (j := J) ltac:(unfold J; lia) HgM) as (P1 & El1 & Hg1).
      pose proof (glu_univ_elem_exp_cumu_ge (Nat.le_max_l iM n0) HgM Hg1 HMσ) as HMσ1.
      destruct (glu_univ_elem_per_univ _ _ _ _ Hg1) as [R0 HR0].
      destruct (ind_glu_of_per p D Hl J R0 m Mm pm ups ns0 HMm Hh HR0 Hu) as [NP NEl AP AEl DP DEl P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf].
      destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg1 Hg2) as [_ EEl].
      apply EEl, HEl2 in HMσ1; destruct HMσ1 as [HMt' Hmm Ps0 HT0 HK0].
      exists J, NP, NEl, AP, AEl, DP, DEl; split; [ exact (Hn0 _ _ Hbu J ltac:(unfold J; lia)) | split; [ exact Hf |] ].
      assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
      destruct HT0 as (_ & HT0); destruct (HT0 _ _ Hid) as (Hpt0 & _ & _).
      rewrite map_wk_id in Hpt0.
      assert (Heq : exps_eq_at Δ (im_params D Mm) (List.map (fun P => P[wk_id]ʷ) Ps0)
                      (List.map (fun U => U[σ]) Us ++ List.map (fun N => N[σ]) Ns)).
      { rewrite map_wk_id.
        eapply glu_params_top_eq; [ exact Hl | exact HMm | exact HΔ | exact (ind_rps_of_per _ _ _ _ _ _ _ _ HR0 Hl HMm _) | exact Hpt0 |].
        rewrite <- EPσ; exact (glu_args_params_top _ _ _ _ _ HassP HsP Hpa). }
      pose proof (HK0 Δ wk_id _ Hid Heq) as H.
      rewrite firstn_app_exact, skipn_app_exact, exp_wk_id in H by (rewrite List.length_map; exact HUl).
      exact H.
    - (** A view: the scrutinee is glued at the container's type, and its
          gluing in the group is the coherence of the view. *)
      destruct (group_fams_glu D HD Hc Hsu ups bu Hgu Hu Hbu) as (NP & NEl & AP & AEl & DP & DEl & Hf).
      exists (Completeness.Inductives.Decl.univ_idx bu), NP, NEl, AP, AEl, DP, DEl;
        split; [ apply universe_index_le_refl | split; [ exact Hf |] ].
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMm Hh) as (D' & Mk' & Hq & HMk' & _ & _ & _ & _ & _).
      pose proof (containers_valid_of_groups VP HVP p D HPD _ _ _ _ _ _ _ HMm Hh Hq) as HgQ.
      destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ (valid_group_valid _ _ HgQ))) as [RQ HRQ].
      destruct (FiledViews.valid_group_views_view_args_values p D Hvg (containers_valid_of_groups VP HVP p D HPD) _ _ _ _ _ _ _ HMm Hh Hq
                  ups ups Hgu Hu) as (cups & _ & Ecups & _ & _).
      destruct (ElimViewRule.pre_base VP p D HVP HPD Γ RΓ HRΓ HΓs RU HRU Us HUl HUs Bks i HBv qc D' m Mm kc Is vm Hq HMm Hh
                  ρ ups cups Hρ HUv Ecups RQ HRQ) as (uB & EuB & HB).
      pose proof (functional_eval_exps' _ _ _ _ EuB Ecs) as <-.
      pose proof (ElimViewRule.pre_length VP p D HVP HPD Γ RΓ HRΓ HΓs RU HRU Us HUl HUs Bks i HBv qc D' m Mm kc Is vm Hq HMm Hh)
        as HIl.
      assert (Lcups : List.length cups = List.length (ind_uparams D'))
        by (rewrite (eval_exps_length _ _ _ Ecups); exact HIl).
      assert (LuB : List.length uB = List.length (ind_uparams D'))
        by (rewrite (eval_exps_length _ _ _ EuB); unfold im_pre; rewrite Hh, List.length_map; exact HIl).
      pose proof (Completeness.Inductives.Model.uparams_of_env D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) cups uB RQ HRQ
                    Lcups LuB ltac:(symmetry; exact HB)) as Hcs.
      unfold im_ref in EaMd; rewrite Hh in EaMd; cbn in EaMd; subst aM.
      assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
      rewrite EPσ in Hpa.
      assert (HlU : List.length (List.map (fun U => U[σ]) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
      assert (Heq : exps_eq_at Δ (im_params D Mm)
                      (List.map (fun P => P[wk_id]ʷ) (List.map (fun U => U[σ]) Us ++ List.map (fun N => N[σ]) Ns))
                      (List.map (fun U => U[σ]) Us ++ List.map (fun N => N[σ]) Ns)).
      { rewrite map_wk_id; split; [ reflexivity |].
        intros k X Y A HX HY HA; rewrite HX in HY; injection HY as <-.
        apply wf_exp_eq_refl; exact (glu_args_typed _ _ _ _ _ _ HassP Hpa k X A HX HA). }
      pose proof (proj1 (Hviewsall p D HPD ups bu _ NP NEl AP AEl DP DEl Hu Hgu Hbu (universe_index_le_refl _) Hf m) Mm qc kc Is vm D' cups uB
                    ns0 ns0 Δ _ _ _ _ mv _ PM ElM HMm Hh Hq Ecups Hcs Hns0 HgM HMσ HGm Hpa Δ wk_id _ _ Hid HlU Heq) as H.
      rewrite exp_wk_id in H; exact H. }
  destruct Hfam as (u & NP & NEl & AP & AEl & DP & DEl & Hule & Hf & HIG).
  (** The elimination, glued. *)
  destruct (nb_exists VP p D HVP HPD u) as (nb & Hnb).
  pose proof (components_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Δ _ HΔ HUga) as HIGC.
  pose proof (nparams_of_glu_args p D Hass ups u NP NEl AP AEl DP DEl Hu Hf m Mm Δ _ _ ns0 HMm HIGC HNga Hns0) as Hgn.
  assert (HMt' : Δ ⊢ M[σ] : im_ty_at p m Mm (List.map (fun U => U[σ]) Us) (List.map (fun N => N[σ]) Ns)).
  { assert (H : Δ ⊢ M[σ] : (ind_mty p D m Us Ns)[σ]) by mauto 2.
    rewrite ind_mty_sub in H by assumption; unfold ind_mty in H; rewrite HMm in H; exact H. }
  destruct (proj1 (proj1 (elim_glu_all VP p D HVP HGall Hviewsall HPD Γ RΓ HRΓ HΓs SbΓ HSbΓ RU HRU Us HUl HUs HUg Bks i HBt' HBv HBg'
                            ρ ups Hρ HUv bu u NP NEl AP AEl DP DEl Hbu Hule Hf nb Hnb) m Δ _ _ _ mv HIG)
              Mm σ oq ns0 HMm Hrvm Hgrp Hσ eq_refl HMt' Hgn Hns0 HGm) as [r a Er Ea Hper Hglr].
  rewrite (blocks_motives_nth _ _ _ Hbm) in Ea, Hglr.
  destruct (per_univ_glu_univ_elem _ _ Hper) as (P & El & HgE).
  pose proof (Hglr P El HgE) as HE.
  (** The type at the instance, against the motive at the values. *)
  assert (Hevl : ⟦ Ns ++ M :: nil ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns0 ++ mv :: nil)
    by (apply eval_exps_app; [ exact Ens | econstructor; [ exact Em | constructor ] ]).
  pose proof (Completeness.Inductives.Decl.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hevl) as Hevτ.
  destruct (Completeness.Inductives.Elim.elim_grp_of_elem _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMm HGm (decl_typed_order _ _ _ Hdt) oq Hgrp)
    as [Hgo _].
  assert (HMv : Γ ⊨ M : ind_mty p D m Us Ns) by (eapply completeness_fundamental_exp; exact HMt).
  pose proof (Completeness.Inductives.Elim.gsub_tau VP p D HVP HPD Γ HΓs Us HUl m Mm HMm HMa Ns M HNl HNs HMv) as Hgτ.
  pose proof (completeness_fundamental_exp _ _ _ (HAt m Mm bm HMm Hbm)) as HAv.
  destruct (Completeness.LogicalRelation.Telescope.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HRΓ
              (Completeness.LogicalRelation.Instance.gsub_valid Hgτ) Hρ Hevτ) as (ares & b & Eares & Eb & Hab).
  assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hba : per_univ i a ares) by (apply per_univ_sym'; exact Hab).
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ Hba HgE) as Hgres.
  refine (mk_glu_rel_exp_with_sub _ _ _ _ _ _ ares r P El Eares _ Hgres _);
    [ eapply eval_exp_elim; [ exact HUv | exact Em | exact Hgo | exact Er ] |].
  cbn [exp_sub].
  assert (HL : List.length (List.map (fun N => N[σ]) Ns ++ M[σ] :: nil) = S (im_nn Mm))
    by (rewrite List.length_app, List.length_map; cbn; lia).
  rewrite <- HL, exp_sub_qn_of_list in HE.
  rewrite exp_sub_sub.
  replace ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil) ⨟ σ])
    with ((eb_motive bm)[sb_of_list σ (List.map (fun N => N[σ]) Ns ++ M[σ] :: nil)]); [ exact HE |].
  apply exp_sub_sb_eq; rewrite sb_of_list_compose_gen, List.map_app; cbn [List.map]; apply sb_of_list_cong, sb_compose_id_left.
Qed.

(** ** The Constructor of a Record View Is Glued

    Applied to parameters and fields glued along its telescopes, the
    constructor of a record view is an element of the record view
    ([con_rview_ind_glu_elem]), so glued at the record type at the view's
    instance ([glu_at_type_all], [rview_glu_at_type]); along its
    telescopes, as for a declared member ([glu_rel_exp_con0]). *)
Section ConRviewFT.
  Variable (VP : qname -> ind_decl -> Prop).
  Hypotheses (HVP : valid_groups VP) (HGall : forall qn G, VP qn G -> glu_ind_decl G)
    (Hviewsall : forall qn G, VP qn G -> glu_views_ok qn G).
  Variables (p : qname) (D : ind_decl).
  Hypothesis (HPD : VP p D).
  Let HG := HGall _ _ HPD.
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (qr : qname) (Is : list exp) (fl : list String.string) (c : String.string) (gs : list carg).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_record qr Is fl) (Hcon : ind_con Mk c = Some gs)
    (HΨ : ⊩ cargs_ctx p D Mk gs ++ im_params D Mk).

  (** The constructor applied to glued parameters and fields is glued at
      the type at the parameters, at a level above the records' sorts. *)
  Lemma con_rview_base : forall Δ Ms vs w (i : nat) b P El, ⊢ Δ ->
      (forall j Mj qr0 Is0 fl0 R, ind_member D j = Some Mj -> im_head Mj = mh_record qr0 Is0 fl0 ->
         record_lookup gc_deps gc_stack qr0 = Some R -> forall ρ b0, ⟦ record_sort R ⟧ ρ ↘ b0 ->
         universe_index_le (Completeness.Inductives.Decl.univ_idx b0) (ul i)) ->
      glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil Ms vs ->
      Completeness.Inductives.Con.con_value p D k Mk c vs w ->
      ⟦ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) ⟧ env_args nil vs ↘ b ->
      DG b ∈ glu_univ_elem i ↘ P ↘ El ->
      (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w w) ->
      forall τ, Δ ⊢ apps (a_con p k c) Ms
        : (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list τ Ms]
        ® w ∈ El.
  Proof.
    intros Δ Ms vs w i b P El HΔ Hbnd Hgall Hw Hb Hglu HPER τ.
    pose proof (RviewEnds.rview_args_nn p D Hg k Mk qr Is fl HMk Hh) as Hnn.
    pose proof (RviewEnds.rview_args_nparams p D Hg k Mk qr Is fl HMk Hh) as Hnp.
    destruct (valid_group_records _ _ Hg _ _ _ _ _ HMk Hh) as [R HR].
    pose proof (RviewEnds.rview_args_names p D Hg k Mk qr Is fl R HMk Hh HR) as Hfl.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    assert (HassC : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    destruct (glu_args_length _ _ _ _ _ _ Hgall) as [LM LV]; rewrite List.length_app, length_cargs_ctx, length_im_params in LM, LV.
    assert (Hnp' : im_np D Mk = ind_nu D) by (unfold im_np; lia).
    rewrite Hnp' in LM, LV.
    (** The parameters, the uniform ones only, and the fields. *)
    set (Us := List.firstn (ind_nu D) Ms) in *; set (As := List.skipn (ind_nu D) Ms) in *.
    set (ups := List.firstn (ind_nu D) vs) in *; set (ws := List.skipn (ind_nu D) vs) in *.
    assert (EM : Ms = Us ++ As) by (symmetry; apply List.firstn_skipn).
    assert (EV : vs = ups ++ ws) by (symmetry; apply List.firstn_skipn).
    assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; lia).
    assert (LAs : List.length As = List.length gs) by (unfold As; rewrite List.length_skipn; lia).
    assert (Lws : List.length ws = List.length gs) by (unfold ws; rewrite List.length_skipn; lia).
    clearbody Us As ups ws; subst Ms vs.
    assert (EP : im_params D Mk = ind_uparams D) by (unfold im_params; rewrite Hnp; reflexivity).
    apply glu_args_app in Hgall as [HgP HgA]; [| exact HassP | rewrite length_im_params, Hnp'; lia | rewrite length_im_params, Hnp'; lia ].
    pose proof HgP as HUs; rewrite EP in HUs.
    pose proof (glu_args_per_tele_args _ _ _ _ _ _ (decl_closed_ass _ Hc) HUs) as Hgu.
    (** The value: the tuple of the fields. *)
    pose proof (Completeness.Inductives.Con.con_value_full_rview VP p D HVP HPD k Mk c gs HMk Hcon qr Is fl (ups ++ ws) w Hh
                  ltac:(rewrite List.length_app, Hnp'; lia) Hw) as Ew.
    rewrite skipn_app_exact in Ew by exact Hu; subst w.
    (** The type's value: the record at the view's instance. *)
    destruct (eval_mty_inv_rview p D k Mk qr Is fl _ _ _ b HMk Hh Hb) as (cs & bs & Ecs & Ebs & ->).
    rewrite Hnn in Ebs; cbn in Ebs; inversion Ebs; subst; rewrite ?List.app_nil_r in *.
    set (Z := cargs_ctx p D Mk gs ++ im_nparams Mk).
    assert (HZ : ⊨ Z ++ ind_uparams D)
      by (unfold Z; rewrite <- List.app_assoc; exact (valid_group_cargs_sem p D Hg Hcv k Mk c gs HMk Hcon)).
    destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
    assert (HlZ : List.length ws = List.length Z) by (unfold Z; rewrite List.length_app, length_cargs_ctx, Hnp; cbn; lia).
    assert (HgPA : glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil (Us ++ As) (ups ++ ws))
      by (apply glu_args_app; [ exact HassP | rewrite length_im_params, Hnp'; exact HUl | rewrite length_im_params, Hnp'; exact Hu
                              | split; assumption ]).
    assert (HE : RZ (env_args nil (ups ++ ws)) (env_args nil (ups ++ ws))).
    { apply (tele_args_env_rel _ _ _ _ _ _ HRZ HZ); [ rewrite !List.length_app, <- HlZ; unfold ind_nu in *; lia |].
      unfold Z; replace ((cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D) with (cargs_ctx p D Mk gs ++ im_params D Mk)
        by (unfold im_params; rewrite List.app_assoc; reflexivity).
      exact (glu_args_per_tele_args _ _ _ _ _ _ HassC HgPA). }
    destruct (Completeness.Inductives.ArgTypes.rview_pre_values p D Hg k Mk qr Is _ R ups Z RZ ws (im_nn Mk) (List.length gs) cs
                HMk Hh HR Hu Hgu HZ HRZ HlZ ltac:(rewrite Hnn; lia) HE Ecs) as (cups & Ecups & Hgc).
    (** The record at the view's instance at [ups], related to the type's
        value: glued the same way, the value related there. *)
    pose proof (RviewEnds.rview_args_container_uparams_len p D Hg k Mk qr Is _ R HMk Hh HR ups cups Ecups) as Lcups.
    destruct (Completeness.Inductives.ArgTypes.vrr_type_rel qr R cups cs HR Hgc Lcups) as [i1 HR1].
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
    assert (H1 : Dom d_record qr cups ≈ d_record qr cs ∈ per_univ i1) by (eexists; exact HR1).
    assert (H0 : Dom d_record qr cs ≈ d_record qr cs ∈ per_univ i) by (eexists; exact HRb).
    pose proof (per_univ_trans' _ _ _ _ _ H0 (per_univ_sym' _ _ _ H1)) as Hrel.
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ Hrel Hglu) as Hglu'.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu') as [Rb' HRb'].
    destruct Hrel as [R3 HR3].
    assert (Hww : Rb' (d_tuple (List.combine (List.map fst (record_fields R)) ws))
                      (d_tuple (List.combine (List.map fst (record_fields R)) ws))).
    { pose proof (HPER _ HRb) as Hw0.
      apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR3 HRb').
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRb HR3); exact Hw0. }
    (** The type: the record view's at the uniform parameters. *)
    assert (ET : (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list τ (Us ++ As)]
               = im_ty_at p k Mk Us nil).
    { rewrite ind_mty_sub by (first [ exact Hc | apply length_ind_uvars ]).
      unfold ind_uvars; rewrite Hnn, Nat.add_0_r, <- LAs, <- HUl, vars_from_sb_of_list_app.
      unfold ind_mty; rewrite HMk; cbn; reflexivity. }
    rewrite ET.
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMk Hh) as (gs0 & Hcs0 & _).
    assert (Hcs : im_cons Mk = (c, gs) :: nil).
    { pose proof Hcon as Hc0; unfold ind_con in Hc0; rewrite Hcs0 in Hc0 |- *; cbn in Hc0.
      destruct (String.eqb c rview_con) eqn:E; [ injection Hc0 as -> | discriminate Hc0 ].
      apply String.eqb_eq in E; rewrite E; reflexivity. }
    pose proof (RviewEnds.rview_args_len p D Hg k Mk qr Is _ R c gs HMk Hh HR Hcs) as Hlg.
    (** The families of the group, and a level above its parts. *)
    destruct (Completeness.Inductives.Model.sort_value D HD ups Hgu Hu) as [bu Hbu].
    destruct (group_fams_glu D HD Hc Hsu ups bu Hgu Hu Hbu) as (NP & NEl & AP & AEl & DP & DEl & Hf).
    destruct (nb_exists VP p D HVP HPD (Completeness.Inductives.Decl.univ_idx bu)) as [nb Hnb].
    (** The constructor's application, typed. *)
    destruct (glu_args_params_top _ _ _ _ _ HassP (decl_closed_params D k Mk Hc HMk) HgP) as [HPl0 HPty _].
    pose proof (wf_exp_eq_con_apps_member Δ p D k Mk c gs Us Us As As Hl HMk Hcon HΔ HPl0 HPl0
                  ltac:(intros j0 P0 P0' T0 E0 E0' HT0; rewrite E0 in E0'; injection E0' as <-; apply wf_exp_eq_refl;
                        eapply HPty; eassumption)
                  LAs LAs
                  ltac:(intros j0 N0 N0' T0 E0 E0' HT0; rewrite E0 in E0'; injection E0' as <-; apply wf_exp_eq_refl;
                        eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ])) as Heqc.
    rewrite List.firstn_all2, List.skipn_all2 in Heqc by lia.
    unfold ind_mty in Heqc; rewrite HMk in Heqc.
    assert (HMt : Δ ⊢ apps_exp (a_con p k c) (Us ++ As) : im_ty_at p k Mk Us nil) by (gen_presups; assumption).
    (** An element of the record view, so glued at the record type. *)
    assert (Hps : ⟦projs (List.map fst (record_fields R)) of d_tuple (List.combine (List.map fst (record_fields R)) ws) ⟧
                    gc_deps ⍮ gc_stack ↘ ws).
    { apply (proj1 (RviewEnds.record_projs_iff R _ _ ws eq_refl)).
      apply (Completeness.Records.Model.tuple_projs R (typed_nodup _ _ R (valid_rview_record_typed _ _ HR)) (record_fields R) ws eq_refl).
      lia. }
    assert (HgP0 : glu_args Δ (im_params D Mk) Id nil (Us ++ nil) (ups ++ nil)) by (rewrite !List.app_nil_r; exact HgP).
    assert (HgA0 : glu_args Δ (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ nil)) (env_args nil (ups ++ nil)) As ws)
      by (rewrite !List.app_nil_r; exact HgA).
    pose proof (con_rview_ind_glu_elem VP p D HVP HPD HG k Mk c gs HMk Hcon ups bu _ NP NEl AP AEl DP DEl Hu Hgu Hbu (universe_index_le_refl _) Hf
                  qr Is _ Δ Us nil As nil ws (apps_exp (a_con p k c) (Us ++ As)) _ Hh HΔ HUl HgP0 HgA0 Hps
                  ltac:(cbn [List.app]; exact Heqc)
                  (fun gs1 t gs2 _ => Hviewsall p D HPD ups bu _ NP NEl AP AEl DP DEl Hu Hgu Hbu (universe_index_le_refl _) Hf (ptyp_mem t)))
      as Hgi.
    pose proof (proj1 (rview_rel VP HVP p D HPD ups Hu Hgu k Mk qr Is _ cups (ul i) Rb' HMk Hh Ecups HRb' _ _) Hww) as HGm.
    pose proof (rview_mty_glu VP HVP HGall p D HPD ups Hu Hgu i Hbnd k Mk qr Is _ cups Δ Us i P El (le_n i) HMk Hh Ecups HΔ HUs Hglu')
      as HT.
    exact (proj2 (proj1 (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu _ NP NEl AP AEl DP DEl Hu Hgu Hbu (universe_index_le_refl _) Hf
                           nb (level_bound_clause _ _ _ _ Hnb) (level_bound_views _ _ _ _ Hnb) (level_bound_records _ _ _ _ Hnb))
                     k Δ Us nil _ _ Hgi) Mk qr Is _ cups i P El HMk Hh Ecups HUs HMt HGm Hglu' HT).
  Qed.

  (** The constructor of a record view is glued at its type. *)
  Lemma glu_rel_exp_con_rview0 : forall (j0 : nat), ⋅ ⊢ con_ty p D k Mk gs : Typeω@j0 -> ⋅ ⊢ a_con p k c : con_ty p D k Mk gs ->
      ⋅ ⊩ a_con p k c : con_ty p D k Mk gs.
  Proof.
    intros j0 Hj Hcty.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (HassC : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk Hin (eq_sym (List.app_nil_r gs))) as HsC.
    (** A level above the records' sorts. *)
    destruct (rviews_sort_bound VP p D HVP HPD (ind_members D) (fun Mj H => List.In_nth_error _ _ H)) as [n0 Hn0].
    pose proof HΨ as [SbC HSbC].
    assert (HSbC0 : EG (cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅ ∈ glu_ctx_env ↘ SbC) by (rewrite List.app_nil_r; exact HSbC).
    destruct (glu_ctx_env_entries_valid _ _ _ HassC HSbC0 (Nat.max j0 n0)) as (i & Hji & HAents).
    assert (Hi : ⋅ ⊢ con_ty p D k Mk gs : Typeω@i) by (eapply lift_exp_ge; [| exact Hj ]; lia).
    assert (Hg0 : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact (glu_ctx_env_wf_ctx HSbC)).
    eapply (glu_closed_const_by _ _ i (fun m0 => ⟦ a_con p k c ⟧ nil ↘ m0));
      [ reflexivity | intros; eapply con_ty_sub; eassumption | exact Hi
      | intros ρ; destruct (Completeness.Inductives.Con.con_value_start VP p D HVP HPD k Mk c HMk ρ) as (m0 & Em0 & _);
        exists m0; split; [ exact Em0 | eapply eval_con_env; exact Em0 ] |].
    intros Δ σ m0 Hσ Em0 a P El Ha Hglu.
    destruct (Completeness.Inductives.Con.con_value_start VP p D HVP HPD k Mk c HMk nil) as (m1 & Em1 & Hv1).
    assert (m1 = m0) as -> by (eapply functional_eval_exp; eassumption).
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
    pose proof Hi as Hi'; unfold con_ty in Hi'; rewrite <- ctx_pi_app in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ HassC Hi') as [HCs _].
    replace (con_ty p D k Mk gs) with ((con_ty p D k Mk gs)[σ]) by (eapply con_ty_sub; eassumption).
    unfold con_ty in Ha |- *; rewrite <- ctx_pi_app in Ha |- *.
    change (a_con p k c) with (apps (a_con p k c) nil).
    eapply (ctx_pi_glu_elem_by (Completeness.Inductives.Con.con_value p D k Mk c) (a_con p k c)
              ((cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅))
      with (Γb := ⋅) (Sb_b := nil_glu_sub_pred) (Sb := SbC) (xs := nil);
      [ reflexivity | | exact HassC | eapply glu_ctx_env_nil; [ reflexivity | exact Hg0 ] | exact HSbC0
      | exists nil; reflexivity
      | intros; eapply HAents; eassumption
      | intros; eapply HCs; eassumption
      | exact Hσ | reflexivity | exact Hv1 | | | | exact Ha | exact Hglu ].
    - intros Δ1 Γ' Sb' Δ' σ' xs x w HT _ _ HlΓ Hw.
      apply (Completeness.Inductives.Con.con_value_step VP p D HVP HPD k Mk c gs HMk Hcon xs x w);
        [ | intros * Hh'; rewrite Hh in Hh'; discriminate | exact Hw ].
      assert (List.length Γ' <= List.length ((cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅)) by (rewrite HT, List.length_app; lia).
      rewrite List.app_nil_r, List.length_app, length_cargs_ctx, length_im_params in *; lia.
    - cbn [apps_exp]; rewrite ctx_pi_app.
      change (ctx_pi (im_params D Mk) (ctx_pi (cargs_ctx p D Mk gs)
                (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))))
        with (con_ty p D k Mk gs).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hcty Hσ) as Hcσ; cbn [exp_sub] in Hcσ; exact Hcσ.
    - intros R a' Ha' HR.
      destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Hcty)) as (env_rel & Henv & j' & Hsimp).
      assert (Hnil : env_rel nil nil) by (inversion Henv; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
      destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m1 & m2 & Hm1 & Hm2 & Hmm).
      unfold con_ty in Ha1; rewrite <- ctx_pi_app in Ha1.
      assert (a1 = a') as -> by (eapply functional_eval_exp; eassumption).
      assert (m1 = m0) as -> by (eapply functional_eval_exp; eassumption).
      assert (m2 = m0) as -> by (eapply functional_eval_exp; eassumption).
      assert (Ha2' : ⟦ ctx_pi (cargs_ctx p D Mk gs ++ im_params D Mk)
                       (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk))) ⟧ nil ↘ a2)
        by (unfold con_ty in Ha2; rewrite <- ctx_pi_app in Ha2; exact Ha2).
      assert (a2 = a') as -> by (eapply functional_eval_exp; eassumption).
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR); exact Hmm.
    - intros Δ' φ Ms vs w' Hφ Hga Hw' b P' El' Hb Hglub HPb; cbn [List.map List.app] in *.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      apply (glu_args_closed_base _ _ _ Id _ _ _ HassC HsC) in Hga.
      eapply (con_rview_base Δ' Ms vs w' i b P' El' HΔ'); [ | exact Hga | exact Hw' | exact Hb | exact Hglub | exact HPb ].
      intros * HMj Hh0 HlR ρ0 b0 Eb0.
      eapply universe_index_le_trans; [ exact (Hn0 _ _ _ _ _ (List.nth_error_In _ _ HMj) Hh0 HlR _ _ Eb0) | apply universe_index_le_ul_max; cbn; lia ].
  Qed.
End ConRviewFT.

End Fixed_GCtx.

(** ** The Groups along a Sound Embedding

    The groups of a well-formed source are valid groups of the target of
    a sound embedding: as along a semantic embedding
    ([valid_groups_of_embedding]), each read at the target, valid there since
    the target is well formed. *)
Lemma valid_groups_of_glu_gctx_embedding : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> gctx_embedding Θ Ξ Θ2 Ξ2 ->
    @valid_groups (gc_mk Θ2 Ξ2) (fun qn G => ind_lookup Θ Ξ qn = Some G).
Proof.
  intros * Hg He.
  pose proof (gctx_embedding_resolution _ _ _ _ He) as Hs.
  pose proof (valid_gctx_embedding_refl _ _ (gctx_embedding_wf _ _ _ _ He)) as He2.
  constructor.
  - intros qn G Hlq.
    destruct (Completeness.Inductives.Elim.decl_of_glookup _ _ _ _ Hg Hlq) as [Hdt Hc].
    pose proof (gctx_embedding_preserves_decl_typed _ _ _ _ _ He Hdt) as Hdt2.
    pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hlq) as Hl2.
    constructor; [ exact Hl2 | exact (valid_gctx_embedding_ind_field _ _ _ _ He2 _ _ Hl2) | exact Hc | exact (decl_typed_sort_univ _ _ _ Hdt) | |
                 exact Hdt2 | exact (ind_lookup_mpath _ _ _ _ Hg Hlq) | ].
    2: { intros * HM Hh.
         destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh) as [R HR].
         pose proof (rview_record_lookup _ _ _ _ _ _ HR) as HlR.
         pose proof (record_lookup_gc_sub _ _ _ _ _ _ Hs HlR) as HlR2.
         exists R; constructor;
           [ exact HlR2 | exact (valid_gctx_embedding_record _ _ _ _ He2 _ _ HlR2)
           | exact (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) HlR)
           | exact (gctx_embedding_preserves_record_typed _ _ _ _ _ He (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR)) ]. }
    apply (@group_structure_of_typed (gc_mk Θ2 Ξ2) G Hdt2).
    intros * HM Hh Hq2.
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (D' & Mk' & Hq & _).
    pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hq) as Hq'.
    cbn in Hq2; rewrite Hq' in Hq2; injection Hq2 as <-.
    exact (gctx_embedding_preserves_decl_typed _ _ _ _ _ He (proj1 (Completeness.Inductives.Elim.decl_of_glookup _ _ _ _ Hg Hq))).
  - intros * Hlq HM Hh Hq2; cbn in Hq2 |- *.
    destruct (Completeness.Inductives.Elim.decl_of_glookup _ _ _ _ Hg Hlq) as [Hdt _].
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (D' & Mk' & Hq & _).
    pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hq) as Hq'.
    rewrite Hq' in Hq2; injection Hq2 as <-; exact Hq.
Qed.
