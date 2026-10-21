(** * The [ι] Rule of a Group

    The eliminator at a constructor of the member [m] is the constructor's
    branch at the non-uniform parameters, the arguments and the recursive
    results ([elim_ihs]): at a recursive argument [f] of a function shape,
    the recursive result is [λx. elim (f x)], under the shape's domains.
    Its value is not the eliminator's own recursive result at [f]
    ([d_ihfn]), so the rule relates the two at the type of the recursive
    result: the eliminator at its blocks moved past the domains, in an
    environment extended by the domains' values, against the eliminator at
    its own (an outer link of [Elim.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con Elim.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma eval_exps_firstn' : forall Ms ρ ms k, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ List.firstn k Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn k ms.
Proof.
  induction Ms as [| M Ms IH]; intros * H; inversion H; subst; destruct k; cbn; try constructor; [ assumption | apply IH; assumption ].
Qed.

(** ** The Eliminator at Blocks Moved by a Substitution

    The blocks [Bks] of an eliminator of the group [D] at [p], of a valid
    family [VP], valid in [Γ] at the uniform parameters [Us]: moved by a
    substitution [β] into [Ψ], the eliminator at a member [j] is valid
    there. *)
Section Blocks.
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.

  Variable (Γ : ctx) (oq : option qname) (Us : list exp) (Bks : list eblock) (i : nat).
  Hypotheses (HΓ : ⊨ Γ) (Hoq : oq = Some p \/ oq = None) (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T)
    (HBks : forall j Mj, ind_member D j = Some Mj -> exists b, List.nth_error Bks j = Some b)
    (HnmA : blocks_nm_ok D Bks)
    (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ)
    (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@i)
    (HnaA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b))
    (HBc : forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
             ⊨ elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)
    (HarA : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
              In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat)
    (HBv : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) ->
             elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B : elim_bty p j Mj c gs (eb_motive b) Us).

  Lemma elim_at_valid : forall Ψ β j Mj Ns M, gsub Ψ β Γ -> ind_member D j = Some Mj -> List.length Ns = im_nn Mj ->
      (forall k N T, List.nth_error Ns k = Some N ->
         List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (List.map (fun U => U[β]) Us)) Ns) k = Some T -> Ψ ⊨ N : T) ->
      Ψ ⊨ M : ind_mty p D j (List.map (fun U => U[β]) Us) Ns ->
      Ψ ⊨ elim_at p D oq (List.map (fun U => U[β]) Us) (blocks_sub Bks β) j M
        : (List.nth j (blocks_motives Bks) a_True)[sb_of_list β (Ns ++ M :: nil)].
  Proof.
    intros * Hβ HMj HNl HNs HM.
    set (Us0 := List.map (fun U => U[β]) Us) in *.
    set (Bks0 := blocks_sub Bks β).
    pose proof (gsub_rel_ctx_wf _ _ _ Hβ) as HΨ.
    destruct (HBks _ _ HMj) as [b Hb].
    assert (HUl0 : List.length Us0 = ind_nu D) by (unfold Us0; rewrite List.length_map; exact HUl).
    assert (HUs0 : forall k U T, List.nth_error Us0 k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us0) k = Some T ->
               Ψ ⊨ U : T).
    { intros k U' T' HU HT; unfold Us0 in HU, HT.
      rewrite <- (tele_insts_sub (ind_uparams D) 0 Id Id β Us Ua (decl_uparams_closed D Hc) ltac:(intros; lia)) in HT.
      apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
      exact (rel_exp_under_ctx_gsub Hβ (HUs _ _ _ HU HT)). }
    assert (HUU0 : forall k U U' T, List.nth_error Us0 k = Some U -> List.nth_error Us0 k = Some U' ->
               List.nth_error (tele_insts (ind_uparams D) Id Us0) k = Some T -> Ψ ⊨ U ≈ U' : T).
    { intros * HU HU' HT; rewrite HU in HU'; injection HU' as <-; exact (HUs0 _ _ _ HU HT). }
    assert (HBks0 : forall j0 Mj0, ind_member D j0 = Some Mj0 -> exists b0, List.nth_error Bks0 j0 = Some b0).
    { intros * HMj0; destruct (HBks _ _ HMj0) as [b0 Hb0]; exists (eblock_sub b0 β); unfold Bks0.
      rewrite nth_error_blocks_sub, Hb0; reflexivity. }
    assert (Hgm : forall k Mk, ind_member D k = Some Mk -> gsub (elim_mctx p D k Mk Us0 ++ Ψ) (sb_qn (S (im_nn Mk)) β) (elim_mctx p D k Mk Us ++ Γ)).
    { intros * HMk.
      pose proof (gsub_qn _ _ _ _ Hβ (elim_mctx_ass p D k Mk Us Hc HMk) (HMall _ _ HMk)) as G.
      rewrite (elim_mctx_sub p D k Mk Us β Hc HMk HUl), length_elim_mctx in G; exact G. }
    assert (HMall0 : forall k Mk, ind_member D k = Some Mk -> ⊨ elim_mctx p D k Mk Us0 ++ Ψ)
      by (intros * HMk; exact (gsub_rel_ctx_wf _ _ _ (Hgm _ _ HMk))).
    assert (HnmA0 : blocks_nm_ok D Bks0) by (apply blocks_nm_ok_sub; exact HnmA).
    assert (HAA0 : forall k Mk b1 b1', ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 -> List.nth_error Bks0 k = Some b1' ->
               elim_mctx p D k Mk Us0 ++ Ψ ⊨ eb_motive b1 ≈ eb_motive b1' : Typeω@i).
    { intros * HMk Hb1 Hb1'; rewrite Hb1 in Hb1'; injection Hb1' as <-.
      destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_motive_sub, (HnmA _ _ _ HMk Hb2).
      pose proof (rel_exp_under_ctx_gsub (Hgm _ _ HMk) (HAv _ _ _ HMk Hb2)) as H; cbn [exp_sub] in H; exact H. }
    assert (Hgb : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
               gsub (elim_bctx p D Mk gs (blocks_motives Bks0) Us0 ++ Ψ)
                 (sb_qn (cargs_nrec gs + List.length gs + im_nn Mk) β) (elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ)).
    { intros * HMk Hcon.
      pose proof (gsub_qn _ _ _ _ Hβ (elim_bctx_ass p D k Mk gs (blocks_motives Bks) Us Hc HMk) (HBc _ _ _ _ HMk Hcon)) as G.
      rewrite (elim_bctx_sub p D k Mk c gs (blocks_motives Bks) (blocks_motives Bks0) Us β Hc HMk (cons_lookup_in _ _ _ Hcon) HUl
                 (fun j0 Mj0 HMj0 => blocks_motives_sub D Bks β j0 Mj0 HnmA HMj0)), length_elim_bctx in G.
      exact G. }
    assert (HBc0 : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
               ⊨ elim_bctx p D Mk gs (blocks_motives Bks0) Us0 ++ Ψ)
      by (intros * HMk Hcon; exact (gsub_rel_ctx_wf _ _ _ (Hgb _ _ _ _ HMk Hcon))).
    assert (HnaA0 : forall k Mk b1, ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 -> brs_names (im_cons Mk) (eb_brs b1)).
    { intros * HMk Hb1; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_brs_sub; apply brs_names_sub; exact (HnaA _ _ _ HMk Hb2). }
    assert (HarA0 : forall k Mk b1 c gs n B, ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 -> ind_con Mk c = Some gs ->
               In (c, n, B) (eb_brs b1) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat).
    { intros * HMk Hb1 Hcon Hin; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_brs_sub in Hin; destruct (brs_in_sub _ _ _ _ _ Hin) as [B0 Hin0]; exact (HarA _ _ _ _ _ _ _ HMk Hb2 Hcon Hin0). }
    assert (HBB0 : forall k Mk b1 b1' c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 ->
               List.nth_error Bks0 k = Some b1' -> ind_con Mk c = Some gs ->
               brs_lookup (eb_brs b1) c = Some (n, B) -> brs_lookup (eb_brs b1') c = Some (n, B') ->
               elim_bctx p D Mk gs (blocks_motives Bks0) Us0 ++ Ψ ⊨ B ≈ B' : elim_bty p k Mk c gs (eb_motive b1) Us0).
    { intros * HMk Hb1 Hb1' Hcon Hlk Hlk'; rewrite Hb1 in Hb1'; injection Hb1' as <-; rewrite Hlk in Hlk'; injection Hlk' as <-.
      destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_brs_sub in Hlk; destruct (brs_lookup_sub_inv _ _ _ _ _ Hlk) as (B0 & Hlk0 & ->).
      pose proof (HarA _ _ _ _ _ _ _ HMk Hb2 Hcon (brs_lookup_in _ _ _ _ Hlk0)) as ->.
      pose proof (rel_exp_under_ctx_gsub (Hgb _ _ _ _ HMk Hcon) (HBv _ _ _ _ _ _ _ HMk Hb2 Hcon (brs_lookup_in _ _ _ _ Hlk0))) as H.
      replace (cargs_nrec gs + List.length gs + im_nn Mk) with (im_nn Mk + List.length gs + cargs_nrec gs) in H by lia.
      rewrite (elim_bty_sub p D k Mk c gs _ Us β Hc HMk HUl) in H.
      rewrite eb_motive_sub, (HnmA _ _ _ HMk Hb2); exact H. }
    assert (Hgr : elim_grp D (if ind_has_views D then Some p else oq) p j).
    { destruct (ind_has_views D) eqn:Hv; [ left; reflexivity |].
      destruct Hoq as [-> | ->]; [ left; reflexivity | right; split; [ reflexivity |] ].
      apply (dt_order _ _ _ Hdt _ _ HMj); exact (no_views_decl _ _ _ Hv HMj). }
    assert (Hb0 : List.nth_error Bks0 j = Some (eblock_sub b β)) by (unfold Bks0; rewrite nth_error_blocks_sub, Hb; reflexivity).
    pose proof (rel_exp_under_ctx_elim_at VP p D HP HPD Ψ _ _ j Mj (eblock_sub b β) Bks0 Bks0 Us0 Us0 Ns M M i HΨ Hgr Hgr
                  HMj Hb0 HBks0 HBks0 HUl0 HUs0 HUl0 HUU0 HNl HNs HM HnmA0 HnmA0 HMall0 HAA0 HnaA0
                  (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) HBc0 HarA0 HBB0) as H.
    rewrite eb_motive_sub, (HnmA _ _ _ HMj Hb) in H.
    replace (S (im_nn Mj)) with (List.length (Ns ++ M :: nil)) in H by (rewrite List.length_app, HNl; cbn; lia).
    rewrite exp_sub_qn_of_list in H.
    rewrite (blocks_motives_nth _ _ _ Hb); unfold elim_at; destruct (ind_has_views D); exact H.
  Qed.
End Blocks.

(** ** The Rule

    An eliminator of the member [m] at a constructor [c] of it, at the
    parameters [Ps] and the arguments [As]. *)
Section Iota.
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hl := vgr_lookup _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := vid_uparams _ HD.

  Variable (Γ : ctx) (oq : option qname) (m : nat) (Mm : imember) (bm : eblock) (Bks : list eblock)
    (c : String.string) (gs : list carg) (Ps As : list exp) (i : nat).
  Let Us := List.firstn (ind_nu D) Ps.
  Let Ns := List.skipn (ind_nu D) Ps.
  Let σP := sb_of_list Id Ps.
  Hypotheses (HΓ : ⊨ Γ) (Hgr : elim_grp D oq p m) (HMm : ind_member D m = Some Mm) (Hbm : List.nth_error Bks m = Some bm)
    (Hcon : ind_con Mm c = Some gs) (HPl : List.length Ps = im_np D Mm)
    (HPs : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊨ P : T)
    (HAl : List.length As = List.length gs)
    (HAs : forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mm gs) σP As) k = Some T -> Γ ⊨ N : T)
    (HBks : forall j Mj, ind_member D j = Some Mj -> exists b, List.nth_error Bks j = Some b)
    (HnmA : blocks_nm_ok D Bks)
    (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ)
    (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@i)
    (HnaA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b))
    (HBc : forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
             ⊨ elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)
    (HarA : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
              In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat)
    (HBv : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) ->
             elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B : elim_bty p j Mj c gs (eb_motive b) Us).
  Let Hoq := elim_grp_oq _ _ _ _ Hgr.
  Let HΨ := vg_cargs_sem p D Hvg Hcv m Mm c gs HMm Hcon.

  Lemma i_HUl : List.length Us = ind_nu D.
  Proof. unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia. Qed.

  Lemma i_HNl : List.length Ns = im_nn Mm.
  Proof. unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia. Qed.

  Lemma i_HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T.
  Proof. exact (proj1 (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs)). Qed.

  Lemma i_HNs : forall k N T, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
      Γ ⊨ N : T.
  Proof. exact (proj2 (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs)). Qed.

  Lemma i_Ps : Ps = Us ++ Ns.
  Proof. symmetry; apply List.firstn_skipn. Qed.

  (** *** The Parameters and the Arguments Before a Position *)
  Lemma gsub_P : gsub Γ σP (im_params D Mm ++ Γ).
  Proof.
    apply gsub_closed_inst; [ exact (member_params_ass D Hc _ _ HMm) | exact (vid_params _ HD _ _ HMm) | exact HΓ
                            | rewrite length_im_params; exact HPl | exact HPs ].
  Qed.

  Lemma gsub_args_pre : forall k, k <= List.length gs ->
      gsub Γ (sb_of_list σP (List.firstn k As)) (cargs_ctx p D Mm (List.firstn k gs) ++ im_params D Mm ++ Γ).
  Proof.
    intros k Hk.
    assert (Heq : gs = List.firstn k gs ++ List.skipn k gs) by (symmetry; apply List.firstn_skipn).
    pose proof (cargs_prefix_sem D p Mm gs HΨ _ _ Heq) as Hp.
    assert (Hpa : tele_ass (cargs_ctx p D Mm (List.firstn k gs) ++ im_params D Mm))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMm) ]).
    destruct (closed_app_sem _ _ Hpa Hp HΓ) as [HpΓ _]; rewrite <- List.app_assoc in HpΓ.
    apply gsub_of_list; [ exact gsub_P | apply cargs_ctx_aux_ass | exact HpΓ
                        | rewrite List.length_firstn, length_cargs_ctx, List.length_firstn; lia |].
    intros j N T HN HT.
    assert (Hj : j < List.length (List.firstn k As)) by (apply List.nth_error_Some; congruence).
    rewrite List.length_firstn in Hj.
    apply (HAs j); [ rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec j k); [ exact HN | lia ] |].
    rewrite Heq at 1; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r.
    rewrite <- (List.firstn_skipn k As), tele_insts_app;
      [| apply cargs_ctx_aux_ass | rewrite List.length_firstn, length_cargs_ctx_aux, List.length_firstn; lia ].
    rewrite List.nth_error_app1; [ exact HT |].
    rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux, !List.length_firstn; lia.
  Qed.

  (** The substitution of a shape's components after [gs1]. *)
  Lemma gsub_sigt : forall gs1 gs2, gs = gs1 ++ gs2 ->
      gsub Γ (cargs_sub σP gs1 As) (cargs_strat gs1 ++ im_params D Mm ++ Γ).
  Proof.
    intros * Heq.
    assert (Lg1 : List.length gs1 <= List.length gs) by (rewrite Heq, List.length_app; lia).
    pose proof (gsub_args_pre _ Lg1) as Hg.
    assert (Hfg : List.firstn (List.length gs1) gs = gs1) by (rewrite Heq; apply firstn_app_exact; reflexivity).
    rewrite Hfg in Hg.
    destruct (gsub_props Hg) as [Hgv Hgl].
    pose proof (cargs_prefix_sem D p Mm gs HΨ _ _ Heq) as Hp.
    assert (Hpa : tele_ass (cargs_ctx p D Mm gs1 ++ im_params D Mm))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMm) ]).
    destruct (closed_app_sem _ _ Hpa Hp HΓ) as [HpΓ _]; rewrite <- List.app_assoc in HpΓ.
    assert (HSa : tele_ass (cargs_strat gs1 ++ im_params D Mm))
      by (apply List.Forall_app; split; [ rewrite cargs_strat_nonrec; apply List.Forall_rev, tele_ass_map_ass
                                       | exact (member_params_ass D Hc _ _ HMm) ]).
    assert (HSs : ⊨ cargs_strat gs1 ++ im_params D Mm)
      by (rewrite (nonrec_args_prefix_cargs_strat gs1 gs2), <- Heq; apply (vid_strat _ HD _ _ _ _ _ HMm Hcon);
          rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    destruct (closed_app_sem _ _ HSa HSs HΓ) as [HSΓ _]; rewrite <- List.app_assoc in HSΓ.
    pose proof (gsub_wk _ _ _ (cargs_wk_ext VP p D HP HPD Γ HΓ Us i_HUl m Mm c gs HMm Hcon gs1 gs2 Heq) HpΓ HSΓ) as G0.
    eapply gsub_eq; [ exact (gsub_comp _ _ _ _ _ G0 HΓ Hgv Hgl) |].
    rewrite <- (cargs_sub_firstn gs1 σP As).
    apply cargs_sub_pat; rewrite List.length_firstn; lia.
  Qed.

  Lemma eval_sigt : forall gs1 gs2 ρ ps avs, gs = gs1 ++ gs2 ->
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ps -> ⟦ As ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ avs ->
      ⟦ cargs_sub σP gs1 As ⟧s ρ ↘ env_args ρ (ps ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)).
  Proof.
    intros * Heq Hp Ha.
    assert (Lg1 : List.length gs1 <= List.length As) by (rewrite HAl, Heq, List.length_app; lia).
    rewrite <- (cargs_sub_firstn gs1 σP As).
    eapply eval_sub_sb_eq; [ apply cargs_sub_pat; rewrite List.length_firstn; lia |].
    pose proof (eval_exps_firstn' As ρ avs (List.length gs1) Ha) as Ha1.
    assert (La1 : List.length (List.firstn (List.length gs1) avs) = List.length gs1)
      by (rewrite List.length_firstn, (eval_exps_length _ _ _ Ha); lia).
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hp) Ha1) as Hτ.
    replace (env_args ρ (ps ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)))
      with (⟪wk_pat (cargs_pat gs1)⟫ (env_args (env_args ρ ps) (List.firstn (List.length gs1) avs)))
      by (rewrite eval_wk_pat_args by exact La1; rewrite <- env_args_app; reflexivity).
    intros x; cbn [sb_compose sb_of_wk sentry_sub]; rewrite (eval_wk_entry _ _ (wk_mono_pat _)).
    exact (Hτ _).
  Qed.

  (** *** A Recursive Argument and Its Recursive Result

      The recursive argument [Mt] of shape [t] after the arguments [gs1],
      its shape ending in the member [ptyp_mem t] ([Mj]); [Ψ kd] is [Γ]
      extended by the shape's first [kd] domains. *)
  Section RecArg.
    #[local] Set Default Proof Using "All".
    Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
    Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
    Variable (Mj : imember).
    Hypothesis (HMj : ind_member D (ptyp_mem t) = Some Mj).
    Let K := List.length (cargs_nonrec gs1).
    Let L := List.length (ptyp_doms t).
    Let σt := cargs_sub σP gs1 As.
    Let Mt := List.nth (List.length gs1) As (a_var 0).
    Let Ψ kd := tele_sub (doms_ctx (List.firstn kd (ptyp_doms t))) σt ++ Γ.
    Let Tg := cargs_strat gs1 ++ im_params D Mm ++ Γ.
    Let Ps' := List.map (fun P => P[sb_qn L σt]) (ptyp_ps t).
    Let xL := apps_vars_iter L Mt.

    Lemma r_strat : cargs_strat gs1 = nonrec_args_prefix gs (List.length (cargs_nonrec gs1)).
    Proof. rewrite Heq; apply nonrec_args_prefix_cargs_strat. Qed.

    Lemma r_HK : K <= List.length (cargs_nonrec gs).
    Proof. unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia. Qed.

    Lemma r_dctx : forall kd, kd <= L -> ⊨ doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mm.
    Proof. intros kd Hk; rewrite r_strat; exact (vid_dctx _ HD m Mm c gs gs1 t gs2 kd HMm Hcon Heq Hk). Qed.

    Lemma r_dass : forall kd, tele_ass (doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mm).
    Proof.
      intros; apply List.Forall_app; split; [ apply List.Forall_rev, tele_ass_map_ass |].
      apply List.Forall_app; split; [ rewrite cargs_strat_nonrec; apply List.Forall_rev, tele_ass_map_ass
                                   | exact (member_params_ass D Hc _ _ HMm) ].
    Qed.

    Lemma r_dlen : forall kd, kd <= L -> List.length (doms_ctx (List.firstn kd (ptyp_doms t))) = kd.
    Proof. intros; rewrite doms_ctx_length, List.length_firstn; unfold L in *; lia. Qed.

    Lemma r_dctxΓ : forall kd, kd <= L -> ⊨ doms_ctx (List.firstn kd (ptyp_doms t)) ++ Tg.
    Proof.
      intros kd Hk; destruct (closed_app_sem _ _ (r_dass kd) (r_dctx kd Hk) HΓ) as [H _].
      unfold Tg; rewrite <- !List.app_assoc in H; exact H.
    Qed.

    Lemma r_gsub : forall kd, kd <= L -> gsub (Ψ kd) (sb_qn kd σt) (doms_ctx (List.firstn kd (ptyp_doms t)) ++ Tg).
    Proof.
      intros kd Hk; unfold Ψ; rewrite <- (r_dlen kd Hk) at 2.
      apply gsub_qn; [ exact (gsub_sigt gs1 _ Heq) | unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass | exact (r_dctxΓ kd Hk) ].
    Qed.

    Lemma r_HΨ : forall kd, kd <= L -> ⊨ Ψ kd.
    Proof. intros kd Hk; exact (gsub_rel_ctx_wf _ _ _ (r_gsub kd Hk)). Qed.

    Lemma r_wk : forall kd, kd <= L -> Ψ kd ⊨ʷ (wk_shiftn kd) : Γ.
    Proof.
      intros kd Hk; pose proof (rel_wk_under_ctx_shiftn _ _ (r_HΨ kd Hk)) as H.
      rewrite length_tele_sub, (r_dlen kd Hk) in H; exact H.
    Qed.

    Lemma r_base : forall kd, kd <= L -> gsub (Ψ kd) (sb_shift_iter kd Id) Γ.
    Proof.
      intros kd Hk; eapply gsub_eq; [ exact (gsub_wk _ _ _ (r_wk kd Hk) (r_HΨ kd Hk) HΓ) |].
      rewrite sb_shift_iter_eq, sb_compose_id_left; reflexivity.
    Qed.

    Lemma r_uc : shape_uc D Us (cargs_strat gs1 ++ im_params D Mm) σt Id.
    Proof.
      intros y Hy.
      assert (Lg1 : List.length gs1 <= List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      unfold σt; rewrite <- (cargs_sub_firstn gs1 σP As).
      rewrite <- (cargs_sub_pat gs1 σP (List.firstn (List.length gs1) As)) by (rewrite List.length_firstn; lia).
      cbn [sb_compose sb_of_wk sentry_sub].
      replace (y + (List.length (cargs_strat gs1 ++ im_params D Mm) - ind_nu D)) with (pat_nargs (cargs_pat gs1) + (im_nn Mm + y))
        by (rewrite List.length_app, length_im_params, pat_nargs_cargs_pat; unfold im_np; lia).
      rewrite wk_pat_ge, length_cargs_pat.
      replace (List.length gs1 + (im_nn Mm + y)) with (List.length (List.firstn (List.length gs1) As) + (im_nn Mm + y))
        by (rewrite List.length_firstn; lia).
      rewrite sb_of_list_ge; unfold σP; rewrite i_Ps, sb_of_list_app.
      replace (im_nn Mm + y) with (List.length Ns + y) by (rewrite i_HNl; lia).
      rewrite sb_of_list_ge; cbn [sb_compose]; rewrite sentry_sub_id; reflexivity.
    Qed.

    Lemma r_ucK : forall kd, kd <= L ->
        shape_uc D Us (doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mm) (sb_qn kd σt) (sb_shift_iter kd Id).
    Proof.
      induction kd as [| kd IH]; intros Hk; [ exact r_uc |].
      destruct (nth_error_lt_some' (ptyp_doms t) kd ltac:(unfold L in Hk; lia)) as [Bk HBk].
      rewrite (firstn_S_snoc _ _ _ HBk), doms_ctx_snoc; cbn [sb_qn sb_shift_iter List.app].
      apply shape_uc_pi; [| apply IH; lia ].
      rewrite !List.length_app, length_im_params; unfold im_np; lia.
    Qed.

    Lemma r_Mt : Γ ⊨ Mt : ptyp_ty_at p D Us σt t.
    Proof.
      assert (Hk : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' As (List.length gs1) Hk) as [M HM0].
      unfold Mt; rewrite (List.nth_error_nth _ _ _ HM0).
      set (As1 := List.firstn (List.length gs1) As).
      assert (LAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      assert (HAeq : As = As1 ++ M :: List.skipn (S (List.length gs1)) As)
        by (unfold As1; rewrite <- (skipn_nth_cons' _ _ _ HM0), List.firstn_skipn; reflexivity).
      apply (HAs (List.length gs1)); [ exact HM0 |].
      rewrite Heq at 1; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; cbn [cargs_ctx_aux].
      rewrite HAeq.
      rewrite (tele_insts_app (cargs_ctx_aux p D (im_nn Mm) (true :: cargs_pat gs1) gs2
                                 ++ ce_ass (ptyp_ty p D (im_nn Mm) (cargs_pat gs1) t) :: nil)
                 (cargs_ctx_aux p D (im_nn Mm) nil gs1)); [| apply cargs_ctx_aux_ass | rewrite length_cargs_ctx_aux; exact LAs1 ].
      rewrite List.nth_error_app2 by (rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux; lia).
      rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux, LAs1.
      replace (List.length gs1 - Nat.min (List.length gs1) (List.length gs1)) with 0 by lia.
      change (M :: List.skipn (S (List.length gs1)) As) with ((M :: nil) ++ List.skipn (S (List.length gs1)) As).
      rewrite tele_insts_app; [| repeat constructor; eexists; reflexivity | reflexivity ].
      cbn; unfold tele_insts at 1; cbn [List.rev List.app tele_insts_aux]; f_equal.
      rewrite ptyp_ty_eq_at, ptyp_ty_at_sub by (try exact Hc; apply length_ind_uvars).
      rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ σt); [ f_equal |].
      - unfold ind_uvars; rewrite length_cargs_pat.
        unfold σP; rewrite <- sb_of_list_app, i_Ps, <- List.app_assoc.
        replace (List.length gs1 + im_nn Mm) with (List.length (Ns ++ As1)) by (rewrite List.length_app, i_HNl; lia).
        rewrite <- i_HUl; apply vars_from_sb_of_list_app.
      - unfold σt; rewrite <- (cargs_sub_firstn gs1 σP As); fold As1.
        apply cargs_sub_pat; exact LAs1.
    Qed.

    Lemma r_tele : ptyp_tele t = doms_ctx (List.firstn L (ptyp_doms t)).
    Proof. unfold ptyp_tele, L; rewrite List.firstn_all; reflexivity. Qed.

    Lemma r_plen : List.length (ptyp_ps t) = im_nn Mj.
    Proof.
      destruct (length_rec_ps D HD m Mm HMm c gs gs1 t gs2 Hcon Heq) as (Mj' & HMj' & H).
      rewrite HMj in HMj'; injection HMj' as <-; exact H.
    Qed.

    Lemma r_Ps_valid : forall kk P T0, List.nth_error (ptyp_ps t) kk = Some P ->
        List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mm))) (ptyp_ps t)) kk = Some T0 ->
        ptyp_tele t ++ Tg ⊨ P : T0.
    Proof.
      intros kk P0 T0 HP0 HT; pose proof (vid_rec _ HD m Mm c gs gs1 t gs2 Mj kk P0 T0 HMm Hcon Heq HMj HP0 HT) as H.
      rewrite <- r_strat in H.
      pose proof (r_dass L) as Ha; pose proof (r_dctx L (le_n _)) as Hs; rewrite <- r_tele in Ha, Hs.
      pose proof (closed_app_valid _ _ _ _ _ Ha Hs HΓ H) as H'; unfold Tg; rewrite <- !List.app_assoc in H'; exact H'.
    Qed.

    (** The leaf's parameters, at instances agreeing with the shape's
        substitution on the uniform parameters. *)
    Lemma r_Ps_gen : forall σ', (forall y, y < ind_nu D -> sentry_exp ((sb_of_list Id Us ⨟ sb_shift_iter L Id) y) = sentry_exp (σ' y)) ->
        forall kk N T0, List.nth_error Ps' kk = Some N -> List.nth_error (tele_insts (im_nparams Mj) σ' Ps') kk = Some T0 -> Ψ L ⊨ N : T0.
    Proof.
      intros σ' Hσ' kk N T0 HN HT.
      unfold Ps' in HN, HT; apply nth_error_map_inv in HN as (P0 & HPk & ->).
      set (σ0 := sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mm))).
      assert (HT1 : exists T1, List.nth_error (tele_insts (im_nparams Mj) σ0 (ptyp_ps t)) kk = Some T1).
      { assert (Hm : kk < List.length (ptyp_ps t)) by (apply List.nth_error_Some; congruence).
        apply nth_error_lt_some'; rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMj).
        rewrite length_im_nparams, <- r_plen; lia. }
      destruct HT1 as [T1 HT1].
      pose proof (r_Ps_valid _ _ _ HPk HT1) as HP1.
      pose proof (r_gsub L (le_n _)) as Hg.
      replace (doms_ctx (List.firstn L (ptyp_doms t)) ++ Tg) with (ptyp_tele t ++ Tg) in Hg by (rewrite r_tele; reflexivity).
      pose proof (rel_exp_under_ctx_gsub Hg HP1) as HP2.
      replace T0 with T1[sb_qn L σt]; [ exact HP2 |].
      rewrite <- (tele_insts_sub_mvc (im_nparams Mj) (ind_nu D) σ0 σ' (sb_qn L σt) (ptyp_ps t)) in HT.
      + apply nth_error_map_inv in HT as (T2 & HT2 & ->); rewrite HT1 in HT2; injection HT2 as ->; reflexivity.
      + exact (decl_closed_nparams_ass D Hc _ _ HMj).
      + exact (decl_nparams_mvc _ _ _ Hdt _ _ HMj).
      + exact (decl_closed_nparams_scoped D Hc _ _ HMj).
      + intros y Hy; unfold σ0; cbn [sb_of_wk sentry_sub wk_shiftn].
        pose proof (r_ucK L (le_n _) y Hy) as H; rewrite <- Hσ' by exact Hy.
        etransitivity; [| exact H ]; f_equal; f_equal.
        rewrite !List.length_app, (r_dlen L (le_n _)), cargs_strat_nonrec, List.length_rev, List.length_map, length_im_params;
          unfold ptyp_depth, K, im_np; fold L; lia.
    Qed.

    Lemma r_UsL : List.map (fun U => U[wk_shiftn L]ʷ) Us = List.map (fun U => U[sb_shift_iter L Id]) Us.
    Proof.
      apply List.map_ext; intros U; rewrite <- exp_sub_of_wk; apply exp_sub_sb_eq.
      rewrite sb_shift_iter_eq, sb_compose_id_left; reflexivity.
    Qed.

    Lemma r_nsub : gsub (Ψ L) (sb_of_list (sb_shift_iter L Id) Ps') (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ).
    Proof.
      apply gsub_of_list; [ exact (r_base L (le_n _)) | apply tele_ass_sub, (decl_closed_nparams_ass D Hc _ _ HMj)
                          | exact (rel_ctx_wf_tail (HMall _ _ HMj))
                          | unfold Ps'; rewrite List.length_map, length_tele_sub, length_im_nparams; exact r_plen |].
      intros kk N T0 HN HT; rewrite tele_insts_tele_sub in HT.
      exact (r_Ps_gen _ (fun y _ => eq_refl) kk N T0 HN HT).
    Qed.

    Lemma r_x_typed : Ψ L ⊨ xL : ind_mty p D (ptyp_mem t) (List.map (fun U => U[sb_shift_iter L Id]) Us) Ps'.
    Proof.
      pose proof r_Mt as HMt.
      rewrite ptyp_ty_at_ctx_pi in HMt; unfold ptyp_depth in HMt; fold L in HMt.
      pose proof (HMall _ _ HMj) as HM'; unfold elim_mctx in HM'; cbn [List.app] in HM'.
      destruct (rel_ctx_wf_ass_inv HM') as [jI HIT].
      pose proof (rel_exp_under_ctx_gsub r_nsub HIT) as HIT'.
      rewrite ind_head_inst in HIT' by (try exact Hc; try exact i_HUl; unfold Ps'; rewrite List.length_map; exact r_plen).
      rewrite <- r_UsL in HIT' |- *.
      unfold xL; rewrite apps_vars_iter_eq.
      unfold Ψ in HIT' |- *; rewrite <- r_tele in HIT' |- *.
      apply (valid_apps_vars L (tele_sub (ptyp_tele t) σt) Γ _ jI Mt);
        [ rewrite length_tele_sub, r_tele; exact (r_dlen L (le_n _))
        | apply tele_ass_sub; unfold ptyp_tele, doms_ctx; apply List.Forall_rev, tele_ass_map_ass
        | pose proof (r_HΨ L (le_n _)) as H; unfold Ψ in H; rewrite <- r_tele in H; exact H
        | exact HIT' | exact HMt ].
    Qed.

    (** The end: the eliminator at its blocks moved past the domains, at the
        argument applied to them. *)
    Lemma r_leaf : Ψ L ⊨ elim_at p D oq (List.map (fun U => U[sb_shift_iter L Id]) Us) (blocks_sub Bks (sb_shift_iter L Id)) (ptyp_mem t) xL
        : (List.nth (ptyp_mem t) (blocks_motives Bks) a_True)[sb_of_list (sb_shift_iter L Id) (Ps' ++ xL :: nil)].
    Proof.
      apply (elim_at_valid VP p D HP HPD Γ oq Us Bks i Hoq i_HUl i_HUs HBks HnmA HMall HAv HnaA HBc HarA HBv
               (Ψ L) (sb_shift_iter L Id) (ptyp_mem t) Mj Ps' xL (r_base L (le_n _)) HMj).
      - unfold Ps'; rewrite List.length_map; exact r_plen.
      - apply r_Ps_gen; intros y Hy; cbn [sb_compose].
        rewrite sb_of_list_map by (rewrite i_HUl; lia); rewrite <- sentry_exp_sub; reflexivity.
      - exact r_x_typed.
    Qed.

    (** The recursive result after [kd] domains. *)
    Lemma r_tm : forall n kd, kd + n = L -> forall Us0 Bks0,
        Us0 = List.map (fun U => U[sb_shift_iter kd Id]) Us -> Bks0 = blocks_sub Bks (sb_shift_iter kd Id) ->
        Ψ kd ⊨ ptyp_ih p D oq Us0 Bks0 (sb_qn kd σt) (apps_vars_iter kd Mt) (ptyp_skip kd t)
          : ptyp_ihty (blocks_motives Bks) (sb_shift_iter kd Id) (sb_qn kd σt) (apps_vars_iter kd Mt) (ptyp_skip kd t).
    Proof.
      induction n as [| n IH]; intros kd Hkn * HU0 HB0; subst Us0 Bks0.
      - assert (Hk : kd = L) by lia; rewrite Hk.
        pose proof (ptyp_skip_end t) as HsL; change (List.length (ptyp_doms t)) with L in HsL; rewrite HsL.
        cbn [ptyp_ih ptyp_ihty]; exact r_leaf.
      - assert (Hk : kd < L) by lia.
        destruct (ptyp_skip_lt kd t Hk) as (Bk & HBk & Hs); rewrite Hs.
        cbn [ptyp_ih ptyp_ihty].
        destruct (vid_dom _ HD m Mm c gs gs1 t gs2 kd Bk HMm Hcon Heq HBk) as (_ & j & HBv0); rewrite <- r_strat in HBv0.
        pose proof (closed_app_valid _ _ _ _ _ (r_dass kd) (r_dctx kd ltac:(lia)) HΓ HBv0) as HBv1.
        rewrite <- !List.app_assoc in HBv1; fold Tg in HBv1.
        pose proof (rel_exp_under_ctx_gsub (r_gsub kd ltac:(lia)) HBv1) as HBk'; cbn [exp_sub] in HBk'.
        assert (HUs1 : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[sb_shift_iter kd Id]) Us)
                       = List.map (fun U => U[sb_shift_iter (S kd) Id]) Us)
          by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
        assert (HBs1 : blocks_wk (blocks_sub Bks (sb_shift_iter kd Id)) ↑ = blocks_sub Bks (sb_shift_iter (S kd) Id))
          by (rewrite <- blocks_sub_of_wk, blocks_sub_sub; reflexivity).
        pose proof (IH (S kd) ltac:(lia) _ _ HUs1 HBs1) as H.
        unfold Ψ in H; rewrite (firstn_S_snoc _ _ _ HBk), doms_ctx_snoc in H; cbn [tele_sub List.app centry_sub] in H.
        rewrite (r_dlen kd ltac:(lia)) in H.
        exact (rel_exp_under_ctx_fn_cong HBk' H).
    Qed.
  End RecArg.

  (** *** The Instance of the Branch's Context *)
  Lemma gsub_args : gsub Γ (sb_of_list Id (Ns ++ As)) (cinst Γ p D Mm Us gs).
  Proof.
    pose proof (gsub_ns VP p D HP HPD Γ HΓ Us m Mm HMm (HMall _ _ HMm) Ns i_HNl i_HNs) as HgN.
    pose proof (HBc _ _ _ _ HMm Hcon) as HB; unfold elim_bctx in HB.
    assert (HC : ⊨ cinst Γ p D Mm Us gs)
      by (unfold cinst; rewrite <- !List.app_assoc in HB; exact (rel_ctx_wf_app_r _ _ HB)).
    rewrite sb_of_list_app; unfold cinst in HC |- *.
    apply gsub_of_list; [ exact HgN | apply tele_ass_sub, cargs_ctx_aux_ass | exact HC
                        | rewrite length_tele_sub, length_cargs_ctx; exact HAl |].
    intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
    rewrite (tele_insts_sb_eq _ _ σP) in HT; [ exact (HAs _ _ _ HN HT) |].
    rewrite <- i_HNl; etransitivity; [ apply sb_qn_of_list |].
    etransitivity; [ apply sb_of_list_cong; intros x; cbn; apply sentry_sub_id |].
    unfold σP; rewrite i_Ps, <- sb_of_list_app; reflexivity.
  Qed.

  Lemma ihs_pre : forall gs1 gs2, gs = gs1 ++ gs2 ->
      ⊨ ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Mm Us gs.
  Proof.
    intros * Heq; pose proof (HBc _ _ _ _ HMm Hcon) as H; unfold elim_bctx in H.
    replace (ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs)
      with (ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1 ++ nil) (0 + cargs_nrec gs1) gs2
              ++ ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1) in H
      by (rewrite <- ihs_ctx_aux_app, <- Heq; reflexivity).
    unfold cinst; rewrite <- !List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  Lemma gsub_iota_ihs : forall rest gs1 L0, gs = gs1 ++ rest -> List.length L0 = cargs_nrec gs1 ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0))
        (ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Mm Us gs) ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0 ++ elim_ihs p D oq Us Bks (cargs_sub σP gs1 As) rest (List.skipn (List.length gs1) As)))
        (ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 (gs1 ++ rest) ++ cinst Γ p D Mm Us gs).
  Proof.
    induction rest as [| [B0 | t] rest IH]; intros gs1 L0 Heq HL Hδ.
    - cbn [elim_ihs]; rewrite !List.app_nil_r; exact Hδ.
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      assert (Hcs : cargs_sub σP (gs1 ++ ca_arg B0 :: nil) As = (cargs_sub σP gs1 As ,, a)).
      { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
        apply cargs_sub_snoc_arg; rewrite List.length_firstn; lia. }
      replace (S (List.length gs1)) with (List.length (gs1 ++ ca_arg B0 :: nil)) by (rewrite List.length_app; cbn; lia).
      rewrite <- Hcs.
      replace (gs1 ++ ca_arg B0 :: rest) with ((gs1 ++ ca_arg B0 :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_app; cbn; lia |].
      rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app]; exact Hδ.
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      set (σg := cargs_sub σP gs1 As).
      assert (Hcs : cargs_sub σP (gs1 ++ ca_rec t :: nil) As = σg).
      { unfold σg; rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
        apply cargs_sub_snoc_rec; rewrite List.length_firstn; lia. }
      assert (Heq0 : gs = gs1 ++ ca_rec t :: rest) by exact Heq.
      destruct (length_rec_ps D HD m Mm HMm c gs gs1 t rest Hcon Heq0) as (Mj & HMj & _).
      set (E := ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1) in *.
      set (θ := ihs_sub (im_nn Mm) Us (List.length gs) (cargs_pat gs1) (cargs_nrec gs1)).
      set (b := cargs_nrec gs1 + List.length gs + im_nn Mm).
      set (x := cargs_nrec gs1 + List.length gs - 1 - List.length (cargs_pat gs1)).
      assert (Hent : ihs_ctx_aux (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 (gs1 ++ ca_rec t :: nil)
                     = ce_ass (ptyp_ihty (blocks_motives Bks) (sb_of_wk (wk_shiftn b)) θ (a_var x) t) :: E)
        by (unfold E, θ, b, x; rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app Nat.add]; reflexivity).
      pose proof (ihs_pre (gs1 ++ ca_rec t :: nil) rest ltac:(rewrite <- List.app_assoc; exact Heq)) as HCT.
      rewrite Hent in HCT; cbn [List.app] in HCT.
      destruct (rel_ctx_wf_ass_inv HCT) as [j HTj].
      set (δ := sb_of_list Id (Ns ++ As ++ L0)) in *.
      assert (Hθδ : sb_eq (θ ⨟ δ) σg).
      { unfold θ, δ, σg; rewrite <- HL.
        exact (ihs_sub_iota D Mm Ps As L0 gs1 gs HPl HAl ltac:(rewrite Heq, List.length_app; lia)). }
      assert (Hbδ : sb_eq (sb_of_wk (wk_shiftn b) ⨟ δ) Id).
      { intros z; unfold b, δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        replace (z + (cargs_nrec gs1 + List.length gs + im_nn Mm)) with (List.length (Ns ++ As ++ L0) + z)
          by (rewrite !List.length_app, i_HNl, HAl, HL; lia).
        rewrite sb_of_list_ge; reflexivity. }
      assert (Hidx : (a_var x)[δ] = a).
      { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ, x.
        rewrite (sb_of_list_nth _ _ _ a) by (rewrite !List.length_app, i_HNl, HAl, HL, Heq, List.length_app, length_cargs_pat; cbn; lia).
        rewrite !List.length_app, i_HNl, HAl, HL, length_cargs_pat.
        replace (im_nn Mm + (List.length gs + cargs_nrec gs1) - 1 - (cargs_nrec gs1 + List.length gs - 1 - List.length gs1))
          with (im_nn Mm + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
        cbn [sentry_exp]; rewrite List.app_nth2 by (rewrite i_HNl; lia); rewrite i_HNl.
        replace (im_nn Mm + List.length gs1 - im_nn Mm) with (List.length gs1) by lia.
        rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact Ha. }
      pose proof (r_tm gs1 t rest Heq0 Mj HMj _ 0 eq_refl Us Bks
                    ltac:(cbn [sb_shift_iter]; rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id; reflexivity)
                    ltac:(cbn [sb_shift_iter]; rewrite blocks_sub_id; reflexivity)) as Hih.
      cbn [sb_shift_iter apps_vars_iter sb_qn ptyp_skip List.firstn doms_ctx List.map List.rev tele_sub List.app] in Hih.
      rewrite (List.nth_error_nth _ _ _ Ha) in Hih; fold σg in Hih.
      replace (Ns ++ As ++ L0 ++ ptyp_ih p D oq Us Bks σg a t :: elim_ihs p D oq Us Bks σg rest (List.skipn (S (List.length gs1)) As))
        with (Ns ++ As ++ (L0 ++ ptyp_ih p D oq Us Bks σg a t :: nil) ++ elim_ihs p D oq Us Bks σg rest (List.skipn (S (List.length gs1)) As))
        by (rewrite <- !List.app_assoc; reflexivity).
      replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec t :: nil)) by (rewrite List.length_app; cbn; lia).
      rewrite <- Hcs.
      replace (gs1 ++ ca_rec t :: rest) with ((gs1 ++ ca_rec t :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite List.length_app, cargs_nrec_app, HL; cbn; lia |].
      rewrite Hent, Hcs.
      replace (Ns ++ As ++ L0 ++ ptyp_ih p D oq Us Bks σg a t :: nil) with ((Ns ++ As ++ L0) ++ ptyp_ih p D oq Us Bks σg a t :: nil)
        by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (sb_of_list_app (Ns ++ As ++ L0) (ptyp_ih p D oq Us Bks σg a t :: nil) Id).
      change (sb_of_list (sb_of_list Id (Ns ++ As ++ L0)) (ptyp_ih p D oq Us Bks σg a t :: nil))
        with (sb_of_list Id (Ns ++ As ++ L0) ,, ptyp_ih p D oq Us Bks σg a t).
      cbn [List.app]; eapply gsub_ass; [ exact Hδ | exact HTj |].
      fold δ; rewrite ptyp_ihty_sub, Hidx.
      rewrite (ptyp_ihty_sb_eq t _ (sb_of_wk (wk_shiftn b) ⨟ δ) Id (θ ⨟ δ) σg a); [ exact Hih | exact Hbδ | exact Hθδ ].
  Qed.

  Lemma gsub_iota : gsub Γ (sb_of_list Id (Ns ++ As ++ elim_ihs p D oq Us Bks σP gs As))
      (elim_bctx p D Mm gs (blocks_motives Bks) Us ++ Γ).
  Proof.
    pose proof gsub_args as Hδ.
    rewrite <- (List.app_nil_r As) in Hδ at 1.
    pose proof (gsub_iota_ihs gs nil nil eq_refl eq_refl ltac:(cbn [ihs_ctx_aux List.app]; exact Hδ)) as H.
    cbn [List.app List.skipn List.length cargs_sub] in H.
    unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
  Qed.

  (** The constructor applied, the scrutinee. *)
  Lemma iota_Mc_valid : Γ ⊨ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As)
      : ind_mty p D m Us Ns.
  Proof.
    apply (con_apps_ref_valid VP p D HP HPD Γ m Mm c gs Us Ns As HΓ HMm Hcon i_HUl i_HUs i_HNl i_HNs HAl).
    intros * HN HT; apply (HAs _ _ _ HN); unfold σP; rewrite i_Ps; exact HT.
  Qed.
End Iota.

End Fixed_GCtx.
