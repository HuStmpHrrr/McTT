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
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
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
      apply (decl_typed_order _ _ _ Hdt _ _ HMj); exact (no_views_decl _ _ _ Hv HMj). }
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
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := valid_ind_decl_uparams _ HD.

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
    apply gsub_closed_inst; [ exact (member_params_ass D Hc _ _ HMm) | exact (valid_ind_decl_params _ HD _ _ HMm) | exact HΓ
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
      by (rewrite (nonrec_args_prefix_cargs_strat gs1 gs2), <- Heq; apply (valid_ind_decl_strat _ HD _ _ _ _ _ HMm Hcon);
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
    Proof. intros kd Hk; rewrite r_strat; exact (valid_ind_decl_dctx _ HD m Mm c gs gs1 t gs2 kd HMm Hcon Heq Hk). Qed.

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
      intros kk P0 T0 HP0 HT; pose proof (valid_ind_decl_rec_field _ HD m Mm c gs gs1 t gs2 Mj kk P0 T0 HMm Hcon Heq HMj HP0 HT) as H.
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
        destruct (valid_ind_decl_dom _ HD m Mm c gs gs1 t gs2 kd Bk HMm Hcon Heq HBk) as (_ & j & HBv0); rewrite <- r_strat in HBv0.
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

  (** The member the constructor's value is of, as the group reads it. *)
  Lemma ref_target : exists Dq Mk, ind_lookup gc_deps gc_stack (fst (im_ref p m Mm)) = Some Dq /\
      ind_member Dq (snd (im_ref p m Mm)) = Some Mk /\ im_unu D Mm = ind_nu Dq /\ im_nn Mk = im_nn Mm.
  Proof.
    unfold im_ref, im_unu; destruct (im_head Mm) as [pm | qc kc Is vm] eqn:Hh; cbn [fst snd].
    - exists D, Mm; repeat split; [ exact Hl | exact HMm ].
    - destruct (view_target_decl VP p D HP HPD m Mm HMm qc kc Is vm Hh) as (Dq & Mk' & pm & Hq & HMk' & _ & HIl).
      destruct (grp_tele_ass_views _ (valid_group_ass _ _ Hvg) m Mm qc kc Is vm HMm Hh) as (Dq0 & Mc & Hq0 & HMc & Hnn & _).
      rewrite Hq in Hq0; injection Hq0 as <-; rewrite HMk' in HMc; injection HMc as <-.
      exists Dq, Mk'; repeat split; [ exact Hq | exact HMk' | exact HIl | exact Hnn ].
  Qed.

  Lemma i_HUt : forall j U, List.nth_error Us j = Some U -> exists T, Γ ⊨ U : T.
  Proof.
    intros j U HU.
    destruct (nth_error_lt_some' (tele_insts (ind_uparams D) Id Us) j) as [T HT].
    { rewrite length_tele_insts by exact Ua.
      assert (j < List.length Us) by (apply List.nth_error_Some; congruence); pose proof i_HUl; unfold ind_nu in *; lia. }
    exists T; exact (i_HUs _ _ _ HU HT).
  Qed.

  (** The group of the eliminator at a member, as [elim_at] writes it. *)
  Lemma elim_at_grp : forall j Mj, ind_member D j = Some Mj -> elim_grp D (if ind_has_views D then Some p else oq) p j.
  Proof.
    intros j Mj HMj.
    destruct (ind_has_views D) eqn:Hv; [ left; reflexivity |].
    destruct Hoq as [-> | ->]; [ left; reflexivity | right; split; [ reflexivity |] ].
    apply (decl_typed_order _ _ _ Hdt _ _ HMj); exact (no_views_decl _ _ _ Hv HMj).
  Qed.

  (** *** The Values at an Environment

      At an environment [C] of [Γ]: the recursive results of the
      eliminator's own evaluation are related, by [rec_results_rel], to
      the values of the recursive results [elim_ihs] in the branch's
      instance. *)
  Section IotaSem.
    #[local] Set Default Proof Using "All".
    Variable (RΓ RU : relation env).
    Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
    Variable (C : env) (u0 ns avs : list domain).
    Hypotheses (HCC : RΓ C C) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ u0)
      (HNC : ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ ns) (HAC : ⟦ As ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ avs).
    Let nr := canon_nparams_rel D u0.
    Let ar := canon_args_rel D u0.
    Let dr := canon_doms_rel u0.
    Let G := grp_rel p D u0 nr ar dr.
    Let Rel := fun j ns m ns' m' =>
      per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
        (env_args C (ns ++ m :: nil)) (env_args C (ns' ++ m' :: nil)).
    #[local] Abbreviation u0_len' := (u0_len D Us i_HUl C u0 HUC).
    #[local] Abbreviation u0_env' := (u0_env VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC).
    #[local] Abbreviation u0_gargs' := (u0_gargs VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC).
    #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
    #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
    #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
    #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
    #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
    #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
    #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
    #[local] Abbreviation Had := (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs').
    #[local] Abbreviation Hass := (valid_group_ass _ _ Hvg).
    #[local] Abbreviation isym := (proj1 (ind_rel_sym_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr))).
    #[local] Abbreviation itrans := (proj1 (ind_rel_trans_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr))).

    Lemma s_Ln : List.length ns = im_nn Mm.
    Proof. rewrite (eval_exps_length _ _ _ HNC); exact i_HNl. Qed.

    Lemma s_La : List.length avs = List.length gs.
    Proof. rewrite (eval_exps_length _ _ _ HAC); exact HAl. Qed.

    Lemma s_Mc : exists cs, List.length cs = im_unu D Mm /\
        ⟦ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As) ⟧ C
          ↘ d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs).
    Proof.
      destruct (rel_exp_under_ctx_simple_at HRΓ iota_Mc_valid _ _ HCC) as (mv & _ & Emv & _ & _).
      assert (LNA : List.length (Ns ++ As) = (im_nn Mm + List.length gs)%nat) by (rewrite List.length_app, i_HNl, HAl; reflexivity).
      destruct (con_ref_apps_value VP p D HP HPD m Mm c gs C Us (Ns ++ As) (ns ++ avs) mv HMm Hcon i_HUl
                  ltac:(apply eval_exps_app; assumption) LNA Emv) as (cs & Lcs & ->).
      exists cs; split; assumption.
    Qed.

    Lemma s_HgN : gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) (sb_of_list Id Us) ++ Γ).
    Proof. exact (gsub_ns VP p D HP HPD Γ HΓ Us m Mm HMm (HMall _ _ HMm) Ns i_HNl i_HNs). Qed.

    (** The scrutinee's relation at [C], and its value there. *)
    Lemma s_scrut : forall x y, per_head (ind_mty p D m Us Ns) (ind_mty p D m Us Ns) C C x y -> G m u0 u0 ns ns x y.
    Proof.
      intros x y Hxy.
      destruct (presup_rel_exp_under_ctx iota_Mc_valid) as [iT HIT].
      destruct (rel_exp_of_typ_inversion_simple_at HRΓ HIT _ _ HCC) as (t1 & t2 & Et1 & Et2 & [R HR]).
      destruct (scrut_rel VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC m Mm HMm (HMall _ _ HMm) Ns i_HNl
                  s_HgN C HCC ns ns HNC HNC t1 t2 _ R Et1 Et2 HR) as [_ ERM].
      apply ERM, (per_head_iff Et1 Et2 HR); exact Hxy.
    Qed.

    Lemma s_self : forall cs, List.length cs = im_unu D Mm ->
        ⟦ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As) ⟧ C
          ↘ d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs) ->
        G m u0 u0 ns ns (d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs))
          (d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) /\
        tele_rel (ar m ns c) (cargs_nonrec gs) (nonrec_arg_vals gs avs) (nonrec_arg_vals gs avs) /\
        con_args_rel p D (okr_at D u0 nr) nr ar dr m u0 u0 ns ns gs avs avs.
    Proof.
      intros cs Lcs Emc.
      destruct (rel_exp_under_ctx_simple_at HRΓ iota_Mc_valid _ _ HCC) as (m1 & m2 & Em1 & Em2 & Hm12).
      assert (m1 = d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) as -> by (eapply functional_eval_exp; eassumption).
      assert (m2 = d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (s_scrut _ _ Hm12) as Hm.
      split; [ exact Hm |].
      assert (Lb : List.length (cs ++ ns) = (im_unu D Mm + im_nn Mm)%nat) by (rewrite List.length_app, Lcs, s_Ln; reflexivity).
      rewrite List.app_assoc in Hm.
      destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMm Lb)
        as (gs0 & bs' & vs' & Ez & _ & _ & Hcon0 & Lbs' & _ & _ & Har & Hia).
      rewrite Hcon in Hcon0; injection Hcon0 as <-.
      injection Ez as Ez.
      destruct (app_split_eq _ _ _ _ Ez ltac:(congruence)) as [<- <-].
      rewrite (skipn_app_exact cs ns _ Lcs) in Har, Hia.
      split; assumption.
    Qed.

    Lemma s_args : tele_rel (ar m ns c) (cargs_nonrec gs) (nonrec_arg_vals gs avs) (nonrec_arg_vals gs avs) /\
        con_args_rel p D (okr_at D u0 nr) nr ar dr m u0 u0 ns ns gs avs avs.
    Proof. destruct s_Mc as (cs & Lcs & Emc); exact (proj2 (s_self cs Lcs Emc)). Qed.

    Lemma s_Hns : tele_rel (nr m) (List.rev (im_nparams Mm)) ns ns.
    Proof.
      destruct s_Mc as (cs & Lcs & Emc).
      exact (ind_rel_ns p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr) _ _ _ _ _ _ _ _ HMm (proj1 (s_self cs Lcs Emc))).
    Qed.

    (** The shape's relation, after related values of the domains. *)
    Lemma s_unfold : forall t ms ws kd, kd <= List.length (ptyp_doms t) -> forall u u' pre' x x' ys ys',
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr m u u' (ms ++ ws) pre' t x x' ->
        tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) kd ys ys' ->
        exists f f', $*| x & ys | gc_deps ⍮ gc_stack ↘ f /\ $*| x' & ys' | gc_deps ⍮ gc_stack ↘ f' /\
          rec_arg_rel p D (okr_at D u0 nr) nr ar dr m u u' (ms ++ ws ++ ys) (pre' ++ ys') (ptyp_skip kd t) f f'.
    Proof.
      intros t ms ws; induction kd as [| kd IH]; intros Hk * Hsh Hys.
      - pose proof Hys as Hys0; rewrite tele_prefix_rel_iff in Hys0; destruct Hys0 as (L1 & L2 & _).
        destruct ys; [| discriminate ]; destruct ys'; [| discriminate ].
        exists x, x'; split; [ constructor | split; [ constructor |] ].
        rewrite !List.app_nil_r; exact Hsh.
      - pose proof Hys as Hys0; rewrite tele_prefix_rel_iff in Hys0; destruct Hys0 as (L1 & L2 & Hr).
        destruct (List.exists_last (l := ys) ltac:(intros ->; discriminate)) as (ys0 & y & ->).
        destruct (List.exists_last (l := ys') ltac:(intros ->; discriminate)) as (ys0' & y' & ->).
        rewrite List.length_app in L1, L2; cbn in L1, L2.
        pose proof (tele_prefix_rel_of_pre _ _ _ _ kd Hys ltac:(lia)) as Hys1.
        rewrite !firstn_app_exact in Hys1 by lia.
        pose proof (Hr kd y y' ltac:(rewrite List.nth_error_app2 by lia; replace (kd - List.length ys0) with 0 by lia; reflexivity)
                      ltac:(rewrite List.nth_error_app2 by lia; replace (kd - List.length ys0') with 0 by lia; reflexivity)) as Hyy.
        rewrite firstn_app_exact in Hyy by lia.
        destruct (IH ltac:(lia) _ _ _ _ _ _ _ Hsh Hys1) as (g & g' & Eg & Eg' & Hsh0).
        destruct (ptyp_skip_lt kd t ltac:(lia)) as (Bk & HBk & Hs).
        rewrite Hs in Hsh0.
        unfold shape_doms_rel in Hyy; rewrite (List.nth_error_nth _ _ _ HBk) in Hyy.
        destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh0 y y' Hyy) as (r & r' & Er & Er' & Hsh1).
        exists r, r'; split; [| split ].
        + apply eval_apps_app; exists g; split; [ exact Eg | econstructor; [ exact Er | constructor ] ].
        + apply eval_apps_app; exists g'; split; [ exact Eg' | econstructor; [ exact Er' | constructor ] ].
        + rewrite <- !List.app_assoc in Hsh1; exact Hsh1.
    Qed.

    Lemma s_HPC : ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ u0 ++ ns.
    Proof. rewrite i_Ps; apply eval_exps_app; [ exact HUC | exact HNC ]. Qed.

    (** The lemmas of [Elim.v] at [C] on both sides. *)
    #[local] Abbreviation EP f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC C HCC Bks i HBks HMall HAv).

    (** *** A Recursive Argument

        The recursive argument of shape [t] after the arguments [gs1], its
        shape ending in the member [Mj]. *)
    Section RecSem.
      #[local] Set Default Proof Using "All".
      Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
      Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
      Variable (Mj : imember).
      Hypothesis (HMj : ind_member D (ptyp_mem t) = Some Mj).
      Let K := List.length (cargs_nonrec gs1).
      Let L := List.length (ptyp_doms t).
      Let σt := cargs_sub σP gs1 As.
      Let Mt := List.nth (List.length gs1) As (a_var 0).
      Let nv := nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs).
      Let ΨL := tele_sub (doms_ctx (List.firstn L (ptyp_doms t))) σt ++ Γ.

      Lemma s_a : exists a, List.nth_error avs (List.length gs1) = Some a /\
          rec_arg_rel p D (okr_at D u0 nr) nr ar dr m u0 u0 (ns ++ nv) (ns ++ nv) t a a.
      Proof.
        destruct s_args as (_ & Hia).
        destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & x' & Hx & Hx' & Hr).
        rewrite Hx in Hx'; injection Hx' as <-; exists x; split; assumption.
      Qed.

      Lemma s_nv : List.length nv = K /\ tele_prefix_rel (ar m ns c) K nv nv.
      Proof.
        destruct s_args as (Hnv & _).
        assert (Lf : List.length (List.firstn (List.length gs1) avs) = List.length gs1)
          by (rewrite List.length_firstn, s_La, Heq, List.length_app; lia).
        split; [ apply length_nonrec_arg_vals; exact Lf |].
        rewrite <- (List.firstn_skipn (List.length gs1) avs) in Hnv.
        exact (nonrec_prefix_gen _ gs gs1 (ca_rec t :: gs2) _ _ _ _ Heq Lf Lf Hnv).
      Qed.

      (** The end of the shape: the eliminator's own recursive result
          against the eliminator at its blocks moved past the domains, in
          the environment extended by the domains' values (an outer
          link). *)
      Lemma s_leaf : forall a, List.nth_error avs (List.length gs1) = Some a ->
          forall ys ys' f f',
          tele_prefix_rel (shape_doms_rel (dr m) ns nv (ptyp_doms t)) L ys ys' ->
          $*| a & ys | gc_deps ⍮ gc_stack ↘ f -> $*| a & ys' | gc_deps ⍮ gc_stack ↘ f' ->
          rec_arg_rel p D (okr_at D u0 nr) nr ar dr m u0 u0 (ns ++ nv ++ ys) (ns ++ nv ++ ys')
            (pt_self (ptyp_mem t) (ptyp_ps t)) f f' ->
          exists re rc, ⟦elim f at (ptyp_mem t) of p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C ↘ re /\
            ⟦ elim_at p D oq (List.map (fun U => U[sb_shift_iter L Id]) Us) (blocks_sub Bks (sb_shift_iter L Id))
                (ptyp_mem t) (apps_vars_iter L Mt) ⟧ env_args C ys' ↘ rc /\
            rec_result_rel dr Rel m u0 u0 (ns ++ nv ++ ys) (ns ++ nv ++ ys') (pt_self (ptyp_mem t) (ptyp_ps t)) f f' re rc.
      Proof.
        intros a Ha * Hys Ef Ef' Hsh.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        pose proof Hys as Hys0; rewrite tele_prefix_rel_iff in Hys0; destruct Hys0 as (Lys & Lys' & _).
        destruct s_nv as (Lnv & Hnvp).
        set (EL := env_args C ys').
        set (σL := sb_shift_iter L Id).
        pose proof (r_HΨ gs1 t gs2 Heq Mj HMj L (le_n _)) as HΨL.
        destruct (rel_ctx_wf_per_ctx_env HΨL) as [RΨ HRΨ].
        (** The environment of the domains. *)
        assert (HEL : RΨ EL EL).
        { destruct (rel_ctx_wf_per_ctx_env (ihs_pre gs1 _ Heq)) as [RS HRS].
          pose proof (doms_rel_refl_r p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HMm ns c gs gs1 t gs2 nv s_Hns Hcon Heq Hnvp
                        L ys ys' (le_n _) Hys) as Hys''.
          pose proof (EP side_dom_gargs m Mm c gs HMm Hcon (HBc _ _ _ _ HMm Hcon) gs1 t gs2 Heq RS HRS L C u0 ns nv ys' (le_n _)
                        u0_env' u0_len' s_Ln Lnv s_Hns Hnvp Hys'') as Hg.
          rewrite List.app_assoc in Hg.
          exact (tele_stage_rel (doms_ctx (List.firstn L (ptyp_doms t))) (cargs_strat gs1 ++ im_params D Mm ++ Γ) Γ σt RΓ C _
                   ltac:(unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass)
                   (r_dctxΓ gs1 t gs2 Heq Mj HMj L (le_n _)) HRΓ (gsub_valid (gsub_sigt gs1 _ Heq)) HCC
                   (eval_sigt gs1 _ C (u0 ++ ns) avs Heq s_HPC HAC) ys' Hg
                   ltac:(rewrite (r_dlen gs1 t gs2 Heq Mj HMj L (le_n _)); exact Lys') RΨ HRΨ). }
        assert (HwL : ΨL ⊨ˢ σL ≈ σL : Γ) by exact (gsub_valid (r_base gs1 t gs2 Heq Mj HMj L (le_n _))).
        assert (Hσw : sb_eq (ι (wk_shiftn L)) σL) by (unfold σL; rewrite sb_shift_iter_eq, sb_compose_id_left; reflexivity).
        assert (Hev : ⟦ σL ⟧s EL ↘ C).
        { apply (eval_sub_sb_eq (ι (wk_shiftn L))); [ exact Hσw |].
          pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn L) EL (wk_mono_shiftn _)) as H.
          unfold EL in H; rewrite <- Lys', eval_wk_shiftn_args in H; rewrite <- Lys'; exact H. }
        (** The scrutinee, moved, against itself. *)
        destruct (exp_inst_link _ _ _ _ _ _ _ _ _ iota_Mc_valid HRΨ HwL HEL Hev) as (mw & mC & Emw & EmC & Hm).
        destruct s_Mc as (cs & Lcs & EMc).
        assert (mC = d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) as -> by (eapply functional_eval_exp; eassumption).
        apply s_scrut, isym in Hm.
        rewrite apps_exp_sub in Emw; cbn [exp_sub] in Emw.
        rewrite !List.map_app, (im_pre_sub D m Mm Us σL Hc HMm i_HUl) in Emw.
        pose proof Emw as Emw0; apply eval_apps_exp in Emw0 as (f0 & ws & _ & Ews & _).
        apply eval_exps_app_inv in Ews as (us1 & zs & -> & _ & Ezs).
        pose proof Ezs as Ezs0; apply eval_exps_app_inv in Ezs0 as (ns1 & as1 & -> & Ens1 & Eas1).
        assert (Ln1 : List.length ns1 = im_nn Mm) by (rewrite (eval_exps_length _ _ _ Ens1), List.length_map; exact i_HNl).
        destruct (con_ref_apps_value VP p D HP HPD m Mm c gs EL (List.map (fun U => U[σL]) Us) _ _ mw HMm Hcon
                    ltac:(rewrite List.length_map; exact i_HUl) Ezs ltac:(rewrite List.length_app, !List.length_map, i_HNl, HAl; reflexivity) Emw)
          as (cs' & Lcs' & ->).
        rewrite (List.app_assoc cs ns avs) in Hm.
        destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMm
                    ltac:(rewrite List.length_app, Lcs, s_Ln; reflexivity))
          as (gs0 & bs' & vs' & Ez & _ & _ & Hcon0 & Lbs' & _ & _ & _ & Hia).
        rewrite Hcon in Hcon0; injection Hcon0 as <-.
        injection Ez as Ez; rewrite List.app_assoc in Ez.
        destruct (app_split_eq _ _ _ _ Ez ltac:(rewrite Lbs', List.length_app, Lcs', Ln1; reflexivity)) as [<- <-].
        rewrite (skipn_app_exact cs ns _ Lcs), (skipn_app_exact cs' ns1 _ Lcs') in Hia.
        destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & x' & Hx & Hx' & Hshw).
        rewrite Ha in Hx; injection Hx as <-.
        (** Along the domains. *)
        destruct (s_unfold t ns nv L (le_n _) _ _ _ a x' ys ys' Hshw Hys) as (f1 & mL & Ef1 & EmL & HshL).
        pose proof (eval_apps_functional _ _ _ _ Ef1 Ef) as ->.
        pose proof (ptyp_skip_end t) as HsL; change (List.length (ptyp_doms t)) with L in HsL; rewrite HsL in HshL.
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HshL) as (bs1 & bs1' & Ebs1 & _ & _ & _ & HfmL).
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs'' & Ebs & Ebs'' & _ & _ & Hff).
        pose proof (functional_eval_exps' _ _ _ _ Ebs1 Ebs) as ->.
        assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some' As _ Hlt) as [M0 HM0].
        assert (EMt : Mt = M0) by (unfold Mt; apply List.nth_error_nth; exact HM0).
        assert (ExL : ⟦ apps_vars_iter L Mt ⟧ EL ↘ mL).
        { rewrite apps_vars_iter_eq.
          apply eval_apps_exp; exists x', ys'; split; [| split; [| exact EmL ] ].
          - destruct (eval_exps_nth _ _ _ (List.length gs1) (Mt[σL]) Eas1) as (v & Hv & Ev).
            + rewrite List.nth_error_map, HM0, EMt; reflexivity.
            + rewrite Hx' in Hv; injection Hv as <-.
              rewrite <- exp_sub_of_wk, (exp_sub_sb_eq Mt _ _ Hσw); exact Ev.
          - unfold EL; pose proof (eval_vars_from_args ys' C nil) as H; cbn [List.length] in H.
            rewrite List.app_nil_r, Lys' in H; exact H. }
        (** The eliminations, at the outer link. *)
        destruct (vals_sub_link VP p D HP HPD Γ HΓ RU HRU Us i_HUl i_HUt
                    (proj2 (gsub_props (gsub_U VP p D HP HPD Γ HΓ Us i_HUl i_HUs))) ΨL RΨ σL EL C u0 HRΨ HwL HEL Hev HUC)
          as (wL & EwL & HwL0).
        assert (LwL : List.length wL = ind_nu D) by (rewrite (eval_exps_length _ _ _ EwL), List.length_map; exact i_HUl).
        pose proof (ups_ok VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC wL u0 HwL0 u0_env' LwL u0_len') as Hok.
        destruct (blocks_sub_facts D Bks σL HBks HnmA HnaA HarA) as (HbA1 & HnmA1 & HnaA1 & HarA1).
        assert (HAA0 : forall j Mj b b0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> List.nth_error Bks j = Some b0 ->
                   elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ eb_motive b0 : Typeω@i).
        { intros * HMj0 Hb Hb0; rewrite Hb in Hb0; injection Hb0 as <-; exact (HAv _ _ _ HMj0 Hb). }
        assert (HB0s : forall j Mj b b0 c gs n B0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
                   List.nth_error Bks j = Some b0 -> ind_con Mj c = Some gs -> brs_lookup (eb_brs b0) c = Some (n, B0) ->
                   n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat /\
                   elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B0 : elim_bty p j Mj c gs (eb_motive b) Us).
        { intros * HMj0 Hb Hb0 Hcon1 Hlb; rewrite Hb in Hb0; injection Hb0 as <-.
          split; [ exact (HarA _ _ _ _ _ _ _ HMj0 Hb Hcon1 (brs_lookup_in _ _ _ _ Hlb))
                 | exact (HBv _ _ _ _ _ _ _ HMj0 Hb Hcon1 (brs_lookup_in _ _ _ _ Hlb)) ]. }
        pose proof (per_ind_elim_all p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had i EL C (blocks_sub Bks σL) Bks wL u0 Hok
                      Rel HbA1 HBks HnmA1 HnmA HnaA1 HnaA HarA1 HarA (decl_typed_nodup _ _ _ Hdt)
                      (EP mot_link Bks HnmA HAA0 ΨL RΨ σL EL C HRΨ HwL HEL Hev HCC)
                      (EP br_out HBc Bks HB0s ΨL RΨ σL EL C HRΨ HwL HEL Hev HCC)) as [PE _].
        pose proof (isym _ _ _ _ _ _ _ HfmL) as HmLf.
        destruct (PE _ _ _ _ _ _ _ HmLf) as (r1 & r2 & Er1 & Er2 & Hr12).
        destruct (elim_grp_of_elem _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj HmLf (decl_typed_order _ _ _ Hdt) _ (elim_at_grp _ _ HMj)) as [Hgr1 _].
        exists r2, r1; split; [ exact Er2 | split ].
        - unfold elim_at; eapply eval_exp_elim; [ exact EwL | exact ExL | exact Hgr1 | exact Er1 ].
        - eapply rec_result_self; [ exact Ebs | exact Ebs'' |].
          pose proof (EP rel_per _ _ HMj _ _ _ _ _ _ HmLf) as HPR.
          apply (proj1 (EP rel_resp _ _ HMj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HmLf (itrans _ _ _ _ _ _ _ Hff _ _ _ _ (isym _ _ _ _ _ _ _ Hff)) Hff r2 r1)).
          symmetry; exact Hr12.
      Qed.

      (** After [kd] domains: the eliminator's own recursive result
          against the value of [ptyp_ih] in the environment extended by the
          domains' values. *)
      Lemma s_clo : forall a, List.nth_error avs (List.length gs1) = Some a ->
          forall n kd, kd + n = L -> forall ys ys' f f',
          tele_prefix_rel (shape_doms_rel (dr m) ns nv (ptyp_doms t)) kd ys ys' ->
          $*| a & ys | gc_deps ⍮ gc_stack ↘ f -> $*| a & ys' | gc_deps ⍮ gc_stack ↘ f' ->
          rec_arg_rel p D (okr_at D u0 nr) nr ar dr m u0 u0 (ns ++ nv ++ ys) (ns ++ nv ++ ys') (ptyp_skip kd t) f f' ->
          forall Us0 Bks0, Us0 = List.map (fun U => U[sb_shift_iter kd Id]) Us -> Bks0 = blocks_sub Bks (sb_shift_iter kd Id) ->
          exists re rc, ⟦ih f of ptyp_skip kd t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C ↘ re /\
            ⟦ ptyp_ih p D oq Us0 Bks0 (sb_qn kd σt) (apps_vars_iter kd Mt) (ptyp_skip kd t) ⟧ env_args C ys' ↘ rc /\
            rec_result_rel dr Rel m u0 u0 (ns ++ nv ++ ys) (ns ++ nv ++ ys') (ptyp_skip kd t) f f' re rc.
      Proof.
        intros a Ha; induction n as [| n IH]; intros kd Hkn * Hys Ef Ef' Hsh * HU0 HB0; subst Us0 Bks0.
        - assert (Hk : kd = L) by lia; rewrite Hk in Hys, Hsh |- *.
          pose proof (ptyp_skip_end t) as HsL; change (List.length (ptyp_doms t)) with L in HsL; rewrite HsL in Hsh |- *.
          cbn [ptyp_ih].
          destruct (s_leaf a Ha ys ys' f f' Hys Ef Ef' Hsh) as (re & rc & Ere & Erc & Hr).
          exists re, rc; split; [ constructor; exact Ere | split; [ exact Erc | exact Hr ] ].
        - assert (Hk : kd < L) by lia.
          destruct (ptyp_skip_lt kd t Hk) as (Bk & HBk & Hs).
          rewrite Hs in Hsh |- *.
          assert (HUs1 : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[sb_shift_iter kd Id]) Us)
                         = List.map (fun U => U[sb_shift_iter (S kd) Id]) Us)
            by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
          assert (HBs1 : blocks_wk (blocks_sub Bks (sb_shift_iter kd Id)) ↑ = blocks_sub Bks (sb_shift_iter (S kd) Id))
            by (rewrite <- blocks_sub_of_wk, blocks_sub_sub; reflexivity).
          do 2 eexists; split; [ constructor | split; [ cbn [ptyp_ih]; constructor |] ].
          apply rec_result_pi; intros c0 c0' Hcc.
          destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c0 c0' Hcc) as (fc & fc' & Efc & Efc' & Hsh').
          assert (Hys1 : tele_prefix_rel (shape_doms_rel (dr m) ns nv (ptyp_doms t)) (S kd) (ys ++ c0 :: nil) (ys' ++ c0' :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hys |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HBk); exact Hcc).
          assert (Efa : $*| a & ys ++ c0 :: nil | gc_deps ⍮ gc_stack ↘ fc)
            by (apply eval_apps_app; exists f; split; [ exact Ef | econstructor; [ exact Efc | constructor ] ]).
          assert (Efa' : $*| a & ys' ++ c0' :: nil | gc_deps ⍮ gc_stack ↘ fc')
            by (apply eval_apps_app; exists f'; split; [ exact Ef' | econstructor; [ exact Efc' | constructor ] ]).
          rewrite <- !List.app_assoc in Hsh'.
          destruct (IH (S kd) ltac:(lia) _ _ _ _ Hys1 Efa Efa' Hsh' _ _ HUs1 HBs1) as (re & rc & Ere & Erc & Hih).
          econstructor; [ exact Efc | exact Efc' | econstructor; [ exact Efc | exact Ere ] | constructor; rewrite env_args_snoc in Erc; exact Erc |].
          rewrite <- !List.app_assoc; exact Hih.
      Qed.
    End RecSem.

    (** The recursive results of the arguments after [gs1]. *)
    Lemma s_ihs : forall rest gs1, gs = gs1 ++ rest ->
        exists ihe ihc, ⟦ihs List.skipn (List.length gs1) avs of rest under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C ↘ ihe /\
          ⟦ elim_ihs p D oq Us Bks (cargs_sub σP gs1 As) rest (List.skipn (List.length gs1) As) ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ ihc /\
          rec_results_rel dr Rel m u0 u0 (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs))
            (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)) rest
            (List.skipn (List.length gs1) avs) (List.skipn (List.length gs1) avs) ihe ihc.
    Proof.
      induction rest as [| g rest IH]; intros gs1 Heq.
      - assert (E : List.skipn (List.length gs1) avs = nil)
          by (apply List.skipn_all2; rewrite s_La, Heq, List.app_nil_r; lia).
        rewrite E; exists nil, nil; split; [ constructor | split; [ cbn; constructor | constructor ] ].
      - assert (Hlt : List.length gs1 < List.length avs) by (rewrite s_La, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some avs _ Hlt) as [v Hv].
        assert (HltA : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some As _ HltA) as [M0 HM0].
        assert (Lf : List.length (List.firstn (List.length gs1) avs) = List.length gs1) by (rewrite List.length_firstn; lia).
        assert (Heq' : gs = (gs1 ++ g :: nil) ++ rest) by (rewrite <- List.app_assoc; exact Heq).
        destruct (IH _ Heq') as (ihe & ihc & Ee & Ec & Hr).
        rewrite List.length_app in Ee, Ec, Hr; cbn [List.length] in Ee, Ec, Hr; rewrite Nat.add_1_r in Ee, Ec, Hr.
        rewrite (firstn_S_nth _ _ _ Hv), nonrec_arg_vals_app in Hr by exact Lf.
        rewrite (skipn_nth_cons _ _ _ Hv), (skipn_nth_cons _ _ _ HM0).
        destruct g as [B0 | t].
        + assert (Hcs : cargs_sub σP (gs1 ++ ca_arg B0 :: nil) As = (cargs_sub σP gs1 As ,, M0)).
          { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ HM0).
            apply cargs_sub_snoc_arg; rewrite List.length_firstn; lia. }
          rewrite Hcs in Ec; cbn [nonrec_arg_vals] in Hr; rewrite List.app_assoc in Hr.
          exists ihe, ihc; split; [ constructor; exact Ee | split; [ cbn [elim_ihs]; exact Ec | constructor; exact Hr ] ].
        + assert (Hcs : cargs_sub σP (gs1 ++ ca_rec t :: nil) As = cargs_sub σP gs1 As).
          { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ HM0).
            apply cargs_sub_snoc_rec; rewrite List.length_firstn; lia. }
          rewrite Hcs in Ec; cbn [nonrec_arg_vals] in Hr; rewrite List.app_nil_r in Hr.
          destruct (length_rec_ps D HD m Mm HMm c gs gs1 t rest Hcon Heq) as (Mj & HMj & _).
          destruct (s_a gs1 t rest Heq Mj HMj) as (a & Ha & Hsh).
          rewrite Hv in Ha; injection Ha as <-.
          destruct (s_clo gs1 t rest Heq Mj HMj v Hv _ 0 eq_refl nil nil v v (tele_prefix_rel_nil _) ltac:(constructor) ltac:(constructor)
                      ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact Hsh) Us Bks
                      ltac:(cbn [sb_shift_iter]; rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id; reflexivity)
                      ltac:(cbn [sb_shift_iter]; rewrite blocks_sub_id; reflexivity)) as (re & rc & Ere & Erc & Hih).
          cbn [apps_vars_iter sb_qn ptyp_skip env_args List.fold_left] in Ere, Erc, Hih.
          rewrite List.app_nil_r in Hih.
          rewrite (List.nth_error_nth _ _ _ HM0) in Erc.
          exists (re :: ihe), (rc :: ihc); split; [ constructor; [ exact Ere | exact Ee ] | split ].
          * cbn [elim_ihs]; constructor; [ exact Erc | exact Ec ].
          * constructor; [ exact Hih | exact Hr ].
    Qed.
  End IotaSem.

  (** *** The Rule *)
  Lemma rel_exp_under_ctx_elim_iota_at : forall n B, brs_lookup (eb_brs bm) c = Some (n, B) ->
      Γ ⊨ a_elim oq Us m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As))
        ≈ B[sb_of_list Id (Ns ++ As ++ elim_ihs p D oq Us Bks σP gs As)]
        : (eb_motive bm)[sb_of_list Id (Ns ++ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                                (im_pre Mm Us ++ Ns ++ As) :: nil)].
  Proof.
    intros n B Hlk.
    set (Mc := apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As)).
    pose proof iota_Mc_valid as HMc; fold Mc in HMc.
    (** The left side, an eliminator. *)
    pose proof (gsub_tau VP p D HP HPD Γ HΓ Us i_HUl m Mm HMm (HMall _ _ HMm) Ns Mc i_HNl i_HNs HMc) as Hg.
    assert (HUU : forall j U U' T, List.nth_error Us j = Some U -> List.nth_error Us j = Some U' ->
               List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊨ U ≈ U' : T)
      by (intros * HU HU' HT; rewrite HU in HU'; injection HU' as <-; exact (i_HUs _ _ _ HU HT)).
    assert (HAA : forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks k = Some b' ->
               elim_mctx p D k Mk Us ++ Γ ⊨ eb_motive b ≈ eb_motive b' : Typeω@i)
      by (intros * HMk Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; exact (HAv _ _ _ HMk Hb)).
    assert (HBB : forall k Mk b b' c0 gs0 n0 B0 B0', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
               List.nth_error Bks k = Some b' -> ind_con Mk c0 = Some gs0 ->
               brs_lookup (eb_brs b) c0 = Some (n0, B0) -> brs_lookup (eb_brs b') c0 = Some (n0, B0') ->
               elim_bctx p D Mk gs0 (blocks_motives Bks) Us ++ Γ ⊨ B0 ≈ B0' : elim_bty p k Mk c0 gs0 (eb_motive b) Us)
      by (intros * HMk Hb Hb' Hc0 Hl1 Hl2; rewrite Hb in Hb'; injection Hb' as <-; rewrite Hl1 in Hl2; injection Hl2 as <-;
          exact (HBv _ _ _ _ _ _ _ HMk Hb Hc0 (brs_lookup_in _ _ _ _ Hl1))).
    pose proof (rel_exp_under_ctx_elim_at VP p D HP HPD Γ oq oq m Mm bm Bks Bks Us Us Ns Mc Mc i HΓ Hgr Hgr HMm Hbm HBks HBks
                  i_HUl i_HUs i_HUl HUU i_HNl i_HNs HMc HnmA HnmA HMall HAA HnaA
                  (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) HBc HarA HBB) as HL.
    (** The right side, the branch at its instance. *)
    pose proof gsub_iota as Hgi.
    pose proof (HBv _ _ _ _ _ _ _ HMm Hbm Hcon (brs_lookup_in _ _ _ _ Hlk)) as HBv'.
    assert (Lih : List.length (elim_ihs p D oq Us Bks σP gs As) = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
    pose proof (rel_exp_under_ctx_gsub Hgi HBv') as HR.
    rewrite (elim_bty_iota p D m Mm c gs (eb_motive bm) Us Ns As _ Hc HMm i_HUl i_HNl HAl Lih) in HR; fold Mc in HR.
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
    destruct (rel_ctx_wf_per_ctx_env Usem) as [RU HRU].
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    destruct (presup_rel_exp_under_ctx HL) as [iT HT].
    destruct (presup_rel_exp_under_ctx HBv') as [iB HTb].
    apply (rel_exp_under_ctx_of_simple HRΓ HL HR).
    intros ρ ρ' Hρρ'.
    assert (Hρ'ρ' : RΓ ρ' ρ') by (etransitivity; [ symmetry; exact Hρρ' | exact Hρρ' ]).
    destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as (l & l' & El & El' & Hll').
    (** The values at [ρ']. *)
    destruct (us_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs ρ' ρ' Hρ'ρ') as (u0 & u0' & Hu0 & Hu0' & _).
    destruct (rel_exp_under_ctx_simple_at HRΓ HMc _ _ Hρ'ρ') as (mv & _ & Emv & _ & _).
    pose proof Emv as Emv0; unfold Mc in Emv0; apply eval_apps_exp in Emv0 as (f0 & ws & _ & Ews & _).
    apply eval_exps_app_inv in Ews as (us1 & vrest & -> & _ & Evrest).
    apply eval_exps_app_inv in Evrest as (ns & avs & -> & HNC & HAC).
    destruct (s_Mc RΓ RU HRΓ HRU ρ' u0 ns avs Hρ'ρ' Hu0 HNC HAC) as (cs & Lcs & EMc).
    destruct (s_self RΓ RU HRΓ HRU ρ' u0 ns avs Hρ'ρ' Hu0 HNC HAC cs Lcs EMc) as (Hself & _ & _).
    destruct (s_ihs RΓ RU HRΓ HRU ρ' u0 ns avs Hρ'ρ' Hu0 HNC HAC gs nil eq_refl) as (ihe & ihc & Ee & Ec & Hir).
    cbn [List.length List.skipn List.firstn nonrec_arg_vals cargs_sub] in Ee, Ec, Hir; rewrite List.app_nil_r in Hir.
    assert (Hsk : List.skipn (im_unu D Mm) (cs ++ ns) = ns) by exact (skipn_app_exact cs ns _ Lcs).
    rewrite (List.app_assoc cs ns avs) in Hself, EMc.
    (** The branch's environments. *)
    pose proof (HBc _ _ _ _ HMm Hcon) as HBm.
    destruct (rel_ctx_wf_per_ctx_env HBm) as [RB HRB].
    assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
    pose proof (cv_bctx_elem VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs ρ' u0 Hρ'ρ' Hu0 ρ' Hρ'ρ' Bks i HBks HMall HAv
                  m Mm c gs HMm Hcon HBm ρ' ρ' Hρ'ρ' Hρ'ρ' u0 u0 _ _ (cs ++ ns) (cs ++ ns) avs avs ihe ihc
                  ltac:(rewrite Hsk; exact Hself) ltac:(rewrite Hsk; exact Hir) RB HRB) as Hec.
    rewrite Hsk in Hec.
    destruct (rel_exp_under_ctx_simple_at HRB HBv' _ _ Hec) as (r1 & r2 & Er1 & Er2 & Hr12).
    (** The eliminator's own value. *)
    destruct ref_target as (Dq & Mk & HDq & HMk & Hunu & Hnn).
    assert (Enp : im_np Dq Mk = List.length (cs ++ ns))
      by (unfold im_np; rewrite List.length_app, Lcs, (eval_exps_length _ _ _ HNC), i_HNl, Hunu, Hnn; lia).
    assert (Eel : ⟦elim d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c ((cs ++ ns) ++ avs) at m of p u0 Bks ⟧
                    gc_deps ⍮ gc_stack ⍮ ρ' ↘ r1).
    { eapply eval_elim_con; [ exact Hl | exact HMm | apply surjective_pairing | exact HDq | exact HMk | exact Hcon | | exact Hbm
                            | exact Hlk | | |].
      - rewrite Enp, List.length_app, (eval_exps_length _ _ _ HAC), HAl; reflexivity.
      - rewrite (HarA _ _ _ _ _ _ _ HMm Hbm Hcon (brs_lookup_in _ _ _ _ Hlk)), Hnn; reflexivity.
      - rewrite Enp, skipn_app_exact by reflexivity; exact Ee.
      - rewrite Enp, skipn_app_exact, firstn_app_exact by reflexivity; rewrite <- Hunu, Hsk; exact Er1. }
    destruct (elim_grp_of_elem _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMm Hself (decl_typed_order _ _ _ Hdt) oq Hgr) as [Hgr1 _].
    assert (l' = r1) as -> by (eapply functional_eval_exp; [ exact El' | eapply eval_exp_elim; [ exact Hu0 | exact EMc | exact Hgr1 | exact Eel ] ]).
    (** The right side's value. *)
    set (Eτ := env_args ρ' (ns ++ avs ++ ihc)) in *.
    assert (Hτ : ⟦ sb_of_list Id (Ns ++ As ++ elim_ihs p D oq Us Bks σP gs As) ⟧s ρ' ↘ Eτ)
      by (apply eval_sb_of_list; [ apply eval_sub_id | apply eval_exps_app; [ exact HNC | apply eval_exps_app; [ exact HAC | exact Ec ] ] ]).
    destruct (exp_inst_link _ _ _ _ _ _ _ _ _ HBv' HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ) as (r & n0 & Er & En0 & Hrn).
    assert (n0 = r2) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hcc : RB Eτ Eτ) by (etransitivity; [ symmetry; exact Hec | exact Hec ]).
    assert (EC1 : per_head (elim_bty p m Mm c gs (eb_motive bm) Us) (elim_bty p m Mm c gs (eb_motive bm) Us)
                    (env_args ρ' (ns ++ avs ++ ihe)) Eτ
                  <~> per_head (elim_bty p m Mm c gs (eb_motive bm) Us) (elim_bty p m Mm c gs (eb_motive bm) Us) Eτ Eτ).
    { apply (per_head_of_typ_resp HRB HTb).
      apply rel_chain_cons; [ exact Hec |]. apply rel_chain_cons; [ exact Hcc |]. apply rel_chain_of_pair; exact Hcc. }
    pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HTb HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ Hτ) as ER.
    rewrite (elim_bty_iota p D m Mm c gs (eb_motive bm) Us Ns As _ Hc HMm i_HUl i_HNl HAl Lih) in ER; fold Mc in ER.
    exists l, r; split; [ exact El | split; [ exact Er |] ].
    set (T := (eb_motive bm)[sb_of_list Id (Ns ++ Mc :: nil)]) in *.
    assert (HT' : Γ ⊨ T : Typeω@iT) by exact (rel_exp_under_ctx_refl_left HT).
    assert (Hl'r2 : per_head T T ρ' ρ' r1 r2) by (apply ER, EC1; exact Hr12).
    assert (Hrr2 : per_head T T ρ' ρ' r r2) by (apply ER; exact Hrn).
    pose proof (per_head_sym _ _ _ _ _ _ HRΓ HT' Hρ'ρ' _ _ Hrr2) as Hr2r.
    pose proof (per_head_trans _ _ _ _ _ _ HRΓ HT' Hρ'ρ' _ _ _ Hl'r2 Hr2r) as Hlr.
    assert (EC : per_head T T ρ' ρ' <~> per_head T T ρ ρ').
    { apply (per_head_of_typ_resp HRΓ HT).
      apply rel_chain_cons; [ exact Hρ'ρ' |]. apply rel_chain_cons; [ symmetry; exact Hρρ' |]. apply rel_chain_of_pair; exact Hρρ'. }
    exact (per_head_trans _ _ _ _ _ _ HRΓ HT' Hρρ' _ _ _ Hll' (proj1 (EC _ _) Hlr)).
  Qed.
End Iota.

End Fixed_GCtx.
