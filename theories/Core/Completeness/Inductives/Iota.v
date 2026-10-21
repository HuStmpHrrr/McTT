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

End Fixed_GCtx.
