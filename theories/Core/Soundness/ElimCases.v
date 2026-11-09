(** * The Eliminator in the Gluing Model

    The gluing rules of the eliminator and of its congruence and view
    rules.  An elimination is glued at the target of a sound embedding,
    where the groups of the source are valid groups
    ([valid_groups_of_glu_gctx_embedding], [Inductives/Elim.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Elim.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution Instance.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Completeness.Modules Require MemberTypes.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
Require Import Mctt.Core.Soundness.Inductives.Con.
Require Import Mctt.Core.Soundness.Inductives.Bridge.
Require Import Mctt.Core.Soundness.Inductives.Elim.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes.
Require Import Mctt.Core.Soundness.Inductives.ArgTypes.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The motive's instance of an eliminator into propositions is a glued
    proposition: the motive is one in its context, moved by the glued
    substitution of the non-uniform parameters and the scrutinee
    ([glu_rel_sub_of_list]).  As [rel_exp_motive_instance_prop]. *)
Lemma glu_rel_exp_motive_instance_prop : forall p D, decl_closed D ->
    forall Γ m Mm bm Ps M, ind_member D m = Some Mm ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Γ ⊩ Pk : T) ->
    Γ ⊩ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ ⊩ eb_motive bm : Propₘ ->
    Γ ⊩ (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] : Propₘ.
Proof.
  intros p D Hc * HMm HPl HPg HM HA.
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  assert (Hti : tele_insts (im_params D Mm) Id Ps
                = tele_insts (ind_uparams D) Id Us ++ tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns).
  { unfold Us, Ns; rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
      [ exact (decl_closed_ass _ Hc) | fold Us; rewrite HUl; reflexivity ]. }
  assert (HlTU : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in *; lia).
  (** The non-uniform parameters, glued at their instances *)
  assert (HNs : forall j N T0, List.nth_error Ns j = Some N ->
             List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T0 -> Γ ⊩ N : T0).
  { intros j N T0 HN HT; apply (HPg (ind_nu D + j)).
    - unfold Ns in HN; rewrite List.nth_error_skipn in HN; exact HN.
    - rewrite Hti, List.nth_error_app2, HlTU by lia; replace (ind_nu D + j - ind_nu D) with j by lia; exact HT. }
  assert (Hrass : all_assumptions (tele_sub (im_nparams Mm) (sb_of_list Id Us)))
    by (apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMm)).
  pose proof (elim_mctx_ass p D m Mm Us Hc HMm) as Hass.
  pose proof (presup_ctx_glu_rel_exp HM) as HΓ.
  pose proof (presup_ctx_glu_rel_exp HA) as HMa.
  assert (Hg : Γ ⊩ˢ sb_of_list Id (Ns ++ M :: nil) : elim_mctx p D m Mm Us ++ Γ).
  { apply glu_rel_sub_of_list; [ exact Hass | exact (glu_rel_sub_id _ HΓ) | exact (glu_tele_entries_of_ctx _ _ Hass HMa)
                               | rewrite List.length_app, length_elim_mctx; cbn; lia |].
    intros j N T0 HN HT.
    unfold elim_mctx in HT; change (ce_ass ?κ0 ?H0 :: ?R) with ((ce_ass κ0 H0 :: nil) ++ R) in HT.
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub; exact HNl).
    assert (Hl2 : List.length (tele_insts (tele_sub (im_nparams Mm) (sb_of_list Id Us)) Id Ns) = im_nn Mm)
      by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_im_nparams; lia).
    destruct (Nat.lt_ge_cases j (im_nn Mm)) as [Hk | Hk].
    - rewrite List.nth_error_app1 in HN by lia.
      rewrite List.nth_error_app1 in HT by lia.
      rewrite tele_insts_tele_sub in HT.
      rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT by (intros x; cbn; apply sentry_sub_id).
      exact (HNs _ _ _ HN HT).
    - rewrite List.nth_error_app2 in HN by lia.
      rewrite List.nth_error_app2, Hl2 in HT by lia.
      rewrite HNl in HN.
      destruct (j - im_nn Mm) as [| j'] eqn:Hk'; cbn in HN, HT; [| destruct j'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      rewrite ind_head_inst by (try exact Hc; try exact HUl; exact HNl).
      rewrite (List.map_ext (fun U => U[Id]) (fun U => U)), List.map_id by (intros; apply exp_sub_id).
      exact HM. }
  exact (glu_rel_exp_sub Hg HA).
Qed.

End Fixed_GCtx.

(** ** The Rules

    The eliminator reads syntactic premises of its rule: its parts are
    typed by their derivations, moved to the target of the embedding. *)

#[local] Generalizable All Variables.

(** An elimination: into a universe, glued at the target by
    [glu_rel_exp_elim]; into propositions, a proof of its motive's
    instance, a glued proposition ([glu_rel_exp_motive_instance_prop],
    [glu_rel_exp_proof]). *)
Lemma glu_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊩ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹{ak_relevant} eb_scrutinee_type b
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r Typeω@i) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊩ eb_motive b : abs_kind_sort r Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B
          : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     motive_kind r ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_elim r p Us m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl HMm Hbm HLb HPl HPt HPg HMt HMg -> Hnm Hann HAt HAg HMx Hna HBx Har HBt HBg Hmk.
  assert (Hel : Θ ⍮ Ξ ⍮ Γ ⊢ a_elim r p (List.firstn (ind_nu D) Ps) m Bks M
                  : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])
    by (eapply wf_elim; eauto).
  pose proof (blocks_scoped_of_elim _ _ _ _ _ _ _ _ _ _ Hel) as HBsc.
  intros Θ2 Ξ2 Hμ.
  pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & Hwe & _ & _ & Hwx & _ & _).
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HMt)) as Hg.
  pose proof (valid_groups_of_glu_gctx_embedding _ _ _ _ Hg Hem) as HVP.
  destruct Hmk.
  2:{ (** Into propositions: a proof of a glued proposition *)
      apply glu_rel_exp_proof; [| exact (Hwe _ _ _ Hel) ].
      apply (glu_rel_exp_motive_instance_prop p D (valid_group_closed _ _ (valid_groups_valid _ HVP p D Hl)) Γ m Mm bm Ps M HMm HPl).
      - intros * HP HT; exact (HPg _ _ _ HP HT _ _ Hμ).
      - exact (HMg _ _ Hμ).
      - exact (HAg _ _ _ HMm Hbm _ _ Hμ). }
  eapply (@glu_rel_exp_elim (gc_mk Θ2 Ξ2) _ p D HVP (glu_gctx_embedding_ind_field _ _ _ _ Hμ) Hl Γ m Mm bm Bks Ps M i
            HMm Hbm HLb HPl); intros.
  all: first
    [ exact HBsc
    | eapply Hwe; eauto
    | eapply Hwx; eauto
    | eapply HPg; eassumption
    | eapply HMg; eassumption
    | eapply HAg; eassumption
    | eapply HBg; eassumption
    | eauto ].
Qed.

(** The congruence and the view rule glue their context. *)
Lemma glu_exp_eq_elim_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_elim_view :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
