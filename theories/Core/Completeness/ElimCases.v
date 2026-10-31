(** * The Eliminator of a Group of Inductive Types

    The semantic rules of the eliminator and of its congruence.  Each holds
    because the group is valid at the target of a sound embedding
    ([valid_groups_of_embedding]), where the elimination is valid
    ([Inductives/Elim.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Con.
From Mctt.Core.Completeness Require Import SubtypingCases PropCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes Elim ElimViewRule.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The motive's instance of an eliminator into propositions is a
    proposition: the motive is one in its context, moved by the
    non-uniform parameters and the scrutinee.  Such an eliminator
    evaluates to the proof [⋆ᵈ] under relevance-directed evaluation, so it
    is related to any term at that type ([rel_exp_under_ctx_proof]). *)
Lemma rel_exp_motive_instance_prop : forall VP p D, valid_groups VP -> VP p D ->
    forall Γ m Mm bm Ps M, ⊨ Γ -> ind_member D m = Some Mm ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Γ ⊨ Pk : T) ->
    Γ ⊨ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    ⊨ elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ ->
    elim_mctx p D m Mm (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive bm : Propₘ ->
    Γ ⊨ (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] : Propₘ.
Proof.
  intros VP p D HP HPD * HΓ HMm HPl HPs HM HMa HA.
  pose proof (valid_group_closed _ _ (valid_groups_valid VP HP p D HPD)) as Hc.
  destruct (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs) as [HUs HNs].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mm) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  pose proof (gsub_tau VP p D HP HPD Γ HΓ _ HUl m Mm HMm HMa _ M HNl HNs HM) as Hg.
  exact (rel_exp_under_ctx_gsub Hg HA).
Qed.

End Fixed_GCtx.

#[local] Generalizable All Variables.

Lemma sem_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : relevance_sort r Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim r oq Us m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl Hgr HMm Hbm HLb HPl HPs HM -> Hnm _ HA HMx HBn HBc Har HB; sem_intro; [ assumption |].
  match goal with He : valid_gctx_embedding _ _ _ _ |- _ => rename He into Hμ end.
  destruct r.
  2:{ (** Into propositions: a proof, related to any term. *)
      apply rel_exp_under_ctx_proof.
      refine (rel_exp_motive_instance_prop _ _ _ (valid_groups_of_embedding _ _ _ _ Hμ) Hl Γ m Mm bm Ps M
                ltac:(assumption) HMm HPl _ ltac:(eassumption) _ _).
      - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
      - exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMm _ _ Hμ))).
      - exact (sem_exp_eq_at_rel (HA _ _ _ HMm Hbm _ _ Hμ)). }
  refine (rel_exp_under_ctx_elim_cong _ _ _ (valid_groups_of_embedding _ _ _ _ Hμ) Hl Γ oq oq m Mm bm Bks Bks Ps Ps M M i
            ltac:(assumption) Hgr Hgr HMm Hbm HLb HLb HPl _ HPl _ ltac:(eassumption) Hnm Hnm _ _ HBn
            (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) _ Har _).
  - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
  - intros * HP HP' HT; rewrite HP in HP'; injection HP' as <-; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
  - intros * HMk; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMk _ _ Hμ))).
  - intros * HMk Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; exact (sem_exp_eq_at_rel (HA _ _ _ HMk Hb _ _ Hμ)).
  - intros * HMk Hcon; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HBc _ _ _ _ HMk Hcon _ _ Hμ))).
  - intros * HMk Hb Hb' Hj Hj' Hcon; rewrite Hb in Hb'; injection Hb' as <-; rewrite Hj in Hj'; injection Hj' as <-.
    exact (sem_exp_eq_at_rel (HB _ _ _ _ _ _ _ HMk Hb Hcon (List.nth_error_In _ _ Hj) _ _ Hμ)).
Qed.

Lemma sem_exp_eq_elim_cong :
  `( ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     elim_grp D oq' p m ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Bks' = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     List.length Ps' = im_np D Mm ->
     (forall k P P' T, nth_error Ps k = Some P -> nth_error Ps' k = Some P' ->
        nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊨ P ≈ P' : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     Us' = List.firstn (ind_nu D) Ps' ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : relevance_sort r Typeω@i) ->
     (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b ≈ eb_motive b' : relevance_sort r Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
        List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        List.nth_error Bks' k = Some b' ->
        nth_error (eb_brs b) i = Some (c, n, B) -> nth_error (eb_brs b') i = Some (c, n, B') ->
        ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B ≈ B'
          : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim r oq Us m Bks M ≈ a_elim r oq' Us' m Bks' M'
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl Hgr Hgr' HMm Hbm HLb HLb' HPl HPs HPl' HPP HMM -> -> Hnm Hnm' _ _ HA HAA HMx HBn HBf HBc Har HBB;
    sem_intro; [ assumption |].
  match goal with He : valid_gctx_embedding _ _ _ _ |- _ => rename He into Hμ end.
  destruct r.
  2:{ (** Into propositions: proofs, related to each other. *)
      apply rel_exp_under_ctx_proof.
      refine (rel_exp_motive_instance_prop _ _ _ (valid_groups_of_embedding _ _ _ _ Hμ) Hl Γ m Mm bm Ps M
                ltac:(assumption) HMm HPl _ ltac:(eapply rel_exp_under_ctx_refl_left; eassumption) _ _).
      - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
      - exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMm _ _ Hμ))).
      - exact (sem_exp_eq_at_rel (HA _ _ _ HMm Hbm _ _ Hμ)). }
  refine (rel_exp_under_ctx_elim_cong _ _ _ (valid_groups_of_embedding _ _ _ _ Hμ) Hl Γ oq oq' m Mm bm Bks Bks' Ps Ps' M M' i
            ltac:(assumption) Hgr Hgr' HMm Hbm HLb HLb' HPl _ HPl' _ ltac:(eassumption) Hnm Hnm' _ _ HBn HBf _ Har _).
  - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
  - intros * HP HP' HT; exact (sem_exp_eq_at_rel (HPP _ _ _ _ HP HP' HT _ _ Hμ)).
  - intros * HMk; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMk _ _ Hμ))).
  - intros * HMk Hb Hb'; exact (sem_exp_eq_at_rel (HAA _ _ _ _ HMk Hb Hb' _ _ Hμ)).
  - intros * HMk Hcon; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HBc _ _ _ _ HMk Hcon _ _ Hμ))).
  - intros * HMk Hb Hb' Hj Hj' Hcon; exact (sem_exp_eq_at_rel (HBB _ _ _ _ _ _ _ _ _ _ HMk Hb Hb' Hj Hj' Hcon _ _ Hμ)).
Qed.

(** The eliminator at a view is its container's at the wrapped blocks
    (E1′, [Inductives/ElimViewRule.v]). *)
Lemma sem_exp_eq_elim_view :
  `( ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     ind_member D m = Some Mm ->
     im_head Mm = mh_view qc k' Is vm ->
     ind_lookup Θ Ξ qc = Some D' ->
     view_wrap_ok D D' vm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : relevance_sort r Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim r oq Us m Bks M
       ≈ a_elim r (Some qc) (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
           (view_wrap r p D D' vm (List.firstn (ind_nu D) Ps) Bks) M
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl Hgr HMm Hh Hq _ Hbm HLb HPl HPs HM -> Hnm _ HA HMx HBn HBc Har HB; sem_intro; [ assumption |].
  match goal with He : valid_gctx_embedding _ _ _ _ |- _ => rename He into Hμ end.
  pose proof (valid_groups_of_embedding _ _ _ _ Hμ) as HVP.
  pose proof (valid_group_lookup _ _ (valid_groups_valid _ HVP qc D' Hq)) as Hq'.
  destruct r.
  2:{ (** Into propositions: proofs, related to each other. *)
      apply rel_exp_under_ctx_proof.
      refine (rel_exp_motive_instance_prop _ _ _ HVP Hl Γ m Mm bm Ps M ltac:(assumption) HMm HPl _ ltac:(eassumption) _ _).
      - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
      - exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMm _ _ Hμ))).
      - exact (sem_exp_eq_at_rel (HA _ _ _ HMm Hbm _ _ Hμ)). }
  refine (rel_exp_under_ctx_elim_view _ _ _ HVP Hl Γ oq m Mm qc k' Is vm D' bm Bks Ps M i
            ltac:(assumption) Hgr HMm Hh Hq' Hbm HLb HPl _ ltac:(eassumption) Hnm _ _ HBn _ Har _).
  - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
  - intros * HMk; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMk _ _ Hμ))).
  - intros * HMk Hb; exact (sem_exp_eq_at_rel (HA _ _ _ HMk Hb _ _ Hμ)).
  - intros * HMk Hcon; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HBc _ _ _ _ HMk Hcon _ _ Hμ))).
  - intros * HMk Hb Hcon Hin; exact (sem_exp_eq_at_rel (HB _ _ _ _ _ _ _ HMk Hb Hcon Hin _ _ Hμ)).
Qed.
