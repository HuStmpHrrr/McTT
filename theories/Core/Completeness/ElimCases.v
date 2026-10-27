(** * The Eliminator of a Group of Inductive Types

    The semantic rules of the eliminator and of its congruence.  Each holds
    because the group is valid at the target of a sound embedding
    ([valid_groups_of_emb]), where the elimination is valid
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
From Mctt.Core.Completeness Require Import SubtypingCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes Elim ElimViewRule.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

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
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim oq Us m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl Hgr HMm Hbm HLb HPl HPs HM -> Hnm _ HA HMx HBn HBc Har HB; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  refine (rel_exp_under_ctx_elim_cong _ _ _ (valid_groups_of_emb _ _ _ _ Hμ) Hl Γ oq oq m Mm bm Bks Bks Ps Ps M M i
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
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : Typeω@i) ->
     (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b ≈ eb_motive b' : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
        List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        List.nth_error Bks' k = Some b' ->
        nth_error (eb_brs b) i = Some (c, n, B) -> nth_error (eb_brs b') i = Some (c, n, B') ->
        ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B ≈ B'
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim oq Us m Bks M ≈ a_elim oq' Us' m Bks' M'
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl Hgr Hgr' HMm Hbm HLb HLb' HPl HPs HPl' HPP HMM -> -> Hnm Hnm' _ _ _ HAA HMx HBn HBf HBc Har HBB;
    sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  refine (rel_exp_under_ctx_elim_cong _ _ _ (valid_groups_of_emb _ _ _ _ Hμ) Hl Γ oq oq' m Mm bm Bks Bks' Ps Ps' M M' i
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
     vwrap_ok D D' vm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim oq Us m Bks M
       ≈ a_elim (Some qc) (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
           (vwrap p D D' vm (List.firstn (ind_nu D) Ps) Bks) M
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl Hgr HMm Hh Hq _ Hbm HLb HPl HPs HM -> Hnm _ HA HMx HBn HBc Har HB; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  pose proof (valid_groups_of_emb _ _ _ _ Hμ) as HVP.
  pose proof (valid_group_lookup _ _ (valid_groups_valid _ HVP qc D' Hq)) as Hq'.
  refine (rel_exp_under_ctx_elim_view _ _ _ HVP Hl Γ oq m Mm qc k' Is vm D' bm Bks Ps M i
            ltac:(assumption) Hgr HMm Hh Hq' Hbm HLb HPl _ ltac:(eassumption) Hnm _ _ HBn _ Har _).
  - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
  - intros * HMk; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMk _ _ Hμ))).
  - intros * HMk Hb; exact (sem_exp_eq_at_rel (HA _ _ _ HMk Hb _ _ Hμ)).
  - intros * HMk Hcon; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HBc _ _ _ _ HMk Hcon _ _ Hμ))).
  - intros * HMk Hb Hcon Hin; exact (sem_exp_eq_at_rel (HB _ _ _ _ _ _ _ HMk Hb Hcon Hin _ _ Hμ)).
Qed.
