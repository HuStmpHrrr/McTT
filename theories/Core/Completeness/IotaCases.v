(** * The [ι] Rule of a Group of Inductive Types

    The semantic rule of [ι]: the eliminator at a constructor of a member
    is the constructor's branch at the arguments and the recursive
    results.  It holds because the group is valid at the target of a sound
    embedding ([valid_groups_of_emb]), where the two sides are related
    ([Inductives/Iota.v]). *)

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
From Mctt.Core.Completeness.Inductives Require Import Elim.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Completeness.Inductives Require Import Iota.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

#[local] Generalizable All Variables.

Lemma sem_exp_eq_elim_iota :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     ind_con Mm c = Some gs ->
     List.length Bks = List.length (ind_members D) ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     List.length As = List.length gs ->
     (forall k N T, nth_error As k = Some N -> nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ N : T) ->
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
        n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     brs_lookup (eb_brs bm) c = Some (n, B) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim oq Us m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                    (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As))
       ≈ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++
                          elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As)]
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                          apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                            (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)] ).
Proof.
  intros * HΓ Hl Hgr HMm Hbm Hcon HLb HPl HPs HAl HAs -> Hnm _ HA HMx HBn HBc Har HB Hlk; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  refine (rel_exp_under_ctx_elim_iota_at _ _ _ (valid_groups_of_emb _ _ _ _ Hμ) Hl Γ oq m Mm bm Bks c gs Ps As i
            ltac:(assumption) Hgr HMm Hbm Hcon HPl _ HAl _ _ Hnm _ _ HBn _ Har _ n B Hlk).
  - intros * HP HT; exact (sem_exp_eq_at_rel (HPs _ _ _ HP HT _ _ Hμ)).
  - intros * HN HT; exact (sem_exp_eq_at_rel (HAs _ _ _ HN HT _ _ Hμ)).
  - intros * HMj; apply nth_error_lt_some'; rewrite HLb; apply List.nth_error_Some; unfold ind_member in HMj; congruence.
  - intros * HMk; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HMx _ _ HMk _ _ Hμ))).
  - intros * HMk Hb; exact (sem_exp_eq_at_rel (HA _ _ _ HMk Hb _ _ Hμ)).
  - intros * HMk Hc0; exact (valid_ctx_rel_ctx_wf (sem_ext_eq_at_ext (HBc _ _ _ _ HMk Hc0 _ _ Hμ))).
  - intros * HMk Hb Hc0 Hin; exact (sem_exp_eq_at_rel (HB _ _ _ _ _ _ _ HMk Hb Hc0 Hin _ _ Hμ)).
Qed.
