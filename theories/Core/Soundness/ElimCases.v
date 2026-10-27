(** * The Eliminator in the Gluing Model

    The gluing rules of the eliminator and of its congruence and view
    rules.  An elimination is glued at the target of a sound embedding,
    where the groups of the source are valid groups
    ([valid_groups_of_glu_emb], [Inductives/Elim.v]). *)

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
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
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
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

(** ** The Rules

    The eliminator reads syntactic premises of its rule: its parts are
    typed by their derivations, moved to the target of the embedding. *)

#[local] Generalizable All Variables.

Lemma glu_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
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
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊩ eb_motive b : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_elim oq Us m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof.
  intros * Hl Hgr HMm Hbm HLb HPl HPt HPg HMt HMg -> Hnm Hann HAt HAg HMx Hna HBx Har HBt HBg Θ2 Ξ2 Hμ.
  pose proof (glu_emb_emb _ _ _ _ Hμ) as Hem.
  destruct (emb_preserves_wf _ _ _ _ Hem) as (_ & Hwe & _ & _ & Hwx & _ & _).
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HMt)) as Hg.
  pose proof (valid_groups_of_glu_emb _ _ _ _ Hg Hem) as HVP.
  eapply (@glu_rel_exp_elim (gc_mk Θ2 Ξ2) _ p D HVP (glu_emb_ind_field _ _ _ _ Hμ) Hl Γ oq m Mm bm Bks Ps M i
            Hgr HMm Hbm HLb HPl); intros.
  all: first
    [ eapply Hwe; eauto
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
