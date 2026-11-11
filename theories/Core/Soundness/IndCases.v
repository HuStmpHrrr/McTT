(** * Inductive Types in the Gluing Model: the Type Former and the Constructors

    The gluing rules of the type former and the constructors of an
    inductive type, and of their congruences.  The type former and the
    constructors are glued at the target of a sound embedding
    ([Inductives/Con.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Completeness.Inductives Require Elim.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases
  Instances.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes.
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon ArgTypes Bridge.
Require Import Mctt.Core.Soundness.Inductives.Elim.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

(** ** The Rules

    The type former and the constructors read syntactic premises of their
    rules: a declaration is typed by its derivation. *)

#[local] Generalizable All Variables.

(** The type former of a declared member: the group of the source is a
    valid group of the target, where the former is glued
    ([glu_rel_exp_ind0]). *)
Lemma glu_ind :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     k < ind_ndecl D ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_ind p k : ind_ty D M ).
Proof.
  intros * HΓ HΓg Hl HM Hlt Θ2 Ξ2 Hμ.
  pose proof (valid_groups_of_glu_gctx_embedding _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as HVP.
  pose proof (valid_groups_valid _ HVP p D Hl) as Hg.
  destruct (member_lt_decl _ _ _ _ _ (valid_group_typed _ _ Hg) HM Hlt) as [pm Hh].
  split; [| exact (proj2 (HΓg _ _ Hμ)) ].
  econstructor; [ exact (proj1 (HΓg _ _ Hμ)) | intros Γ' τ Hτ ].
  cbn [exp_sub]; rewrite (ind_ty_sub D k M τ (valid_group_closed _ _ Hg) HM).
  apply glu_rel_exp_nil_weaken; [ exact (glu_rel_sub_inst_ctx _ _ _ Hτ) |].
  exact (glu_rel_exp_ind0 p D (valid_group_lookup _ _ Hg) (glu_gctx_embedding_ind_field _ _ _ _ Hμ _ _ Hl) (valid_group_closed _ _ Hg) (valid_group_typed _ _ Hg)
           (valid_group_sort _ _ Hg) (valid_group_ass _ _ Hg)
           (valid_group_self_ends _ HVP (glu_gctx_embedding_ind_field _ _ _ _ Hμ) p D Hl) k M pm HM Hh).
Qed.

(** A constructor, of a declared member or of a view: glued at the target
    ([glu_rel_exp_con0], [glu_rel_exp_con_view0]), closed, then weakened. *)
Lemma glu_con :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     ind_con M c = Some gs ->
     ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D M gs ++ im_params D M ->
     ⊩ Θ ⍮ Ξ ⍮ cargs_ctx p D M gs ++ im_params D M ->
     (forall gs1 t gs2 j, gs = gs1 ++ ca_rec t :: gs2 -> j <= List.length (ptyp_doms t) ->
        ⊢ Θ ⍮ Ξ ⍮ (shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D M gs1 ++ im_params D M)
                  ▹{ak_relevant} ptyp_ty p D (im_nn M) (List.repeat false j ++ cargs_pat gs1) (ptyp_skip j t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D k M gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_con p k c : con_ty p D k M gs ).
Proof.
  intros * HΓ HΓg Hl HM Hcon HΨ HΨg Hsh HT Θ2 Ξ2 Hμ.
  pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & Hwe & _).
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg0.
  pose proof (valid_groups_of_glu_gctx_embedding _ _ _ _ Hg0 Hem) as HVP.
  pose proof (glu_gctx_embedding_ind_field _ _ _ _ Hμ) as HGall.
  pose proof (valid_group_self_ends _ HVP HGall) as HSall.
  pose proof (glu_rview_records_of_glu_gctx_embedding _ _ _ _ Hg0 Hμ) as HRall.
  pose proof (fun qn G H => glu_views_ok_all _ qn G HVP H (HGall _ _ H) HGall HSall HRall) as Hviewsall.
  assert (Hc0 : Θ ⍮ Ξ ⍮ ⋅ ⊢ a_con p k c : con_ty p D k M gs)
    by (eapply wf_con; [ constructor; exact Hg0 | eassumption .. ]).
  pose proof (Hwe _ _ _ HT) as HT2; pose proof (Hwe _ _ _ Hc0) as Hc2.
  pose proof (glu_rel_ctx_types_ctx _ (proj1 (HΨg _ _ Hμ))) as HΨ2.
  split; [| exact (proj2 (HΓg _ _ Hμ)) ].
  econstructor; [ exact (proj1 (HΓg _ _ Hμ)) | intros Γ' τ Hτ ].
  cbn [exp_sub]; rewrite (con_ty_sub p D k M c gs τ (valid_group_closed _ _ (valid_groups_valid _ HVP p D Hl)) HM Hcon).
  apply glu_rel_exp_nil_weaken; [ exact (glu_rel_sub_inst_ctx _ _ _ Hτ) |].
  destruct (im_head M) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
  - exact (glu_rel_exp_con0 _ p D HVP Hl (HGall _ _ Hl) (Hviewsall _ _ Hl) HGall HSall k M pm c gs HM Hh Hcon HΨ2 i HT2 Hc2).
  - exact (glu_rel_exp_con_view0 _ HVP HGall Hviewsall HSall p D Hl k M qc kc Is vm c gs HM Hh Hcon HΨ2
             (fun Dq Mc gs' Hq HMc Hc => glu_rel_ctx_types_ctx _ (glu_group_cargs _ HVP HGall HSall qc Dq kc Mc c gs'
                                         (valid_groups_containers _ HVP _ _ _ _ _ _ _ _ _ Hl HM Hh Hq) HMc Hc))
             i HT2 Hc2).
  - exact (glu_rel_exp_con_rview0 _ HVP HGall Hviewsall HSall HRall p D Hl k M qr Is fl c gs HM Hh Hcon HΨ2 i HT2 Hc2).
Qed.

Lemma glu_exp_eq_ind_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_con_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** A constructor of a view against the container's: the context. *)
Lemma glu_exp_eq_con_view :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** A constructor of a record view against the tuple of its fields: the
    context. *)
Lemma glu_exp_eq_con_rview :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
