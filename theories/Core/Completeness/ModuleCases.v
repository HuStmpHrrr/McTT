(** * The Rules of Module Expressions

    The rules of [⊢ᵐ] and of members in the PER model.  Each reads its
    premises at the target of a sound embedding ([sem_intro]) and
    concludes there by its lemma at one global context, in
    [Modules/ModuleLemmas.v] and [Modules/Slots.v]. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup Paths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Contexts Functions Lets Levels Subtyping Props
  Universes Variables Instance Telescope.
From Mctt.Core.Completeness.Modules Require Import Slots MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Con Elim ElimViewRule Iota Decl.
From Mctt.Core.Completeness.Modules Require Import ModuleValues Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Mem Canon App Sel ModuleLemmas.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Fixed_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Lemma sem_me_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H ).
Proof. intros * HH; sem_intro; first [ assumption | exact (rel_modexp_under_ctx_sym HH) ]. Qed.

Lemma sem_me_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H'' ).
Proof. intros * H1 H2; sem_intro; first [ assumption | exact (rel_modexp_under_ctx_trans H1 H2) ]. Qed.

Lemma sem_me_unit :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_unit fp ≈ me_unit fp ).
Proof. intros; sem_intro0; close_modexp_left valid_modexp_unit. Qed.

Lemma sem_me_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_var x ≈ me_var x ).
Proof.
  intros * Hw HΓ Hl; sem_intro; add_valid_slots;
    pose proof (valid_modexp_var Hgw _ _ Hgm Hsub _ _ _ ltac:(eapply wf_me_var; eassumption) HΓ Hok Hl) as [Hs HK];
    [ assumption | eapply rel_modexp_under_ctx_var; eassumption | exact Hs | exact Hs ].
Qed.

Lemma sem_me_lit :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_lit U ≈ me_lit U' ).
Proof.
  intros * HU; sem_intro; [ assumption | exact (rel_unit_under_ctx_lit _ _ _ HU) | apply (valid_modexp_of_valid_unit _ _ Hgf); assumption .. ].
Qed.

Lemma sem_me_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod_tele R = Some T ->
     mdenote Θ Ξ Γ (me_mem H' y) R' ->
     mdesc_mod_tele R' = Some T' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ me_mem H' y ).
Proof. intros; sem_intro0; close_modexp valid_modexp_mem. Qed.

Lemma sem_me_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ H R ->
     mdesc_mod_tele R = Some T ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ B : Srt ->
     evaluated_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : B ->
     mdenote Θ Ξ Γ H' R' ->
     mdesc_mod_tele R' = Some T' ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B' : Srt' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ B' : Srt' ->
     evaluated_sort Srt' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app H N ≈ me_app H' N' ).
Proof. intros; sem_intro0; close_modexp valid_modexp_app. Qed.

Lemma sem_me_delta_slot :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_var x ≈ me_lit U ).
Proof.
  intros * Hw HΓ Hl; sem_intro; add_valid_slots;
    pose proof (valid_modexp_var Hgw _ _ Hgm Hsub _ _ _ ltac:(eapply wf_me_var; eassumption) HΓ Hok Hl) as [Hs HK];
    [ assumption | eapply rel_modexp_under_ctx_delta_slot; eassumption | exact Hs
    | exact (valid_modexp_of_valid_unit _ _ Hgf _ _ HK) ].
Qed.

Lemma sem_me_delta_sel :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ me_mem H y ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod R = Some Rm ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ mdesc_unit Rm ).
Proof.
  intros * HH Hm Hmd; sem_intro; try assumption;
    assert (Hc : Γ ⊨ᵐ me_mem H y ≈ mdesc_unit Rm /\ valid_unit Θ Ξ Γ (mdesc_unit Rm))
      by (eapply valid_modexp_canon; eassumption).
  - exact (proj1 Hc).
  - exact (valid_modexp_of_valid_unit _ _ Hgf _ _ (proj2 Hc)).
Qed.

Lemma sem_me_beta_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_body sm_open (gmod_sub Φ (sb_qn (length Δ) (Id,,N))))) ).
Proof. intros; sem_intro0; close_modexp valid_modexp_beta_body. Qed.

Lemma sem_me_beta_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (length Δ) (Id,,N)]ᵐ)) ).
Proof. intros; sem_intro0; close_modexp valid_modexp_beta_alias. Qed.

Lemma sem_me_beta_alias0 :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E ->
     frame_free_target Θ Ξ Γ E ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E ).
Proof. intros; sem_intro0; close_modexp_left valid_modexp_beta_alias0. Qed.

Lemma sem_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     (forall M, mdesc_reduct R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊨ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x : A ).
Proof.
  intros * HH Hm Ht _ _ _; sem_intro; [ assumption |].
  assert (Hsm : valid_mem Γ H x A (mdesc_reduct R)) by (eapply (proj2 (valid_unit_mem_all _ _ Hgm Hgf)); eassumption).
  exact (rel_mem_of_valid_mem _ _ _ _ _ _ HH Hsm).
Qed.

Lemma sem_exp_eq_mem_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdenote Θ Ξ Γ (me_mem H' x) R' ->
     mdesc_type R' = Some A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H' x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x ≈ a_mem H' x : A ).
Proof.
  intros * HH Hm Ht Hm' Ht' _; sem_intro; [ assumption |].
  assert (Hsm : valid_mem Γ H x A (mdesc_reduct R)) by (eapply (proj2 (valid_unit_mem_all _ _ Hgm Hgf)); eassumption).
  apply rel_exp_under_ctx_sym.
  exact (rel_mem_of_valid_mem _ _ _ _ _ _ (rel_modexp_under_ctx_sym HH) Hsm).
Qed.

Lemma sem_exp_eq_mem_delta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdesc_reduct R = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x ≈ M : A ).
Proof.
  intros * HH Hm Ht Hr; sem_intro; [ assumption |].
  assert (Hsm : valid_mem Γ H x A (mdesc_reduct R)) by (eapply (proj2 (valid_unit_mem_all _ _ Hgm Hgf)); eassumption).
  rewrite Hr in Hsm.
  exact (rel_mem_red_of_valid_mem _ _ _ _ _ _ HH Hsm).
Qed.
