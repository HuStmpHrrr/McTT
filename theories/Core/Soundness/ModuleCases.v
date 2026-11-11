(** * The Global Rules in the Gluing Model, at the Target

    The soundness counterpart of [Core/Completeness/ModuleCases.v]: the
    members, at the target of a sound embedding ([glu_gctx_embedding]), where the
    members of the stored bodies that have no δ-reduct, the axioms and
    abstract definitions read bare, glue as neutrals.  Module values are
    not glued: a member with a δ-reduct glues as the reduct, which
    [wf_mem] premises typed, and one without is the filed member its module
    expression is equal to ([mem_alias_filed]).  The rules of the members,
    the extensions, the units and the module expressions are stated after
    them, as the cases of the gluing judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Modules Require Import Values.
From Mctt.Core.Completeness Require Import ModuleCases.
From Mctt.Core.Completeness.Global Require Import Embedding.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases UnitCases Selection.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Equations, at the target *)

(** A term equal to one that glues glues, the equation moved to the target. *)
Lemma glu_rel_exp_of_eq_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ M N A,
    glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ N A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.
Proof.
  intros * He Heq Hg.
  destruct (gctx_embedding_preserves_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ He)) as (_ & _ & Hwq & _).
  eapply (@glu_rel_exp_of_eq (gc_mk Θ2 Ξ2)); [ exact Hg | exact (Hwq _ _ _ _ Heq) ].
Qed.

(** ** 2. Members

    [mem_no_red] is in [Selection.v]. *)

(** A member glues: as its δ-reduct, which glues by the premise of [wf_mem];
    without one, as the filed member it is equal to. *)
Lemma glu_rel_exp_mem_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ H x R A,
    glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A ->
    (forall M, mdesc_reduct R = Some M -> forall Θ0 Ξ0, glu_gctx_embedding Θ Ξ Θ0 Ξ0 -> @glu_rel_exp (gc_mk Θ0 Ξ0) Γ M A) ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem H x) A.
Proof.
  intros * He HH Hm Ht HM HΓ.
  destruct (mdesc_reduct R) as [M |] eqn:Hr.
  - eapply glu_rel_exp_of_eq_of_embedding; [ exact He | eapply wf_exp_eq_mem_delta; eassumption | exact (HM _ eq_refl _ _ He) ].
  - pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    destruct (mem_no_red _ _ _ _ _ _ _ Hm Ht Hr) as (R0 & p & T & Φ & Φ0 & b & pv & κ & oM & Hm0 & Hmd & Hp & Hn).
    pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm0) Hmd) as Hl; cbn in Hl.
    eapply glu_rel_exp_of_eq_of_embedding; [ exact He | eapply mem_alias_filed; eassumption |].
    eapply glu_gctx_embedding_glob; eassumption.
Qed.

(** ** 3. The rules

    The members read syntactic premises of their rules: the premises the
    case needs at the target are the syntactic ones moved along the
    embedding. *)

#[local] Generalizable All Variables.

(** *** Members *)

Lemma glu_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     (forall M, mdesc_reduct R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊩ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_mem H x : A ).
Proof. glu_intro; eapply glu_rel_exp_mem_of_embedding; eassumption. Qed.

Lemma glu_exp_eq_mem_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdenote Θ Ξ Γ (me_mem H' x) R' ->
     mdesc_type R' = Some A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_mem H' x : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_mem_delta :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdesc_reduct R = Some M ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** *** Module expressions

    The extensions and the units are in [Extensions.v] and
    [UnitEqCases.v]. *)

Lemma glu_me_unit :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_var :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_lit :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_mem :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod_tele R = Some T ->
     mdenote Θ Ξ Γ (me_mem H' y) R' ->
     mdesc_mod_tele R' = Some T' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_app :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_delta_slot :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_delta_sel :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod R = Some Rm ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_beta_body :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : X ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_beta_alias :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : X ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_beta_alias0 :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_sym :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_trans :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
