(** * The Global Rules in the Gluing Model, at the Target

    The soundness counterpart of [Core/Completeness/Modules/ModuleLemmas.v]: the
    members and the module expressions, at every target of a sound
    embedding ([glu_gctx_embedding]).  A member is glued by
    [glu_rel_exp_member_under_sub], read through the stored modules its
    module expression reads.  A module expression equation glues both its
    sides ([glu_modexp]): at the instances, with deep parts, the context's
    module parts deep.  A path is glued as the module it names
    ([glu_rel_modexp_under_sub_path_mod_of_source]), a slot and a literal
    by their units, a selection by [glu_rel_modexp_under_sub_mem_of_source],
    an application by [glu_rel_modexp_under_sub_app]; the right-hand side
    of [δ] for selections is the unit the selection's deep description
    stands for ([glu_desc_deep_of_source], [glu_mdesc_unit_of_deep]), and
    that of [β] the literal instantiated, deep by (c). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup Paths DescTyping LookupSound.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Contexts LogicalRelation.Variables Modules.ModuleValues
  LogicalRelation.Instance Modules.ModexpInstances Modules.UnitEq Modules.UnitDeep Modules.Sel Modules.Mem
  Modules.DescDeep.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** At a target *)

Section AtTarget.
  Variables (Θs : gdeps) (Ξs : gstack) (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hgs : ⊢ᵍ Θs ⍮ Ξs.
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis Hμ : glu_gctx_embedding Θs Ξs Θ Ξ.
  #[local] Instance GCt : GCtx := gc_mk Θ Ξ.

  (** A literal of a deep unit typed at the source is glued at the target. *)
  Lemma glu_modexp_at_target_lit : forall Γ U,
      Θs ⍮ Ξs ⍮ Γ ⊢ᵘ U ≈ U -> glu_rel_ctx_types Γ -> glu_ctx_deep Γ -> glu_unit_deep Γ U ->
      glu_modexp_at_target Θ Ξ Γ (me_lit U).
  Proof.
    intros * HU HΓ Hd HUd.
    destruct (gctx_embedding_preserves_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as (_ & _ & _ & _ & _ & Hwu & _).
    constructor; [| exact HUd | exact Hd ].
    apply glu_rel_modexp_under_sub_lit; [ exact HΓ | exact (Hwu _ _ _ HU) |].
    intros Γ' τ Hτ; exact (glu_unit_deep_inst _ _ HUd _ _ Hτ).
  Qed.

  (** An application, typed at the source, of a glued module expression to
      a glued argument at its next parameter is glued at the target: at the
      instances by [glu_rel_modexp_under_sub_app], at the description grown
      to the target; the argument is a deep part, at the parameter of every
      description of the head there. *)
  Lemma glu_modexp_at_target_app : forall Γ H N R T B T1 Srt,
      Θs ⍮ Ξs ⍮ Γ ⊢ᵐ H ≈ H -> glu_modexp_at_target Θ Ξ Γ H ->
      mdenote Θs Ξs Γ H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
      Θs ⍮ Ξs ⍮ Γ ⊢ B : Srt -> evaluated_sort Srt -> Θs ⍮ Ξs ⍮ Γ ⊢ N : B -> glu_rel_exp_under_sub Γ N B ->
      glu_modexp_at_target Θ Ξ Γ (me_app H N).
  Proof.
    intros * HH [HHi HHp HHd] Hm HT Hv HB HS HN HNg.
    pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
    pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hsub.
    destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & Hwe & _ & _ & _ & _ & Hwm & _).
    assert (HHN : Θs ⍮ Ξs ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N)
      by (eapply wf_me_app; eauto using wf_exp_eq_refl).
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ Hm) as (Rt & HmRt & Hgr).
    pose proof (mdesc_grows_mtele _ _ _ _ _ _ _ Hgr HT) as HTt.
    constructor; [| | exact HHd ].
    - exact (glu_rel_modexp_under_sub_app _ _ Hg _ _ _ _ _ _ _ _ (Hwm _ _ _ HHN) HHi HNg HmRt HTt Hv (Hwe _ _ _ HB) HS (Hwe _ _ _ HN)).
    - cbn [glu_modexp_parts_deep]; split; [ exact HHp |].
      constructor; [ exact (Hwm _ _ _ HH) |].
      intros R' T' B' T1' HmR' HT' Hv'.
      rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmR' _ HmRt), HTt in HT'; injection HT' as <-.
      rewrite Hv in Hv'; injection Hv' as <- _; exact HNg.
  Qed.

End AtTarget.

(** ** The rules

    The members read syntactic premises of their rules: the premises the
    case needs at the target are the syntactic ones moved along the
    embedding. *)

#[local] Generalizable All Variables.

(** A module expression glued at every target gives its context's gluing. *)
Lemma glu_ctx_of_modexp : forall Θ Ξ Γ H, glu_modexp Θ Ξ Γ H -> ⊩ Θ ⍮ Ξ ⍮ Γ.
Proof.
  intros * HH Θ2 Ξ2 Hμ; destruct (HH _ _ Hμ) as [HHi _ HHd].
  split; [ exact (glu_rel_modexp_under_sub_ctx _ _ HHi) | exact HHd ].
Qed.

(** *** Members *)




(** *** Module expressions

    The extensions and the units are in [Modules/Extensions.v] and
    [Modules/UnitEq.v]. *)








(** A literal given its outermost parameter: the application by
    [glu_modexp_at_target_app] at the literal's description, whose
    telescope ends in the parameter; the literal instantiated deep by (c),
    the parameter typed at the instances as the unit's outermost one. *)
Lemma glu_me_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) D ≈ gu_mk (Δ ++ ce_ass κ X :: nil) D ->
     glu_unit_eq Θ Ξ Γ (gu_mk (Δ ++ ce_ass κ X :: nil) D) (gu_mk (Δ ++ ce_ass κ X :: nil) D) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : X ->
     glu_modexp Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N) /\
     glu_modexp Θ Ξ Γ (me_lit (gu_mk (tele_sub Δ (Id,,N)) (moddef_sub D (sb_qn (length Δ) (Id,,N))))) ).
Proof.
  intros * HU HUe HN HNg.
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hgs.
  destruct (gen_beta _ _ _ _ _ _ _ _ HU HN) as [Hl Hr]; cbn [gen_m] in Hl.
  destruct Hl as (HL & R & T & B & T1 & Srt & HmR & HT & Hv & HB & HS & HNB).
  (** The literal's telescope ends in the parameter *)
  assert (EB : B = X).
  { inversion HmR; subst; try match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    - match goal with Hb : mdesc_body _ ?sm _ _ _ = Some _ |- _ =>
        destruct sm; cbn in Hb; [ injection Hb as <- | discriminate ] end.
      cbn in HT; injection HT as <-; rewrite tele_view_last in Hv; injection Hv as <- _; reflexivity.
    - destruct (mdesc_mod_tele_up_inv _ _ _ HT) as (T0 & ->).
      rewrite app_assoc, tele_view_last in Hv; injection Hv as <- _; reflexivity. }
  subst B.
  destruct HUe as [HΓg HUg _].
  split; intros Θ2 Ξ2 Hμ; destruct (HΓg _ _ Hμ) as [HΓt HΓd]; destruct (HUg _ _ Hμ) as [_ HUd _];
    pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  - exact (glu_modexp_at_target_app _ _ _ _ Hgs Hg2 Hμ _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU)
             (glu_modexp_at_target_lit _ _ _ _ Hμ _ _ HU HΓt HΓd HUd) HmR HT Hv HB HS HNB (proj1 (HNg _ _ Hμ))).
  - cbn [gen_m] in Hr; rewrite gunit_sub_mk in Hr.
    (** The outermost parameter, glued at the instances *)
    assert (HX : @glu_rel_ext_under_sub (gc_mk Θ2 Ξ2) Γ (Δ ++ ce_ass κ X :: nil)).
    { destruct D as [sm Φ | E]; cbn [glu_unit_deep] in HUd;
        [ exact (glu_rel_ext_under_sub_app_inv _ (proj1 HUd)) | exact (glu_alias_deep_parts_params _ _ _ _ HUd) ]. }
    pose proof (glu_rel_ext_under_sub_app_inv _ HX) as HX1; cbn [glu_rel_ext_under_sub] in HX1.
    destruct HX1 as [_ (S & HSk & HXS)].
    exact (glu_modexp_at_target_lit _ _ _ _ Hμ _ _ (unit_eq_of_full _ _ _ _ Hr) HΓt HΓd
             (glu_unit_deep_beta _ _ _ _ _ _ _ HUd (glu_rel_exp_under_sub_wf HXS) HSk (proj1 (HNg _ _ Hμ)))).
Qed.





