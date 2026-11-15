(** * The Set Rules of Inductive Types

    The rules of the type formers and constructors of inductive types in
    the set model, with the constructor views.  The lemmas they rest on are
    in [Inductives/Model.v] and [Inductives/Elim.v]. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution Universes Props Functions.
From Mctt.Core.SetModel Require Import Modules.ValidUnit Modules.MemberTypes Modules.Sel Inductives.Model
  Records.Model Inductives.Elim.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members Presup CoreInversions.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing UniformParams.
Import ListNotations.

Section Inductives.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_rule_ind : forall Γ p k D Mk, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ ->
    ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk ->
    set_exp_eq Θ Ξ T γ Γ (ind_ty D Mk) (a_ind p k) (a_ind p k).
Proof.
  intros * Hc HΓ HDs Hk. set_open. destruct HΓ as [HΓ _]. pose proof (set_source_groups T γ Θ Ξ Hμ _ _ HDs) as HG.
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θ Ξ Hμ) HDs) as HD.
  destruct (set_group_ok_former_types _ _ _ _ _ HG _ _ Hk) as (FA & HFA).
  apply (set_exp_eq_closed_global T γ Hfn Hmods Hgw _ _ (global_former γ p k) FA); try assumption.
  - exact (decl_closed_ind_ty _ _ _ (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hgw) HD) Hk).
  - exact (set_group_ok_formers_typed _ _ _ _ _ HG _ _ _ Hk HFA).
  - intros ρ. econstructor; eassumption.
Qed.

Lemma set_rule_con : forall Γ p k c D Mk gs i, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ ->
    ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    Θ ⍮ Ξ ⍮ nil ⊢ con_ty p D k Mk gs : a_typ i -> set_exp_eq Θ Ξ T γ nil (a_typ i) (con_ty p D k Mk gs) (con_ty p D k Mk gs) ->
    set_exp_eq Θ Ξ T γ Γ (con_ty p D k Mk gs) (a_con p k c) (a_con p k c).
Proof.
  intros * Hc HΓ HDs Hk Hcon Hw Hty. set_open. destruct HΓ as [HΓ _]. destruct Hty as (FS & FA & FA' & [_ HFA _ _ _]).
  pose proof (set_source_groups T γ Θ Ξ Hμ _ _ HDs) as HG.
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θ Ξ Hμ) HDs) as HD.
  apply (set_exp_eq_closed_global T γ Hfn Hmods Hgw _ _ (global_constructor γ p k c) FA); try assumption.
  - exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ Hw))).
  - exact (set_group_ok_constructors_typed _ _ _ _ _ HG _ _ _ _ _ Hk Hcon HFA).
  - intros ρ. econstructor; eassumption.
Qed.

End Inductives.
Section Eliminator.
  (** The context the rules' premises are read at ([Ξ] names contexts below) *)
  Variable Θr : gdeps.
  Variable Ξr : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** A constructor of a view at the uniform parameters [Us], typed one by
    one and holding in the model, applied to [Ms], is in the model the
    container's constructor at the view's instance there. *)
Lemma set_rule_con_view : forall Γ p D j Mj qc k Is vm c Us Ms A,
    set_ctx_slots Θr Ξr T γ Γ ->
    ind_lookup Θr Ξr p = Some D ->
    ind_member D j = Some Mj ->
    im_head Mj = mh_view qc k Is vm ->
    List.length Us = ind_nu D ->
    (forall n U B, List.nth_error Us n = Some U -> List.nth_error (tele_insts (ind_uparams D) sb_id Us) n = Some B ->
       Θr ⍮ Ξr ⍮ Γ ⊢ U : B) ->
    (forall n U B, List.nth_error Us n = Some U -> List.nth_error (tele_insts (ind_uparams D) sb_id Us) n = Some B ->
       set_exp_eq Θr Ξr T γ Γ B U U) ->
    Θr ⍮ Ξr ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) : A ->
    set_exp_eq Θr Ξr T γ Γ A (apps_exp (a_con p j c) (Us ++ Ms)) (apps_exp (a_con p j c) (Us ++ Ms)) ->
    set_exp_eq Θr Ξr T γ Γ A (apps_exp (a_con qc k c) (im_pre Mj Us ++ Ms)) (apps_exp (a_con qc k c) (im_pre Mj Us ++ Ms)) ->
    set_exp_eq Θr Ξr T γ Γ A (apps_exp (a_con p j c) (Us ++ Ms)) (apps_exp (a_con qc k c) (im_pre Mj Us ++ Ms)).
Proof.
  intros * HΓ HDsrc Hj Hh HUl HUt0 HUsem0 HLt HL HR. set_open. destruct HΓ as [HΓ _].
  pose proof (fun n U B H1 H2 => proj1 (proj2 (gctx_embedding_preserves_wf _ _ _ _ Hμe)) _ _ _ (HUt0 n U B H1 H2)) as HUt.
  pose proof (fun n U B H1 H2 => HUsem0 n U B H1 H2 _ _ Hμ) as HUsem. cbv beta in HUt, HUsem.
  destruct HL as (FA & FL & FL' & [HFA HFL _ _ HLm]). destruct HR as (FA2 & FR & FR' & [_ HFR _ _ _]).
  exists FA, FL, FR. constructor; [exact HFA | exact HFL | exact HFR | | exact HLm].
  eapply set_con_view_values_eq; eassumption.
Qed.

(** The constructor of a record view at the uniform parameters [Us] and
    the fields [Ms], typed one by one and holding in the model, is in the
    model the tuple of the fields. *)
Lemma set_rule_con_rview : forall Γ p D j Mj qr Is fl c gs Us Ms A,
    set_ctx_slots Θr Ξr T γ Γ ->
    ind_lookup Θr Ξr p = Some D ->
    ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl ->
    ind_con Mj c = Some gs ->
    List.length Us = ind_nu D ->
    (forall n U B, List.nth_error Us n = Some U -> List.nth_error (tele_insts (ind_uparams D) sb_id Us) n = Some B ->
       Θr ⍮ Ξr ⍮ Γ ⊢ U : B) ->
    (forall n U B, List.nth_error Us n = Some U -> List.nth_error (tele_insts (ind_uparams D) sb_id Us) n = Some B ->
       set_exp_eq Θr Ξr T γ Γ B U U) ->
    List.length Ms = List.length fl ->
    (forall n N B, List.nth_error Ms n = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mj gs) (sb_of_list sb_id Us) Ms) n = Some B -> Θr ⍮ Ξr ⍮ Γ ⊢ N : B) ->
    (forall n N B, List.nth_error Ms n = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mj gs) (sb_of_list sb_id Us) Ms) n = Some B -> set_exp_eq Θr Ξr T γ Γ B N N) ->
    Θr ⍮ Ξr ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) : A ->
    set_exp_eq Θr Ξr T γ Γ A (apps_exp (a_con p j c) (Us ++ Ms)) (apps_exp (a_con p j c) (Us ++ Ms)) ->
    set_exp_eq Θr Ξr T γ Γ A (a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl Ms))
      (a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl Ms)) ->
    set_exp_eq Θr Ξr T γ Γ A (apps_exp (a_con p j c) (Us ++ Ms)) (a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl Ms)).
Proof.
  intros * HΓ HDsrc Hj Hh Hgs HUl HUt0 HUsem0 HMl HMt0 HMsem0 HLt HL HR. set_open. destruct HΓ as [HΓ _].
  pose proof (fun n U B H1 H2 => proj1 (proj2 (gctx_embedding_preserves_wf _ _ _ _ Hμe)) _ _ _ (HUt0 n U B H1 H2)) as HUt.
  pose proof (fun n U B H1 H2 => HUsem0 n U B H1 H2 _ _ Hμ) as HUsem.
  pose proof (fun n N B H1 H2 => proj1 (proj2 (gctx_embedding_preserves_wf _ _ _ _ Hμe)) _ _ _ (HMt0 n N B H1 H2)) as HMt.
  pose proof (fun n N B H1 H2 => HMsem0 n N B H1 H2 _ _ Hμ) as HMsem. cbv beta in HUt, HUsem, HMt, HMsem.
  destruct HL as (FA & FL & FL' & [HFA HFL _ _ HLm]). destruct HR as (FA2 & FR & FR' & [_ HFR _ _ _]).
  exists FA, FL, FR. constructor; [exact HFA | exact HFL | exact HFR | | exact HLm].
  eapply set_con_rview_values_eq; eassumption.
Qed.

End Eliminator.
