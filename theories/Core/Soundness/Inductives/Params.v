(** * Glued Arguments of Closed Telescopes of Parameters

    Terms glued at the instances of a closed glued telescope, along a glued
    substitution, are glued arguments of the telescope at their values
    ([params_glu_args]).  The value of each instance is related to the
    value of the entry's type at the values before it ([closed_inst_typ]),
    and the witness the term moves to is the entry's type, glued at the
    substitution the arguments before it make ([glu_args_of_related]).
    Used by the inductive types' and the records' formers at their
    parameters. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.LogicalRelation Require Substitution Instance.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness.Modules Require MemberTypes Filed.
From Mctt.Core.Completeness Require ContextCases UnitCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation.
From Mctt.Core.Soundness.Inductives Require Import Args.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** An entry of a context, by its index in the reversed context: the
    context split around it, with the part after it of that length. *)
Lemma ctx_rev_split : forall (C : ctx) k e, List.nth_error (List.rev C) k = Some e ->
    exists C1 Pre, C = C1 ++ e :: Pre /\ List.length Pre = k.
Proof.
  intros * H; destruct (List.nth_error_split _ _ H) as (l1 & l2 & E & Hl).
  exists (List.rev l2), (List.rev l1); split; [| rewrite List.length_rev; exact Hl ].
  rewrite <- (List.rev_involutive C), E, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity.
Qed.

(** A prefix of a sequence is the shorter sequence. *)
Lemma firstn_seq_le : forall k n s, k <= n -> List.firstn k (List.seq s n) = List.seq s k.
Proof.
  intros * Hk; replace n with (k + (n - k)) by lia.
  rewrite List.seq_app, List.firstn_app, List.length_seq, Nat.sub_diag, List.firstn_all2 by (rewrite List.length_seq; lia).
  cbn; apply List.app_nil_r.
Qed.

(** An instance of a telescope's suffix [Pre] at the first terms is the
    instance of the whole telescope there. *)
Lemma tele_insts_prefix_nth : forall C1 Pre Ms k T, all_assumptions Pre -> List.length Pre <= List.length Ms ->
    List.nth_error (tele_insts Pre Id (List.firstn (List.length Pre) Ms)) k = Some T ->
    List.nth_error (tele_insts (C1 ++ Pre) Id Ms) k = Some T.
Proof.
  intros * Hass Hle HT.
  rewrite <- (List.firstn_skipn (List.length Pre) Ms), tele_insts_app by (try exact Hass; rewrite List.length_firstn; lia).
  rewrite List.nth_error_app1; [ exact HT |].
  assert (k < List.length (tele_insts Pre Id (List.firstn (List.length Pre) Ms))) by (apply List.nth_error_Some; congruence).
  exact H.
Qed.

(** Terms valid at the instances of a telescope are valid at the instances
    of its suffix. *)
Lemma tele_typed_prefix : forall C1 Pre Γ Ms, all_assumptions Pre -> List.length Pre <= List.length Ms ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts (C1 ++ Pre) Id Ms) k = Some T -> Γ ⊨ N : T) ->
    forall k N T, List.nth_error (List.firstn (List.length Pre) Ms) k = Some N ->
      List.nth_error (tele_insts Pre Id (List.firstn (List.length Pre) Ms)) k = Some T -> Γ ⊨ N : T.
Proof.
  intros * Hass Hle HMs k N T HN HT.
  assert (Hk : k < List.length (List.firstn (List.length Pre) Ms)) by (apply List.nth_error_Some; congruence).
  rewrite List.length_firstn in Hk.
  apply (HMs k); [| exact (tele_insts_prefix_nth C1 Pre Ms k T Hass Hle HT) ].
  rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec k (List.length Pre)); [ exact HN | discriminate ].
Qed.

(** Terms typed at the instances of a telescope are scoped by the context. *)
Lemma typed_insts_scoped : forall Γ C Ms, all_assumptions C -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊢ N : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ms.
Proof.
  intros * Hass Hl HMs; apply List.Forall_forall; intros N HN.
  destruct (List.In_nth_error _ _ HN) as [k Hk].
  assert (Hk' : k < List.length C) by (rewrite <- Hl; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some (tele_insts C Id Ms) k) as [Tk HTk]; [ rewrite length_tele_insts by exact Hass; lia |].
  exact (wf_exp_scoped_term _ _ _ _ _ (HMs _ _ _ Hk HTk)).
Qed.

(** The instances of a closed telescope of parameters of evaluated kinds
    are of evaluated sorts: each entry's sort, substituted
    ([rel_exp_under_ctx_gsub]). *)
Lemma closed_inst_sorts : forall C Γ Ms, all_assumptions C -> ⊨ C -> ⊨ Γ -> (exists l, rel_params_evaluated ⋅ C l) ->
    List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ms ->
    forall k T, List.nth_error (tele_insts C Id Ms) k = Some T -> exists Srt, evaluated_sort Srt /\ Γ ⊨ T : Srt.
Proof.
  intros * Hass HC HΓ HCev Hl HMs HMss k T HT.
  destruct (tele_insts_nth _ _ _ _ _ HT) as (κ & A & HA & ->).
  destruct (ctx_rev_split C k _ HA) as (C1 & Pre & EC & HPl).
  assert (HPa : all_assumptions Pre)
    by (rewrite EC in Hass; unfold all_assumptions in Hass; apply List.Forall_app in Hass as [_ H']; inversion H'; assumption).
  pose proof HC as HC1; rewrite EC in HC1; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HC1) as HC2.
  pose proof (rel_ctx_wf_tail HC2) as HPre.
  destruct (Completeness.Inductives.Model.closed_evaluated_over C Γ Hass HC HΓ HCev _ _ _ _ EC) as [i HAi].
  assert (Hle : List.length Pre <= List.length Ms) by (rewrite Hl, EC, List.length_app; cbn; lia).
  rewrite EC in HMs; replace (C1 ++ ce_ass κ A :: Pre) with ((C1 ++ ce_ass κ A :: nil) ++ Pre) in HMs
    by (rewrite <- List.app_assoc; reflexivity).
  pose proof (tele_typed_prefix _ _ _ _ HPa Hle HMs) as HMs'.
  assert (Lf : List.length (List.firstn (List.length Pre) Ms) = List.length Pre) by (rewrite List.length_firstn; lia).
  pose proof (gsub_closed_inst Pre Γ _ HPa HPre HΓ Lf HMs' (Forall_firstn' _ _ _ HMss)) as Hgs.
  rewrite HPl in Hgs.
  destruct HAi as [HAi | HAi]; pose proof (Completeness.LogicalRelation.Instance.rel_exp_under_ctx_gsub Hgs HAi) as H;
    cbn [exp_sub] in H; eexists; (split; [ constructor | exact H ]).
Qed.

(** The instances' sorts, likewise. *)
Lemma tele_sorts_prefix : forall C1 Pre Γ Ms, all_assumptions Pre -> List.length Pre <= List.length Ms ->
    (forall k T, List.nth_error (tele_insts (C1 ++ Pre) Id Ms) k = Some T -> exists Srt, evaluated_sort Srt /\ Γ ⊨ T : Srt) ->
    forall k T, List.nth_error (tele_insts Pre Id (List.firstn (List.length Pre) Ms)) k = Some T ->
      exists Srt, evaluated_sort Srt /\ Γ ⊨ T : Srt.
Proof. intros * Hass Hle HTs k T HT; exact (HTs k T (tele_insts_prefix_nth C1 Pre Ms k T Hass Hle HT)). Qed.

(** Terms glued along [σ] at the instances of a closed glued telescope are
    glued arguments of it, at their values: each instance's value is
    related to the entry's type's at the values before it
    ([closed_inst_typ]), and the entry's type is the witness
    ([glu_args_of_related]). *)
Lemma params_glu_args_at : forall C SbC Γ RΓ Δ σ ρ Ms vs, all_assumptions C -> ctx_scoped 0 C -> ⊨ C -> ⊨ Γ ->
    EG C ∈ glu_ctx_env ↘ SbC -> ⊢ Δ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (exists l, rel_params_evaluated ⋅ C l) -> List.Forall (exp_scoped (List.length Γ)) Ms ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T ->
       exists i : nat, glu_rel_exp_with_sub i Δ N T σ ρ) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> glu_args Δ C Id nil (List.map (fun M => M[σ]) Ms) vs.
Proof.
  intros * Hass Hs HC HΓ HSbC HΔ HRΓ Hρ Hl HMs HCev HMss HMg Hv.
  pose proof (closed_inst_sorts C Γ Ms Hass HC HΓ HCev Hl HMs HMss) as HTs.
  assert (Lv : List.length vs = List.length C) by (rewrite <- Hl; exact (Completeness.Inductives.Model.eval_exps_length _ _ _ Hv)).
  assert (HSbC' : EG C ++ ⋅ ∈ glu_ctx_env ↘ SbC) by (rewrite List.app_nil_r; exact HSbC).
  destruct (glu_ctx_env_entries_valid C ⋅ SbC Hass HSbC' 0) as (iv & _ & HAv).
  assert (Hnil : EG ⋅ ∈ glu_ctx_env ↘ nil_glu_sub_pred) by (econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]).
  eapply (glu_args_of_related C ⋅ SbC nil_glu_sub_pred iv Δ Id nil);
    [ exact Hass | exact HSbC' | exact Hnil | exact HAv | cbn; apply wf_sub_nil'; exact HΔ
    | rewrite List.length_map; exact Hl | exact Lv |].
  intros k M T v κ A b0 HM HT Hv' HA Hb0.
  apply nth_error_map_inv in HM as (N & HN & ->).
  rewrite <- (tele_insts_sub C 0 Id Id σ Ms Hass Hs ltac:(intros; lia)) in HT.
  apply nth_error_map_inv in HT as (T0 & HT0 & ->).
  destruct (HMg k N T0 HN HT0) as [i [a m P El Ea Em Hgl HNg]].
  destruct (Completeness.Inductives.Model.eval_exps_nth _ _ _ _ _ Hv HN) as (v0 & Hv0 & Ev0).
  rewrite Hv0 in Hv'; injection Hv' as <-.
  (** The instance is of an evaluated kind, so the term's value is its
      evaluation. *)
  destruct (HTs k T0 HT0) as (Srt & HSrt & HT0s).
  destruct (Completeness.ContextCases.rel_typ_evaluated_at
              (Completeness.ContextCases.rel_type_evaluated_of_evaluated_sort HSrt HT0s) HRΓ ρ ρ Hρ) as (a0 & Ea0 & Hka).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (Em' : ⟦ N ⟧ ρ ↘ m) by (unfold glu_term_value in Em; destruct (domain_kind a); first [ exact Em | inversion Hka ]).
  assert (m = v0) as -> by (eapply functional_eval_exp; eassumption).
  destruct (tele_insts_nth _ _ _ _ _ HT0) as (κ0 & A0 & HA0 & ET0).
  rewrite HA in HA0; injection HA0 as <- <-.
  (** The value of the instance, against the type at the values before it
      ([closed_inst_typ]). *)
  destruct (ctx_rev_split C k _ HA) as (C1 & Pre & EC & HPl).
  assert (HPa : all_assumptions Pre) by (rewrite EC in Hass; unfold all_assumptions in Hass; apply List.Forall_app in Hass as [_ H']; inversion H'; assumption).
  pose proof HC as HC1; rewrite EC in HC1; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HC1) as HC2.
  destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HC2) as (SrtA & HkA & HAs).
  destruct (rel_type_of_sort (sort_kind_type_sort _ _ HkA) HAs) as [j HAj].
  pose proof (rel_ctx_wf_tail HC2) as HPre.
  assert (Hle : List.length Pre <= List.length Ms) by (rewrite Hl, EC, List.length_app; cbn; lia).
  rewrite EC in HMs, HTs; replace (C1 ++ ce_ass κ A :: Pre) with ((C1 ++ ce_ass κ A :: nil) ++ Pre) in HMs, HTs
    by (rewrite <- List.app_assoc; reflexivity).
  pose proof (tele_typed_prefix _ _ _ _ HPa Hle HMs) as HMs'.
  pose proof (tele_sorts_prefix _ _ _ _ HPa Hle HTs) as HTs'.
  assert (Lf : List.length (List.firstn (List.length Pre) Ms) = List.length Pre) by (rewrite List.length_firstn; lia).
  destruct (Completeness.Modules.Filed.closed_inst_typ Pre Γ _ A j RΓ HPa HPre HΓ Lf HMs' HTs' (Forall_firstn' _ _ _ HMss) HAj HRΓ ρ Hρ)
    as (ms & a' & b & i' & R & Ems & Ea' & Eb & HR).
  rewrite HPl in Ea', Ems; rewrite <- ET0 in Ea'.
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (ms = List.firstn k vs) as -> by (eapply functional_eval_exps; [ exact Ems | exact (eval_exps_firstn _ _ _ k Hv) ]).
  assert (Eb' : ⟦ A ⟧ env_tele nil (List.rev C) (List.firstn k vs) ↘ b).
  { rewrite EC, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc, env_tele_prefix; [ exact Eb |].
    rewrite List.length_firstn, List.length_rev; lia. }
  assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
  destruct (Decl.per_univ_elem_to_nat _ _ _ _ HR) as [n HRn].
  exists i, n, a, P, El; split; [ exact Hgl | split; [ exists R; exact HRn | exact HNg ] ].
Qed.

(** Terms glued at the instances of a closed glued telescope are glued
    arguments of it, at their values. *)
Lemma params_glu_args : forall C SbC Γ RΓ Sb Δ σ ρ Ms vs, all_assumptions C -> ctx_scoped 0 C -> ⊨ C -> ⊨ Γ ->
    EG C ∈ glu_ctx_env ↘ SbC ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (exists l, rel_params_evaluated ⋅ C l) -> List.Forall (exp_scoped (List.length Γ)) Ms ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊩ N : T) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> glu_args Δ C Id nil (List.map (fun M => M[σ]) Ms) vs.
Proof.
  intros * Hass Hs HC HΓ HSbC HRΓ HSb Hσ Hl HMs HCev HMss HMg Hv.
  eapply params_glu_args_at; [ exact Hass | exact Hs | exact HC | exact HΓ | exact HSbC
                             | exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HSb _ _ _ Hσ))
                             | exact HRΓ | exact (glu_ctx_env_per_env HSb HRΓ Hσ) | exact Hl | exact HMs | exact HCev | exact HMss | | exact Hv ].
  intros k N T HN HT.
  destruct (glu_rel_exp_clean_inversion1 HSb (HMg k N T HN HT)) as [i Hi].
  exists i; exact (Hi _ _ _ Hσ).
Qed.

End Fixed_GCtx.
