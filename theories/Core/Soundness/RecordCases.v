(** * Record Types in the Gluing Model: the Rules

    The gluing rules of the record type former, of tuples and of
    projections, of their congruences, of field-β and of η.  Each term
    rule holds at the target of a sound embedding by [Records/Model.v]:
    there the record is the source's, found in a well-formed global
    context, and the premises of the rule are glued.  The type former's
    rule reads its declaration's gluing off its premises
    ([glu_record_decl]). *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Records Require Import Syntax.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases Instances.
From Mctt.Core.Soundness.Inductives Require Import Args.
From Mctt.Core.Soundness.Records Require Import Former Model.
Import Domain_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

#[local] Generalizable All Variables.

(** A record of the source, found at the target of a sound embedding. *)
Lemma record_lookup_of_glu_gctx_embedding : forall Θ Ξ Θ2 Ξ2 p R, glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> record_lookup Θ Ξ p = Some R ->
    record_lookup Θ2 Ξ2 p = Some R.
Proof.
  intros * Hμ Hl.
  exact (record_lookup_gc_sub _ _ _ _ _ _ (gctx_embedding_resolution _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) Hl).
Qed.

(** ** The Type Former *)

(** The type former: its declaration is glued at the target, by the
    premises; it is glued there at [⋅] ([glu_rel_exp_record0]), then
    weakened. *)
Lemma glu_record :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     record_lookup Θ Ξ p = Some R ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ record_ty R : Typeω@i ->
     Θ ⍮ Ξ ⍮ record_params R ⊩ᵤ record_sort R ->
     (forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
        Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊩ T : abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_record p : record_ty R ).
Proof.
  intros * HΓ HΓg Hl Hty HSg HTg Θ2 Ξ2 Hμ.
  glu_gctx_embedding_wf.
  pose proof (Hwc _ HΓ) as HΓ2.
  pose proof (ctx_wf_gctx _ _ _ HΓ2) as Hg2.
  pose proof (record_lookup_of_glu_gctx_embedding _ _ _ _ _ _ Hμ Hl) as Hl2.
  pose proof (wf_record_closed _ _ _ _ _ HΓ2 Hl2) as Hc.
  destruct (HSg _ _ Hμ) as [HPg HSu _].
  destruct (HΓg _ _ Hμ) as [HΓt HΓd]; split; [| exact HΓd ].
  econstructor; [ exact HΓt | intros Γ' τ Hτ ].
  cbn [exp_sub]; rewrite record_ty_sub by exact Hc.
  apply glu_rel_exp_nil_weaken; [ exact (glu_rel_sub_inst_ctx _ _ _ Hτ) |].
  eapply (@glu_rel_exp_record0 (gc_mk Θ2 Ξ2) p R Hg2 Hl2); [| exact (Hwe _ _ _ Hty) ].
  constructor; [ exact HPg | exact HSu |].
  intros * Hk; exact (proj1 (HTg _ _ _ Hk _ _ Hμ)).
Qed.

Lemma glu_exp_eq_record_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** ** Tuples and Projections *)

Lemma glu_tuple :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ T : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊩ N : A) ->
     List.map fst fs = List.map fst (record_fields R) ->
     (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
     (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ Γ ⊩ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_tuple T fs : T ).
Proof.
  intros * HTt HTg HTeq Hrt Hl Hn HNt HNg Hfs HMt HMg Θ2 Ξ2 Hμ.
  glu_gctx_embedding_wf.
  pose proof (Hwe _ _ _ HTt) as HTt2.
  pose proof (presup_exp_ctx HTt2) as HΓ2.
  pose proof (ctx_wf_gctx _ _ _ HΓ2) as Hg2.
  pose proof (record_lookup_of_glu_gctx_embedding _ _ _ _ _ _ Hμ Hl) as Hl2.
  pose proof (wf_record_closed _ _ _ _ _ HΓ2 Hl2) as Hc.
  split; [| exact (proj2 (HTg _ _ Hμ)) ].
  econstructor; [ exact (glu_rel_exp_under_sub_ctx _ _ _ (proj1 (HTg _ _ Hμ))) | intros Γ' τ Hτ ].
  pose proof (glu_rel_sub_inst_typed _ _ _ Hτ) as Hτt.
  cbn [exp_sub].
  (** The fields' terms and the instances of their types, at the instance *)
  assert (Hfl : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  assert (EU : forall k f U, List.nth_error (record_fields R) k = Some (f, U) ->
                 U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))][τ]
                 = U[sb_of_list Id (List.map (fun N => N[τ]) Ns
                                    ++ List.firstn k (List.map snd (List.map (fun f => (fst f, (snd f)[τ])) fs)))]).
  { intros * Hk; assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
    rewrite (record_field_sub R k f U Ns (List.firstn k (List.map snd fs)) τ Hc Hk Hn)
      by (rewrite List.length_firstn, List.length_map; lia).
    rewrite <- List.firstn_map, !List.map_map; reflexivity. }
  assert (Hfs' : forall k f M U, List.nth_error (List.map (fun f => (fst f, (snd f)[τ])) fs) k = Some (f, M) ->
                   List.nth_error (record_fields R) k = Some (f, U) ->
                   exists M0, M = M0[τ] /\ List.nth_error fs k = Some (f, M0)).
  { intros * HM _; apply nth_error_map_inv in HM as ([g M0] & HM0 & E); cbn in E; injection E as -> ->.
    exists M0; split; [ reflexivity | exact HM0 ]. }
  eapply (@glu_rel_exp_tuple (gc_mk Θ2 Ξ2) p R Hg2 Hl2 (glu_gctx_embedding_record_field _ _ _ _ Hμ _ _ Hl)
            Γ' T[τ] (List.map (fun N => N[τ]) Ns) (List.map (fun f => (fst f, (snd f)[τ])) fs) i).
  - exact (glu_rel_exp_under_sub_inst_conv (proj1 (HTg _ _ Hμ)) Hτ eq_refl).
  - pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ (Hweq _ _ _ _ HTeq) Hτt) as H.
    rewrite apps_exp_sub in H; exact H.
  - pose proof (sub_preserves_exp _ _ _ _ _ _ _ (Hwe _ _ _ Hrt) Hτt) as H.
    cbn [exp_sub] in H; rewrite record_ty_sub in H by exact Hc; exact H.
  - rewrite List.length_map; exact Hn.
  - intros j N A HN HA.
    rewrite <- (record_params_insts_sub R Ns τ Hc) in HA.
    apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HA as (A0 & HA0 & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (Hwe _ _ _ (HNt _ _ _ HN0 HA0)) Hτt).
  - intros j N A HN HA.
    rewrite <- (record_params_insts_sub R Ns τ Hc) in HA.
    apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HA as (A0 & HA0 & ->).
    exact (glu_rel_exp_under_sub_inst _ _ _ (proj1 (HNg _ _ _ HN0 HA0 _ _ Hμ)) _ _ Hτ).
  - rewrite List.map_map; exact Hfs.
  - intros k f M U HM HU.
    destruct (Hfs' _ _ _ _ HM HU) as (M0 & -> & HM0).
    rewrite <- (EU _ _ _ HU).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (Hwe _ _ _ (HMt _ _ _ _ HM0 HU)) Hτt).
  - intros k f M U HM HU.
    destruct (Hfs' _ _ _ _ HM HU) as (M0 & -> & HM0).
    exact (glu_rel_exp_under_sub_inst_conv (proj1 (HMg _ _ _ _ HM0 HU _ _ Hμ)) Hτ (EU _ _ _ HU)).
Qed.

Lemma glu_proj :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : apps_exp (a_record p) Ns ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : apps_exp (a_record p) Ns ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊩ N : A) ->
     List.nth_error (record_fields R) k = Some (f, U) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ U[sb_of_list Id (Ns ++ record_pre R k M)] : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)] ).
Proof.
  intros * HMt HMg Hl Hn HNt HNg Hfk HUg HSrt Θ2 Ξ2 Hμ.
  glu_gctx_embedding_wf.
  pose proof (Hwe _ _ _ HMt) as HMt2.
  pose proof (presup_exp_ctx HMt2) as HΓ2.
  pose proof (ctx_wf_gctx _ _ _ HΓ2) as Hg2.
  pose proof (record_lookup_of_glu_gctx_embedding _ _ _ _ _ _ Hμ Hl) as Hl2.
  pose proof (wf_record_closed _ _ _ _ _ HΓ2 Hl2) as Hc.
  assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  split; [| exact (proj2 (HMg _ _ Hμ)) ].
  econstructor; [ exact (glu_rel_exp_under_sub_ctx _ _ _ (proj1 (HMg _ _ Hμ))) | intros Γ' τ Hτ ].
  pose proof (glu_rel_sub_inst_typed _ _ _ Hτ) as Hτt.
  (** The field's type at the instance *)
  assert (EU : U[sb_of_list Id (Ns ++ record_pre R k M)][τ]
               = U[sb_of_list Id (List.map (fun N => N[τ]) Ns ++ record_pre R k M[τ])]).
  { rewrite (record_field_sub R k f U Ns (record_pre R k M) τ Hc Hfk Hn) by (apply length_record_pre; lia).
    rewrite record_pre_sub; reflexivity. }
  cbn [exp_sub]; rewrite EU.
  eapply (@glu_rel_exp_proj (gc_mk Θ2 Ξ2) p R Hg2 Hl2 (glu_gctx_embedding_record_field _ _ _ _ Hμ _ _ Hl)
            Γ' M[τ] (List.map (fun N => N[τ]) Ns) k f U Srt).
  - exact (glu_rel_exp_under_sub_inst_conv (proj1 (HMg _ _ Hμ)) Hτ (apps_exp_sub _ _ _)).
  - rewrite List.length_map; exact Hn.
  - intros j N A HN HA.
    rewrite <- (record_params_insts_sub R Ns τ Hc) in HA.
    apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HA as (A0 & HA0 & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (Hwe _ _ _ (HNt _ _ _ HN0 HA0)) Hτt).
  - intros j N A HN HA.
    rewrite <- (record_params_insts_sub R Ns τ Hc) in HA.
    apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HA as (A0 & HA0 & ->).
    exact (glu_rel_exp_under_sub_inst _ _ _ (proj1 (HNg _ _ _ HN0 HA0 _ _ Hμ)) _ _ Hτ).
  - exact Hfk.
  - rewrite <- EU.
    exact (glu_rel_exp_under_sub_inst_conv (proj1 (HUg _ _ Hμ)) Hτ (type_sort_sub Srt τ HSrt)).
  - exact HSrt.
Qed.

(** ** The Equations

    An equation glues its context. *)

Lemma glu_exp_eq_tuple_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ a_tuple T fs : T ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_proj_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_field_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ a_tuple T fs : T ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_record_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
