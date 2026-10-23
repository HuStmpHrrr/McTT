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
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases.
From Mctt.Core.Soundness.Inductives Require Import Args.
From Mctt.Core.Soundness.Records Require Import Model.
Import Domain_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

#[local] Generalizable All Variables.

(** A record of the source, found at the target of a sound embedding. *)
Lemma record_lookup_of_glu_emb : forall Θ Ξ Θ2 Ξ2 p R, glu_emb Θ Ξ Θ2 Ξ2 -> record_lookup Θ Ξ p = Some R ->
    record_lookup Θ2 Ξ2 p = Some R.
Proof.
  intros * Hμ Hl.
  exact (record_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ (gem_emb _ _ _ _ Hμ)) Hl).
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
        Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊩ T : (record_sort R)[wk_shiftn k]ʷ) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_record p : record_ty R ).
Proof.
  intros * HΓ HΓg Hl Hty HSg HTg Θ2 Ξ2 Hμ.
  glu_emb_wf.
  pose proof (Hwc _ HΓ) as HΓ2.
  pose proof (ctx_wf_gctx _ _ _ HΓ2) as Hg2.
  pose proof (record_lookup_of_glu_emb _ _ _ _ _ _ Hμ Hl) as Hl2.
  destruct (HSg _ _ Hμ) as [HPg HSu].
  apply glu_rel_exp_nil_weaken; [ exact (HΓg _ _ Hμ) |].
  eapply (@glu_rel_exp_record0 (gc_mk Θ2 Ξ2) p R Hg2 Hl2); [| exact (Hwe _ _ _ Hty) ].
  constructor; [ exact HPg | exact HSu |].
  intros * Hk; exact (HTg _ _ _ Hk _ _ Hμ).
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
  glu_emb_wf.
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx (Hwe _ _ _ HTt))) as Hg2.
  eapply (@glu_rel_exp_tuple (gc_mk Θ2 Ξ2) p R Hg2 (record_lookup_of_glu_emb _ _ _ _ _ _ Hμ Hl));
    [ exact (HTg _ _ Hμ) | exact (Hweq _ _ _ _ HTeq) | exact (Hwe _ _ _ Hrt) | exact Hn
    | intros * HN HA; exact (Hwe _ _ _ (HNt _ _ _ HN HA)) | intros * HN HA; exact (HNg _ _ _ HN HA _ _ Hμ)
    | exact Hfs | intros * HM HU; exact (Hwe _ _ _ (HMt _ _ _ _ HM HU)) | intros * HM HU; exact (HMg _ _ _ _ HM HU _ _ Hμ) ].
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
     Θ ⍮ Ξ ⍮ Γ ⊩ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)] ).
Proof.
  intros * HMt HMg Hl Hn HNt HNg Hfk Θ2 Ξ2 Hμ.
  glu_emb_wf.
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx (Hwe _ _ _ HMt))) as Hg2.
  eapply (@glu_rel_exp_proj (gc_mk Θ2 Ξ2) p R Hg2 (record_lookup_of_glu_emb _ _ _ _ _ _ Hμ Hl));
    [ exact (HMg _ _ Hμ) | exact Hn | intros * HN HA; exact (Hwe _ _ _ (HNt _ _ _ HN HA))
    | intros * HN HA; exact (HNg _ _ _ HN HA _ _ Hμ) | exact Hfk ].
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
