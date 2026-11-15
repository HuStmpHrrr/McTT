(** * The Set Rules of Records

    The rules of record types, tuples and projections in the set model,
    their congruences, the field [β]-rule and record [η].  The lemmas they
    rest on are in [Records/Model.v]. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution Universes.
From Mctt.Core.SetModel Require Import Modules.ValidUnit Modules.MemberTypes Modules.Sel Inductives.Model Records.Model.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members Records.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.System.Records Require Import Typing.
From Mctt.Core.Syntactic.System.Records Require Syntax.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
Import ListNotations.

Section Records.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_rule_record_eta : forall Γ M p R Ns, set_ctx_slots Θ Ξ T γ Γ ->
    record_lookup Θ Ξ p = Some R -> List.length Ns = List.length (record_params R) ->
    NoDup (List.map fst (record_fields R)) ->
    set_exp_eq Θ Ξ T γ Γ (apps_exp (a_record p) Ns) M M ->
    set_exp_eq Θ Ξ T γ Γ (apps_exp (a_record p) Ns) (a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M))
      (a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M)) ->
    set_exp_eq Θ Ξ T γ Γ (apps_exp (a_record p) Ns) M (a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M)).
Proof.
  intros * HΓ HRs Hl Hnd HMe HTe. set_open. destruct HΓ as [HΓ _].
  destruct HMe as (FA & FM & FM' & HM). destruct HTe as (GA & GT & GT' & HT).
  apply (set_exp_eq_of_sides T γ _ _ _ _ _ _ _ _ _ _ HM HT).
  pose proof (record_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θ Ξ Hμ) HRs) as HR.
  pose proof HM as [HFA HFM _ _ HMm]. pose proof HT as [_ HGT _ _ _]. pose proof (set_source_records T γ Θ Ξ Hμ _ _ HRs) as HSR.
  intros ρ Hρ.
  pose proof (set_denotes_exists _ _ _ _ _ HFA _ Hρ) as Hap. destruct (set_interp_apps_inv T γ _ _ _ _ _ Hap) as (v0 & ns & Hv0 & Hns & Eap).
  inversion Hv0; subst.
  assert (Hlns : List.length ns = List.length Ns) by (clear - Hns; induction Hns; cbn; congruence).
  pose proof (HMm _ Hρ) as Hv. rewrite Eap in Hv.
  destruct (set_record_ok_instances _ _ _ _ _ HSR ns _ ltac:(lia) Hv) as (ρp & Hρp & Ens).
  eapply set_mem_eq_r in Hv; [| apply code_carrier_resp; eapply set_eq_trans;
                                 [apply apply_values_resp; [apply set_eq_refl | exact Ens] | exact (set_record_ok_former_value _ _ _ _ _ HSR _ Hρp)]].
  eapply set_mem_eq_r in Hv; [| apply code_carrier_type_code].
  destruct (proj1 (set_record_ok_carrier _ _ _ _ _ HSR _ _ Hρp) Hv) as (vs & [Hlvs Etup _]).
  rewrite (set_record_ok_names _ _ _ _ _ HSR) in Hlvs, Etup. rewrite List.length_map in Hlvs.
  eapply set_eq_trans; [exact Etup |].
  pose proof (set_denotes_exists _ _ _ _ _ HGT _ Hρ) as Ht. inversion Ht; subst.
  match goal with Hfs : set_interp_fields _ _ _ _ (record_eta_fields R M) ?ws0 |- _ =>
    apply set_eq_sym; apply tuple_code_resp; rename Hfs into Hws; set (ws := ws0) in * end.
  assert (Hlws : List.length ws = List.length (record_fields R))
    by (rewrite <- (List.length_map fst ws), (set_interp_fields_names T γ _ _ _ _ Hws); unfold record_eta_fields;
        rewrite !List.length_map; reflexivity).
  apply Forall2_of_nth; [rewrite List.length_combine, List.length_map; lia |].
  intros i [g w] [g' v] Hw Hv'.
  assert (Hi : i < List.length (record_fields R)) by (rewrite <- Hlws; apply List.nth_error_Some; congruence).
  destruct (List.nth_error (record_fields R) i) as [[f U] |] eqn:Hf; [| apply List.nth_error_None in Hf; lia].
  assert (He : List.nth_error (record_eta_fields R M) i = Some (f, a_proj f M))
    by (unfold record_eta_fields; rewrite List.nth_error_map, Hf; reflexivity).
  destruct (set_interp_fields_nth T γ _ _ _ _ Hws _ _ _ He) as (w' & Hw' & Hpw). rewrite Hw in Hw'. injection Hw' as <- <-.
  destruct (List.nth_error vs i) as [vi |] eqn:Hvi; [| apply List.nth_error_None in Hvi; lia].
  assert (Hc : List.nth_error (List.combine (List.map fst (record_fields R)) vs) i = Some (g, vi)).
  { clear - Hf Hvi. revert i vs Hf Hvi. induction (record_fields R) as [| [f0 U0] l IH]; intros [| i] [| v vs] Hf Hvi; cbn in *;
      try discriminate; [injection Hf as -> _; injection Hvi as ->; reflexivity | exact (IH _ _ Hf Hvi)]. }
  rewrite Hc in Hv'. injection Hv' as <- <-. split; [reflexivity |].
  inversion Hpw; subst.
  match goal with Hu : set_interp _ _ _ _ M ?u |- _ =>
    eapply set_eq_trans; [apply tuple_field_resp; exact (set_denotes_unique _ _ _ _ _ HFM _ _ _ Hρ Hu) |] end.
  eapply set_eq_trans; [apply tuple_field_resp; exact Etup |]. apply tuple_field_at.
  - rewrite map_fst_combine_le by (rewrite List.length_map; lia). exact Hnd.
  - apply (In_combine_nth _ _ i); [rewrite List.nth_error_map, Hf; reflexivity | exact Hvi].
Qed.

Lemma set_rule_proj : forall Γ M p R Ns k f U, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : B) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       set_exp_eq Θ Ξ T γ Γ B N N) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps_exp (a_record p) Ns -> set_exp_eq Θ Ξ T γ Γ (apps_exp (a_record p) Ns) M M ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub U (sb_of_list sb_id (Ns ++ record_pre R k M))) (a_proj f M) (a_proj f M).
Proof.
  intros * Hc HΓ Hr HRs Hl HNs0 HNr0 HMw HMe Hk. set_open. destruct HΓ as [HΓ _]. destruct HMe as (FA & FM & FM' & HM).
  pose proof (fun k N B H1 H2 => proj1 (proj2 (gctx_embedding_preserves_wf _ _ _ _ Hμe)) _ _ _ (HNs0 k N B H1 H2)) as HNs.
  pose proof (fun k N B H1 H2 => HNr0 k N B H1 H2 _ _ Hμ) as HNr. cbv beta in HNs, HNr.
  pose proof (record_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θ Ξ Hμ) HRs) as HR.
  pose proof HM as [_ HFM _ _ _].
  assert (HP : forall g, set_denotes T γ Γ (a_proj g M) (fun ρ => tuple_field (FM ρ) g))
    by (intros g; apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ); intros ρ Hρ;
        exact (set_interp_proj T γ _ _ _ _ _ (set_denotes_exists _ _ _ _ _ HFM _ Hρ))).
  assert (Hall : forall j i f' U', i < j -> List.nth_error (record_fields R) i = Some (f', U') ->
            set_rel_exp_eq T γ Γ (exp_sub U' (sb_of_list sb_id (Ns ++ record_pre R i M))) (a_proj f' M) (a_proj f' M)).
  { induction j as [| j IH]; intros i f' U' Hi Hf'; [lia |].
    destruct (Nat.lt_ge_cases i j) as [Hij | Hij]; [exact (IH _ _ _ Hij Hf') |]. assert (i = j) by lia. subst i.
    destruct (set_proj_field T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ _ _ _ _ _ _ _ _ Hc HΓ Hr HRs Hl HNs HNr HMw HM Hf' IH) as (FU & HFU & Hmem).
    exists FU, (fun ρ => tuple_field (FM ρ) f'), (fun ρ => tuple_field (FM ρ) f').
    constructor; [exact HFU | exact (HP f') | exact (HP f') | intros; apply set_eq_refl | exact Hmem]. }
  exact (Hall (S k) k f U ltac:(lia) Hk).
Qed.

Lemma set_rule_record : forall Γ p R i, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ -> record_lookup Θ Ξ p = Some R ->
    Θ ⍮ Ξ ⍮ nil ⊢ record_ty R : a_typ i -> set_exp_eq Θ Ξ T γ nil (a_typ i) (record_ty R) (record_ty R) ->
    set_exp_eq Θ Ξ T γ Γ (record_ty R) (a_record p) (a_record p).
Proof.
  intros * Hc HΓ HRs Hw Hty. set_open. destruct HΓ as [HΓ _]. destruct Hty as (FS & FA & FA' & [_ HFA _ _ _]).
  pose proof (set_source_records T γ Θ Ξ Hμ _ _ HRs) as HSR.
  pose proof (record_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θ Ξ Hμ) HRs) as HR.
  apply (set_exp_eq_closed_global T γ Hfn Hmods Hgw _ _ (global_record_former γ p) FA); try assumption.
  - exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ Hw))).
  - exact (set_record_ok_former_typed _ _ _ _ _ HSR _ HFA).
  - intros ρ. econstructor; eassumption.
Qed.

Lemma set_rule_record_cong : forall Γ p R i, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ -> record_lookup Θ Ξ p = Some R ->
    Θ ⍮ Ξ ⍮ nil ⊢ record_ty R : a_typ i -> set_exp_eq Θ Ξ T γ nil (a_typ i) (record_ty R) (record_ty R) ->
    set_exp_eq Θ Ξ T γ Γ (record_ty R) (a_record p) (a_record p).
Proof. exact set_rule_record. Qed.

Lemma set_rule_proj_cong : forall Γ C f M M' A, set_exp_eq Θ Ξ T γ Γ C M M' ->
    set_exp_eq Θ Ξ T γ Γ A (a_proj f M) (a_proj f M) -> set_exp_eq Θ Ξ T γ Γ A (a_proj f M') (a_proj f M') ->
    set_exp_eq Θ Ξ T γ Γ A (a_proj f M) (a_proj f M').
Proof.
  intros * HMe HLe HRe. set_open.
  destruct HMe as (FC & FM & FM' & [_ HM HM' EM _]). destruct HLe as (FA & FP & FP' & HL). destruct HRe as (GA & GP & GP' & HR).
  apply (set_exp_eq_of_sides T γ _ _ _ _ _ _ _ _ _ _ HL HR).
  pose proof HL as [_ HP _ _ _]. pose proof HR as [_ HP' _ _ _]. intros ρ Hρ.
  eapply set_eq_trans; [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HP _ _ _ Hρ
                                                    (set_interp_proj T γ _ _ _ _ _ (set_denotes_exists _ _ _ _ _ HM _ Hρ))) |].
  eapply set_eq_trans; [apply tuple_field_resp; exact (EM _ Hρ) |].
  exact (set_denotes_unique _ _ _ _ _ HP' _ _ _ Hρ (set_interp_proj T γ _ _ _ _ _ (set_denotes_exists _ _ _ _ _ HM' _ Hρ))).
Qed.

Lemma set_rule_tuple_cong : forall Γ A fs A' fs', set_exp_eq Θ Ξ T γ Γ A (a_tuple A fs) (a_tuple A fs) ->
    set_exp_eq Θ Ξ T γ Γ A (a_tuple A' fs') (a_tuple A' fs') -> List.map fst fs' = List.map fst fs ->
    forall (R : record_decl), List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
       List.nth_error (record_fields R) k = Some (f, U) -> exists B, set_exp_eq Θ Ξ T γ Γ B M M') ->
    set_exp_eq Θ Ξ T γ Γ A (a_tuple A fs) (a_tuple A' fs').
Proof.
  intros * HLe HRe Hn R HnR Hf0k. set_open.
  destruct HLe as (FA & FL & FL' & HL). destruct HRe as (GA & GR & GR' & HR).
  assert (Hf0 : forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
            List.nth_error (record_fields R) k = Some (f, U) -> exists B, set_rel_exp_eq T γ Γ B M M')
    by (intros * Hk Hk' HU; destruct (Hf0k _ _ _ _ _ Hk Hk' HU) as (B & HB); exists B; exact (HB _ _ Hμ)).
  assert (Hf : forall k f M M', List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') -> exists B, set_rel_exp_eq T γ Γ B M M').
  { intros k f M M' Hk Hk'. pose proof (f_equal (fun l => List.nth_error l k) HnR) as E. cbn beta in E.
    rewrite !List.nth_error_map, Hk in E.
    destruct (List.nth_error (record_fields R) k) as [[g U] |] eqn:HU; cbn in E; [| discriminate]. injection E as <-.
    exact (Hf0 _ _ _ _ _ Hk Hk' HU). }
  apply (set_exp_eq_of_sides T γ _ _ _ _ _ _ _ _ _ _ HL HR).
  pose proof HL as [_ HP _ _ _]. pose proof HR as [_ HP' _ _ _]. intros ρ Hρ.
  pose proof (set_denotes_exists _ _ _ _ _ HP _ Hρ) as H1. pose proof (set_denotes_exists _ _ _ _ _ HP' _ Hρ) as H2.
  inversion H1; subst. inversion H2; subst.
  apply tuple_code_resp.
  match goal with Hvs : set_interp_fields _ _ _ _ fs ?vs, Hvs' : set_interp_fields _ _ _ _ fs' ?vs' |- _ =>
    apply (set_interp_fields_eq T γ _ _ _ _ _ _ Hvs Hvs' Hn) end.
  intros * Hk Hk' Hv Hv'. destruct (Hf _ _ _ _ Hk Hk') as (B & FB & FM & FM' & [_ HM HM' EM _]).
  eapply set_eq_trans; [exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hρ Hv) |].
  eapply set_eq_trans; [exact (EM _ Hρ) |]. apply set_eq_sym. exact (set_denotes_unique _ _ _ _ _ HM' _ _ _ Hρ Hv').
Qed.

Lemma set_rule_field_beta : forall Γ A fs f M B, NoDup (List.map fst fs) ->
    set_exp_eq Θ Ξ T γ Γ A (a_tuple A fs) (a_tuple A fs) -> field_lookup fs f = Some M ->
    set_exp_eq Θ Ξ T γ Γ B (a_proj f (a_tuple A fs)) (a_proj f (a_tuple A fs)) ->
    set_exp_eq Θ Ξ T γ Γ B M M -> set_exp_eq Θ Ξ T γ Γ B (a_proj f (a_tuple A fs)) M.
Proof.
  intros * Hnd HTe Hl HPe HMe. set_open.
  destruct HTe as (FA & FL & FL' & [_ HL _ _ _]). destruct HPe as (FB & FP & FP' & HP). destruct HMe as (GB & GM & GM' & HM).
  apply (set_exp_eq_of_sides T γ _ _ _ _ _ _ _ _ _ _ HP HM).
  pose proof HP as [_ HPd _ _ _]. pose proof HM as [_ HMd _ _ _]. intros ρ Hρ.
  pose proof (set_denotes_exists _ _ _ _ _ HL _ Hρ) as H1.
  inversion H1; subst.
  match goal with Hvs : set_interp_fields _ _ _ _ fs ?vs |- _ =>
    destruct (set_interp_fields_lookup T γ _ _ _ _ Hvs _ _ Hl) as (v & Hin & Hv);
    pose proof (set_interp_fields_names T γ _ _ _ _ Hvs) as Hnames end.
  eapply set_eq_trans; [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HPd _ _ _ Hρ (set_interp_proj T γ _ _ _ _ _ H1)) |].
  match goal with E : tuple_code _ = FL ρ |- _ => rewrite <- E end.
  eapply set_eq_trans; [apply tuple_field_at; [rewrite Hnames; exact Hnd | exact Hin] |].
  exact (set_denotes_unique _ _ _ _ _ HMd _ _ _ Hρ Hv).
Qed.

Lemma set_rule_tuple : forall Γ A fs p R Ns i, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : B) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       set_exp_eq Θ Ξ T γ Γ B N N) ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Θ ⍮ Ξ ⍮ Γ ⊢ M : exp_sub U (sb_of_list sb_id (Ns ++ List.firstn k (List.map snd fs)))) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       set_exp_eq Θ Ξ T γ Γ (exp_sub U (sb_of_list sb_id (Ns ++ List.firstn k (List.map snd fs)))) M M) ->
    set_exp_eq Θ Ξ T γ Γ (a_typ i) A (apps_exp (a_record p) Ns) ->
    set_exp_eq Θ Ξ T γ Γ A (a_tuple A fs) (a_tuple A fs).
Proof.
  intros * Hc HΓ Hr HRs Hl HNs0 HNr0 Hn HFs0 HFr0 HAe. set_open. destruct HΓ as [HΓ _].
  pose proof (fun k N B H1 H2 => proj1 (proj2 (gctx_embedding_preserves_wf _ _ _ _ Hμe)) _ _ _ (HNs0 k N B H1 H2)) as HNs.
  pose proof (fun k N B H1 H2 => HNr0 k N B H1 H2 _ _ Hμ) as HNr.
  pose proof (fun k f M U H1 H2 => proj1 (proj2 (gctx_embedding_preserves_wf _ _ _ _ Hμe)) _ _ _ (HFs0 k f M U H1 H2)) as HFs.
  pose proof (fun k f M U H1 H2 => HFr0 k f M U H1 H2 _ _ Hμ) as HFr. cbv beta in HNs, HNr, HFs, HFr.
  destruct HAe as (FS & FA & FAp & HA). pose proof HA as [_ HFA _ _ _].
  destruct (set_tuple_value_typed T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ _ _ _ _ _ _ _ Hc HΓ Hr HRs Hl HNs HNr Hn HFs HFr HA)
    as (Fs & HT & Hm).
  exists FA, (fun ρ => tuple_code (Fs ρ)), (fun ρ => tuple_code (Fs ρ)).
  constructor; [exact HFA | exact HT | exact HT | intros; apply set_eq_refl | exact Hm].
Qed.

End Records.
