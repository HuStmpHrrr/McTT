(** * Selections of Glued Module Values

    A submodule selected from a glued module value is glued as the
    selection ([glu_dmod_sel]).  A value lacking a parameter recurses
    through its applications: the selection from the application is moved
    to the application of the selection, which has the same module part
    ([mdenote_mem_app_part]), by the transfer between module expressions
    with the same module part ([glu_dmod_same_part_typed]).  The transfer
    needs no equation between the module expressions: their members are
    equal through their δ-reducts or as the filed members they are
    ([wf_exp_eq_mem_same_part]). *)

From Stdlib Require Import Lia List PeanoNat RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound Presup.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.Modules Require Import Values ModuleVal.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases ModuleValues.
From Mctt.Core.Soundness.Global Require Import GlobalValues.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Members of Module Expressions with the Same Module Part *)

Lemma mdesc_ats_term_none_eq : forall Ns κ A R, mdesc_ats (mdesc_term κ A None) Ns = Some R -> exists A', R = mdesc_term κ A' None.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [ exact (IH _ _ _ Ha) | discriminate ].
Qed.

(** A member looked up as a term of no δ-reduct is an axiom or an abstract
    definition of a stored body, read bare: the module expression's module
    part is the body's path at no argument and no outside parameter. *)
Lemma mem_no_red : forall Θ Ξ Γ H x R A,
    mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A -> mdesc_reduct R = None ->
    exists R0 p T Φ Φ0 b pv κ oM,
      mdenote Θ Ξ Γ H R0 /\ mdesc_mod R0 = Some (mdesc_closed nil p T Φ nil) /\
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv κ A oM)) /\ (if b then oM else None) = None.
Proof.
  intros * Hm Ht Hr.
  assert (HR : exists κ, R = mdesc_term κ A None)
    by (destruct R as [κ A' om | | | ]; cbn in Ht, Hr; try discriminate; subst; injection Ht as ->; eauto).
  destruct HR as [κ ->].
  inversion Hm as [| | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hrd |]; subst.
  destruct R0m as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in He; try discriminate.
  - (* an open body reads only transparent definitions and modules *)
    destruct (gm_prefix_upto Φx x) as [[| Φ' y E0 | ? ? ?] |]; try discriminate.
    destruct E0 as [[] pv κ' A' [M |] | pv U | | |]; try discriminate; injection He as <- <- <-.
    + inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
    + inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn in Hrd; destruct (gm_fill Φ'); cbn in Hrd; [| discriminate ].
      injection Hrd as Heq; destruct Re; cbn in Hmm, Heq; try contradiction; discriminate.
    + (* a definition with a module part reads as one, with both parts *)
      inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
  - destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
    injection Hrd as Heq.
    destruct E0 as [b pv κ' A' oM | pv [Δ [sm Φy | E'] ] | pv pq k' D ΦD | pv Ad Md Ud | pv Rr ΦR ].
    + (* a definition: one of no body, read bare *)
      cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read] in Hats.
      destruct (if b then oM else None) as [M |] eqn:Ho.
      * exfalso; destruct (mdesc_ats_some_red _ _ _ _ _ Hats) as (A1 & M1 & ->).
        rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
      * destruct (mdesc_ats_term_none_eq _ _ _ _ Hats) as (A1 & ->).
        destruct (mdesc_named_term_none Θ' Ns (apps (a_mem (qname_mod p) x) Ns) κ' A1) as [(Hn & -> & ->) | Hn];
          rewrite Hn in Heq; cbn in Heq; [| discriminate ].
        cbn in Hats; injection Hats as ->; injection Heq as -> ->.
        exists R0, p, T, Φ, Φ0, b, pv, κ, oM; repeat split; assumption.
    + exfalso; assert (Hmm : mdesc_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (mdesc_ats_read_mod _ _ Hmm) in Hats.
      pose proof (mdesc_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; assert (Hmm : mdesc_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (mdesc_ats_read_mod _ _ Hmm) in Hats.
      pose proof (mdesc_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a member of a group: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read ind_former_desc] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a definition with a module part: read with its module part, no term *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a record type: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [mdesc_ats_read record_former_desc] in Hats.
      mdesc_dm_read_shape Hats.
      rewrite mdesc_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** The members [x] of two typed module expressions with the same module
    part, looked up alike, are equal: through their common δ-reduct, or,
    with none, as the filed member of the bare stored body the module part
    is ([mem_alias_filed]). *)
Lemma wf_exp_eq_mem_same_part : forall Γ H0 H1 x R A R0 R1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H0 ≈ H0 -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H1 ≈ H1 ->
    mdenote gc_deps gc_stack Γ (me_mem H0 x) R -> mdenote gc_deps gc_stack Γ (me_mem H1 x) R ->
    mdesc_type R = Some A ->
    mdenote gc_deps gc_stack Γ H0 R0 -> mdenote gc_deps gc_stack Γ H1 R1 -> mdesc_mod R0 = mdesc_mod R1 ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_mem H0 x ≈ a_mem H1 x : A.
Proof.
  intros * HH0 HH1 Hm0 Hm1 Ht HR0 HR1 Ep.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH0)) as Hg.
  destruct (mdesc_reduct R) as [M |] eqn:Hr.
  - (** Both are the reduct *)
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_mem_delta; eassumption |].
    apply wf_exp_eq_sym; eapply wf_exp_eq_mem_delta; eassumption.
  - (** Both are the filed member of the bare body *)
    destruct (mem_no_red _ _ _ _ _ _ _ Hm0 Ht Hr) as (R0' & p & T & Φ & _ & _ & _ & _ & _ & HR0' & Hmd0 & _).
    destruct (mem_no_red _ _ _ _ _ _ _ Hm1 Ht Hr) as (R1' & p' & T' & Φ' & _ & _ & _ & _ & _ & HR1' & Hmd1 & _).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0' _ HR0) in Hmd0.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1' _ HR1) in Hmd1.
    assert (HR0m : mdesc_mod R0 = Some (mdesc_closed nil p' T' Φ' nil)) by congruence.
    eapply wf_exp_eq_trans; [ exact (mem_alias_filed _ _ _ _ _ _ _ _ _ _ _ HH0 HR0 HR0m Hm0 Ht) |].
    apply wf_exp_eq_sym; exact (mem_alias_filed _ _ _ _ _ _ _ _ _ _ _ HH1 HR1 Hmd1 Hm1 Ht).
Qed.

(** A term glued as the member of [H1] is glued as the member of a typed
    [H0] with the same module part, looked up alike, at the same type: the
    members are equal ([wf_exp_eq_mem_same_part]), read where the gluing
    is. *)
Lemma glu_elem_at_same_part : forall {Γ1 H0 H1 x R A' Δ σ1 a m R0 R1 Rm} {i : nat} {P El},
    gc_deps ⍮ gc_stack ⍮ Γ1 ⊢ᵐ H0 ≈ H0 -> gc_deps ⍮ gc_stack ⍮ Γ1 ⊢ᵐ H1 ≈ H1 ->
    mdenote gc_deps gc_stack Γ1 (me_mem H0 x) R ->
    mdenote gc_deps gc_stack Γ1 (me_mem H1 x) R ->
    mdesc_type R = Some A' ->
    mdenote gc_deps gc_stack Γ1 H0 R0 -> mdenote gc_deps gc_stack Γ1 H1 R1 ->
    mdesc_mod R0 = Some Rm -> mdesc_mod R1 = Some Rm ->
    Δ ⊢ˢ σ1 : Γ1 ->
    glu_elem_at Δ A'[σ1] (a_mem H1 x)[σ1] a m i P El ->
    glu_elem_at Δ A'[σ1] (a_mem H0 x)[σ1] a m i P El.
Proof.
  intros * HH0 HH1 Hm0 Hm1 HA HR0 HR1 E0 E1 Hσ [Hu HT HM].
  constructor; [ exact Hu | exact HT |].
  eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hu | exact HM |].
  apply wf_exp_eq_sym; cbn [exp_sub].
  eapply wf_exp_eq_mem_same_part;
    [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hσ) | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH1 Hσ)
    | eapply wf_sub_mdenote_mem; [ exact HH0 | exact Hm0 | exact Hσ ]
    | eapply wf_sub_mdenote_mem; [ exact HH1 | exact Hm1 | exact Hσ ]
    | eapply mdesc_type_sub; exact HA
    | eapply wf_sub_mdenote; [ exact HH0 | exact HR0 | exact Hσ ]
    | eapply wf_sub_mdenote; [ exact HH1 | exact HR1 | exact Hσ ]
    | rewrite (mdesc_mod_sub _ _ _ E0), (mdesc_mod_sub _ _ _ E1); reflexivity ].
Qed.

(** A typed module expression has a module part, the one of whatever it
    denotes. *)
Lemma modexp_mod_part : forall Γ H R, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ H R ->
    exists Rm, mdesc_mod R = Some Rm.
Proof.
  intros * HH Hm.
  destruct (me_denotes _ _ _ _ _ HH) as (R0 & Rm & Hm0 & HRm).
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ Hm) in HRm; eauto.
Qed.

(** A module value glued as [H1] is glued as a typed [H0] with the same
    module part both ways at every substitution, neither naming an open
    frame: as [glu_dmod_same_part], with no equation between them; the
    members are equal through the module part ([glu_elem_at_same_part]). *)
Lemma glu_dmod_same_part_typed :
  (forall Δ σ0 Γ0 H1 h, glu_dmod Δ σ0 Γ0 H1 h ->
     forall H0, gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H0 -> same_part Γ0 H0 H1 -> same_part Γ0 H1 H0 ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> names_no_frame H0[ζ]ᵐ) ->
       (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ0 -> names_no_frame H1[ζ]ᵐ) ->
       glu_dmod Δ σ0 Γ0 H0 h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A global module *)
    intros * Hσ HH1 Hl Hlen Hdesc Hargs _ H0 HH Hs01 Hs10 Hq0 Hq1.
    (** The same module part, read off [H1[ζ]] *)
    assert (Hpart : forall Δ' φ Γ1 ζ σ1 RH, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
               mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH ->
               exists R1, mdenote gc_deps gc_stack Γ1 H1[ζ]ᵐ R1 /\ mdesc_mod R1 = mdesc_mod RH).
    { intros * Hst Hm.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      destruct (modexp_mod_part _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) Hm) as (Rm & HRm).
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (R1 & Hm1 & HR1m).
      exists R1; split; [ exact Hm1 | congruence ]. }
    eapply glu_dmod_global; [ exact Hσ | exact HH | exact Hl | exact Hlen | |].
    + intros * Hst Hm.
      destruct (Hpart _ _ _ _ _ _ Hst Hm) as (R1 & Hm1 & E1).
      rewrite <- E1; exact (Hdesc _ _ _ _ _ _ Hst Hm1).
    + intros * Hst Hm HNs.
      destruct (Hpart _ _ _ _ _ _ Hst Hm) as (R1 & Hm1 & E1).
      rewrite <- E1 in HNs; exact (Hargs _ _ _ _ _ _ _ Hst Hm1 HNs).
  - (** A body *)
    intros * Hσ HH1 Hmem Hsub IHsub H0 HH Hs01 Hs10 Hq0 Hq1.
    apply glu_dmod_body; [ exact Hσ | exact HH | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst Hm HA HS HAt.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      pose proof (same_denote_mem_part x Hs01 Hq0 _ _ _ Hζ Hm) as Hm1.
      destruct (Hg _ _ _ _ _ _ _ _ Hst Hm1 HA HS HAt) as (i & P & El & Hgl).
      exists i, P, El.
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) as HH0ζ.
      pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH1 Hζ) as HH1ζ.
      destruct (me_denotes _ _ _ _ _ HH0ζ) as (R0 & Rm & HR0 & HRm).
      destruct (Hs01 _ _ _ _ Hζ HR0 HRm) as (R1 & HR1 & HR1m).
      exact (glu_elem_at_same_part HH0ζ HH1ζ Hm Hm1 HA HR0 HR1 HRm HR1m (glu_sub_through_rest _ _ _ _ _ _ _ _ Hst) Hgl).
    + intros * Hp Hu Hb Hc.
      pose proof (Hsub _ _ _ _ _ _ _ Hp Hu Hb Hc) as Hg1.
      pose proof (same_denote_mem_part y Hs01 Hq0) as Hd01.
      pose proof (same_denote_mem_part y Hs10 Hq1) as Hd10.
      (** The selection from [H0] is typed: it denotes what the one from
          [H1] does *)
      assert (HHy : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H0 y ≈ me_mem H0 y).
      { assert (HHy1 : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ me_mem H1 y ≈ me_mem H1 y) by (destruct Hg1; assumption).
        destruct (me_mod_tele_exists HHy1) as (R & T & HR & HT).
        assert (HR0 : mdenote gc_deps gc_stack Γ0 (me_mem H0 y) R).
        { pose proof (Hd10 _ Id R (wf_sub_id _ _ _ (presup_modexp_eq_ctx HH))) as Hd; rewrite !modexp_sub_id in Hd; exact (Hd HR). }
        eapply wf_me_mem; [ exact HH | exact HR0 | exact HT | exact HR0 | exact HT ]. }
      eapply IHsub; [ exact Hp | exact Hu | exact Hb | exact Hc | exact HHy
                    | exact (same_part_of_denote Hd01) | exact (same_part_of_denote Hd10)
                    | intros Γ2 ζ Hζ; apply names_no_frame_mem; [ exact (ctx_wf_gctx _ _ _ (wf_sub_cod _ _ _ _ _ Hζ)) | exact (Hq0 _ _ Hζ) ]
                    | intros Γ2 ζ Hζ; apply names_no_frame_mem; [ exact (ctx_wf_gctx _ _ _ (wf_sub_cod _ _ _ _ _ Hζ)) | exact (Hq1 _ _ Hζ) ] ].
  - (** A value lacking a parameter *)
    intros * Hσ HH1 Hn Hpar Happ IHapp H0 HH Hs01 Hs10 Hq0 Hq1.
    eapply glu_dmod_fun; [ exact Hσ | exact HH | exact Hn | | ].
    + intros * Hst Hm.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      destruct (modexp_mod_part _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) Hm) as (Rm & HRm).
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (RH1 & Hm1 & HRm1).
      destruct (Hpar _ _ _ _ _ _ Hst Hm1) as (T & B & T1 & [HT Hv Hgl]).
      exists T, B, T1; constructor; [| exact Hv | exact Hgl ].
      exact (mdesc_mod_tele_part _ _ _ HT (ex_intro _ Rm (conj HRm1 HRm))).
    + intros * Hst Hm HT Hv HS HB * Hu HP HN Hhc.
      pose proof (glu_sub_through_mid _ _ _ _ _ _ _ _ Hst) as Hζ.
      assert (HRm : exists Rm, mdesc_mod RH = Some Rm)
        by (unfold mdesc_mod_tele in HT; destruct (mdesc_mod RH); [ eexists; reflexivity | discriminate ]).
      destruct HRm as [Rm HRm].
      destruct (Hs01 _ _ _ _ Hζ Hm HRm) as (RH1 & Hm1 & HRm1).
      pose proof (mdesc_mod_tele_part _ _ _ HT (ex_intro _ Rm (conj HRm HRm1))) as HT1.
      pose proof (Happ _ _ _ _ _ _ _ _ _ _ Hst Hm1 HT1 Hv HS HB _ _ _ _ _ _ Hu HP HN Hhc) as Hg1.
      pose proof (same_part_sub Hζ Hs01) as Hs01'; pose proof (same_part_sub Hζ Hs10) as Hs10'.
      eapply IHapp; [ exact Hst | exact Hm1 | exact HT1 | exact Hv | exact HS | exact HB | exact Hu | exact HP | exact HN
                    | exact Hhc | | exact (same_part_app_var _ _ Hs01') | exact (same_part_app_var _ _ Hs10')
                    | intros; apply names_no_frame_of_none; reflexivity | intros; apply names_no_frame_of_none; reflexivity ].
      (** The application of [H0] is typed: its premises are those of
          [H1]'s application, the module parts being the same *)
      assert (HHg : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ me_app H1[ζ]ᵐ[Wk]ᵐ #0 ≈ me_app H1[ζ]ᵐ[Wk]ᵐ #0)
        by (destruct Hg1; assumption).
      destruct (proj1 (modexp_gen _ _ _ _ _ HHg)) as [HH1w (R' & T' & B' & T1' & S' & HR' & HT' & Hv' & HB' & HS' & HN')].
      assert (HRm' : exists Rm', mdesc_mod R' = Some Rm')
        by (unfold mdesc_mod_tele in HT'; destruct (mdesc_mod R'); [ eexists; reflexivity | discriminate ]).
      destruct HRm' as [Rm' HRm'].
      destruct (Hs10' (Γ1 ▹{domain_kind a} B) Wk R' Rm' ltac:(eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg)) HR' HRm')
        as (R0 & HR0 & HRm0).
      pose proof (mdesc_mod_tele_part _ _ _ HT' (ex_intro _ Rm' (conj HRm' HRm0))) as HT0.
      assert (HHw : gc_deps ⍮ gc_stack ⍮ Γ1 ▹{domain_kind a} B ⊢ᵐ H0[ζ]ᵐ[Wk]ᵐ ≈ H0[ζ]ᵐ[Wk]ᵐ).
      { eapply sub_preserves_modexp; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hζ) |].
        eapply wf_sub_shift; exact (presup_modexp_eq_ctx HHg). }
      eapply wf_me_app; [ exact HHw | exact HR0 | exact HT0 | exact Hv' | exact HB' | exact HS' | exact HN'
                        | apply wf_exp_eq_refl; exact HN' | exact HR0 | exact HT0 | exact Hv' | exact HB' | exact HS' | exact HN' ].
Qed.

End Fixed_GCtx.
