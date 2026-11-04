(** * Term Members of Valid Units

    A term member a valid unit, or a module expression valid in what it
    denotes, has by lookup is valid at the type lookup reads, its δ-reduct
    at it too ([valid_unit_mem_all]).  A definition of an expanded body is
    related to the definition of the same name of any body the module PER
    relates to it ([body_sel_term]); a unit lacking parameters types its
    members at the [Π] over them ([unit_walk]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas MemberWf DescTyping LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Canon.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.


Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.
  Hypothesis Hgf : valid_filed_mods Θm Ξm.

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_modexp := (valid_modexp Θm Ξm).

(** The term part a context entry holds: a definition's, or a definition
    with a module part's. *)
Definition centry_tm (e : centry) : option (exp * exp) :=
  match e with
  | ce_def A M | ce_dm A M _ => Some (A, M)
  | _ => None
  end.

(** The context entry of a body entry with a term part holds that term
    part. *)
Lemma body_ctx_tm : forall Φ x E A M, entry_tm E = Some (A, M) ->
    exists e, body_ctx (gm_ext Φ x E) = e :: body_ctx Φ /\ centry_tm e = Some (A, M).
Proof.
  intros * HE; destruct E as [b pv r A' [M' |] | | | pv A' M' U |]; cbn in HE; try discriminate;
    injection HE as <- <-; eexists; split; reflexivity.
Qed.

(** A context entry's term part is valid where the entry is, its type of
    either sort: a definition tagged propositional has a proposition as its
    type, so no universe can be asked of it ([rel_ctx_wf_def_inv]). *)
Lemma rel_ctx_wf_tm_inv : forall Γ e A M, ⊨ e :: Γ -> centry_tm e = Some (A, M) ->
    (exists Srt, type_sort Srt /\ Γ ⊨ A : Srt) /\ Γ ⊨ M : A.
Proof.
  intros * H He; destruct e; cbn in He; try discriminate; injection He as <- <-.
  - exact (rel_ctx_wf_def_inv H).
  - destruct (rel_ctx_wf_dm_inv H) as ([i HA] & HM & _); split; [ exists Typeω@i; split; [ apply type_sort_universe | exact HA ] | exact HM ].
Qed.

(** The type of a definition of a body tagged relevant is a relevant type,
    of a universe or of levels, in the context the body before it makes. *)
Lemma body_sorts_valid_relevant_entry : forall Φ D x Φ' E A M, body_sorts_valid Φ D ->
    gm_prefix_upto Φ x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) -> entry_relevance E = relevant ->
    exists Srt, relevant_sort Srt /\ body_ctx Φ' ++ D ⊨ A : Srt.
Proof.
  intros * Hsv Hp HE Hr.
  pose proof (body_sorts_valid_prefix _ _ _ _ Hp Hsv) as [_ Hh].
  destruct (Hh _ _ HE) as (Srt & HS & Hi); rewrite Hr in Hi; cbn [relevance_sort] in Hi; exists Srt; split; assumption.
Qed.

(** The type of a definition of a body tagged [r] is a type of the sort at
    [r], in the context the body before it makes. *)
Lemma body_sorts_valid_entry : forall Φ D x Φ' E A M, body_sorts_valid Φ D ->
    gm_prefix_upto Φ x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) ->
    exists Srt, relevant_sort Srt /\ body_ctx Φ' ++ D ⊨ A : relevance_sort (entry_relevance E) Srt.
Proof.
  intros * Hsv Hp HE.
  pose proof (body_sorts_valid_prefix _ _ _ _ Hp Hsv) as [_ Hh].
  exact (Hh _ _ HE).
Qed.

(** ** Definitions of a Body *)

(** A definition of a valid expanded body tagged relevant, against the
    definition of the same name of any body related to it. *)
Lemma body_sel_term : forall D Φ, gm_noopen Φ -> body_shape Φ Φ -> ⊨ body_ctx Φ ++ D -> body_sorts_valid Φ D ->
    gmod_scoped (List.length D) Φ ->
    forall RD ρ, EF D ≈ D ∈ per_ctx_env ↘ RD -> RD ρ ρ ->
    forall x Φ' E A M, gm_prefix_upto Φ x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) -> entry_relevance E = relevant ->
    exists ρ' a i RA r, ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' /\ ⟦ A ⟧ ρ' ↘ a /\ per_univ_elem i RA a a /\ ⟦ M ⟧ ρ' ↘ r /\
      forall ρh Φh, per_body ρh Φh ρ Φ ->
        exists Φh' Eh Ah Mh ρh' rh, gm_prefix_upto Φh x = Some (gm_ext Φh' x Eh) /\ entry_tm Eh = Some (Ah, Mh) /\
          entry_relevance Eh = relevant /\ ⟦ Φh' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρh' /\ ⟦ Mh ⟧ ρh' ↘ rh /\ RA rh r.
Proof.
  intros D Φ; revert D; induction Φ as [| Φ IH y E | Φ IH H its Φg];
    intros D Hno Hsx HC Hsv Hsc RD ρ HRD Hρ x Φx' E' A M Hp HEt Hrel; cbn in Hno; try contradiction; [ discriminate |].
  destruct (body_sorts_valid_relevant_entry _ _ _ _ _ _ _ Hsv Hp HEt Hrel) as (SrtE & HSE & HAE).
  cbn [body_shape] in Hsx; destruct Hsx as (Hsx0 & _ & HsE).
  pose proof (proj1 Hsc) as Hsc0.
  cbn [gm_prefix_upto] in Hp; destruct (String.eqb x y) eqn:Exy.
  - (* the entry itself, a definition or a definition with a module part *)
    apply String.eqb_eq in Exy; subst y; injection Hp as <- ->.
    destruct (body_ctx_tm Φ x _ _ _ HEt) as (e & He & Hetm); rewrite He in HC; cbn [app] in HC.
    destruct (rel_ctx_wf_tm_inv _ _ _ _ HC Hetm) as [_ HM].
    pose proof (rel_ctx_wf_tail HC) as HC0.
    pose proof (proj1 Hsv) as Hsv0.
    pose proof (gm_noopen_nopens _ Hno) as Hn.
    destruct (rel_ctx_wf_per_ctx_env HC0) as [R1 HR1].
    destruct (body_env_exists _ _ Hn (proj1 (body_shape_fill _ _ Hn Hsx0)) HC0 Hsv0 Hsc0 _ _ HRD HR1 _ Hρ) as (ρ1 & Hb1 & Hρ1).
    destruct (rel_param_typed_of_sort _ _ _ HSE HAE) as [i HAp].
    pose proof (rel_param_typed_type _ _ _ HAp) as HA.
    pose proof (rel_type_relevant_of_relevant_sort HSE HAE) as HAr.
    destruct (rel_type_inversion_simple_at HR1 HA _ _ Hρ1) as (a & a' & Ha & Ha' & [RA HRA]).
    pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
    destruct (rel_exp_under_ctx_simple_at_relevant HR1 HM _ _ Hρ1 (HAr _ HR1 _ _ Hρ1)) as (r & _ & Hr & _ & _).
    assert (Hra : domain_relevance a = relevant)
      by (destruct (HAr _ HR1 _ _ Hρ1) as (a0 & Ea0 & Hr0); functional_eval_rewrite_clear; exact Hr0).
    exists ρ1, a, i, RA, r; split; [ exact Hb1 | split; [ exact Ha | split; [ exact HRA | split; [ exact Hr |] ] ] ].
    intros ρh Φh Hbh.
    inversion Hbh; subst; try (cbn in HEt; discriminate).
    all: cbn in HEt; injection HEt as -> ->.
    (* a definition tagged relevant, as this one: related values *)
    all: try match goal with
         | Hor : ?r0 = propositional \/ PER.Definitions.rel_elem _ _ _ _ _ |- _ =>
             cbn [entry_relevance] in Hrel; subst r0; destruct Hor as [Hor | Hor]; [ discriminate |]
         end.
    all: match goal with
         | Hb1' : ⟦ ?Φr ⟧ᵇ _ ⍮ _ ⍮ ?ρr ↘ ?ρ1', Hbh1 : ⟦ ?Φh0 ⟧ᵇ _ ⍮ _ ⍮ ?ρl ↘ ?ρh1,
           HT : PER.Definitions.rel_typ _ _ ?ρh1 _ ?ρ1' ?Rr, HM' : context [PER.Definitions.rel_elem _ ?ρh1 _ ?ρ1' ?Rr] |- _ =>
             pose proof (functional_eval_body_env _ _ _ _ Hb1' Hb1) as ->;
             destruct HT as [ah a2 Hah Ha2 HRah];
             functional_eval_rewrite_clear;
             (* a definition with a module part: its type is relevant, as this one's *)
             lazymatch type of HM' with
             | _ \/ _ =>
                 destruct HM' as [(a0 & Ea0 & Hpa0) | HM']; [ exfalso; functional_eval_rewrite_clear;
                                                             pose proof (per_univ_elem_relevance _ _ _ _ HRah); congruence |]
             | _ => idtac
             end;
             destruct HM' as [mh m2 Hmh Hm2 HRm];
             functional_eval_rewrite_clear;
             let E := fresh "E" in
             assert (E : Rr <~> RA) by (eapply per_univ_elem_left_irrel; [ exact HRah | exact HRA ]);
             exists Φh0; do 5 eexists; split; [ cbn; rewrite String.eqb_refl; reflexivity |];
             split; [ reflexivity | split; [ reflexivity | split; [ exact Hbh1 | split; [ exact Hmh | apply E; exact HRm ] ] ] ]
         end.
  - (* an entry before it *)
    assert (HC0 : ⊨ body_ctx Φ ++ D) by (destruct E as [? ? ? ? [] | | | |]; cbn in HsE; try contradiction; exact (rel_ctx_wf_tail HC)).
    destruct (IH _ Hno Hsx0 HC0 (proj1 Hsv) Hsc0 _ _ HRD Hρ _ _ _ _ _ Hp HEt Hrel) as (ρ' & a & i & RA & r & Hb & Ha & HRA & Hr & Hh).
    exists ρ', a, i, RA, r; split; [ exact Hb | split; [ exact Ha | split; [ exact HRA | split; [ exact Hr |] ] ] ].
    intros ρh Φh Hbh.
    assert (Hrest : exists Φh0 Eh, Φh = gm_ext Φh0 y Eh /\ per_body ρh Φh0 ρ Φ)
      by (inversion Hbh; subst; eauto).
    destruct Hrest as (Φh0 & Eh & -> & Hbh0).
    destruct (Hh _ _ Hbh0) as (Φh' & Eh' & Ah & Mh & ρh' & rh & Hph & HEh & HrEh & Hbh' & Hmh & Hrr).
    exists Φh', Eh', Ah, Mh, ρh', rh; split; [ cbn; rewrite Exy; exact Hph | split; [ exact HEh | split; [ exact HrEh | split; [ exact Hbh' | split; assumption ] ] ] ].
Qed.

(** ** What the Term Members of Literals Denote *)

Lemma mdesc_type_mod_none : forall R, mdesc_is_mod R -> mdesc_type R = None.
Proof. intros [| | | ] H; cbn in *; first [ contradiction | reflexivity ]. Qed.

(** A term part of a body, a definition's or a definition with a module
    part's, filled in, over the parameters. *)
Lemma body_mem_desc : forall Γ Δ Φ Φx x R A, body_xp Θm Ξm (Δ ++ Γ) Φ Φx ->
    mdenote Θm Ξm Γ (me_mem (me_lit (gu_open Δ Φ)) x) R -> mdesc_type R = Some A ->
    exists Φ' E A0 M0 σ, gm_prefix_upto Φx x = Some (gm_ext Φ' x E) /\ entry_tm E = Some (A0, M0) /\ gm_fill Φ' = Some σ /\
      A = ctx_pi_at (entry_relevance E) Δ A0[σ] /\ mdesc_reduct R = Some (ctx_fn Δ M0[σ]) /\
      mdesc_relevance R = entry_relevance E.
Proof.
  intros * Hx Hm Ht.
  inversion Hm as [? ? ? ? ? Hq _ | ? ? ? ? ? ? ? ? ? Hq _ | | | |? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd He Hed Hr | ? ? ? ? ? ? Hq _]; subst;
    [ cbn in Hq; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
  inversion Hm0; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
  match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
  match goal with Hx' : body_xp _ _ _ Φ ?Φx1 |- _ =>
    pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgm)))) _ _ _ Hx _ Hx') as <- end.
  cbn in Hmd; injection Hmd as <-.
  cbn in He; destruct (gm_prefix_upto Φx x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  destruct E0 as [[|] pv r0 A0 [M0 |] | pv U | | pv A0 M0 U |]; try discriminate; injection He as <- <- <-.
  - inversion Hed; subst; cbn in Hr.
    destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    cbn in Ht; injection Ht as <-.
    do 5 eexists; split; [ reflexivity | split; [ reflexivity | split; [ exact Hf | split; [ reflexivity | split; reflexivity ] ] ] ].
  - exfalso; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmod end.
    cbn in Hr; destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
    rewrite (mdesc_type_mod_none _ (mdesc_is_mod_up Δ _ (mdesc_is_mod_sub _ σ Hmod))) in Ht; discriminate.
  - (* a definition with a module part: its term part *)
    inversion Hed; subst; cbn in Hr.
    destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    cbn in Ht; injection Ht as <-.
    do 5 eexists; split; [ reflexivity | split; [ reflexivity | split; [ exact Hf | split; [ reflexivity |] ] ] ].
    split; cbn; reflexivity.
Qed.

(** The outside parameters of a closed module part read with more of them:
    the same, except that a term of no δ-reduct read bare is read as its
    name with them. *)
Lemma mdesc_named_app : forall Θ Δ Ns M R,
    mdesc_named (Θ ++ Δ) Ns M R = mdesc_named Θ Ns M R \/
    (Θ = nil /\ Ns = nil /\ exists r A0, R = mdesc_term r A0 None /\ mdesc_named (Θ ++ Δ) Ns M R = mdesc_term r A0 (Some M)).
Proof.
  intros [| e Θ] [| e' Δ] [| N Ns] M R; cbn [List.app]; try (left; reflexivity).
  destruct R as [r A0 [M0 |] | | |]; try (left; reflexivity).
  right; repeat split; eauto.
Qed.

(** A term member of an alias is its target's, over the parameters; or,
    when the target is a filed module read bare and the member has no
    δ-reduct there, the member read as its name over the parameters. *)
Lemma alias_mem_desc : forall Γ Δ E x R A, ⊢ Θm ⍮ Ξm ⍮ Δ ++ Γ ->
    mdenote Θm Ξm Γ (me_mem (me_lit (gu_mk Δ (md_alias E))) x) R -> mdesc_type R = Some A ->
    exists R', mdenote Θm Ξm (Δ ++ Γ) (me_mem E x) R' /\
      (R = mdesc_up Δ R' \/
       exists r A0 RE p T Φ, R' = mdesc_term r A0 None /\ mdenote Θm Ξm (Δ ++ Γ) E RE /\
         mdesc_mod RE = Some (mdesc_closed nil p T Φ nil) /\ R = mdesc_up Δ (mdesc_term r A0 (Some (a_mem (qname_mod p) x)))).
Proof.
  intros * HΔΓ Hm Ht.
  inversion Hm as [? ? ? ? ? Hq _ | ? ? ? ? ? ? ? ? ? Hq _ | | | |? ? ? R0 R0m Γy Ee rd R1 ? Hm0 Hmd He Hed Hr | ? ? ? ? ? ? Hq _]; subst;
    [ cbn in Hq; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
  inversion Hm0; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? ? RE REm HmE HmodE]; subst end.
  pose proof (mdesc_mod_is_mod _ _ HmodE) as HisE.
  rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ HisE)) in Hmd; injection Hmd as <-.
  destruct REm as [| Δe Φ Φx | Θ p T Φ Ns |]; cbn in HisE; try contradiction; cbn [mdesc_up] in He, Hed.
  - (* an open module part *)
    cbn in He; destruct (gm_prefix_upto Φx x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
    pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
    assert (He' : exists Ee', mdesc_entry (mdesc_open Δe Φ Φx) x = Some (body_ctx Φ' ++ Δe, Ee', reader_open Δe Φ') /\
                    Ee = Ee' /\ Γy = body_ctx Φ' ++ Δe ++ Δ /\ rd = reader_open (Δe ++ Δ) Φ').
    { cbn; rewrite Hp; destruct E0 as [[|] ? ? ? [] | | | |]; try discriminate; injection He as <- <- <-; eexists; repeat split. }
    destruct He' as (Ee' & He' & -> & -> & ->).
    cbn [mdesc_read] in Hr; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    exists (mdesc_up Δe (mdesc_sub R1 σ)); split; [| left; rewrite mdesc_up_cat; reflexivity ].
    cbn [mdesc_entry_path] in Hed; rewrite <- !app_assoc in Hed.
    eapply mdenote_mem; [ exact HmE | exact HmodE | exact He' | cbn [mdesc_entry_path]; rewrite <- app_assoc; exact Hed | cbn; rewrite Hf; reflexivity ].
  - (* a closed module part *)
    cbn in He; destruct (gm_prefix_upto Φ x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    cbn [mdesc_read] in Hr; destruct (mdesc_ats_read R1 Ns) as [R2 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
    assert (Hed' : edenote Θm Ξm (nil ++ Δ ++ Γ) (Some (qname_in p x)) (ge_read T E0) R1).
    { destruct E0 as [? ? ? ? | pv U | | pv Ad Md Ud | ] eqn:EE0; cbn [ge_read] in Hed |- *;
        [ inversion Hed; subst; constructor | | inversion Hed; subst; econstructor; eassumption | |
          inversion Hed; subst; econstructor; eassumption ].
      2:{ (* a definition with a module part: closed, so read alike in any
             context *)
        pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgm HmE) HmodE) as Hc; cbn in Hc.
        pose proof (loc_closed _ _ Hgm _ _ _ Hc) as HU.
        assert (He0 : mdesc_entry (mdesc_closed Θ p T Φ Ns) x = Some (nil, ge_read T E0, reader_closed Θ Ns (apps (a_mem (qname_mod p) x) Ns)))
          by (subst E0; cbn; rewrite Hp; reflexivity).
        destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU He0) as (_ & HsE & _).
        subst E0; cbn [ge_read] in HsE.
        pose proof (ctx_app_wf_right _ _ _ _ HΔΓ) as HΓ.
        assert (Hσ : sub_mod_compat (sb_of_wk (wk_shiftn (List.length Δ))) (Δ ++ Γ) Γ)
          by (eapply wf_sub_mod_compat, wf_sub_of_wk, wf_wk_shiftn_app; eassumption).
        exact (edenote_closed_move _ _ _ _ _ _ _ _ (wf_gstack_closed _ _ Hgm) HsE Hed Hσ). }
      exfalso.
      assert (HU : exists U', match U with | gu_mk Δ (md_body sm_closed Φ) => ge_mod pv (gu_mk (Δ ++ T) (md_body sm_closed Φ)) | _ => ge_mod pv U end = ge_mod pv U')
        by (destruct U as [? [[] ?|?]]; eexists; reflexivity).
      destruct HU as [U' HU]; rewrite HU in Hed; inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ =>
        rewrite (mdesc_ats_read_mod _ _ (udenote_is_mod _ _ _ _ _ _ Hu)) in Ha;
        pose proof (mdesc_ats_is_mod _ _ _ (udenote_is_mod _ _ _ _ _ _ Hu) Ha) as Hmod end.
      rewrite mdesc_up_cat in Ht.
      destruct R2; cbn in Hmod; try contradiction; rewrite mdesc_named_fix in Ht by reflexivity; cbn in Ht; discriminate. }
    exists (mdesc_up Θ (mdesc_named Θ Ns (apps (a_mem (qname_mod p) x) Ns) R2)); split.
    { eapply mdenote_mem; [ exact HmE | exact HmodE | cbn; rewrite Hp; reflexivity | exact Hed' | cbn; rewrite Ha; reflexivity ]. }
    destruct (mdesc_named_app Θ Δ Ns (apps (a_mem (qname_mod p) x) Ns) R2) as [Hn | (-> & -> & r & A0 & -> & Hn)];
      rewrite Hn; [ left; rewrite mdesc_up_cat; reflexivity |].
    right; exists r, A0, RE, p, T, Φ; split; [ reflexivity | split; [ exact HmE | split; [ exact HmodE | reflexivity ] ] ].
Qed.

(** A member of no δ-reduct of a module expression whose module part is a
    filed module read bare is related to that filed member. *)
Lemma valid_mem_bare_name : forall Γ E RE p T Φ x A,
    valid_modexp Γ E -> mdenote Θm Ξm Γ E RE -> mdesc_mod RE = Some (mdesc_closed nil p T Φ nil) ->
    valid_mem Γ E x A None -> valid_mem Γ E x A (Some (a_mem (qname_mod p) x)).
Proof.
  intros * Hs Hm Hmd Hsm.
  assert (HEP : Γ ⊨ᵐ E ≈ mdesc_unit (mdesc_closed nil p T Φ nil)) by (eapply valid_modexp_canon; eassumption).
  cbn [mdesc_unit me_apps] in HEP.
  pose proof (valid_mem_transport _ _ _ _ _ _ (rel_modexp_under_ctx_sym HEP) Hsm) as HsmP.
  pose proof (rel_mem_of_valid_mem _ _ _ _ _ _ (rel_modexp_under_ctx_trans (rel_modexp_under_ctx_sym HEP) HEP) HsmP) as HPx.
  destruct Hsm as [HA _ HS].
  constructor; [ exact HA | intros M [= <-]; exact HPx |].
  intros RΓ HR ρ Hρ.
  destruct (HS _ HR _ Hρ) as [k a i RA Hk Ha HRA Hmt _].
  destruct (rel_modexp_at _ _ _ _ _ HEP HR _ _ Hρ) as (k1 & kp & Hk1 & Hkp & Hkk).
  pose proof (functional_eval_modexp _ _ _ _ Hk1 Hk) as ->.
  apply mk_valid_mem_at with (valid_mem_at_mod := k) (valid_mem_at_typ := a) (valid_mem_at_lvl := i) (valid_mem_at_rel := RA); try assumption.
  intros Hrel M [= <-]; destruct (Hmt Hrel _ (per_dmod_sym _ _ Hkk)) as [r r' Hr Hr' Hrr].
  apply (mk_rel_mem_reduct _ _ _ _ _ r r'); [ eapply eval_mem_of_sel; eassumption | assumption | assumption ].
Qed.

(** ** Units Lacking Parameters *)

(** A unit's closure lacking its parameters types a member at the [Π] over
    them of the type its closure with all of them given types it at, and
    the [λ] over them of a term related to that member is related to it.
    The type is a relevant type of either sort, a type of a universe or a
    type of levels: the [Π] is read in the PER model, whatever its sort
    ([rel_type_ctx_pi]).  The closure applied to an argument stores it at
    the parameter's type ([eval_appm_local]), the [Π] and the [λ] at its
    value: the types and the reducts there are related through their
    judgments. *)
Lemma unit_walk : forall Δ Γ D x A0 om0 RΓ lp k0,
    tele_ass Δ -> rel_params_relevant Γ Δ lp -> ⊨ Δ ++ Γ -> Δ ++ Γ ⊨ᵗ A0 ≈ A0 at k0 -> rel_type_relevant (Δ ++ Γ) A0 ->
    (forall M0, om0 = Some M0 -> Δ ++ Γ ⊨ M0 : A0) ->
    (forall R, EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R -> forall ρ, R ρ ρ -> forall k, ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k ->
       exists a i Ra, ⟦ A0 ⟧ ρ ↘ a /\ per_univ_elem i Ra a a /\ dmod_has_mem k x Ra /\
         forall M0, om0 = Some M0 -> exists m r, ⟦ M0 ⟧ ρ ↘ m /\ k ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Ra m r) ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ, RΓ ρ ρ -> forall k, ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k -> per_dmod k k ->
    exists a i Ra, ⟦ ctx_pi Δ A0 ⟧ ρ ↘ a /\ per_univ_elem i Ra a a /\ dmod_has_mem k x Ra /\
      forall M0, om0 = Some M0 -> exists m r, ⟦ ctx_fn Δ M0 ⟧ ρ ↘ m /\ k ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Ra m r.
Proof.
  induction Δ as [| e Δ0 IH] using rev_ind; intros * HΔ HΔr HC HA HAr HM Hbase HΓ ρ Hρ k Hk Hkk; cbn [List.app] in *.
  - exact (Hbase _ HΓ _ Hρ _ Hk).
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? [X ->] _]; subst.
    destruct (rel_params_relevant_snoc_inv _ _ _ _ HΔr) as [HX HΔ0r].
    pose proof (rel_param_typed_type _ _ _ HX) as HXt.
    destruct (rel_type_ctx_pi _ _ _ _ _ HΔ HC HΔr HA HAr) as [HPi _].
    rewrite <- app_assoc in HC, HA, HAr, HM, Hbase; cbn [List.app] in HC, HA, HAr, HM, Hbase.
    destruct (rel_type_ctx_pi _ _ _ _ _ HΔ0 HC HΔ0r HA HAr) as [HcodT HcodR].
    assert (HMf : forall M0, om0 = Some M0 -> Γ ▹ X ⊨ ctx_fn Δ0 M0 : ctx_pi Δ0 A0)
      by (intros M0 HM0; exact (rel_exp_ctx_fn _ _ _ _ _ _ HΔ0 HC HΔ0r HA HAr (HM _ HM0))).
    pose proof (per_ctx_env_of_typ HΓ HXt) as HΓX.
    assert (HP : PER RΓ) by (eapply per_env_PER; exact HΓ).
    pose proof (functional_eval_close _ _ _ _ _ Hk (close_unsat (Δ0 ++ ce_ass X :: nil) D ρ ltac:(rewrite length_app; cbn; lia))) as ->.
    rewrite ctx_pi_app in HPi |- *; cbn [ctx_pi_at] in HPi |- *.
    destruct (rel_type_inversion_simple_at HΓ HPi _ _ Hρ) as (a & a' & Ha & Ha' & [Ra HRa]).
    pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
    inversion Ha; subst.
    match goal with H3 : ⟦ X ⟧ ρ ↘ ?a0 |- _ => rename H3 into HXa; rename a0 into a0 end.
    set (k := dm_local (Δ0 ++ ce_ass X :: nil) (moddef_expand D) ρ) in *.
    assert (Hnp : next_param k a0) by (constructor; exact HXa).
    assert (Hsel : k ·ₜ x gc_deps ⍮ gc_stack ↘ d_member k (x :: nil)) by (apply eval_sel_unsat; rewrite length_app; cbn; lia).
    destruct (rel_type_inversion_simple_at HΓ HXt _ _ Hρ) as (x0 & x0' & Hx0 & Hx0' & [RX HRX]).
    pose proof (functional_eval_exp _ _ _ _ Hx0 HXa) as ->; pose proof (functional_eval_exp _ _ _ _ Hx0' HXa) as ->.
    destruct (rel_param_typed_relevant HX _ HΓ _ _ Hρ) as (x1 & Hx1 & Hra0).
    pose proof (functional_eval_exp _ _ _ _ Hx1 HXa) as ->.
    (* the step to one more argument: the closure stores it at [X]'s
       closure, the [Π] at [X]'s value *)
    assert (Hstep : forall j Rx c, per_univ_elem j Rx a0 a0 -> Rx c c -> forall kc b, $ᵐ| k & c | gc_deps ⍮ gc_stack ↘ kc ->
               ⟦ ctx_pi Δ0 A0 ⟧ ρ ↦ c ⦂ entry_type_value a0 ↘ b ->
               exists l Rb, per_univ_elem l Rb b b /\ dmod_has_mem kc x Rb /\
                 forall M0, om0 = Some M0 -> exists m r, ⟦ ctx_fn Δ0 M0 ⟧ ρ ↦ c ⦂ entry_type_value a0 ↘ m /\
                   kc ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Rb m r).
    { intros j Rx c HRx Hc kc b Hkc Hb.
      assert (ERx : Rx <~> RX) by (eapply per_univ_elem_right_irrel; [ exact HRx | exact HRX ]).
      pose proof (proj1 (ERx c c) Hc) as HcX.
      pose proof (entry_readable_of_elem HRX HcX) as [Rv _].
      pose proof (entry_readable_of_elem_closure HXa HXa HRX HcX) as [Rc Rc'].
      assert (Hρc : per_env_extend X X RΓ (ρ ↦ c ⦂ entry_type_closure X ρ) (ρ ↦ c ⦂ entry_type_closure X ρ))
        by (apply (mk_per_ctx_env_cons_rel _ _ _ _ (ρ ↦ c ⦂ entry_type_closure X ρ) (ρ ↦ c ⦂ entry_type_closure X ρ) Hρ);
            [ eapply per_head_of; [ exact HXa | exact HXa | exact HRX | exact HcX ] | intros _; eexists; reflexivity
            | intros _; eexists; reflexivity | split; [ exact Rc | cbn; lia ] | split; [ exact Rc' | cbn; lia ] ]).
      assert (Hmix : per_env_extend X X RΓ (ρ ↦ c ⦂ entry_type_value a0) (ρ ↦ c ⦂ entry_type_closure X ρ))
        by (apply (mk_per_ctx_env_cons_rel _ _ _ _ (ρ ↦ c ⦂ entry_type_value a0) (ρ ↦ c ⦂ entry_type_closure X ρ) Hρ);
            [ eapply per_head_of; [ exact HXa | exact HXa | exact HRX | exact HcX ] | intros _; eexists; reflexivity
            | intros _; eexists; reflexivity | split; [ exact Rv | cbn; lia ] | split; [ exact Rc | cbn; lia ] ]).
      destruct (per_dmod_appm _ _ _ Hkk Hnp) as (ih & Rh & ah & Hph & HRh & Happ).
      pose proof (next_param_functional _ _ Hph _ Hnp) as ->.
      assert (Eh : Rh <~> RX) by (eapply per_univ_elem_right_irrel; [ exact HRh | exact HRX ]).
      destruct (Happ c c (proj2 (Eh _ _) HcX)) as (kc1 & kc2 & Hk1 & Hk2 & Hkk').
      pose proof (functional_eval_appm _ _ _ _ Hk1 Hkc) as ->; pose proof (functional_eval_appm _ _ _ _ Hk2 Hkc) as ->.
      inversion Hkc as [| ? ? ? ? ? ? Hkc' Hl |]; subst.
      apply app_inj_tail in Hl as [<- [= <-]].
      destruct (IH _ _ _ _ _ _ _ _ HΔ0 HΔ0r HC HA HAr HM Hbase HΓX _ Hρc _ ltac:(apply eval_close_expand_iff; exact Hkc') Hkk')
        as (b' & l & Rb & Hb' & HRb & Hm & Hred).
      destruct (extension_value_closure_type _ _ _ _ _ _ _ _ _ _ _ _ HΓ HXt HcodT Hρ HXa HRX HcX Hb Hb') as [Q HQ].
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HQ (proj1 (per_univ_elem_sym _ _ _ _ HQ))) as (Rb0 & HRb0 & _).
      assert (ERb : Rb0 <~> Rb) by (eapply per_univ_irrel_rel; [ exact HRb0 | eexists; exact HQ | exact HRb ]).
      assert (HPb0 : PER Rb0) by (eapply per_elem_PER; exact HRb0).
      eexists _, Rb0; split; [ exact HRb0 |].
      split; [ apply (dmod_has_mem_iff _ _ Rb); [ exact Hm | symmetry; exact ERb ] |].
      intros M0 HM0.
      destruct (Hred _ HM0) as (m' & r & Hm' & Hr & Hmr).
      (* the reduct at [X]'s value, against it at [X]'s closure *)
      destruct (valid_at _ _ _ _ _ (HMf _ HM0) HcodT HcodR HΓX _ _ Hmix)
        as (mv & mc & av & iv & Rv' & Hmv & Hmc & Hav & HRv' & Hmvc).
      pose proof (functional_eval_exp _ _ _ _ Hmc Hm') as ->.
      pose proof (functional_eval_exp _ _ _ _ Hav Hb) as ->.
      assert (Ev : Rv' <~> Rb0) by (eapply per_univ_elem_right_irrel; [ exact HRv' | exact HRb0 ]).
      exists mv, r; split; [ exact Hmv | split; [ exact Hr |] ].
      etransitivity; [ apply Ev; exact Hmvc | apply ERb; exact Hmr ]. }
    eexists (Πᵈ a0 ρ (ctx_pi Δ0 A0)), _, Ra; split; [ exact Ha | split; [ exact HRa | split ] ].
    + eapply dmod_has_mem_fun; [ exact Hnp | exact Hkk | exact HRa | exists lp, RX; exact HRX | exact Hra0 | | eexists; exact Hsel ].
      intros j Rx c HRx Hc kc b Hkc Hb; destruct (Hstep _ _ _ HRx Hc _ _ Hkc Hb) as (l & Rb & HRb & Hm & _).
      exists l, Rb; split; assumption.
    + intros M0 HM0; rewrite ctx_fn_app; cbn [ctx_fn].
      exists (λᵈ a0 ρ (ctx_fn Δ0 M0)), (d_member k (x :: nil)).
      split; [ apply eval_exp_fn; exact HXa |]; split; [ exact Hsel |].
      eapply red_fun; [ exact Hnp | exact HRa | exists lp, RX; exact HRX | exact Hkk | exact Hsel | exact Hra0 | exact Hra0 |].
      intros j Rx c HRx Hc kc b Hkc Hb; destruct (Hstep _ _ _ HRx Hc _ _ Hkc Hb) as (l & Rb & HRb & Hm & Hred).
      destruct (Hred _ HM0) as (m & r & Hm0 & Hr & Hmr).
      exists l, Rb, m, r; repeat split; try assumption; apply eval_app_fn; exact Hm0.
Qed.

(** ** Definitions of a Saturated Body *)

(** A definition filled in, at an environment, against its value in the
    environment the body before it makes. *)
Lemma body_def_rel : forall D Φx x Φ' E A M σ,
    gm_nopens Φx = 0 -> ⊨ body_ctx Φx ++ D -> body_sorts_valid Φx D -> gmod_scoped (List.length D) Φx ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) -> entry_relevance E = relevant ->
    gm_fill Φ' = Some σ ->
    forall RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> forall ρ, RD ρ ρ ->
    exists ρ1 a1 a3 m1 m3 (i : nat) R, ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\
      ⟦ A[σ] ⟧ ρ ↘ a1 /\ ⟦ A ⟧ ρ1 ↘ a3 /\ per_univ_elem i R a1 a3 /\
      ⟦ M[σ] ⟧ ρ ↘ m1 /\ ⟦ M ⟧ ρ1 ↘ m3 /\ R m1 m3.
Proof.
  intros * Hn HC Hsv Hsc Hp HE Hrel Hf RD HD ρ Hρ.
  destruct (body_sorts_valid_relevant_entry _ _ _ _ _ _ _ Hsv Hp HE Hrel) as (Srt & HSrt & HA).
  destruct (rel_param_typed_of_sort _ _ _ HSrt HA) as [i HAp].
  pose proof (rel_param_typed_type _ _ _ HAp) as HAt.
  pose proof (rel_type_relevant_of_relevant_sort HSrt HA) as HAr.
  pose proof (proj1 (body_sorts_valid_prefix _ _ _ _ Hp Hsv)) as Hsv'.
  pose proof (proj1 (gmod_scoped_prefix_upto _ _ _ _ Hp Hsc)) as Hsc'.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as [Ψ HΨ].
  destruct (body_ctx_tm Φ' x _ _ _ HE) as (e & He & Hetm); rewrite He in HΨ.
  rewrite HΨ, <- app_assoc in HC; cbn [List.app] in HC.
  pose proof (rel_ctx_wf_app_r _ _ HC) as HC1.
  pose proof (rel_ctx_wf_tail HC1) as HC0.
  destruct (rel_ctx_wf_tm_inv _ _ _ _ HC1 Hetm) as [_ HM].
  pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn in Hn'.
  destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
  destruct (fill_rel _ _ _ Hn' Hf HC0 Hsv' Hsc' _ _ HD HR0 _ Hρ) as (ρσ & ρ1 & Hσ & Hb & H01).
  pose proof (fill_gsub _ _ _ Hn' Hf HC0 Hsc') as Hg.
  pose proof (gsub_valid Hg) as Hτ.
  destruct (rel_type_inst _ _ _ _ _ _ HAt Hτ HD _ _ Hρ Hσ) as (a1 & a2 & Ha1 & Ha2 & [Ra12 H12]).
  destruct (rel_type_inversion_simple_at HR0 HAt _ _ H01) as (a2' & a3 & Ha2' & Ha3 & [Ra23 H23]).
  functional_eval_rewrite_clear.
  destruct (valid_inst _ _ _ _ _ _ HM HAr Hτ HD _ _ Hρ Hσ) as (m1 & m2 & a2' & j & Rm & Hm1 & Hm2 & Ha2' & HRm & Hm12).
  destruct (valid_at _ _ _ _ _ HM HAt HAr HR0 _ _ H01) as (m2' & m3 & a2'' & j' & Rm' & Hm2' & Hm3 & Ha2'' & HRm' & Hm23).
  functional_eval_rewrite_clear.
  assert (E1 : Rm <~> Ra12) by (eapply per_univ_elem_right_irrel; [ exact HRm | apply per_univ_elem_sym; exact H12 ]).
  assert (E2 : Rm' <~> Ra12) by (eapply per_univ_elem_right_irrel; [ exact HRm' | apply per_univ_elem_sym; exact H12 ]).
  assert (E3 : Ra23 <~> Ra12) by (eapply per_univ_elem_right_irrel; [ exact H23 | apply per_univ_elem_sym; exact H12 ]).
  assert (HP12 : PER Ra12) by (eapply per_elem_PER; exact H12).
  assert (H13 : per_univ_elem i Ra12 a1 a3)
    by (eapply per_univ_trans; [ exact H12 | exact (per_univ_elem_resp_iff H23 E3) ]).
  exists ρ1, a1, a3, m1, m3, i, Ra12; repeat split; try assumption.
  apply E1 in Hm12; apply E2 in Hm23; etransitivity; eassumption.
Qed.

(** A definition of an expanded body filled in, against the member of the
    body's value: the member is the definition's value. *)
Lemma body_base : forall D Φx x Φ' E A M σ,
    gm_noopen Φx -> body_shape Φx Φx -> ⊨ body_ctx Φx ++ D -> body_sorts_valid Φx D -> gmod_scoped (List.length D) Φx ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) -> entry_relevance E = relevant ->
    gm_fill Φ' = Some σ ->
    forall RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> forall ρ, RD ρ ρ -> forall sm,
    exists a i Ra, ⟦ A[σ] ⟧ ρ ↘ a /\ per_univ_elem i Ra a a /\ dmod_has_mem (dm_local nil (md_body sm Φx) ρ) x Ra /\
      exists m r, ⟦ M[σ] ⟧ ρ ↘ m /\ dm_local nil (md_body sm Φx) ρ ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Ra m r.
Proof.
  intros * Hno Hsx HC Hsv Hsc Hp HEt Hrel Hf RD HD ρ Hρ sm.
  pose proof (gm_noopen_nopens _ Hno) as Hn.
  destruct (body_sel_term _ _ Hno Hsx HC Hsv Hsc _ _ HD Hρ _ _ _ _ _ Hp HEt Hrel) as (ρ' & a & i & RA & r & Hb' & Ha & HRA & Hr & Hh).
  destruct (body_def_rel _ _ _ _ _ _ _ _ Hn HC Hsv Hsc Hp HEt Hrel Hf _ HD _ Hρ)
    as (ρ1 & a1 & a3 & m1 & m3 & i1 & R1 & Hb1 & Ha1 & Ha3 & HR13 & Hm1 & Hm3 & HRm).
  pose proof (functional_eval_body_env _ _ _ _ Hb1 Hb') as ->.
  functional_eval_rewrite_clear.
  assert (Hpx : gm_prefix_upto (gm_expand Φx) x = Some (gm_ext Φ' x E)) by (rewrite (gm_expand_noopen _ Hno); exact Hp).
  assert (Hsel : dm_local nil (md_body sm Φx) ρ ·ₜ x gc_deps ⍮ gc_stack ↘ r)
    by (eapply eval_sel_body; [ exact Hpx | exact HEt | exact Hrel | exact Hb' | exact Hr ]).
  assert (HPR : PER R1) by (eapply per_elem_PER; exact HR13).
  assert (HR11 : per_univ_elem i1 R1 a1 a1) by (etransitivity; [ exact HR13 | symmetry; exact HR13 ]).
  assert (ER : R1 <~> RA) by (eapply per_univ_elem_right_irrel; [ apply per_univ_elem_sym; exact HR13 | exact HRA ]).
  exists a1, i1, R1; split; [ exact Ha1 | split; [ exact HR11 | split ] ].
  - intros h Hh0.
    inversion Hh0; subst;
      [| exfalso; match goal with Hn0 : next_param (dm_local nil (md_body _ _) _) _ |- _ => exact (next_param_body_nil _ _ _ _ Hn0) end ].
    match goal with Hb0 : per_body ?ρh ?Φh ρ Φx |- _ => rename Hb0 into Hbh end.
    destruct (Hh _ _ Hbh) as (Φh' & Eh & Ah & Mh & ρh' & rh & Hph & HEh & HrEh & Hbh' & Hmh & Hrr).
    pose proof (proj1 (per_body_noopen _ _ _ _ Hbh)) as Hnoh.
    apply (mk_rel_mem_val _ _ _ _ rh r);
      [ eapply eval_sel_body; [ rewrite (gm_expand_noopen _ Hnoh); exact Hph | exact HEh | exact HrEh | exact Hbh' | exact Hmh ]
      | exact Hsel | apply ER; exact Hrr ].
  - exists m1, r; split; [ exact Hm1 | split; [ exact Hsel | exact HRm ] ].
Qed.

(** A definition of a body filled in: its type of the sort it is tagged
    with, its body of that type. *)
Lemma body_def_valid : forall D Φx x Φ' E A M σ,
    gm_nopens Φx = 0 -> ⊨ body_ctx Φx ++ D -> body_sorts_valid Φx D -> gmod_scoped (List.length D) Φx ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) -> gm_fill Φ' = Some σ ->
    (exists Srt, relevant_sort Srt /\ D ⊨ A[σ] : relevance_sort (entry_relevance E) Srt) /\ D ⊨ M[σ] : A[σ].
Proof.
  intros * Hn HC Hsv Hsc Hp HE Hf.
  destruct (body_sorts_valid_entry _ _ _ _ _ _ _ Hsv Hp HE) as (Srt & HSrt & HA).
  pose proof (proj1 (gmod_scoped_prefix_upto _ _ _ _ Hp Hsc)) as Hsc'.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as [Ψ HΨ].
  destruct (body_ctx_tm Φ' x _ _ _ HE) as (e & He & Hetm); rewrite He in HΨ.
  rewrite HΨ, <- app_assoc in HC; cbn [List.app] in HC.
  pose proof (rel_ctx_wf_app_r _ _ HC) as HC1.
  pose proof (rel_ctx_wf_tail HC1) as HC0.
  destruct (rel_ctx_wf_tm_inv _ _ _ _ HC1 Hetm) as [_ HM].
  pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn in Hn'.
  pose proof (fill_gsub _ _ _ Hn' Hf HC0 Hsc') as Hg.
  split; [ exists Srt; split; [ exact HSrt |] | exact (rel_exp_under_ctx_gsub Hg HM) ].
  pose proof (rel_exp_under_ctx_gsub Hg HA) as H0.
  destruct (entry_relevance E); cbn [relevance_sort] in H0 |- *;
    [ rewrite (type_sort_sub _ _ (relevant_sort_type_sort _ HSrt)) in H0 | rewrite (type_sort_sub _ _ type_sort_prop) in H0 ];
    exact H0.
Qed.

(** ** The Term Members of Valid Units *)

Lemma valid_unit_mem_all :
  (forall Γ K, valid_unit Γ K -> forall x R A, mdenote Θm Ξm Γ (me_mem K x) R -> mdesc_type R = Some A ->
     valid_mem Γ K x A (mdesc_reduct R) /\ valid_member_type Γ A (mdesc_relevance R)) /\
  (forall Γ H, valid_modexp Γ H -> forall x R A, mdenote Θm Ξm Γ (me_mem H x) R -> mdesc_type R = Some A ->
     valid_mem Γ H x A (mdesc_reduct R) /\ valid_member_type Γ A (mdesc_relevance R)).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs x R A Hm Ht.
    eapply filed_mem; first [ exact Hgm | exact Hgf | exact Hgl | exact HΓ | exact Hs | exact (wf_me_apps_args_scoped _ _ _ _ _ Hw)
                            | exact Hm | exact Ht ].
  - (* a body *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΔr HΓ HC Hsv Hsl IHsl Hs Hsx HK Hopv Hops IHops x R A Hm Ht.
    destruct (body_mem_desc _ _ _ _ _ _ _ Hx Hm Ht) as (Φ' & E & A0 & M0 & σ & Hp & HEt & Hf & -> & -> & ->).
    pose proof (rel_ctx_wf_app_r _ _ HC) as HΔΓ.
    pose proof (body_xp_result_noopen _ _ _ _ _ Hx) as Hno.
    pose proof (gm_noopen_nopens _ Hno) as Hn.
    pose proof (body_xp_scoped_of_wf _ _ _ _ _ _ Hw Hx) as Hsc.
    destruct (body_def_valid _ _ _ _ _ _ _ _ Hn HC Hsv Hsc Hp HEt Hf) as ((Srt & HSrt & HAσ) & HMσ).
    destruct HΔr as [lp HΔr].
    destruct (entry_relevance E) eqn:Hrel; cbn [relevance_sort valid_member_type] in HAσ |- *.
    2:{ (* a definition tagged a proposition: a proof, nothing asked of its value *)
      destruct (valid_exp_under_ctx_ctx_pi_at propositional _ _ _ 0 HΔ HΔΓ HAσ) as [j HP]; cbn [relevance_sort] in HP.
      split; [| exact HP ].
      apply valid_mem_of_prop; [ exact HP | intros M' [= <-]; exact (valid_exp_under_ctx_ctx_fn propositional _ _ _ _ 0 HΔ HΔΓ HAσ HMσ) |].
      intros RΓ HRΓ ρ Hρ; destruct (rel_modexp_at _ _ _ _ _ HK HRΓ _ _ Hρ) as (k & k' & Hk & Hk' & Hkk); exists k'; exact Hk'. }
    destruct (rel_param_typed_of_sort _ _ _ HSrt HAσ) as [kA HAp].
    pose proof (rel_param_typed_type _ _ _ HAp) as HAt.
    pose proof (rel_type_relevant_of_relevant_sort HSrt HAσ) as HAr.
    destruct (rel_type_ctx_pi _ _ _ _ _ HΔ HΔΓ HΔr HAt HAr) as [HPt HPr].
    split; [| split; [ eexists; exact HPt | exact HPr ] ].
    constructor; [ eexists; exact HPt | intros M' [= <-]; exact (rel_exp_ctx_fn _ _ _ _ _ _ HΔ HΔΓ HΔr HAt HAr HMσ) |].
    intros RΓ HRΓ ρ Hρ.
    destruct (rel_modexp_at _ _ _ _ _ HK HRΓ _ _ Hρ) as (k & k' & Hk & Hk' & Hkk).
    pose proof (functional_eval_modexp _ _ _ _ Hk' Hk) as ->.
    apply eval_me_lit_iff in Hk.
    destruct (unit_walk Δ Γ (md_body sm_open Φ) x A0[σ] (Some M0[σ]) RΓ lp kA HΔ HΔr HΔΓ HAt HAr
                ltac:(intros M1 HM1; injection HM1 as <-; exact HMσ)
                ltac:(intros R' HR' ρ' Hρ' k0 Hk0; inversion Hk0; subst;
                      rewrite <- (body_xp_expand _ _ _ _ _ Hx);
                      destruct (body_base _ _ _ _ _ _ _ _ Hno Hsx HC Hsv Hsc Hp HEt Hrel Hf _ HR' _ Hρ' sm_open)
                        as (a & i' & Ra & Ha & HRa & Hm' & m & r & Hm0 & Hr & Hmr);
                      exists a, i', Ra; repeat split; try assumption; intros M1 [= <-]; exists m, r; repeat split; assumption)
                HRΓ _ Hρ _ Hk Hkk)
      as (a & i' & Ra & Ha & HRa & Hmt & Hred).
    apply mk_valid_mem_at with (valid_mem_at_mod := k) (valid_mem_at_typ := a) (valid_mem_at_lvl := i') (valid_mem_at_rel := Ra);
      [ exact Hk' | exact Ha | exact HRa | intros _; exact Hmt |].
    intros _ M' [= <-]; destruct (Hred _ eq_refl) as (m & r & Hm0 & Hr & Hmr).
    exact (mk_rel_mem_reduct _ _ _ _ _ m r Hm0 Hr Hmr).
  - (* an alias *)
    intros Γ Δ E Hw HΔ HΔr HΓ HΔΓ HK HE Hsmt IHE x R A Hm Ht.
    (* the target's member, its δ-reduct, if any, or the filed member it
       is read as over the parameters *)
    assert (Hk : exists r' A' om', A = ctx_pi_at r' Δ A' /\ mdesc_reduct R = option_map (ctx_fn Δ) om' /\ mdesc_relevance R = r' /\
                   valid_mem (Δ ++ Γ) E x A' om' /\ valid_member_type (Δ ++ Γ) A' r').
    { pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf; destruct Hf as [_ _ _ HwΔΓ _ _ _ _ _ _].
      destruct (alias_mem_desc _ _ _ _ _ _ HwΔΓ Hm Ht) as (R' & Hm' & [-> | (r0 & A0 & RE & p & T & Φ & -> & HmE & HmdE & ->)]).
      - destruct (mdesc_type_up_inv _ _ _ Ht) as (A' & Ht' & ->).
        exists (mdesc_relevance R'), A', (mdesc_reduct R').
        split; [ reflexivity | split; [ apply mdesc_reduct_up | split; [ apply mdesc_relevance_up | exact (IHE _ _ _ Hm' Ht') ] ] ].
      - cbn in Ht; injection Ht as <-.
        destruct (IHE _ _ _ Hm' eq_refl) as [HvE HsE].
        exists r0, A0, (Some (a_mem (qname_mod p) x)); split; [ reflexivity | split; [ reflexivity | split; [ reflexivity |] ] ].
        exact (conj (valid_mem_bare_name _ _ _ _ _ _ _ _ Hsmt HmE HmdE HvE) HsE). }
    destruct Hk as (r' & A' & om' & -> & -> & HrR & [HA0' HM' HS'] & HA').
    rewrite HrR.
    destruct HΔr as [lp HΔr].
    destruct r'; cbn [valid_member_type] in HA' |- *.
    2:{ (* a proof member: nothing asked of its value *)
      destruct (valid_exp_under_ctx_ctx_pi_at propositional _ _ _ 0 HΔ HΔΓ HA') as [j HP]; cbn [relevance_sort] in HP.
      split; [| exact HP ].
      apply valid_mem_of_prop; [ exact HP | intros M Hom; destruct om' as [M' |]; cbn in Hom; [ injection Hom as <- | discriminate ];
                                            exact (valid_exp_under_ctx_ctx_fn propositional _ _ _ _ 0 HΔ HΔΓ HA' (HM' _ eq_refl)) |].
      intros RΓ HRΓ ρ Hρ; destruct (rel_modexp_at _ _ _ _ _ HK HRΓ _ _ Hρ) as (k & k' & Hk & Hk' & Hkk); exists k'; exact Hk'. }
    destruct HA' as [[kA HAt] HAr].
    destruct (rel_type_ctx_pi _ _ _ _ _ HΔ HΔΓ HΔr HAt HAr) as [HPt HPr].
    split; [| split; [ eexists; exact HPt | exact HPr ] ].
    constructor; [ eexists; exact HPt
                 | intros M Hom; destruct om' as [M' |]; cbn in Hom; [ injection Hom as <- | discriminate ];
                   exact (rel_exp_ctx_fn _ _ _ _ _ _ HΔ HΔΓ HΔr HAt HAr (HM' _ eq_refl)) |].
    intros RΓ HRΓ ρ Hρ.
    destruct (rel_modexp_at _ _ _ _ _ HK HRΓ _ _ Hρ) as (k & k' & Hk & Hk' & Hkk).
    pose proof (functional_eval_modexp _ _ _ _ Hk' Hk) as ->.
    apply eval_me_lit_iff in Hk.
    destruct (unit_walk Δ Γ (md_alias E) x A' om' RΓ lp kA HΔ HΔr HΔΓ HAt HAr HM'
                ltac:(intros R0 HR0 ρ0 Hρ0 k0 Hk0; inversion Hk0; subst; try (cbn in *; lia);
                      destruct (HS' _ HR0 _ Hρ0) as [k1 a i' Ra Hk1 Ha HRa Hm1 Hred1];
                      destruct (HAr _ HR0 _ _ Hρ0) as (a0 & Ea0 & Hra);
                      pose proof (functional_eval_exp _ _ _ _ Ha Ea0) as Eaa; subst a0;
                      specialize (Hm1 Hra); specialize (Hred1 Hra);
                      match goal with Hk2 : ⟦ E ⟧ᵐ _ ⍮ _ ⍮ ρ0 ↘ k0 |- _ => pose proof (functional_eval_modexp _ _ _ _ Hk1 Hk2) as -> end;
                      exists a, i', Ra; repeat split; try assumption;
                      intros M0 HM0; destruct (Hred1 _ HM0) as [m r Hm2 Hr2 Hmr2]; exists m, r; repeat split; assumption)
                HRΓ _ Hρ _ Hk Hkk)
      as (a & i' & Ra & Ha & HRa & Hmt & Hred).
    apply mk_valid_mem_at with (valid_mem_at_mod := k) (valid_mem_at_typ := a) (valid_mem_at_lvl := i') (valid_mem_at_rel := Ra);
      [ exact Hk' | exact Ha | exact HRa | intros _; exact Hmt |].
    intros _ M Hom; destruct om' as [M' |]; cbn in Hom; [ injection Hom as <- | discriminate ].
    destruct (Hred _ eq_refl) as (m & r & Hm0 & Hr & Hmr).
    exact (mk_rel_mem_reduct _ _ _ _ _ m r Hm0 Hr Hmr).
  - (* a module expression equal to a valid unit *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK x R' A Hm Ht.
    inversion Hm as [? ? ? ? ? _ _ | ? ? ? pq k D ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd He Hed Hr
                    | ? ? ? Rr ? ? Hq Hk]; subst;
      [ cbn in Ht; discriminate | | |].
    3:{ (* the open frame of a record type's module under [H]: likewise *)
      cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
      change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hk.
      destruct (gs_find_record_tele _ _ _ Hk) as (? & ? & Ht0).
      destruct (frame_parent _ _ Hgm _ _ _ _ Ht0) as (Tq & Φq & Hfq & _).
      assert (Hgl : gc_loc Θm Ξm mq = Some (Tq, Φq)) by (unfold gc_loc; rewrite Hfq; reflexivity).
      assert (Hs : valid_args Γ Tq nil)
        by (apply (mk_valid_args _ _ _ Tq nil); [ rewrite app_nil_r; reflexivity | reflexivity | constructor | exact I
                                                 | intros k0 N0 A0 HN0; destruct k0; discriminate
                                                 | intros k0 A0 HA0; destruct k0; discriminate ]).
      rewrite (mod_qname_inv _ _ Hq0) in Hm |- *.
      change (qname_mod mq) with (me_apps (qname_mod mq) nil) in Hm |- *.
      assert (HΓ : ⊨ Γ) by (eapply valid_unit_ctx_wf; exact HK).
      eapply filed_mem; first [ exact Hgm | exact Hgf | exact Hgl | exact HΓ | exact Hs | exact Hm | exact Ht | constructor ]. }
    { (* the open frame of a member's module under [H]: [H] names a frame,
         a filed module at no argument *)
      cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
      change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hk.
      destruct (gs_find_ind_tele _ _ _ Hk) as (? & ? & Ht0).
      destruct (frame_parent _ _ Hgm _ _ _ _ Ht0) as (Tq & Φq & Hfq & _).
      assert (Hgl : gc_loc Θm Ξm mq = Some (Tq, Φq)) by (unfold gc_loc; rewrite Hfq; reflexivity).
      assert (Hs : valid_args Γ Tq nil)
        by (apply (mk_valid_args _ _ _ Tq nil); [ rewrite app_nil_r; reflexivity | reflexivity | constructor | exact I
                                                 | intros k0 N0 A0 HN0; destruct k0; discriminate
                                                 | intros k0 A0 HA0; destruct k0; discriminate ]).
      rewrite (mod_qname_inv _ _ Hq0) in Hm |- *.
      change (qname_mod mq) with (me_apps (qname_mod mq) nil) in Hm |- *.
      assert (HΓ : ⊨ Γ) by (eapply valid_unit_ctx_wf; exact HK).
      eapply filed_mem; first [ exact Hgm | exact Hgf | exact Hgl | exact HΓ | exact Hs | exact Hm | exact Ht | constructor ]. }
    pose proof (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm0 _ HmH) as ->.
    rewrite HmodH in Hmd; injection Hmd as <-.
    assert (HmKx : mdenote Θm Ξm Γ (me_mem K x) R') by (eapply mdenote_mem; [ exact HmK | exact HmodK | exact He | exact Hed | exact Hr ]).
    destruct (IHK _ _ _ HmKx Ht) as [HvK HsK].
    exact (conj (valid_mem_transport _ _ _ _ _ _ HHK HvK) HsK).
Qed.

End Fixed_GCtx.
