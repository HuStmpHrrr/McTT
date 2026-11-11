(** * The Members of Glued Module Values

    A term member of a module expression whose value is glued
    ([glu_dmod]) is glued at its type, at every glued environment, at any
    type glued at the value of the member's type.  The member is glued at
    its own type at the start: a saturated body's member at its entry's
    type ([glu_body_member]), a saturated global module's at its stored
    type over the module's telescope ([glu_def_over_tele]).  The type it
    is wanted at is glued at a related value, so the two types are equal
    ([glu_elem_to_target]).  A value lacking a parameter has a member
    closure, glued at a [Π] by its values at glued arguments, the members
    of the applications ([wf_exp_eq_mem_app]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System SystemOpt.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound Presup.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Modules Require Import Values.
From Mctt.Core.Completeness.Modules Require Filed Mem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation VariableCases ModuleValues Selection MemberApp.
From Mctt.Core.Soundness.Inductives Require Import Args.
From Mctt.Core.Soundness.Global Require Import GlobalValues.
Import Domain_Notations Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** A sort of types is the sort of a kind next to a universe. *)
Lemma type_sort_abs_kind_inv : forall S, type_sort S -> exists κ (l : nat), S = abs_kind_sort κ Typeω@l.
Proof. intros S []; [ exists ak_relevant, i | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity. Qed.

(** A type glued at a value, of a sort of types, is no type of levels'
    value. *)
Lemma glu_typ_not_level_sort : forall {i : nat} {a P El Γ A S},
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> Γ ⊢ A ® P -> type_sort S -> Γ ⊢ A : S -> not_level_sort a.
Proof.
  intros * Hg HA HS HAt.
  destruct (type_sort_abs_kind_inv _ HS) as (κ & l & ->).
  exact (proj2 (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hg HA HAt)).
Qed.

(** ** The types of members read at arguments *)

(** A term's type at an argument does not depend on its body or its kind:
    it is read off the type's [Π] ([pi_view]). *)
Lemma mdesc_at_term_type : forall r A om N R1, mdesc_at (mdesc_term r A om) N = Some R1 ->
    forall r', exists B, mdesc_at (mdesc_term r' A None) N = Some (mdesc_term r' B None) /\ mdesc_type R1 = Some B.
Proof.
  intros * H r'; cbn [mdesc_at] in H |- *; destruct (pi_view A) as [[X C] |]; [| discriminate ].
  destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection H as <-; eexists; split; reflexivity.
Qed.

Lemma mdesc_term_part_at_term_type : forall r A om N R1, mdesc_term_part_at (mdesc_term r A om) N = Some R1 ->
    forall r', exists B, mdesc_at (mdesc_term r' A None) N = Some (mdesc_term r' B None) /\ mdesc_type R1 = Some B.
Proof.
  intros * H r'; destruct om as [M |]; [| exact (mdesc_at_term_type _ _ _ _ _ H r') ].
  cbn [mdesc_term_part_at mdesc_at] in H |- *; destruct (pi_view A) as [[X C] |]; [| discriminate ].
  destruct (fn_view M); [| destruct (app_const M) ]; try discriminate; injection H as <-; eexists; split; reflexivity.
Qed.

Lemma mdesc_ats_term_type : forall Ns r A om R1, mdesc_ats (mdesc_term r A om) Ns = Some R1 ->
    forall r', exists B, mdesc_ats (mdesc_term r' A None) Ns = Some (mdesc_term r' B None) /\ mdesc_type R1 = Some B.
Proof.
  induction Ns as [| N Ns IH]; intros * H r'; cbn [mdesc_ats] in H |- *; [ injection H as <-; eexists; split; reflexivity |].
  destruct (mdesc_at (mdesc_term r A om) N) as [R0 |] eqn:E; [| discriminate ].
  destruct (mdesc_at_term_type _ _ _ _ _ E r') as (B0 & E0 & HB0); rewrite E0.
  assert (exists A0 om0, R0 = mdesc_term r A0 om0) as (A0 & om0 & ->)
    by (cbn [mdesc_at] in E; destruct (pi_view A) as [[? ?] |]; [ destruct om as [M |]; [ destruct (fn_view M) |] |];
        try discriminate; injection E as <-; eauto).
  cbn in HB0; injection HB0 as ->; exact (IH _ _ _ _ H r').
Qed.

Lemma mdesc_term_part_ats_term_type : forall Ns r A om R1, mdesc_term_part_ats (mdesc_term r A om) Ns = Some R1 ->
    forall r', exists B, mdesc_ats (mdesc_term r' A None) Ns = Some (mdesc_term r' B None) /\ mdesc_type R1 = Some B.
Proof.
  induction Ns as [| N Ns IH]; intros * H r'; cbn [mdesc_term_part_ats mdesc_ats] in H |- *;
    [ injection H as <-; eexists; split; reflexivity |].
  destruct (mdesc_term_part_at (mdesc_term r A om) N) as [R0 |] eqn:E; [| discriminate ].
  destruct (mdesc_term_part_at_term_type _ _ _ _ _ E r') as (B0 & E0 & HB0); rewrite E0.
  destruct (Filed.mdesc_term_part_at_term _ _ _ _ _ E) as (A0 & om0 & ->).
  cbn in HB0; injection HB0 as ->; exact (IH _ _ _ _ H r').
Qed.

(** A stored entry's description, of a [Π] over a telescope of assumptions,
    read at as many arguments: of the codomain at them. *)
Lemma mdesc_ats_read_type_full : forall Ns T κ A0 RE R1, all_assumptions T -> List.length Ns = List.length T ->
    mdesc_type RE = Some (ctx_pi_at κ T A0) -> (forall Θd A M Rm, RE = mdesc_dm Θd A M Rm -> Θd = nil) ->
    mdesc_ats_read RE Ns = Some R1 -> mdesc_type R1 = Some A0[sb_of_list Id Ns].
Proof.
  intros * HT Hl Ht Hdm Ha.
  assert (Hfull : forall B, mdesc_ats (mdesc_term κ (ctx_pi_at κ T A0) None) Ns = Some (mdesc_term κ B None) ->
                  B = A0[sb_of_list Id Ns]).
  { intros B HB.
    change (mdesc_term κ (ctx_pi_at κ T A0) None) with (mdesc_up (nil ++ T) (mdesc_term κ A0 None)) in HB.
    rewrite (mdesc_ats_up_term_none Ns T nil κ A0 HT ltac:(lia)) in HB; injection HB as <-; reflexivity. }
  destruct RE as [r A om | | | Θd A M Rm]; cbn in Ht; try discriminate.
  - injection Ht as ->.
    rewrite mdesc_ats_read_other in Ha by (intros; discriminate).
    destruct (mdesc_ats_term_type _ _ _ _ _ Ha κ) as (B & HB & ->).
    rewrite (Hfull B HB); reflexivity.
  - pose proof (Hdm _ _ _ _ eq_refl) as ->; cbn in Ht; injection Ht as ->.
    cbn [mdesc_ats_read] in Ha.
    destruct (mdesc_term_part_ats (mdesc_term ak_relevant (ctx_pi_at κ T A0) (Some M)) Ns) as [[r1 B [M' |] | | |] |] eqn:Htp;
      try discriminate.
    destruct (mdesc_ats Rm Ns) as [Rm' |]; [ injection Ha as <- | discriminate ].
    destruct (mdesc_term_part_ats_term_type _ _ _ _ _ Htp κ) as (B' & HB' & HtB); cbn in HtB; injection HtB as ->.
    rewrite (Hfull B' HB'); reflexivity.
Qed.

(** ** Saturated bodies *)

(** The member of a saturated body value glued as [H], at a type value of
    an evaluated kind related to the member types of the value
    ([dmod_mem_type_rel]), is glued as the member at any type [T] glued
    there, its own type equal to [T]: glued at the entry's own type value
    through the identity factorization ([glu_body_member]), moved to the
    related one ([glu_elem_to_target]).  A proof is no such member: its
    type is a proposition ([per_body_proof_kind]). *)
Lemma glu_mem_body_value_at : forall Δ σ Γ H sm Φ ρh x R A Srt m a2 (k : nat) P2 El2 T,
    glu_dmod Δ σ Γ H (dm_local nil (md_body sm Φ) ρh) ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A -> type_sort Srt -> Γ ⊢ A : Srt ->
    dm_local nil (md_body sm Φ) ρh ·ₜ x gc_deps ⍮ gc_stack ↘ m ->
    per_dmod (dm_local nil (md_body sm Φ) ρh) (dm_local nil (md_body sm Φ) ρh) ->
    dmod_mem_type_rel (dm_local nil (md_body sm Φ) ρh) x a2 ->
    evaluated_kind (domain_kind a2) ->
    DG a2 ∈ glu_univ_elem k ↘ P2 ↘ El2 -> Δ ⊢ T ® P2 ->
    (exists l : nat, Δ ⊢ A[σ] ≈ T : abs_kind_sort (domain_kind a2) Typeω@l) /\ Δ ⊢ (a_mem H x)[σ] : T ® m ∈ El2.
Proof.
  intros * Hg Hm HA HS HAt Hsel Hhh Hty Hev Hg2 HT.
  inversion Hg; subst;
    [| exfalso; match goal with Hn : next_param (dm_local nil _ _) _ |- _ => inversion Hn; subst end;
       match goal with Hl : _ ++ _ :: nil = nil |- _ => destruct Δ0; discriminate end ].
  match goal with Hσ0 : Δ ⊢ˢ σ : Γ, Hmem0 : forall (x0 : String.string) _ _ _ _ _, _ -> _ -> _ -> _ -> exists _ _, glu_body_member _ _ _ _ _ _ _ _ _ _ |- _ =>
    rename Hσ0 into Hσ, Hmem0 into Hmem end.
  inversion Hhh; subst;
    [| exfalso; match goal with Hn : next_param (dm_local nil _ _) _ |- _ => inversion Hn; subst end;
       match goal with Hl : _ ++ _ :: nil = nil |- _ => destruct Δ0; discriminate end ].
  match goal with Hb : per_body ρh Φ ρh Φ |- _ => rename Hb into Hbb end.
  pose proof (proj1 (KindsPER.per_body_noopen _ _ _ _ Hbb)) as Hno.
  inversion Hsel; subst.
  - match goal with Hl : 0 < length nil |- _ => inversion Hl end.
  - (** A definition of an evaluated kind *)
    destruct (Hmem _ _ _ _ _ _ H3 H4 H5 H8) as (a & m' & [Ea Em Hfield]).
    pose proof (functional_eval_exp _ _ _ _ Em H10) as ->.
    pose proof (dmod_mem_type_body sm Φ ρh x _ _ _ _ _ _ H3 H4 H8 Ea) as Hmt.
    destruct (Hty _ _ Hhh Hmt) as [j Hj].
    pose proof (wf_sub_cod _ _ _ _ _ Hσ) as HwΓ.
    assert (Hst : glu_sub_through Δ σ Γ Δ wk_id Γ Id σ).
    { constructor; [ apply kripke_id; exact (wf_sub_dom _ _ _ _ _ Hσ) | apply wf_sub_id; exact HwΓ | exact Hσ |].
      apply wf_sub_eq_of_sb_eq; [ exact (wf_sub_sb_wk Hσ (kripke_id _ (wf_sub_dom _ _ _ _ _ Hσ))) |].
      rewrite sb_compose_id_left; intros n; unfold sb_wk; destruct (σ n); cbn;
        [ reflexivity | rewrite exp_wk_id | rewrite modexp_wk_id | rewrite exp_wk_id, modexp_wk_id ]; reflexivity. }
    rewrite <- (modexp_sub_id H) in Hm.
    destruct (Hfield _ _ _ _ _ _ _ _ Hst Hm HA HS HAt) as (i & P & El & [Hga HAP HMm]).
    rewrite !modexp_sub_id in HMm.
    (** Its type is no type of levels' *)
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HAt Hσ) as HAσ.
    destruct (type_sort_abs_kind_inv _ HS) as (κS & lS & ->).
    rewrite abs_kind_sort_sub in HAσ; cbn [exp_sub] in HAσ.
    pose proof (proj2 (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hga HAP HAσ)) as Hnl.
    exact (glu_elem_to_target Hj Hga Hg2 Hnl HMm HT).
  - (** A proof: its type is a proposition, not of the evaluated kind of
        the member's type *)
    exfalso.
    match goal with Hp : gm_prefix_upto _ x = Some (gm_ext ?Φ1 x ?E), Ht : entry_tm ?E = Some _, Hk : entry_kind ?E = ak_propositional |- _ =>
      rename Hp into Hp0, Ht into Ht0, Hk into Hk0 end.
    destruct E as [b pv κ A1 [M1 |] | | | | ]; cbn in Ht0, Hk0; try discriminate; injection Ht0 as <- <-; subst κ.
    pose proof Hp0 as Hp'; rewrite (gm_expand_noopen _ Hno) in Hp'.
    destruct (per_body_proof_kind _ _ _ _ Hbb _ _ _ _ _ _ Hp') as (ρ1 & b0 & Hb1 & Eb0 & Kb0).
    destruct (Hty _ _ Hhh (dmod_mem_type_body _ _ _ _ _ _ _ _ _ _ Hp0 eq_refl Hb1 Eb0)) as [j [Rj Hj]].
    rewrite <- (per_univ_elem_kind _ _ _ _ Hj), Kb0 in Hev; inversion Hev.
Qed.

(** A type glued at its own value is equal to any type glued at a related
    value ([glu_univ_elem_per_univ_typ_escape], at an index above
    both). *)
Lemma glu_typ_to_target : forall {ie i : nat} {k : universe_index} {ae a Pe Ele P El Δ A T},
    Dom ae ≈ a ∈ per_univ k -> DG ae ∈ glu_univ_elem ie ↘ Pe ↘ Ele -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort ae -> Δ ⊢ A ® Pe -> Δ ⊢ T ® P ->
    exists l : nat, Δ ⊢ A ≈ T : abs_kind_sort (domain_kind a) Typeω@l.
Proof.
  intros * [R HR] Hge Hga Hnl HA HT.
  set (n := Nat.max (Nat.max ie i) (large_level k)).
  destruct (glu_univ_elem_cumu_ge (i := ie) (j := n) ltac:(unfold n; lia) Hge) as (Pn & Eln & Hgn).
  destruct (glu_univ_elem_cumu_ge (i := i) (j := n) ltac:(unfold n; lia) Hga) as (Pn' & Eln' & Hgn').
  pose proof (glu_univ_elem_typ_cumu_ge (i := ie) (j := n) ltac:(unfold n; lia) Hge Hgn HA) as HAn.
  pose proof (glu_univ_elem_typ_cumu_ge (i := i) (j := n) ltac:(unfold n; lia) Hga Hgn' HT) as HTn.
  assert (HRn : Dom ae ≈ a ∈ per_univ n)
    by (exists R; eapply per_univ_elem_cumu_universe_index; [ exact HR | apply universe_index_le_ul_max; unfold n; lia ]).
  pose proof (glu_univ_elem_per_univ_typ_escape HRn Hgn Hgn' Hnl HAn HTn) as HAT.
  rewrite (per_univ_elem_kind _ _ _ _ HR) in HAT.
  eexists; exact HAT.
Qed.

(** A chain of submodules, then a term member, is a chain ending in the
    term member. *)
Lemma eval_selmc_selt : forall h ch hc x r,
    h ·ₘ* ch gc_deps ⍮ gc_stack ↘ hc -> hc ·ₜ x gc_deps ⍮ gc_stack ↘ r -> h ·ₜ* (ch ++ x :: nil) gc_deps ⍮ gc_stack ↘ r.
Proof.
  intros * Hc; induction Hc; intros Hx; cbn [List.app]; [ constructor; exact Hx | econstructor; [ eassumption | auto ] ].
Qed.

(** The term member of a value lacking a parameter is a member closure,
    which, given an argument, is the member of the value given it
    ([eval_app_member]). *)
Lemma selt_appm_comm : forall h a, next_param h a -> forall x m, h ·ₜ x gc_deps ⍮ gc_stack ↘ m ->
    forall n hc r, $ᵐ| h & n | gc_deps ⍮ gc_stack ↘ hc -> hc ·ₜ x gc_deps ⍮ gc_stack ↘ r -> $| m & n | gc_deps ⍮ gc_stack ↘ r.
Proof.
  intros * Hnp; inversion Hnp; subst; intros * Hsel * Happ Hr.
  - (** A closure *)
    inversion Hsel; subst; try (destruct Δ; discriminate).
    econstructor; [ exact Happ | constructor; exact Hr ].
  - (** A global module past its arguments *)
    rename H into Hgl, H0 into Hn.
    assert (Hlt : List.length args < List.length T)
      by (pose proof (proj1 (List.nth_error_Some (List.rev T) (List.length args)) ltac:(rewrite Hn; discriminate)) as Hl';
          rewrite List.length_rev in Hl'; exact Hl').
    inversion Hsel; subst;
      try (match goal with Hs : module_saturated _ _ _ _ |- _ => pose proof (Hs _ _ Hgl); lia end);
      try (match goal with Hl' : gc_loc _ _ p = Some _, Hlen : List.length args = _ |- _ =>
             rewrite Hgl in Hl'; injection Hl' as <- <-; lia end).
    econstructor; [ exact Happ | constructor; exact Hr ].
  - (** A submodule closure: its base given the argument, selected again *)
    inversion Hsel; subst.
    inversion Happ; subst.
    econstructor; [ eassumption | apply eval_selmc_selt with (hc := hc); assumption ].
Qed.

(** An equation at a type is one at a type equal to it at a sort of
    types. *)
Lemma wf_exp_eq_conv_kind : forall Γ M M' A A' κ (l : nat),
    Γ ⊢ M ≈ M' : A -> Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@l -> Γ ⊢ M ≈ M' : A'.
Proof.
  intros * HM HA.
  eapply wf_exp_eq_subtyp'; [ exact HM |].
  eapply wf_subtyp_refl; [ exact (presup_exp_eq_right HA) | apply type_sort_abs_kind; constructor | exact HA ].
Qed.

End Fixed_GCtx.

(** ** Saturated global modules *)

Section Members.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  #[local] Instance GCm : GCtx := gc_mk Θ Ξ.
  Import Fixed_Notations.

  (** A member of a well-formed module expression at an environment of its
      context, in the PER model ([valid_unit_mem_all]): the module's value,
      the type's, and, at an evaluated kind, the member of every related
      value and its type related. *)
  Lemma mem_valid_at : forall Γ H x R A RΓ ρ,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A ->
      EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> valid_mem_at H x A (mdesc_reduct R) ρ.
  Proof.
    intros * HH Hm HA HRΓ Hρ.
    pose proof (valid_gctx_embedding_refl _ _ Hg) as Hv.
    destruct completeness_fundamental as (_ & _ & _ & _ & _ & _ & _ & Km).
    destruct (Km _ _ _ _ _ HH _ _ Hv) as [_ _ HvH _].
    destruct (proj2 (Mem.valid_unit_mem_all Θ Ξ Hg (valid_gctx_embedding_filed _ _ _ _ Hv)) _ _ HvH _ _ _ Hm HA)
      as [[_ _ Hvals] _].
    exact (Hvals _ HRΓ _ Hρ).
  Qed.

  (** A term member of a stored module read in some context is one read
      bare over no context, of the same type and kind: its entry denotes
      there too, its module part, if any, by the alias's validity
      ([syn_V]). *)
  Lemma bare_member_exists : forall p T Φ x Φ0 E0 Γ RE,
      gc_loc Θ Ξ p = Some (T, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E0) ->
      edenote Θ Ξ Γ (Some (qname_in p x)) (ge_read T E0) RE -> mdesc_type RE <> None ->
      exists R0, mdenote Θ Ξ ⋅ (me_mem (qname_mod p) x) R0 /\ mdesc_type R0 = mdesc_type RE /\ mdesc_kind R0 = mdesc_kind RE.
  Proof.
    intros * Hgl Hp Hed Ht.
    pose proof (gc_loc_loc _ _ _ _ _ Hgl) as Hl.
    destruct (filed_denote _ _ Hg _ _ _ ⋅ nil Hgl) as (S1 & HS1 & HS1m); cbn [me_apps] in HS1.
    assert (He : mdesc_entry (mdesc_closed nil p T Φ nil) x = Some (nil, ge_read T E0, reader_closed nil nil (a_mem (qname_mod p) x)))
      by (cbn; rewrite Hp; reflexivity).
    assert (HE0 : exists RE0, edenote Θ Ξ (nil ++ ⋅) (Some (qname_in p x)) (ge_read T E0) RE0 /\
                    mdesc_type RE0 = mdesc_type RE /\ mdesc_kind RE0 = mdesc_kind RE).
    { destruct E0 as [b pv r A oM | pv [Δ [sm Φy | Ea]] | pv pq k D Φ' | pv Ad Md [Δ [sm Φy | Ea]] | pv pr Rr Φ'];
        cbn [ge_read] in Hed |- *.
      - inversion Hed; subst; eexists; split; [ constructor | split; reflexivity ].
      - exfalso; destruct sm; inversion Hed; subst;
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm end;
          destruct RE; cbn in Hm, Ht; first [ contradiction | apply Ht; reflexivity ].
      - exfalso; inversion Hed; subst;
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm end;
          destruct RE; cbn in Hm, Ht; first [ contradiction | apply Ht; reflexivity ].
      - inversion Hed; subst; eexists; split; [ econstructor; eassumption | split; reflexivity ].
      - exfalso; inversion Hed.
      - (** A definition with a module part: its module part denotes over no
            context, by the alias's validity *)
        inversion Hed; subst.
        destruct (loc_valid _ _ _ _ _ (gctx_valid_syn _ _ Hg) Hl) as [_ HgV].
        destruct (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HgV Hp) as (HVm & _ & _).
        cbn in HVm; destruct HVm as (_ & HΔ & _ & _ & Hall).
        destruct (Hall ⋅ ltac:(rewrite List.app_nil_r; exact HΔ)) as [(R1 & HR1) Hok].
        destruct (Hok _ HR1) as (_ & (Rm1 & HRm1) & _).
        eexists; split; [ econstructor; econstructor; [ cbn [List.app]; exact HR1 | exact HRm1 ] | split; reflexivity ].
      - inversion Hed; subst; eexists; split; [ econstructor; eassumption | split; reflexivity ]. }
    destruct HE0 as (RE0 & Hed0 & Ht0 & Hk0).
    exists RE0; split; [| split; assumption ].
    assert (Hm : mdenote Θ Ξ ⋅ (me_mem (qname_mod p) x) (mdesc_up nil (mdesc_named nil nil (apps (a_mem (qname_mod p) x) nil) RE0)))
      by (eapply mdenote_mem; [ exact HS1 | exact HS1m | exact He | exact Hed0 | cbn [mdesc_read]; rewrite mdesc_ats_read_nil; reflexivity ]).
    rewrite mdesc_up_nil, mdesc_named_nil in Hm; exact Hm.
  Qed.

  (** A term member of a stored module, read bare over no context, is its
      stored entry, even when the module is an open frame: a path naming
      an entry is no open frame's own path ([gc_entry]), and an open frame
      has no entry yet of a name it is defining ([gc_unit_mem_parent]). *)
  Lemma bare_member_entry : forall p T Φ x Φ0 E0 R0,
      gc_loc Θ Ξ p = Some (T, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E0) ->
      mdenote Θ Ξ ⋅ (me_mem (qname_mod p) x) R0 ->
      edenote Θ Ξ (nil ++ ⋅) (Some (qname_in p x)) (ge_read T E0) R0.
  Proof.
    intros * Hgl Hp Hm0.
    pose proof (gc_loc_loc _ _ _ _ _ Hgl) as Hl.
    pose proof (loc_closed _ _ Hg _ _ _ Hl) as HU.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
    pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl x _) Hent) as HeE.
    assert (Hnt : forall U T0, gs_find_tele Ξ (qname_in p x) <> Some (U, nil, T0)).
    { intros U T0 Ht; unfold gc_entry, gc_entry_u in HeE; rewrite gs_find_tele_find, Ht in HeE; cbn in HeE.
      rewrite gm_entry_nil in HeE; discriminate. }
    pose proof (qname_mod_qname p) as Hpq.
    inversion Hm0 as [? ? pu ? ? Hq Hu | ? ? pu pq k D Mk Tm Φm Hq Hk _ _ | | | | ? ? ? R0' R0m Γy E rd RE ? Hm0' Hmd He Hed Hr
                     | ? ? pu Rr Tm Φm Hq Hk _]; subst.
    - (** A unit: the module is an open frame without the entry *)
      exfalso.
      destruct (gc_unit_mem_parent _ _ Hg _ _ _ _ Hu) as (mq & T' & Φ' & Hmq & Hf & Hfr).
      rewrite Hpq in Hmq; injection Hmq as <-.
      unfold gc_loc in Hgl; rewrite Hf in Hgl; injection Hgl as <- <-.
      exact (Hfr (gm_prefix_upto_in_names _ _ _ Hp)).
    - exfalso; cbn in Hq; rewrite Hpq in Hq; injection Hq as <-.
      destruct (gs_find_ind_tele _ _ _ Hk) as (U & T0 & Ht); exact (Hnt _ _ Ht).
    - (** The entry of the stored module, at no argument *)
      destruct (filed_denote _ _ Hg _ _ _ ⋅ nil Hgl) as (S1 & HS1 & HS1m); cbn [me_apps] in HS1.
      rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0' _ HS1), HS1m in Hmd; injection Hmd as <-.
      destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU He) as (-> & _ & ->).
      cbn in He; rewrite Hp in He; injection He as <-.
      cbn [mdesc_read] in Hr; rewrite mdesc_ats_read_nil in Hr; cbn [option_map] in Hr; injection Hr as <-.
      rewrite mdesc_up_nil, mdesc_named_nil; exact Hed.
    - exfalso; cbn in Hq; rewrite Hpq in Hq; injection Hq as <-.
      destruct (gs_find_record_tele _ _ _ Hk) as (U & T0 & Ht); exact (Hnt _ _ Ht).
  Qed.

  (** The member of a module expression whose module part is a saturated
      stored module at arguments glued as the value's, at any type [T]
      glued at a type value related to the member types of the values
      related to it, its own type equal to [T]: the stored member applied
      ([glu_global_apps_at]), which the member is ([mem_closed_part]); its
      own type, the stored type at the arguments
      ([mdesc_ats_read_type_full]), is glued over the module's telescope
      there ([glu_def_over_tele]), at the member type of the value, so it
      is [T] ([glu_typ_to_target]).  The stored module is no open frame,
      so that its member read bare is its entry. *)
  Lemma glu_global_member_value_at : forall p T Φ x R0 As A0 (j : nat) Γ1 H1 RH Ns1 R A' Δ σ1 args m a (i : nat) P El Tin,
      gc_loc Θ Ξ p = Some (T, Φ) -> List.length args = List.length T ->
      mdenote Θ Ξ ⋅ (me_mem (qname_mod p) x) R0 -> mdesc_type R0 = Some As -> evaluated_kind (mdesc_kind R0) ->
      ⋅ ⊩ a_mem (qname_mod p) x : As ->
      As = ctx_pi_at (mdesc_kind R0) T A0 -> T ⊩ A0 : abs_kind_sort (mdesc_kind R0) Typeω@j ->
      Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H1 ≈ H1 -> names_no_frame H1 -> mdenote Θ Ξ Γ1 H1 RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
      mdenote Θ Ξ Γ1 (me_mem H1 x) R -> mdesc_type R = Some A' ->
      Δ ⊢ˢ σ1 : Γ1 ->
      glu_tele_args Δ (List.rev T) nil nil (List.map (fun N => N[σ1]) Ns1) args ->
      dm_global p args ·ₜ x Θ ⍮ Ξ ↘ m ->
      (forall h b, per_dmod h (dm_global p args) -> dmod_mem_type h x b -> exists j, Dom b ≈ a ∈ per_univ j) ->
      not_level_sort a -> DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ Tin ® P ->
      (exists l : nat, Δ ⊢ A'[σ1] ≈ Tin : abs_kind_sort (domain_kind a) Typeω@l) /\ Δ ⊢ (a_mem H1 x)[σ1] : Tin ® m ∈ El.
  Proof.
    intros * Hgl Hlen Hm0 Ht0 Hk HGa -> HA0 HH1 Hq1 HmH HRH Hm Ht Hσ1 Hargs Hsel Hrel Hnl Hga HTin.
    pose proof (wf_gstack_closed _ _ Hg) as Hc.
    pose proof (wf_sub_dom _ _ _ _ _ Hσ1) as HΔ.
    destruct (glu_global_apps_at _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgl Hlen Hm0 Ht0 Hk HGa HΔ Hargs Hsel Hrel Hnl Hga HTin)
      as [Hper Happs].
    pose proof (gc_loc_loc _ _ _ _ _ Hgl) as Hl.
    pose proof (loc_closed _ _ Hg _ _ _ Hl) as HU.
    (** The member's entry, read at the arguments *)
    apply (@mdenote_mem_no_frame GCm _ _ _ _ _ Hg Hq1 Hm); intros R0' R0m Γy E rd RE Hm0' HR0m' He Hed Hrd.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0' _ HmH), HRH in HR0m'; injection HR0m' as <-.
    destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU He) as (-> & HsE & ->).
    cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read RE Ns1) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
    rewrite mdesc_up_nil, mdesc_type_named in Ht.
    (** The member read bare is the same entry, at no argument *)
    pose proof He as He1; cbn in He1.
    destruct (gm_prefix_upto Φ x) as [[| Φ0 z E0 | ] |] eqn:Hp; try discriminate.
    injection He1 as <-.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & Heq & _); injection Heq as <- -> <-.
    pose proof (bare_member_entry _ _ _ _ _ _ _ Hgl Hp Hm0) as Hed0.
    assert (Hed0' : edenote Θ Ξ (nil ++ Γ1) (mdesc_entry_path (mdesc_closed nil p T Φ Ns1) x) (ge_read T E0) R0).
    { apply (edenote_closed_move _ _ _ _ _ _ _ Id Hc HsE Hed0); intros y U Hy; inversion Hy. }
    rewrite (proj1 (proj2 (proj2 (mdenote_functional_all _ _ Hg))) _ _ _ _ Hed _ Hed0') in Hats.
    rewrite ?mdesc_up_nil, ?mdesc_named_nil in *.
    set (RE0 := R0) in *.
    (** Its type at the arguments: the stored type over the telescope, at
        them *)
    pose proof (valid_filed_mod_tele_all_assumptions _ _ _ _ _
                  (valid_gctx_embedding_filed _ _ _ _ (valid_gctx_embedding_refl _ _ Hg) _ _ _ Hgl)) as HTa.
    assert (HlN : List.length Ns1 = List.length T)
      by (rewrite <- (List.length_map (fun N => N[σ1]) Ns1), (glu_tele_args_length _ _ _ _ _ _ Hargs), Hlen; reflexivity).
    assert (Hdm : forall Θd A M Rm, RE0 = mdesc_dm Θd A M Rm -> Θd = nil).
    { intros * ->; inversion Hed0; subst; try reflexivity;
        match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm; cbn in Hmm; contradiction end. }
    pose proof (mdesc_ats_read_type_full _ _ _ _ _ _ HTa HlN Ht0 Hdm Hats) as HtA; rewrite Ht in HtA; injection HtA as ->.
    (** Glued over the telescope at the arguments *)
    destruct (glu_rel_exp_sort_typ HA0 (sort_kind_abs_kind_sort _ j)) as (SbA & iA & HSbA & HA0w & HAg).
    destruct HGa as [SbN HSbN kN _].
    assert (Hnil : Δ ⊢ˢ sb_of_list sb_closed_base nil ® nil ∈ SbN)
      by (inversion HSbN as [Sb' ESb _ | | | | ]; subst; apply ESb; apply wf_sub_nil'; exact HΔ).
    assert (HSbA' : EG List.rev (List.rev T) ++ ⋅ ∈ glu_ctx_env ↘ SbA) by (rewrite List.rev_involutive, List.app_nil_r; exact HSbA).
    pose proof (glu_tele_args_env _ _ _ _ _ _ Hargs ⋅ _ (List.Forall_rev HTa)
                  ltac:(rewrite List.length_map, List.length_rev; exact HlN) HSbN Hnil _ HSbA') as Hσ'.
    destruct (HAg _ _ _ Hσ') as [ae Pe Ele Eae Hgae HAe].
    (** Its value is the member type of the value, so related to [a] *)
    assert (Hmt : dmod_mem_type (dm_global p args) x ae)
      by (eapply dmod_mem_type_global; [ exact Hgl | exact Hlen | exact Hm0 | exact Ht0 | exact Eae ]).
    destruct (Hrel _ _ Hper Hmt) as [k Hk'].
    destruct Hk' as [Rk HRk].
    pose proof (proj2 (per_univ_elem_not_level_sort_iff _ _ _ _ HRk) Hnl) as Hnle.
    destruct (glu_typ_to_target (ex_intro _ Rk HRk) Hgae Hga Hnle HAe HTin) as [l Heq].
    (** The member's own type is the stored type at the arguments *)
    pose proof (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HA0w)) as [HsA0 _].
    rewrite <- HlN in HsA0.
    cbn [List.app] in Heq; rewrite <- (tele_type_inst_sub _ _ σ1 HsA0) in Heq.
    split; [ exists l; exact Heq |].
    (** The member is the stored member applied *)
    pose proof (mem_closed_part _ _ _ _ _ _ _ _ _ _ _ _ _ HH1 HmH HRH Hm (eq_trans (mdesc_type_named _ _ _ _) Ht)) as Heq0;
      cbn [ctx_fn] in Heq0.
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Heq0 Hσ1) as Heq1.
    rewrite apps_exp_sub in Heq1; cbn [exp_sub] in Heq1; rewrite (mod_qname_sub _ _ _ (qname_mod_qname p)) in Heq1.
    pose proof (wf_exp_eq_conv_kind _ _ _ _ _ _ _ Heq1 Heq) as Heq2.
    exact (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hga _ _ _ _ _ Happs (wf_exp_eq_sym _ _ _ _ _ _ Heq2)).
  Qed.

End Members.
