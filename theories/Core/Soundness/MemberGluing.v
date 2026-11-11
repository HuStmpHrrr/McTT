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
From Mctt.Core.Soundness Require UniverseCases.
From Mctt.Core.Completeness.Consequences Require AnnotatedUpto.
From Mctt.Core.Soundness.Global Require Import GlobalValues.
From Mctt.Core.Soundness Require Import UnitDeep.
Import Domain_Notations Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The child entries of a stored module, as it grows *)

(** The child [y] of a body is read off its entry [y]: as the body with
    that entry alone. *)
Lemma gm_child_of_entry : forall Φ y E T, gm_entry Φ (y :: nil) = Some E ->
    gm_submodule T Φ y nil = gm_submodule T (gm_ext gm_nil y E) y nil /\
    gm_subbody T Φ y nil = gm_subbody T (gm_ext gm_nil y E) y nil.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH H its Φg _]; intros * He; cbn in He |- *; [ discriminate | | exact (IH _ _ _ He) ].
  destruct (String.eqb y z) eqn:Eyz; [| exact (IH _ _ _ He) ].
  apply String.eqb_eq in Eyz; subst z; injection He as ->; rewrite String.eqb_refl; split; reflexivity.
Qed.

(** An entry grown keeps the child it stands for: the same module, and a
    body over the same telescope. *)
Lemma gm_child_grows : forall y E1 E2 T, entry_grows E1 E2 ->
    gm_submodule T (gm_ext gm_nil y E1) y nil = gm_submodule T (gm_ext gm_nil y E2) y nil /\
    (forall T' Φ2, gm_subbody T (gm_ext gm_nil y E2) y nil = Some (T', Φ2) ->
       exists Φ1, gm_subbody T (gm_ext gm_nil y E1) y nil = Some (T', Φ1)).
Proof.
  intros * Hgr; cbn [gm_submodule gm_subbody]; rewrite String.eqb_refl.
  destruct E1 as [b pv r A oM | pv [Δ [sm Φ | E]] | pv pq k D Φ | pv A M [Δ [sm Φ | E]] | pv p R Φ];
    destruct E2 as [b' pv' r' A' oM' | pv' [Δ' [sm' Φ' | E']] | pv' pq' k' D' Φ' | pv' A' M' [Δ' [sm' Φ' | E']] | pv' p' R' Φ'];
    cbn in Hgr; try discriminate;
    first [ injection Hgr; intros; subst; split; [ reflexivity | intros * H; eexists; exact H ]
          | destruct Hgr as (-> & -> & ->); split; [ reflexivity | intros * H; injection H as <- <-; eexists; reflexivity ]
          | destruct Hgr as (-> & -> & -> & ->); split; [ reflexivity | intros * H; injection H as <- <-; eexists; reflexivity ] ].
Qed.

(** The child [y] of a module stored at [p] in a global context and in one
    it grows into, an entry of the smaller one: stored in the bigger one
    over a telescope, it is stored in the smaller one over the same; an
    alias in the bigger one is the same alias in the smaller one. *)
Lemma loc_child_grow : forall Θ1 Ξ1 Θ2 Ξ2, ⊢ᵍ Θ1 ⍮ Ξ1 -> ⊢ᵍ Θ2 ⍮ Ξ2 -> gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    forall p T Φ1 Φ2 y E1, loc Θ1 Ξ1 p T Φ1 -> loc Θ2 Ξ2 p T Φ2 -> gm_entry Φ1 (y :: nil) = Some E1 ->
    (forall T' Φ', gc_loc Θ2 Ξ2 (qname_in p y) = Some (T', Φ') -> exists Φ1', gc_loc Θ1 Ξ1 (qname_in p y) = Some (T', Φ1')) /\
    (forall U, gc_module Θ2 Ξ2 (qname_in p y) = Some (mr_alias U) -> gc_module Θ1 Ξ1 (qname_in p y) = Some (mr_alias U)).
Proof.
  intros * Hg1 Hg2 Hs * Hl1 Hl2 He1.
  pose proof (proj2 (loc_entry _ _ Hg1 _ _ _ Hl1 _ _) He1) as Hc1.
  destruct (gc_sub_entry_field _ _ _ _ Hs _ _ Hc1) as (E2 & Hc2 & Hgr).
  pose proof (proj1 (loc_entry _ _ Hg2 _ _ _ Hl2 _ _) Hc2) as He2.
  destruct (gm_entry_head _ _ _ He1) as (z1 & ip1 & [= <- <-] & Hin1).
  destruct (gm_entry_head _ _ _ He2) as (z2 & ip2 & [= <- <-] & Hin2).
  destruct (loc_read _ _ Hg1 _ _ _ Hl1 _ Hin1 nil) as (_ & _ & Hm1 & Hb1).
  destruct (loc_read _ _ Hg2 _ _ _ Hl2 _ Hin2 nil) as (_ & _ & Hm2 & Hb2).
  rewrite <- qname_in_app in Hm1, Hb1, Hm2, Hb2.
  destruct (gm_child_of_entry _ _ _ T He1) as [Em1 Eb1].
  destruct (gm_child_of_entry _ _ _ T He2) as [Em2 Eb2].
  destruct (gm_child_grows y _ _ T Hgr) as [Em Eb].
  (** Neither child is an open frame: each is an entry *)
  assert (Hnf : forall Θ Ξ E, gc_entry Θ Ξ (qname_in p y) = Some E -> gc_frame Ξ (qname_in p y) = None).
  { intros * Hc; unfold gc_frame; destruct (gs_find_tele Ξ (qname_in p y)) as [[[[Δ [[|] Φ0 | E0]] [| ? ?]] T0] |] eqn:Ht;
      try reflexivity.
    rewrite (gc_entry_tele_nil _ _ _ _ _ Ht) in Hc; discriminate. }
  split.
  - intros * Hl'; unfold gc_loc in Hl' |- *; rewrite (Hnf _ _ _ Hc2) in Hl'; rewrite (Hnf _ _ _ Hc1).
    rewrite Hb2, Eb2 in Hl'; destruct (Eb _ _ Hl') as (Φ1' & HΦ1').
    exists Φ1'; rewrite Hb1, Eb1; exact HΦ1'.
  - intros U Hm; rewrite Hm1, Em1, Em, <- Em2, <- Hm2; exact Hm.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** A sort of types is the sort of a kind next to a universe. *)
Lemma type_sort_abs_kind_inv : forall S, type_sort S -> exists κ (l : nat), S = abs_kind_sort κ Typeω@l.
Proof. intros S []; [ exists ak_relevant, i | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity. Qed.

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

(** Reading a description at arguments keeps its kind: a term stays a
    term of its tag, and anything else stays no term. *)
Lemma mdesc_kind_ats_read : forall Ns R R1, (forall Θd A M Rm, R = mdesc_dm Θd A M Rm -> Θd = nil) ->
    mdesc_ats_read R Ns = Some R1 -> mdesc_kind R1 = mdesc_kind R.
Proof.
  intros * Hdm Ha.
  destruct R as [r A om | Δ Φ Φx | Θ0 p T Φ Ns' | Θd A M Rm].
  - rewrite mdesc_ats_read_other in Ha by (intros; discriminate).
    destruct (mdesc_ats_term _ _ _ _ _ Ha) as (? & ? & ->); reflexivity.
  - rewrite mdesc_ats_read_other in Ha by (intros; discriminate).
    assert (Hm : mdesc_is_mod R1) by (eapply mdesc_ats_is_mod; [| exact Ha ]; exact I); destruct R1; cbn in Hm |- *; first [ contradiction | reflexivity ].
  - rewrite mdesc_ats_read_other in Ha by (intros; discriminate).
    assert (Hm : mdesc_is_mod R1) by (eapply mdesc_ats_is_mod; [| exact Ha ]; exact I); destruct R1; cbn in Hm |- *; first [ contradiction | reflexivity ].
  - pose proof (Hdm _ _ _ _ eq_refl) as ->.
    cbn [mdesc_ats_read] in Ha; mdesc_dm_read_shape Ha; reflexivity.
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

(** A type value related to a [Π] into an evaluated kind is a [Π] of the
    same kinds: a [Π] into propositions is the only proposition among
    them. *)
Lemma per_univ_pi_left_shape : forall (j : universe_index) R κd κc a ρ B a2, evaluated_kind κc ->
    DF d_pi κd κc a ρ B ≈ a2 ∈ per_univ_elem j ↘ R -> exists a' ρ' B', a2 = d_pi κd κc a' ρ' B'.
Proof.
  intros * Hk HR.
  invert_per_univ_elem HR.
  all: try (do 3 eexists; reflexivity).
Qed.

(** A term over a weakened context, its top variable put back, then given
    an extended substitution, is the term at that substitution: the
    composite agrees with it pointwise. *)
Lemma exp_sub_shift_var0_extend : forall X τ N, X[Wk,,#0][τ,,N] = X[τ,,N].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq; intros n.
  rewrite (sb_extend_compose _ _ _ n); destruct n; [ reflexivity | exact (sb_shift_extend _ _ n) ].
Qed.

(** The same, the term lifted over the weakening first. *)
Lemma exp_sub_q_shift_var0_extend : forall X τ N, X[q Wk][Id,,#0][τ,,N] = X[τ,,N].
Proof. intros; rewrite exp_sub_q_extend; apply exp_sub_shift_var0_extend. Qed.

(** A module expression weakened, then given an extended substitution, is
    the module expression at the substitution. *)
Lemma modexp_sub_shift_extend : forall H τ N, H[Wk]ᵐ[τ,,N]ᵐ = H[τ]ᵐ.
Proof. intros; rewrite modexp_sub_sub; apply modexp_sub_sb_eq, sb_shift_extend. Qed.

(** A codomain lifted over the weakening past its domain, then given the
    top variable, is equal to itself ([wf_sub_eq_var_zero]): the two
    substitutions differ only on module variables, which a typed term does
    not read at the top. *)
Lemma codomain_wk_var0_eq : forall Γ κ A Srt C S, Γ ⊢ A : Srt -> sort_kind Srt κ -> type_sort S ->
    Γ ▹{κ} A ⊢ C : S -> Γ ▹{κ} A ⊢ C[wk_q wk_shift]ʷ[Id,,#0] ≈ C : S.
Proof.
  intros * HA HS HSt HC.
  assert (HΓA : ⊢ Γ ▹{κ} A) by mauto 3.
  assert (Hw : Γ ▹{κ} A ⊢ʷ wk_shift : Γ) by mauto 2.
  assert (HC' : Γ ▹{κ} A ▹{κ} A[wk_shift]ʷ ⊢ C[wk_q wk_shift]ʷ : S)
    by (eapply wk_preserves_sort; [ exact HC | exact HSt | eapply wf_wk_q'; [ exact Hw | exact HA | exact HS ] ]).
  rewrite <- (exp_wk_q_shift_single C) at 2.
  eapply sub_eq_preserves_sort; [ exact HC' | exact HSt | eapply wf_sub_eq_var_zero; eassumption ].
Qed.

(** The same, the codomain lifted over the weakening as a substitution. *)
Lemma codomain_var0_eq : forall Γ κ A Srt C S, Γ ⊢ A : Srt -> sort_kind Srt κ -> type_sort S ->
    Γ ▹{κ} A ⊢ C : S -> Γ ▹{κ} A ⊢ C[q Wk][Id,,#0] ≈ C : S.
Proof.
  intros * HA HS HSt HC.
  assert (E : C[q Wk] = C[wk_q wk_shift]ʷ) by (rewrite <- exp_sub_of_wk_q_extend; apply exp_sub_sb_eq; intros [| n]; reflexivity).
  rewrite E; exact (codomain_wk_var0_eq _ _ _ _ _ _ HA HS HSt HC).
Qed.

(** An equation at the sort of a kind next to a universe holds next to a
    larger one: the twin of [abs_kind_sort_lift] for equations. *)
Lemma abs_kind_sort_eq_lift : forall Γ M M' κ (i n : nat), i <= n ->
    Γ ⊢ M ≈ M' : abs_kind_sort κ Typeω@i -> Γ ⊢ M ≈ M' : abs_kind_sort κ Typeω@n.
Proof. intros * Hle HM; destruct κ; cbn in *; [ exact (lift_exp_eq_ge _ _ _ _ _ _ _ Hle HM) | exact HM | exact HM ]. Qed.

(** A term of a type is of every type equal to it at a sort of types. *)
Lemma wf_exp_conv_kind : forall Γ M A A' κ (l : nat),
    Γ ⊢ M : A -> Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@l -> Γ ⊢ M : A'.
Proof.
  intros * HM HA.
  eapply wf_exp_subtyp'; [ exact HM |].
  eapply wf_subtyp_refl; [ exact (presup_exp_eq_right HA) | apply type_sort_abs_kind; constructor | exact HA ].
Qed.

(** Equal types of a sort have related values at an environment of the
    context, by completeness. *)
Lemma eq_type_value_rel : forall Γ A A' S RΓ ρ a',
    Γ ⊢ A ≈ A' : S -> type_sort S -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> ⟦ A' ⟧ ρ ↘ a' ->
    exists a (i : nat), ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HAA HS HRΓ Hρ Ea'.
  destruct (rel_type_of_sort HS (completeness_fundamental_exp_eq _ _ _ _ HAA)) as [i Hi].
  destruct (rel_type_inversion_simple Hi) as [R' [HR' HAr]].
  assert (Hirr : RΓ <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (HAr _ _ (proj1 (Hirr _ _) Hρ)) as (a0 & a0' & Ea0 & Ea0' & Ha).
  pose proof (functional_eval_exp _ _ _ _ Ea0' Ea') as ->.
  exists a0, i; split; assumption.
Qed.

(** Related [Π]s into an evaluated kind: their domains are related, and so
    are their codomains at related arguments. *)
Lemma per_univ_pi_parts : forall (j : universe_index) R κd κc a ρ B a' ρ' B', evaluated_kind κc ->
    DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem j ↘ R ->
    exists in_rel, DF a ≈ a' ∈ per_univ_elem j ↘ in_rel /\
      (forall c c', Dom c ≈ c' ∈ in_rel -> exists b b', ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b /\
         ⟦ B' ⟧ ρ' ↦ c' ⦂ entry_type_value a' ↘ b' /\ Dom b ≈ b' ∈ per_univ j).
Proof.
  intros * Hk HR.
  invert_per_univ_elem HR.
  exists in_rel; split; [ exact equiv_a_a' |].
  intros c c' Hc; destruct (H0 _ _ Hc) as [b b' Eb Eb' Hbb'].
  exists b, b'; split; [ exact Eb | split; [ exact Eb' | eexists; exact Hbb' ] ].
Qed.

(** The domain of a [Π] into an evaluated kind is of the [Π]'s domain
    kind, the two kinds those of a [Π]. *)
Lemma per_univ_pi_kinds : forall (j : universe_index) R κd κc a ρ B a2, evaluated_kind κc ->
    DF d_pi κd κc a ρ B ≈ a2 ∈ per_univ_elem j ↘ R -> domain_kind a = κd /\ pi_kinds κd κc.
Proof.
  intros * Hk HR.
  invert_per_univ_elem HR; split; first [ reflexivity | assumption ].
Qed.

(** Related values lacking a parameter: their next parameters are related,
    and so are their values at related arguments, the left one existing. *)
Lemma per_dmod_fun_parts : forall h h1 a a1, per_dmod h h1 -> next_param h a -> next_param h1 a1 ->
    exists (i : universe_index) R, DF a ≈ a1 ∈ per_univ_elem i ↘ R /\
      (forall c c', Dom c ≈ c' ∈ R -> exists hc, $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc /\
         forall hc', $ᵐ| h1 & c' | gc_deps ⍮ gc_stack ↘ hc' -> per_dmod hc hc').
Proof.
  intros * Hp Hn Hn1; inversion Hp; subst.
  - (** A saturated global value lacks no parameter *)
    exfalso; inversion Hn; subst.
    match goal with Hl : gc_loc _ _ p = Some (T, _), Hl' : gc_loc _ _ p = Some _ |- _ =>
      rewrite Hl in Hl'; injection Hl' as <- <- end.
    match goal with Ht : List.nth_error _ _ = Some _ |- _ =>
      rewrite (proj2 (List.nth_error_None _ _)) in Ht by (rewrite List.length_rev; lia); discriminate end.
  - (** Nor does a saturated body *)
    exfalso; inversion Hn; subst.
    match goal with Hl : _ ++ _ :: nil = nil |- _ => destruct Δ; discriminate end.
  - match goal with H0 : next_param h ?a0, H1 : next_param h1 ?a0' |- _ =>
      pose proof (next_param_functional _ _ Hn _ H0) as <-; pose proof (next_param_functional _ _ Hn1 _ H1) as <- end.
    exists i, R; split; [ assumption |].
    intros c c' Hc.
    match goal with Hex : forall c c', R c c' -> exists hc, _, Hrel : forall c c' hc hc', R c c' -> _ -> _ -> per_dmod hc hc' |- _ =>
      destruct (Hex _ _ Hc) as [hc Ehc]; exists hc; split; [ exact Ehc | intros hc' Ehc'; exact (Hrel _ _ _ _ Hc Ehc Ehc') ] end.
Qed.

(** [Π]s with equal domains and codomains equal over the right domain are
    equal ([wf_exp_eq_pi_cong_at_max]): the codomains' equation moves to
    the left domain ([ctx_sub_extend_eq]). *)
Lemma pi_eq_of_parts : forall Δ κd κc A A' C C' (i j : nat),
    Δ ⊢ A ≈ A' : abs_kind_sort κd Typeω@i ->
    Δ ▹{κd} A' ⊢ C ≈ C' : abs_kind_sort κc Typeω@j ->
    pi_kinds κd κc ->
    Δ ⊢ a_pi κd κc A C ≈ a_pi κd κc A' C' : abs_kind_sort κc Typeω@(Nat.max i j).
Proof.
  intros * HAA HCC Hk.
  pose proof (presup_exp_eq_left HAA) as HA.
  pose proof (ctx_sub_extend_eq _ _ _ _ _ _ _ (presup_exp_eq_right HAA) HA (sort_kind_abs_kind_sort _ _)
                (wf_exp_eq_sym _ _ _ _ _ _ HAA)) as Hsub.
  exact (wf_exp_eq_pi_cong_at_max _ _ _ _ _ _ _ _ _ _ _ HA HAA (ctxsub_exp_eq _ _ _ _ _ _ _ (ctx_sub_escape _ _ _ _ Hsub) HCC) Hk).
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

  (** The completeness facts of a member at a value related to the
      module's value at an environment, at a type value related to the
      type's there: the value is related to itself, its member types to
      the type value, and its member to itself at the type value's
      element PER ([mem_valid_at]). *)
  Lemma mem_value_facts : forall Γ H x R A RΓ ρ h' h a2' a2 (j : universe_index) m,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A ->
      EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h' -> per_dmod h h' ->
      ⟦ A ⟧ ρ ↘ a2' -> Dom a2' ≈ a2 ∈ per_univ j -> evaluated_kind (domain_kind a2) -> h ·ₜ x Θ ⍮ Ξ ↘ m ->
      per_dmod h h /\ dmod_mem_type_rel h x a2 /\
      (forall (i : universe_index) R2, DF a2 ≈ a2 ∈ per_univ_elem i ↘ R2 -> Dom m ≈ m ∈ R2).
  Proof.
    intros * HH Hm HA HRΓ Hρ Eh Hhh' Ea Ha Hev Hsel.
    destruct (mem_valid_at _ _ _ _ _ _ _ HH Hm HA HRΓ Hρ) as [h0 a0 i0 R0 Eh0 Ea0 HR0 Hhas _ Hty].
    pose proof (functional_eval_modexp _ _ _ _ Eh0 Eh) as ->.
    pose proof (functional_eval_exp _ _ _ _ Ea0 Ea) as ->.
    destruct Ha as [Ra HRa].
    assert (Hev' : evaluated_kind (domain_kind a2')) by (rewrite (per_univ_elem_kind _ _ _ _ HRa); exact Hev).
    pose proof (proj1 per_dmod_sym_all _ _ Hhh') as Hh'h.
    pose proof (proj1 per_dmod_trans_all _ _ Hhh' _ Hh'h) as Hhh.
    split; [ exact Hhh | split ].
    - intros h0 b Hh0 Hb.
      destruct (Hty Hev' _ _ (proj1 per_dmod_trans_all _ _ Hh0 _ Hhh') Hb) as [j0 Hb0].
      exists j0; exact (per_univ_trans' _ _ _ _ _ Hb0 (ex_intro _ Ra HRa)).
    - intros i R2 HR2.
      destruct (Hhas Hev' _ Hhh') as [ml mr Eml Emr Hmm].
      pose proof (functional_eval_sel _ _ _ _ Eml Hsel) as ->.
      pose proof (per_elem_PER HR0) as HP0.
      assert (Hm0 : R0 m m) by (etransitivity; [ exact Hmm | symmetry; exact Hmm ]).
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa HR0) as E1.
      pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRa HR2) as E2.
      apply E2, E1; exact Hm0.
  Qed.

  (** A context extended by a well-formed type, in the PER model: its PER
      is the canonical extension ([per_ctx_env_extend]), relating an
      environment of the context extended by a value related to itself at
      the type's value there ([per_env_extend_intro']). *)
  Lemma ctx_env_extend_at : forall Γ B Srt κ RΓ ρ aB (i : universe_index) RB c,
      Γ ⊢ B : Srt -> sort_kind Srt κ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
      ⟦ B ⟧ ρ ↘ aB -> DF aB ≈ aB ∈ per_univ_elem i ↘ RB -> Dom c ≈ c ∈ RB ->
      EF Γ ▹{κ} B ≈ Γ ▹{κ} B ∈ per_ctx_env ↘ per_env_extend B B RΓ /\
      Dom ρ ↦ c ⦂ entry_type_value aB ≈ ρ ↦ c ⦂ entry_type_value aB ∈ per_env_extend B B RΓ.
  Proof.
    intros * HB HS HRΓ Hρ Ea HRB Hc.
    destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS) (completeness_fundamental_exp _ _ _ HB)) as [i0 Hi].
    pose proof (rel_type_under_ctx_not_level_sort _ _ _ _ Hi) as Hn.
    destruct (rel_type_inversion_simple Hi) as [R' [HR' HA]].
    assert (Hirr : RΓ <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
    split.
    - eapply per_ctx_env_extend; [ exact HRΓ | intros ρ1 ρ2 H12; apply HA, Hirr, H12 | intros ρ1 ρ2 H12; exact (Hn _ HRΓ _ _ H12) ].
    - apply per_env_extend_intro'; [ exact Hρ | | exact (proj1 (entry_readable_of_elem HRB Hc)) | exact (proj1 (entry_readable_of_elem HRB Hc)) ].
      intros i1 R1 a1 a1' E1 E1' HR1.
      pose proof (functional_eval_exp _ _ _ _ E1 Ea) as ->; pose proof (functional_eval_exp _ _ _ _ E1' Ea) as ->.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRB HR1) as E; apply E; exact Hc.
  Qed.

  (** A well-formed module expression, weakened past an assumption, at an
      environment of the extended context: its value is related to the
      module expression's at the tail.  The two values need not be equal,
      the weakening retagging the tail ([eval_sub_shift]); completeness
      relates them through the weakening ([rel_modexp]) and the retagged
      tail ([per_ctx_env_retag_left]). *)
  Lemma modexp_wk_value_rel : forall Γ κ B H RΓ RB ρ c t h0,
      ⊢ Γ ▹{κ} B -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
      EF Γ ▹{κ} B ≈ Γ ▹{κ} B ∈ per_ctx_env ↘ RB -> RB (ρ ↦ c ⦂ t) (ρ ↦ c ⦂ t) ->
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h0 ->
      exists h1, ⟦ H[Wk]ᵐ ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↦ c ⦂ t ↘ h1 /\ per_dmod h1 h0.
  Proof.
    intros * HΓB HH HRΓ Hρ HRB Hρ' Eh0.
    pose proof (proj2 (proj2 completeness_fundamental_modules) _ _ _ HH) as HHc.
    pose proof (rel_sub_shift (completeness_fundamental_ctx _ HΓB)) as Hw.
    pose proof HHc as [R0 HR0 Hbody].
    destruct (Hbody _ _ HRB _ _ Hw _ _ _ _ Hρ' (eval_sub_shift _ _) (eval_sub_shift _ _)) as [hσ hh h' h'σ' E1 E2 E3 E4 Hch].
    assert (Hσh : per_dmod hσ hh) by (inversion Hch; subst; assumption).
    change ((ρ ↦ c ⦂ t)↯) with ρ in E2.
    destruct (Completeness.UnitCases.rel_modexp_at _ _ _ _ _ HHc HRΓ _ _ (per_ctx_env_retag_left HRΓ _ _ Hρ))
      as (h2 & h3 & Eh2 & Eh3 & Hh23).
    pose proof (functional_eval_modexp _ _ _ _ Eh2 E2) as ->.
    pose proof (functional_eval_modexp _ _ _ _ Eh3 Eh0) as ->.
    exists hσ; split; [ exact E1 | exact (proj1 per_dmod_trans_all _ _ Hσh _ Hh23) ].
  Qed.

  (** A type, weakened past an assumption, at an environment of the
      extended context: its value is related to the type's at the tail, as
      [modexp_wk_value_rel] has it for module expressions. *)
  Lemma typ_wk_value_rel : forall Γ κ B A Srt RΓ RB ρ c t aA,
      ⊢ Γ ▹{κ} B -> Γ ⊢ A : Srt -> type_sort Srt -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
      EF Γ ▹{κ} B ≈ Γ ▹{κ} B ∈ per_ctx_env ↘ RB -> RB (ρ ↦ c ⦂ t) (ρ ↦ c ⦂ t) ->
      ⟦ A ⟧ ρ ↘ aA ->
      exists a1 (i : nat), ⟦ A[Wk] ⟧ ρ ↦ c ⦂ t ↘ a1 /\ Dom a1 ≈ aA ∈ per_univ i.
  Proof.
    intros * HΓB HA HS HRΓ Hρ HRB Hρ' Ea.
    destruct (rel_type_of_sort HS (completeness_fundamental_exp _ _ _ HA)) as [i Hi].
    pose proof (rel_sub_shift (completeness_fundamental_ctx _ HΓB)) as Hw.
    pose proof Hi as [R0 HR0 Hbody _].
    destruct (Hbody _ _ HRB _ _ Hw _ _ _ _ Hρ' (eval_sub_shift _ _) (eval_sub_shift _ _)) as [aσ a0 a0' aσ' E1 E2 E3 E4 Hch].
    assert (Hσa : per_univ i aσ a0) by (inversion Hch; subst; assumption).
    change ((ρ ↦ c ⦂ t)↯) with ρ in E2.
    destruct (rel_type_inversion_simple Hi) as [R' [HR' HAr]].
    assert (Hirr : RΓ <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (HAr _ _ (proj1 (Hirr _ _) (per_ctx_env_retag_left HRΓ _ _ Hρ))) as (a2 & a3 & Ea2 & Ea3 & Ha23).
    pose proof (functional_eval_exp _ _ _ _ Ea2 E2) as ->.
    pose proof (functional_eval_exp _ _ _ _ Ea3 Ea) as ->.
    exists aσ, i; split; [ exact E1 | exact (per_univ_trans' _ _ _ _ _ Hσa Ha23) ].
  Qed.

  (** A well-formed module expression lacking a parameter, weakened past
      it, at an environment of the context extended by it: its value lacks
      a parameter related to the parameter's value there
      ([valid_unit_app_all] at the variable). *)
  Lemma next_param_wk_at : forall Γ κ B SrtB H RH T T1 RB ρ',
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H RH -> mdesc_mod_tele RH = Some T -> tele_view T = Some (B, T1) ->
      evaluated_sort SrtB -> Γ ⊢ B : SrtB -> sort_kind SrtB κ ->
      EF Γ ▹{κ} B ≈ Γ ▹{κ} B ∈ per_ctx_env ↘ RB -> RB ρ' ρ' -> ModexpRel.modexp_next_param_at H[Wk]ᵐ B[Wk] ρ'.
  Proof.
    intros * HH Hm HT Hv HS HB Hsk HRB Hρ'.
    assert (HΓB : ⊢ Γ ▹{κ} B) by (eapply wf_ctx_extend; eassumption).
    assert (HWk : Γ ▹{κ} B ⊢ˢ Wk : Γ) by (eapply wf_sub_shift; exact HΓB).
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH HWk) as HHw.
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HH Hm HWk) as Hmw.
    pose proof (mdesc_mod_tele_sub _ _ Wk _ (wf_mdenote_scoped _ _ _ _ _ _ HH Hm) HT) as HTw.
    pose proof (tele_view_sub T Wk) as Hvw; rewrite Hv in Hvw; cbn [option_map fst snd] in Hvw.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB HWk) as HBw.
    assert (EBS : SrtB[Wk] = SrtB) by (destruct HS; reflexivity).
    rewrite EBS in HBw.
    assert (H0t : Γ ▹{κ} B ⊢ #0 : B[Wk])
      by (rewrite exp_sub_of_shift; apply wf_vlookup; [ exact HΓB | constructor ]).
    pose proof (valid_gctx_embedding_refl _ _ Hg) as Hve.
    destruct completeness_fundamental as (_ & _ & _ & _ & _ & _ & _ & Km).
    destruct (Km _ _ _ _ _ HHw _ _ Hve) as [_ _ HvH _].
    assert (Hrp : exists i, rel_param_typed (Γ ▹{κ} B) B[Wk] i)
      by (destruct HS; [ exists i; left | exists 0; right ]; exact (completeness_fundamental_exp _ _ _ HBw)).
    destruct Hrp as [i Hrp].
    destruct (proj2 (@App.valid_unit_app_all GCm Hg Θ Ξ Hg (gc_sub_refl _ _) (valid_gctx_embedding_filed _ _ _ _ Hve))
                _ _ HvH _ _ _ _ _ i #0 Hmw HTw Hvw HS HBw Hrp H0t (completeness_fundamental_exp _ _ _ H0t)) as [Hnp _].
    exact (Hnp _ HRB _ Hρ').
  Qed.

  (** Every path a stored module's path extends is stored: its parent is
      ([loc_parent]), up the chain. *)
  Lemma path_prefix_loc : forall m2 F T Φ, loc Θ Ξ F T Φ -> forall m1, q_chain F = m1 ++ m2 -> m1 <> nil ->
      exists TΦ, gc_loc Θ Ξ (q_abs (q_unit F) m1) = Some TΦ.
  Proof.
    induction m2 as [| z m2 IH] using List.rev_ind; intros * Hl m1 Ec Hne.
    - rewrite List.app_nil_r in Ec; rewrite <- Ec.
      destruct F as [u ch]; cbn [q_unit q_chain]; exists (T, Φ); exact (gc_loc_of_loc _ _ Hg _ _ _ Hl).
    - rewrite List.app_assoc in Ec.
      assert (EqF : F = qname_in (q_abs (q_unit F) (m1 ++ m2)) z)
        by (destruct F as [u ch]; cbn in Ec |- *; unfold qname_in; cbn; rewrite <- Ec; reflexivity).
      rewrite EqF in Hl; destruct (loc_parent _ _ Hg _ _ _ _ Hl) as (T' & Φ' & Hl').
      exact (IH _ _ _ Hl' m1 eq_refl Hne).
  Qed.

  (** The value of a type of a sort at an environment, up to [per_univ],
      is no [LevelSort] ([rel_type_under_ctx_not_level_sort]). *)
  Lemma type_value_not_level_sort : forall Γ A Srt RΓ ρ a2' a2 (j : universe_index),
      Γ ⊢ A : Srt -> type_sort Srt ->
      EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> ⟦ A ⟧ ρ ↘ a2' -> Dom a2' ≈ a2 ∈ per_univ j -> not_level_sort a2.
  Proof.
    intros * HA HS HRΓ Hρ Ea [Ra HRa].
    destruct (rel_type_of_sort HS (completeness_fundamental_exp _ _ _ HA)) as [i Hi].
    destruct (rel_type_under_ctx_not_level_sort _ _ _ _ Hi _ HRΓ _ _ Hρ) as (a & Ea0 & Hna).
    pose proof (functional_eval_exp _ _ _ _ Ea0 Ea) as ->.
    exact (proj1 (per_univ_elem_not_level_sort_iff _ _ _ _ HRa) Hna).
  Qed.

  (** The next parameter of a value related to a module expression's at an
      environment is related to the value there of the parameter's type
      in the module's telescope: both are related to the parameter's value
      at the environment extended by a variable, weakened
      ([next_param_wk_at], [typ_wk_value_rel], [modexp_wk_value_rel]). *)
  Lemma next_param_value_rel : forall Γ H RH T B T1 SrtB κ RΓ ρ h' h a aB,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H RH -> mdesc_mod_tele RH = Some T -> tele_view T = Some (B, T1) ->
      evaluated_sort SrtB -> Γ ⊢ B : SrtB -> sort_kind SrtB κ ->
      EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h' -> per_dmod h h' -> next_param h a ->
      ⟦ B ⟧ ρ ↘ aB -> exists i, Dom a ≈ aB ∈ per_univ i.
  Proof.
    intros * HH HmH HT Hv HS HB Hsk HRΓ Hρ Eh' Hhh' Hnp EaB.
    pose proof (sort_kind_type_sort _ _ Hsk) as HSt.
    destruct (rel_type_of_sort HSt (completeness_fundamental_exp _ _ _ HB)) as [iB0 HiB].
    destruct (rel_type_inversion_simple HiB) as [R' [HR' HBr]].
    assert (Hirr : RΓ <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (HBr _ _ (proj1 (Hirr _ _) Hρ)) as (b0 & b0' & Eb0 & Eb0' & [RB HRB]).
    pose proof (functional_eval_exp _ _ _ _ Eb0 EaB) as ->; pose proof (functional_eval_exp _ _ _ _ Eb0' EaB) as ->.
    (** A variable of the parameter's type *)
    pose proof (type_value_not_level_sort _ _ _ _ _ _ _ _ HB HSt HRΓ Hρ EaB (ex_intro _ RB HRB)) as Hnl.
    pose proof (var_per_elem 0 HRB Hnl) as Hc0.
    destruct (ctx_env_extend_at _ _ _ _ _ _ _ _ _ _ HB Hsk HRΓ Hρ EaB HRB Hc0) as [HRΓb Hρ''].
    assert (HΓB : ⊢ Γ ▹{κ} B) by (eapply wf_ctx_extend; eassumption).
    (** The weakened module's next parameter, related to the weakened
        type's value, related to the type's *)
    destruct (next_param_wk_at _ _ _ _ _ _ _ _ _ _ HH HmH HT Hv HS HB Hsk HRΓb Hρ'') as [h1 a1 b1 ib Rb1 Eh1 Hn1 Eb1 Hab1].
    destruct (typ_wk_value_rel _ _ _ _ _ _ _ _ _ _ _ HΓB HB HSt HRΓ Hρ HRΓb Hρ'' EaB) as (b1' & i1 & Eb1' & Hb1).
    pose proof (functional_eval_exp _ _ _ _ Eb1' Eb1) as ->.
    (** The weakened module's value, related to the value *)
    destruct (modexp_wk_value_rel _ _ _ _ _ _ _ _ _ _ HΓB HH HRΓ Hρ HRΓb Hρ'' Eh') as (h1' & Eh1' & Hh1h').
    pose proof (functional_eval_modexp _ _ _ _ Eh1' Eh1) as ->.
    pose proof (proj1 per_dmod_trans_all _ _ Hhh' _ (proj1 per_dmod_sym_all _ _ Hh1h')) as Hhh1.
    destruct (per_dmod_fun_parts _ _ _ _ Hhh1 Hnp Hn1) as (iR & R & HaR & _).
    exists iR.
    exact (per_univ_trans' _ _ _ _ _ (per_univ_trans' _ _ _ _ _ (ex_intro _ R HaR) (ex_intro _ Rb1 Hab1)) Hb1).
  Qed.

  (** The value of a member's type at an environment, up to [per_univ], is
      of the member's kind: its type is of the sort of its kind
      ([desc_ok_ty_at]). *)
  Lemma mem_type_value_kind : forall Γ H x R A RΓ ρ a2' a2 (j : universe_index),
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A ->
      EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> ⟦ A ⟧ ρ ↘ a2' -> Dom a2' ≈ a2 ∈ per_univ j ->
      domain_kind a2 = mdesc_kind R.
  Proof.
    intros * HH Hm HA HRΓ Hρ Ea [Ra HRa].
    pose proof (mem_desc_ok _ _ _ _ _ _ _ (gctx_valid_syn _ _ Hg) HH Hm) as Hok.
    destruct (desc_ok_ty_at _ _ _ _ _ Hok HA) as [i HAi].
    pose proof (FunctionCases.rel_type_kind_of_sort_kind (sort_kind_abs_kind_sort _ _) (completeness_fundamental_exp _ _ _ HAi)) as HK.
    destruct (HK _ HRΓ _ _ Hρ) as (a & Ea0 & Hka).
    pose proof (functional_eval_exp _ _ _ _ Ea0 Ea) as ->.
    rewrite <- (per_univ_elem_kind _ _ _ _ HRa); exact Hka.
  Qed.

  (** The outermost parameter of what a well-formed module expression
      denotes is a type of a universe or of levels: an open module's and
      the outer parameters of a closed one are ([params_evaluated] of
      [desc_ok]); a closed one's next stored parameter is, in its stored
      telescope ([loc_params_evaluated]), at the arguments given
      ([args_ok]). *)
  Lemma mod_next_param_typed : forall Γ H R T B T1,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
      exists Srt, evaluated_sort Srt /\ Γ ⊢ B : Srt.
  Proof.
    intros * HH Hm HT Hv.
    unfold mdesc_mod_tele in HT; destruct (mdesc_mod R) as [Rm |] eqn:HRm; [| discriminate ].
    pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) HRm) as Hok.
    assert (Hpe : forall Δ l B' T1', params_evaluated Θ Ξ Γ Δ l -> all_assumptions Δ -> tele_view Δ = Some (B', T1') ->
               exists Srt, evaluated_sort Srt /\ Γ ⊢ B' : Srt).
    { intros * HP Ha Hv'.
      destruct (tele_view_ass _ _ _ Ha Hv') as [κ ->].
      destruct (HP T1' κ B' nil eq_refl) as [HB | HB]; cbn [List.app] in HB; eexists; (split; [ constructor | exact HB ]). }
    inversion Hok; subst; cbn [mdesc_tele] in HT; try discriminate.
    - (** An open module: its parameters *)
      injection HT as <-; eapply Hpe; eassumption.
    - destruct (length Ns <=? length T0) eqn:Hle; [ injection HT as <- | discriminate ].
      destruct (List.rev Θ') as [| e r] eqn:Er.
      2:{ (** A closed module under outer parameters: the outermost one *)
          assert (Hv' : exists B' T1', tele_view Θ' = Some (B', T1')).
          { unfold tele_view; rewrite Er.
            assert (Hin : List.In e Θ') by (apply List.in_rev; rewrite Er; left; reflexivity).
            destruct (proj1 (List.Forall_forall _ _) H8 _ Hin) as (κ & B' & ->).
            cbn; eexists; eexists; reflexivity. }
          destruct Hv' as (B' & T1' & Hv').
          destruct (tele_view_app_r (tele_sub (firstn (length T0 - length Ns) T0) (sb_of_list Id Ns)) _ _ _ Hv') as (Y1 & HY).
          rewrite Hv in HY; injection HY as -> _.
          exact (Hpe _ _ _ _ H9 H8 Hv'). }
      (** A closed module under no outer parameter: its next stored
          parameter, at the arguments *)
      assert (Θ' = nil) as -> by (rewrite <- (List.rev_involutive Θ'), Er; reflexivity).
      rewrite List.app_nil_r in Hv; cbn [List.app] in H7.
      destruct H7 as [Tr Tf -> Hl Ha Hs HTf HN].
      replace (firstn (length (Tr ++ Tf) - length Ns) (Tr ++ Tf)) with Tr in Hv
        by (rewrite List.length_app, Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; rewrite List.app_nil_r; reflexivity).
      rewrite tele_view_sub in Hv.
      destruct (tele_view Tr) as [[B0 T10] |] eqn:Hv0; cbn in Hv; [ injection Hv as <- _ | discriminate ].
      assert (Har : all_assumptions Tr) by (apply List.Forall_app in H3; exact (proj1 H3)).
      destruct (tele_view_ass _ _ _ Har Hv0) as [κ ->].
      destruct (loc_grow _ _ _ _ H1 _ _ _ H2) as [Φ2 Hl2].
      destruct (loc_params_evaluated _ _ _ _ _ (gctx_valid_syn _ _ Hg) Hl2) as [lT HRT].
      assert (HB0 : param_typed Θ Ξ (Tf ++ nil) B0 lT) by (apply (HRT T10 κ B0 Tf); rewrite <- List.app_assoc; reflexivity).
      rewrite List.app_nil_r in HB0.
      pose proof (wf_sub_of_list_id _ _ _ _ _ Ha HTf (eq_sym Hl) HN) as Hσ.
      destruct HB0 as [HB0 | HB0];
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ (closed_tele_weaken_exp _ _ _ _ _ _ Hs HB0 HTf) Hσ) as HBσ;
        cbn [exp_sub] in HBσ; eexists; (split; [ constructor | exact HBσ ]).
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

  (** The type of a term member of a module stored at a source of a sound
      embedding, the [Π] over the module's telescope of a type glued over
      it at the target: a definition's, a definition with a module part's
      ([glu_def_over_tele]), a type former's ([glu_gctx_embedding_ind_former_type],
      [glu_gctx_embedding_record_former_type]), the former's parameters
      ending in the telescope ([ge_coherent]). *)
  Lemma stored_type_over_tele : forall Θs Ξs, ⊢ᵍ Θs ⍮ Ξs -> glu_gctx_embedding Θs Ξs Θ Ξ ->
      forall p T Φ x Φ0 E0 Γ RE As,
      loc Θs Ξs p T Φ -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E0) ->
      edenote Θs Ξs Γ (Some (qname_in p x)) (ge_read T E0) RE -> mdesc_type RE = Some As ->
      exists A0 (j : nat), As = ctx_pi_at (mdesc_kind RE) T A0 /\ T ⊩ A0 : abs_kind_sort (mdesc_kind RE) Typeω@j.
  Proof.
    intros Θs Ξs Hgs Hμ * Hl Hp Hed Ht.
    pose proof (gm_coherent_prefix _ _ _ _ _ (loc_coherent _ _ Hgs _ _ _ Hl) Hp) as HcoE.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
    pose proof (proj2 (loc_entry _ _ Hgs _ _ _ Hl x _) Hent) as HeE.
    destruct E0 as [b pv r A oM | pv [Δ [sm Φy | Ea]] | pv pq k D Φ' | pv Ad Md U | pv pr Rr Φ'];
      cbn [ge_read] in Hed.
    - inversion Hed; subst; cbn in Ht; injection Ht as <-.
      destruct (glu_gctx_embedding_def_tele _ _ _ _ Hμ _ _ _ _ _ _ _ _ _ _ Hl Hp) as (A0 & j & [Heq HA0 _]).
      exists A0, j; split; assumption.
    - exfalso; destruct sm; inversion Hed; subst;
        match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm end;
        destruct RE; cbn in Hm, Ht; first [ contradiction | discriminate ].
    - exfalso; inversion Hed; subst;
        match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm end;
        destruct RE; cbn in Hm, Ht; first [ contradiction | discriminate ].
    - (** A type former of a group *)
      inversion Hed; subst; cbn in Ht; injection Ht as <-.
      cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HuD & _) _].
      destruct (gc_entry_ind _ _ _ _ _ _ _ _ HeE) as [_ Hml].
      pose proof (ind_mlookup_group _ _ Hgs _ _ _ _ Hml) as Hlk.
      assert (Hpar : im_params D Mk = (im_nparams Mk ++ Δ0) ++ T) by (unfold im_params; rewrite HuD, app_assoc; reflexivity).
      destruct (glu_gctx_embedding_ind_former_type _ _ _ _ Hμ _ _ _ _ _ _ Hlk ltac:(eassumption) Hpar) as [j HA0].
      exists (ctx_pi (im_nparams Mk ++ Δ0) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ), j; split; [| exact HA0 ].
      cbn [mdesc_kind ind_former_desc]; rewrite Hpar, ctx_pi_app; reflexivity.
    - (** A definition with a module part: its term part *)
      inversion Hed; subst; cbn in Ht; injection Ht as <-.
      destruct (glu_gctx_embedding_def_mod_tele _ _ _ _ Hμ _ _ _ _ _ _ _ _ _ Hl Hp) as (A0 & j & [Heq HA0 _]).
      exists A0, j; split; assumption.
    - (** A record type former *)
      inversion Hed; subst; cbn in Ht; injection Ht as <-.
      cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HpR & _) _].
      assert (Hlk : record_lookup Θs Ξs (qname_in p x) = Some Rr).
      { unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ HeE), HeE; reflexivity. }
      destruct (glu_gctx_embedding_record_former_type _ _ _ _ Hμ _ _ _ _ Hlk HpR) as [j HA0].
      exists (ctx_pi Δ0 (record_sort Rr)), j; split; [| exact HA0 ].
      cbn [mdesc_kind record_former_desc]; rewrite HpR, ctx_pi_app; reflexivity.
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
      Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H1 ≈ H1 -> not_frame_former H1 x -> mdenote Θ Ξ Γ1 H1 RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
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
    apply (@mdenote_mem_typed GCm _ _ _ _ _ _ Hq1 Hm Ht); intros R0' R0m Γy E rd RE Hm0' HR0m' He Hed Hrd.
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

  (** *** Type formers read as members *)

  (** The member [x] of a saturated module [F] that names the module of a
      group member, under declaration or filed, is the member's type former
      applied to the module's arguments ([eval_sel_global_ind]). *)
  Lemma sel_global_ind_former : forall F TF ΦF x pq k D,
      gc_loc Θ Ξ F = Some (TF, ΦF) -> ind_mlookup Θ Ξ (qname_in F x) = Some (pq, k, D) ->
      forall args r, List.length args = List.length TF -> $*| d_ind pq k nil & args | Θ ⍮ Ξ ↘ r ->
        dm_global F args ·ₜ x Θ ⍮ Ξ ↘ r.
  Proof.
    intros * HlF Hf * Hl Er.
    eapply eval_sel_global_ind;
      [ intros T' Φ' Hl'; rewrite HlF in Hl'; injection Hl' as <- <-; lia
      | rewrite <- qname_in_app; exact (ind_mlookup_resolve _ _ _ _ Hf)
      | rewrite <- qname_in_app; exact Hf
      | exact Er ].
  Qed.

  (** So is a record type's, the record type former ([eval_sel_global_record]). *)
  Lemma sel_global_record_former : forall F TF ΦF x R,
      gc_loc Θ Ξ F = Some (TF, ΦF) -> record_lookup Θ Ξ (qname_in F x) = Some R ->
      forall args r, List.length args = List.length TF -> $*| d_record (qname_in F x) nil & args | Θ ⍮ Ξ ↘ r ->
        dm_global F args ·ₜ x Θ ⍮ Ξ ↘ r.
  Proof.
    intros * HlF Hf * Hl Er.
    eapply eval_sel_global_record;
      [ intros T' Φ' Hl'; rewrite HlF in Hl'; injection Hl' as <- <-; lia
      | rewrite <- qname_in_app; exact (record_lookup_resolve _ _ _ _ Hf)
      | rewrite <- qname_in_app; exact Hf
      | rewrite <- qname_in_app; exact Er ].
  Qed.

  (** The frame of a group member under declaration at [F.x]: its parent
      [F] is a frame too, whose telescope ends the member's parameters
      ([frame_ind_uparams], [gs_find_tele_frame]). *)
  Lemma frame_ind_former_parent : forall F x pq k D Mk,
      gs_find_ind Ξ (qname_in F x) = Some (pq, k, D) -> ind_member D k = Some Mk ->
      exists TF ΦF A1, gc_frame Ξ F = Some (TF, ΦF) /\
        ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ = ctx_pi TF A1.
  Proof.
    intros * Hf HMk.
    destruct (frame_ind_loc _ _ Hg _ _ _ _ Hf) as (U & T0 & Tp & Φp & Mk' & Htl & Hfr & _ & HMk').
    rewrite HMk in HMk'; injection HMk' as <-.
    pose proof (frame_ind_uparams _ _ Hg _ _ _ _ _ _ Hf Hfr) as EUp.
    destruct (gs_find_tele_body _ _ Hg _ _ _ _ Htl) as (ΔU & ΦU & ->).
    unfold gc_frame in Hfr; rewrite Htl in Hfr; injection Hfr as <- <-.
    destruct (gs_find_tele_frame _ _ Hg _ _ _ Htl) as [(Hch & _) | (c & y & V & T1 & Hch & HtF & _ & ET0)];
      [ cbn in Hch; apply (f_equal (@List.length _)) in Hch; rewrite List.length_app in Hch; cbn in Hch; lia |].
    cbn [qname_in q_chain q_unit] in Hch, HtF; apply List.app_inj_tail in Hch as [<- <-].
    replace (q_abs (q_unit F) (q_chain F)) with F in HtF by (destruct F; reflexivity).
    destruct (gs_find_tele_body _ _ Hg _ _ _ _ HtF) as (ΔV & ΦV & ->); cbn [gu_params] in ET0; subst T0.
    exists (ΔV ++ T1), ΦV, (ctx_pi (im_nparams Mk ++ ΔU) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ); split.
    - unfold gc_frame; rewrite HtF; reflexivity.
    - unfold im_params; rewrite <- EUp, List.app_assoc, ctx_pi_app; reflexivity.
  Qed.

  (** The frame of a record type under declaration at [F.x]: its parent
      [F] is a frame too, whose telescope ends the record's parameters
      ([frame_record_split]). *)
  Lemma frame_record_former_parent : forall F x R,
      gs_find_record Ξ (qname_in F x) = Some R ->
      exists TF ΦF A1, gc_frame Ξ F = Some (TF, ΦF) /\ ctx_pi (record_params R) (record_sort R) = ctx_pi TF A1.
  Proof.
    intros * Hf.
    destruct (frame_record_loc _ _ Hg _ _ Hf) as (U & T0 & Tp & Φp & Htl & _ & _).
    destruct (frame_record_split _ _ Hg _ _ _ _ Hf Htl) as (Δr & _ & ERp).
    destruct (gs_find_tele_frame _ _ Hg _ _ _ Htl) as [(Hch & _) | (c & y & V & T1 & Hch & HtF & _ & ET0)];
      [ cbn in Hch; apply (f_equal (@List.length _)) in Hch; rewrite List.length_app in Hch; cbn in Hch; lia |].
    cbn [qname_in q_chain q_unit] in Hch, HtF; apply List.app_inj_tail in Hch as [<- <-].
    replace (q_abs (q_unit F) (q_chain F)) with F in HtF by (destruct F; reflexivity).
    destruct (gs_find_tele_body _ _ Hg _ _ _ _ HtF) as (ΔV & ΦV & ->); cbn [gu_params] in ET0; subst T0.
    exists (ΔV ++ T1), ΦV, (ctx_pi Δr (record_sort R)); split.
    - unfold gc_frame; rewrite HtF; reflexivity.
    - rewrite ERp, ctx_pi_app; reflexivity.
  Qed.

  (** The type of the type former of a group member under declaration is
      closed ([ind_former_desc_scoped]). *)
  Lemma frame_ind_former_type_closed : forall p pq k D Mk σ,
      gs_find_ind Ξ p = Some (pq, k, D) -> ind_member D k = Some Mk ->
      (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[σ] = ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ.
  Proof.
    intros * Hf HMk.
    destruct (frame_ind_loc _ _ Hg _ _ _ _ Hf) as (U & T0 & Tm & Φm & Mk' & _ & _ & Hlp & _).
    pose proof (wf_gstack_closed _ _ Hg) as Hc.
    pose proof (ind_former_desc_scoped pq k D Mk (mdesc_closed nil p Tm Φm nil) 0 (stack_closed_ind _ _ _ _ _ (proj2 Hc) Hf) HMk
                  (conj I (conj (gc_loc_closed _ _ _ _ _ Hc Hlp) (List.Forall_nil (exp_scoped _))))) as HRs.
    pose proof (mdesc_type_sub (ind_former_desc pq k D Mk (mdesc_closed nil p Tm Φm nil)) _ σ eq_refl) as E.
    rewrite (mdesc_closed_sub _ _ HRs) in E; cbn in E; injection E as E; symmetry; exact E.
  Qed.

  (** So is a record type's under declaration ([record_former_desc_scoped]). *)
  Lemma frame_record_former_type_closed : forall p R σ,
      gs_find_record Ξ p = Some R ->
      (ctx_pi (record_params R) (record_sort R))[σ] = ctx_pi (record_params R) (record_sort R).
  Proof.
    intros * Hf.
    destruct (frame_record_loc _ _ Hg _ _ Hf) as (U & T0 & Tm & Φm & _ & _ & Hlp).
    pose proof (wf_gstack_closed _ _ Hg) as Hc.
    destruct (stack_closed_record _ _ _ (proj2 Hc) Hf) as [HF HS0].
    pose proof (record_former_desc_scoped p R (mdesc_closed nil p Tm Φm nil) 0 (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)) HS0
                  (conj I (conj (gc_loc_closed _ _ _ _ _ Hc Hlp) (List.Forall_nil (exp_scoped _))))) as HRs.
    pose proof (mdesc_type_sub (record_former_desc p R (mdesc_closed nil p Tm Φm nil)) _ σ eq_refl) as E.
    rewrite (mdesc_closed_sub _ _ HRs) in E; cbn in E; injection E as E; symmetry; exact E.
  Qed.

  (** *** Module expressions naming a stored module *)

  (** A module expression naming the module stored at [q], every
      description of which reads it with no argument, over a telescope
      glued, is glued at the instances: at every environment its value is
      the stored module at no argument ([eval_path_mod]), glued along the
      telescope ([glu_dmod_global_path]). *)
  Lemma glu_rel_modexp_under_sub_path : forall Γ H pm T Φ,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mod_qname H = Some pm -> gc_loc Θ Ξ pm = Some (T, Φ) -> ⊩ T ->
      (forall Γ1 R, mdenote Θ Ξ Γ1 H R -> mdesc_mod R = Some (mdesc_closed nil pm T Φ nil)) ->
      glu_rel_ctx_types Γ -> glu_rel_modexp_under_sub Γ H.
  Proof.
    intros * HH Hq Hl HT Hd HΓ; constructor; [ exact HΓ |].
    intros Γ' τ Hτ; rewrite (mod_qname_sub _ _ τ Hq).
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH (glu_rel_sub_inst_typed _ _ _ Hτ)) as HH'.
    rewrite (mod_qname_sub _ _ τ Hq) in HH'.
    intros Sb HSb Δ σ ρ Hσ.
    exists (dm_global pm nil); split.
    - rewrite (mod_qname_inv _ _ Hq).
      apply (Evaluation.Modules.eval_path_mod Θ Ξ); intros m1 m2 Ec Hne.
      exact (path_prefix_loc _ _ _ _ (gc_loc_loc _ _ _ _ _ Hl) _ Ec Hne).
    - eapply (@glu_dmod_global_path GCm _ _ _ Hg Hl (gc_loc_tele_all_assumptions _ _ Hg _ _ _ Hl)
                (proj1 (gc_loc_closed _ _ _ _ _ (wf_gstack_closed _ _ Hg) Hl)) HT (List.length T));
        [ cbn; lia | exact (glu_ctx_env_sub_escape HSb _ _ _ Hσ) | exact HH' | |].
      + intros * Hst Hm; rewrite (mod_qname_sub _ _ _ Hq) in Hm; exists nil; exact (Hd _ _ Hm).
      + intros * Hst Hm HR; rewrite (mod_qname_sub _ _ _ Hq) in Hm; rewrite (Hd _ _ Hm) in HR.
        injection HR as <-; constructor.
  Qed.

End Members.

(** ** Saturated global modules, from the source of a sound embedding *)

Section MembersFromSource.
  Variables (Θs : gdeps) (Ξs : gstack) (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hgs : ⊢ᵍ Θs ⍮ Ξs.
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis Hμ : glu_gctx_embedding Θs Ξs Θ Ξ.
  #[local] Instance GCt : GCtx := gc_mk Θ Ξ.
  Import Fixed_Notations.

  (** A term member [x] stored at the source in the module [p] of the
      telescope [T]: what the member of a saturated global module value is
      glued from ([glu_global_member_src]).  It names the path and the
      member only, so that it holds of every module expression whose
      description reads the stored module, at every context. *)
  Record src_stored_member (p : qname) (T : ctx) (x : String.string) (Γe : ctx) (Φs Φ0 : gmod) (E0 : gentry)
      (REs : mdesc) (As : typ) : Prop := mk_src_stored_member
    { (** [p] is stored at the source, of the telescope [T] and the body [Φs] *)
      src_stored_member_loc : loc Θs Ξs p T Φs
      (** [x] is an entry [E0] of the body, after [Φ0] *)
    ; src_stored_member_prefix : gm_prefix_upto Φs x = Some (gm_ext Φ0 x E0)
      (** The entry, read under the telescope in a context [Γe], denotes
          [REs]; the context is arbitrary, as the consumers read the entry
          at any context ([bare_member_exists], [stored_type_over_tele]),
          and [src_stored_member_of_mem] picks [⋅ ++ Γ1], where the
          member's description reads it *)
    ; src_stored_member_denote : edenote Θs Ξs Γe (Some (qname_in p x)) (ge_read T E0) REs
      (** [REs] has the type [As] *)
    ; src_stored_member_type : mdesc_type REs = Some As
      (** of an evaluated kind *)
    ; src_stored_member_kind : evaluated_kind (mdesc_kind REs) }.

  (** The member of a module expression naming no open frame, whose
      description at the source reads the stored module [p] (under outer
      parameters [Θ']), of a type of an evaluated kind, is stored at [p]:
      its entry, read by [mdenote_mem_typed], moved to no context
      ([edenote_closed_move]). *)
  Lemma src_stored_member_of_mem : forall Γ1 H1 RHs Θ' p T Φs Ns1 x Rs A',
      @not_frame_former (gc_mk Θs Ξs) H1 x -> mdenote Θs Ξs Γ1 H1 RHs -> mdesc_mod RHs = Some (mdesc_closed Θ' p T Φs Ns1) ->
      mdenote Θs Ξs Γ1 (me_mem H1 x) Rs -> mdesc_type Rs = Some A' -> evaluated_kind (mdesc_kind Rs) ->
      exists Γe Φ0 E0 REs As, src_stored_member p T x Γe Φs Φ0 E0 REs As.
  Proof.
    intros * Hqs HmHs HRHs Hms Hts Hk.
    apply (@mdenote_mem_typed (gc_mk Θs Ξs) _ _ _ _ _ _ Hqs Hms Hts); intros S0 S0m Γy E rd REs Hs0 HS0m He Hed Hrd.
    rewrite (proj1 (mdenote_functional_all _ _ Hgs) _ _ _ Hs0 _ HmHs), HRHs in HS0m; injection HS0m as <-.
    pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgs HmHs) HRHs) as Hls; cbn in Hls.
    pose proof (loc_closed _ _ Hgs _ _ _ Hls) as HUs.
    destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HUs He) as (-> & HsE & ->).
    pose proof He as He1; cbn in He1.
    destruct (gm_prefix_upto Φs x) as [[| Φ0 z E0 | ] |] eqn:Hps; try discriminate.
    injection He1 as <-.
    destruct (gm_prefix_entry _ _ _ Hps) as (? & ? & Heq & _); injection Heq as <- -> <-.
    cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read REs Ns1) as [R1s |] eqn:Hats; cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
    rewrite mdesc_kind_up, mdesc_kind_named in Hk.
    assert (Hdm : forall Θd A M Rm, REs = mdesc_dm Θd A M Rm -> Θd = nil).
    { intros * ->; inversion Hed; subst; try reflexivity;
        match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm; cbn in Hmm; contradiction end. }
    rewrite (mdesc_kind_ats_read _ _ _ Hdm Hats) in Hk.
    assert (HtRE : exists As, mdesc_type REs = Some As).
    { destruct (mdesc_type_up_inv _ _ _ Hts) as (A1 & HA1 & _); rewrite mdesc_type_named in HA1.
      destruct REs as [r0 A0 om0 | Δ0 Φ1 Φx1 | Θ0 p0 T0 Φ1 Ns0 | Θd A0 M0 Rm0]; cbn; eauto; exfalso;
        rewrite mdesc_ats_read_mod in Hats by exact I;
        assert (Hmm : mdesc_is_mod R1s) by (eapply mdesc_ats_is_mod; [| exact Hats ]; exact I);
        destruct R1s; cbn in Hmm, HA1; first [ contradiction | discriminate ]. }
    destruct HtRE as (As & HtRE).
    exists (⋅ ++ Γ1), Φ0, E0, REs, As; constructor; assumption.
  Qed.

  (** [glu_global_member_value_at], its stored member read at the source
      ([src_stored_member]): the member read bare there is glued at the
      target ([glu_bare_member_at]) and read bare there as grown
      ([mdenote_grow_all]); its stored type is glued over the telescope
      ([stored_type_over_tele]). *)
  Lemma glu_global_member_src : forall p T Γe Φs Φ0 E0 REs As Φ x Γ1 H1 RH Ns1 R A' Δ σ1 args m a (i : nat) P El Tin,
      src_stored_member p T x Γe Φs Φ0 E0 REs As ->
      gc_loc Θ Ξ p = Some (T, Φ) -> List.length args = List.length T ->
      Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H1 ≈ H1 -> not_frame_former H1 x -> mdenote Θ Ξ Γ1 H1 RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
      mdenote Θ Ξ Γ1 (me_mem H1 x) R -> mdesc_type R = Some A' ->
      Δ ⊢ˢ σ1 : Γ1 ->
      glu_tele_args Δ (List.rev T) nil nil (List.map (fun N => N[σ1]) Ns1) args ->
      dm_global p args ·ₜ x Θ ⍮ Ξ ↘ m ->
      (forall h b, per_dmod h (dm_global p args) -> dmod_mem_type h x b -> exists j, Dom b ≈ a ∈ per_univ j) ->
      not_level_sort a -> DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ Tin ® P ->
      (exists l : nat, Δ ⊢ A'[σ1] ≈ Tin : abs_kind_sort (domain_kind a) Typeω@l) /\ Δ ⊢ (a_mem H1 x)[σ1] : Tin ® m ∈ El.
  Proof.
    intros * [Hls Hps Hed HtRE Hk] Hgl Hlen HH1 Hq1 HmH HRH Hm Ht Hσ1 Hargs Hsel Hrel Hnl Hga HTin.
    (** Read bare at the source, glued at the target *)
    pose proof (gc_loc_of_loc _ _ Hgs _ _ _ Hls) as Hgls.
    destruct (bare_member_exists _ _ Hgs _ _ _ _ _ _ _ _ Hgls Hps Hed ltac:(rewrite HtRE; discriminate))
      as (R0s & HR0s & HtR0s & HkR0s).
    rewrite HtRE in HtR0s; rewrite <- HkR0s in Hk.
    pose proof (glu_bare_member_at _ _ _ _ _ _ _ _ _ _ Hgs Hμ Hgls HR0s HtR0s Hk) as HGa.
    (** Read bare at the target, grown *)
    pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
    pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hsub.
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HR0s) as (R0 & HR0 & Hgr).
    pose proof (mdesc_grows_ty _ _ _ _ _ _ _ Hgr HtR0s) as HtR0.
    assert (HkR0 : mdesc_kind R0 = mdesc_kind R0s)
      by (destruct Hgr; [ reflexivity | cbn in HtR0s; discriminate | reflexivity ]).
    (** Its stored type, glued over the telescope *)
    destruct (stored_type_over_tele _ _ _ _ Hgs Hμ _ _ _ _ _ _ _ _ _ Hls Hps Hed HtRE) as (A0 & j & HAs & HA0).
    rewrite <- HkR0s, <- HkR0 in HAs, HA0.
    rewrite <- HkR0 in Hk.
    exact (glu_global_member_value_at _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hgl Hlen HR0 HtR0 Hk HGa HAs HA0 HH1 Hq1 HmH HRH Hm Ht Hσ1 Hargs Hsel Hrel Hnl Hga HTin).
  Qed.

  (** What [glu_mem_rec] proves of a module value [h] glued as [H[σ]]
      over [Δ] ([glu_dmod Δ σ Γ H h]): a term member [x] of [H] typed at
      the target, stored at the source in every stored module [H]'s
      description reads, at an environment [ρ] of [Γ] where [H]'s value
      is related to [h], is glued at every type [Tin] glued at a value
      [a2] related to its type's there, as [h]'s member, its type equal to
      [Tin]. *)
  #[local] Definition glu_mem_goal (Δ : ctx) (σ : sub) (Γ : ctx) (H : modexp) (h : dmod) : Prop :=
    forall x R A Srt RΓ ρ h' a2' a2 (j : universe_index) m (k : nat) P2 El2 Tin,
      (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ -> not_frame_former H[ζ]ᵐ x) ->
      (forall RH Θ' p T Φ Ns, mdenote Θ Ξ Γ H RH -> mdesc_mod RH = Some (mdesc_closed Θ' p T Φ Ns) ->
         exists Γe Φs Φ0 E0 REs As, src_stored_member p T x Γe Φs Φ0 E0 REs As) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A ->
      type_sort Srt -> Γ ⊢ A : Srt -> Γ ⊢ a_mem H x : A ->
      EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h' -> per_dmod h h' ->
      ⟦ A ⟧ ρ ↘ a2' -> Dom a2' ≈ a2 ∈ per_univ j -> evaluated_kind (domain_kind a2) ->
      h ·ₜ x Θ ⍮ Ξ ↘ m ->
      DG a2 ∈ glu_univ_elem k ↘ P2 ↘ El2 -> Δ ⊢ Tin ® P2 ->
      (exists l : nat, Δ ⊢ A[σ] ≈ Tin : abs_kind_sort (domain_kind a2) Typeω@l) /\ Δ ⊢ (a_mem H x)[σ] : Tin ® m ∈ El2.

  (** A saturated global module value: its arguments read off the module
      part through the identity factorization, its member glued from the
      member stored at the source ([glu_global_member_src]). *)
  Lemma glu_mem_global_case : forall Δ σ Γ H p T Φ args,
      Δ ⊢ˢ σ : Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> gc_loc Θ Ξ p = Some (T, Φ) -> List.length args = List.length T ->
      (forall Δ' φ Γ1 ζ σ1 RH, glu_sub_through Δ σ Γ Δ' φ Γ1 ζ σ1 ->
         mdenote Θ Ξ Γ1 H[ζ]ᵐ RH -> exists Ns1, mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1)) ->
      (forall Δ' φ Γ1 ζ σ1 RH Ns1, glu_sub_through Δ σ Γ Δ' φ Γ1 ζ σ1 ->
         mdenote Θ Ξ Γ1 H[ζ]ᵐ RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
         glu_tele_args Δ' (List.rev T) nil nil (List.map (fun N => N[σ1]) Ns1) args) ->
      glu_mem_goal Δ σ Γ H (dm_global p args).
  Proof.
    intros * Hσ HH Hgl Hlen Hd Ha; unfold glu_mem_goal.
    intros x R A Srt RΓ ρ h' a2' a2 j m k P2 El2 Tin Hnf Hsrc HmR HtR HS HAt HxA HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel Hga2 HTin.
    (** The module's description, the stored module at arguments read off
        through the identity factorization *)
    destruct (me_denotes _ _ _ _ _ HH) as (RH & Rm & HmH & HRm).
    pose proof (glu_sub_through_id _ _ _ Hσ) as Hst.
    assert (HmH' : mdenote Θ Ξ Γ H[Id]ᵐ RH) by (rewrite modexp_sub_id; exact HmH).
    destruct (Hd _ _ _ _ _ _ Hst HmH') as [Ns1 HNs1].
    pose proof (Ha _ _ _ _ _ _ _ Hst HmH' HNs1) as Hargs.
    destruct (Hsrc _ _ _ _ _ _ HmH HNs1) as (Γe & Φs & Φ0 & E0 & REs & As & Hsm).
    pose proof (Hnf _ _ (wf_sub_id _ _ _ (presup_modexp_eq_ctx HH))) as Hnf0; rewrite modexp_sub_id in Hnf0.
    (** The completeness facts of the member *)
    destruct (mem_value_facts _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ HH HmR HtR HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel) as (_ & Hty & _).
    pose proof (type_value_not_level_sort _ _ _ _ _ _ _ _ _ _ HAt HS HRΓ Hρ Ea2' Ha2) as Hnl.
    exact (glu_global_member_src _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hsm Hgl Hlen HH Hnf0 HmH HNs1 HmR HtR Hσ Hargs Hsel Hty Hnl Hga2 HTin).
  Qed.

  (** A saturated body value: its member is glued at the entry's type
      ([glu_mem_body_value_at]), with the completeness facts at the value
      ([mem_value_facts]). *)
  Lemma glu_mem_body_case : forall Δ σ Γ H sm Φ ρh,
      glu_dmod Δ σ Γ H (dm_local nil (md_body sm Φ) ρh) -> glu_mem_goal Δ σ Γ H (dm_local nil (md_body sm Φ) ρh).
  Proof.
    intros * Hgd; unfold glu_mem_goal.
    intros x R A Srt RΓ ρ h' a2' a2 j m k P2 El2 Tin Hnf Hsrc HmR HtR HS HAt HxA HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel Hga2 HTin.
    assert (HH : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H) by (inversion Hgd; assumption).
    destruct (mem_value_facts _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ HH HmR HtR HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel) as (Hhh & Hty & _).
    exact (glu_mem_body_value_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgd HmR HtR HS HAt Hsel Hhh Hty Hev Hga2 HTin).
  Qed.

  (** A value lacking a parameter: its member is a member closure, glued
      at the [Π] the member's type is ([mem_app_shape]) by its values at
      glued arguments, the members of the value's applications, glued by
      recursion ([glu_dmod_fun]'s application clause), at the
      application's member read at the extended context; the member
      applied is that member ([mem_app_shape_eq]).  The type is the
      [Π] glued: its domain by the value's next parameter's gluing
      ([glu_typ_to_target]), its codomain at the variable. *)
  Lemma glu_mem_fun_case : forall Δ σ Γ H h a,
      Δ ⊢ˢ σ : Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> next_param h a ->
      (forall Δ' φ Γ1 ζ σ1 RH, glu_sub_through Δ σ Γ Δ' φ Γ1 ζ σ1 ->
         mdenote Θ Ξ Γ1 H[ζ]ᵐ RH -> exists T B T1, glu_dmod_next_param_desc Δ' Γ1 σ1 RH a T B T1) ->
      (forall Δ' φ Γ1 ζ σ1 RH T B T1 Srt, glu_sub_through Δ σ Γ Δ' φ Γ1 ζ σ1 ->
         mdenote Θ Ξ Γ1 H[ζ]ᵐ RH -> mdesc_mod_tele RH = Some T -> tele_view T = Some (B, T1) ->
         type_sort Srt -> Γ1 ⊢ B : Srt ->
         forall N c hc (i : nat) P El, DG a ∈ glu_univ_elem i ↘ P ↘ El ->
           Δ' ⊢ B[σ1] ® P -> Δ' ⊢ N : B[σ1] ® c ∈ El ->
           $ᵐ| h & c | Θ ⍮ Ξ ↘ hc ->
           glu_mem_goal Δ' (σ1 ,, N) (Γ1 ▹{domain_kind a} B) (me_app H[ζ]ᵐ[Wk]ᵐ #0) hc) ->
      glu_mem_goal Δ σ Γ H h.
  Proof.
    intros * Hσ HH Hnp Hpar Happ; unfold glu_mem_goal.
    intros x R A Srt RΓ ρ h' a2' a2 j m k P2 El2 Tin Hnf Hsrc HmR HtR HS HAt HxA HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel Hga2 HTin.
    (** The module's next parameter, typed at the target *)
    destruct (me_denotes _ _ _ _ _ HH) as (RH & Rm & HmH & HRm).
    pose proof (glu_sub_through_id _ _ _ Hσ) as Hst.
    assert (HmH' : mdenote Θ Ξ Γ H[Id]ᵐ RH) by (rewrite modexp_sub_id; exact HmH).
    destruct (Hpar _ _ _ _ _ _ Hst HmH') as (TH & BH & T1H & [HTH HvH HgluH]).
    destruct (mod_next_param_typed _ _ Hg _ _ _ _ _ _ HH HmH HTH HvH) as (SrtB & HSB & HBt).
    assert (Hsk : exists κB, sort_kind SrtB κB) by (destruct HSB; eexists; econstructor).
    destruct Hsk as [κB Hsk].
    assert (HΓB : ⊢ Γ ▹{κB} BH) by (eapply wf_ctx_extend; eassumption).
    assert (HWk : Γ ▹{κB} BH ⊢ˢ Wk : Γ) by (eapply wf_sub_shift; exact HΓB).
    (** The member of the module applied to the variable, at the target *)
    pose proof (wf_me_app_shift _ _ _ _ _ _ _ _ HH HmH HTH HvH HBt HSB Hsk) as HHapp.
    pose proof (Hnf _ _ HWk) as HnfW.
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH HmR HWk) as HmRw.
    pose proof (mdesc_type_sub _ _ Wk HtR) as HtRw.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HxA HWk) as HxAw; cbn [exp_sub] in HxAw.
    destruct (@wf_exp_eq_mem_app GCt Hg _ _ _ _ _ _ HHapp HnfW HmRw HtRw HxAw) as (B1 & C1 & R' & [Hprm Hpi Hmem' Hmty Heq]).
    pose proof (Hprm _ _ _ _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HH HmH HWk)
                  (mdesc_mod_tele_sub _ _ Wk _ (wf_mdenote_scoped _ _ _ _ _ _ HH HmH) HTH)
                  (tele_view_sub_some _ _ _ Wk HvH)) as EB1; subst B1.
    destruct Hpi as (κ & κc & HApi).
    destruct A; cbn in HApi; try discriminate.
    injection HApi as <- <- EB EC; subst C1.
    apply (f_equal (fun Z => Z[Id,,#0])) in EB; cbn beta in EB.
    rewrite !exp_sub_sub, !(exp_sub_sb_eq _ _ _ (sb_shift_extend Id _)), !exp_sub_id in EB; subst A1.
    rename A2 into C, a0 into κd, a1 into κc.
    clear Hprm HtRw HxAw HmRw HmH' HRm Rm Hst.
    (** The type's value: a [Π], related to the glued one *)
    pose proof Ea2' as Ea2; inversion Ea2; subst.
    match goal with Hb : ⟦ BH ⟧ ρ ↘ ?b |- _ => rename Hb into EaB; rename b into aB end.
    destruct Ha2 as [Rj HRj].
    pose proof (per_univ_elem_kind _ _ _ _ HRj) as Hk2; cbn [domain_kind] in Hk2; rewrite <- Hk2 in Hev; clear Hk2.
    destruct (per_univ_pi_left_shape _ _ _ _ _ _ _ _ Hev HRj) as (aB2 & ρ2 & C2 & ->).
    destruct (per_univ_pi_parts _ _ _ _ _ _ _ _ _ _ Hev HRj) as (inj & HaBj & Hcod).
    destruct (per_univ_pi_kinds _ _ _ _ _ _ _ _ Hev HRj) as (HkaB & Hpk).
    (** The glued [Π] and the type glued at it *)
    destruct (glu_univ_elem_per_univ _ _ _ _ Hga2) as [Rk HRk].
    destruct (per_univ_pi_parts _ _ _ _ _ _ _ _ _ _ Hev HRk) as (ink & HaBk & _).
    destruct (glu_univ_elem_pi_clean_inversion1 HaBk Hev Hga2) as (IP & IEl & OP & OEl & elr & HgaB2 & HgC2 & Hpel & HP2 & HEl2).
    pose proof (proj1 (HP2 _ _) HTin) as HTinP.
    inversion HTinP as [? ? IT OT HTeq HIT HOT HIP HOP]; subst; clear HTinP.
    cbn [domain_kind].
    (** The kinds: the parameter's, the domain's and the value's next
        parameter's are one *)
    destruct (FunctionCases.rel_type_kind_of_sort_kind Hsk (completeness_fundamental_exp _ _ _ HBt) _ HRΓ _ _ Hρ)
      as (aB0 & EaB0 & HkB).
    pose proof (functional_eval_exp _ _ _ _ EaB0 EaB) as ->.
    destruct (next_param_value_rel _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH HmH HTH HvH HSB HBt Hsk HRΓ Hρ Eh' Hhh' Hnp EaB)
      as [ia [Ra HaaB]].
    assert (Eka : κB = domain_kind a) by (rewrite (per_univ_elem_kind _ _ _ _ HaaB); symmetry; exact HkB).
    rewrite HkB in *; subst κB; clear EaB0.
    (** The domain: the parameter's type at [σ], glued at the value's next
        parameter, is the glued [Π]'s domain *)
    destruct (HgluH _ (sort_kind_type_sort _ _ Hsk) HBt) as (ia' & Pa & Ela & [Hga HBσ]).
    pose proof (per_univ_elem_pi_domain_not_level_sort Hev HRk) as HnlB2.
    pose proof (per_univ_trans' _ _ _ _ _ (ex_intro _ Ra HaaB) (ex_intro _ inj HaBj)) as Hab2.
    assert (Hnla : not_level_sort a)
      by (destruct Hab2 as [Rab Hab]; exact (proj2 (per_univ_elem_not_level_sort_iff _ _ _ _ Hab) HnlB2)).
    pose proof (HIP _ _ (kripke_id _ (wf_sub_dom _ _ _ _ _ Hσ))) as HITP; rewrite exp_wk_id in HITP.
    destruct (glu_typ_to_target Hab2 Hga HgaB2 Hnla HBσ HITP) as [ld HBIT].
    assert (EkB2 : domain_kind aB2 = domain_kind a)
      by (destruct Hab2 as [Rab Hab]; symmetry; exact (per_univ_elem_kind _ _ _ _ Hab)).
    rewrite EkB2 in HBIT; rewrite Eka in *.
    (** The codomain, typed, and the member type at the extension equal
        to it *)
    destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HAt) as [Sd lc Hskd HBd HCt _].
    pose proof (codomain_var0_eq _ _ _ _ _ _ HBd Hskd (type_sort_abs_kind _ _ (type_sort_universe lc)) HCt) as HCeq.
    (** The application reads the stored modules the module reads
        ([mdesc_at_closed_back], [mdesc_sub_closed_back]) *)
    assert (Hsrc' : forall RK Θ' p T Φ Ns, mdenote Θ Ξ (Γ ▹{domain_kind a} BH) (me_app H[Wk]ᵐ #0) RK ->
              mdesc_mod RK = Some (mdesc_closed Θ' p T Φ Ns) -> exists Γe Φs Φ0 E0 REs As, src_stored_member p T x Γe Φs Φ0 E0 REs As).
    { intros * HmK HRK.
      inversion HmK as [? ? ? ? ? Hq | ? ? ? ? ? ? ? ? ? Hq | | | ? ? ? R0 ? Hm0 Hat | | ? ? ? ? ? ? Hq]; subst;
        try (cbn in Hq; discriminate).
      rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm0 _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HH HmH HWk)) in Hat.
      destruct (mdesc_at_closed_back _ _ _ _ _ _ _ _ Hat HRK) as (Θ'' & Ns' & HmW).
      destruct (mdesc_sub_closed_back _ _ _ _ _ _ _ HmW) as (Θ3 & Ns3 & HmRH).
      exact (Hsrc _ _ _ _ _ _ HmH HmRH). }
    pose proof (presup_exp_eq_right Heq) as HxA'.
    pose proof (presup_exp_eq_left HCeq) as HCt'.
    pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HaBj HaBk) as Eij.
    assert (HaBjj : per_univ_elem j inj aB aB)
      by (pose proof (@per_univ_PER _ j inj) as HP; etransitivity; [ exact HaBj | symmetry; exact HaBj ]).
    (** At every glued argument, the member closure applied is glued as the
        member of the application *)
    assert (Hstep : forall Δ' φ N n (equiv_n : ink n n), Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ N : IT[φ]ʷ ® n ∈ IEl ->
              exists r, $| m & n | Θ ⍮ Ξ ↘ r /\
                ((exists l : nat, Δ' ⊢ C[sb_wk σ φ,,N] ≈ OT[sb_of_wk φ,,N] : abs_kind_sort κc Typeω@l) /\
                 Δ' ⊢ (a_mem H x)[sb_wk σ φ] $ N : OT[sb_of_wk φ,,N] ® r ∈ OEl n equiv_n)).
    { intros Δ' φ N n Hn Hφ HN.
      assert (Hnj : inj n n) by (apply Eij; exact Hn).
      (** The environment extended by the argument *)
      destruct (ctx_env_extend_at _ _ _ _ _ _ _ _ _ _ _ _ HBt Hsk HRΓ Hρ EaB HaBjj Hnj) as [HRΓb Hρ''].
      destruct (modexp_wk_value_rel _ _ _ _ _ _ _ _ _ _ _ _ HΓB HH HRΓ Hρ HRΓb Hρ'' Eh') as (h1 & Eh1 & Hh1h').
      destruct (next_param_wk_at _ _ Hg _ _ _ _ _ _ _ _ _ _ HH HmH HTH HvH HSB HBt Hsk HRΓb Hρ'')
        as [h1' ap1 b1 ib Rb1 Eh1' Hn1 Eb1 Hab1].
      pose proof (functional_eval_modexp _ _ _ _ Eh1' Eh1) as ->.
      pose proof (proj1 per_dmod_trans_all _ _ Hhh' _ (proj1 per_dmod_sym_all _ _ Hh1h')) as Hhh1.
      destruct (per_dmod_fun_parts _ _ _ _ Hhh1 Hnp Hn1) as (iR & RR & HaR & Happs).
      assert (HnR : RR n n).
      { pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HaR HaaB) as E1.
        pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HaaB HaBjj) as E2.
        apply E1, E2; exact Hnj. }
      destruct (Happs _ _ HnR) as (hc & Ehc & Hhc).
      (** The application's value at the extended environment *)
      destruct (per_dmod_fun_parts _ _ _ _ (proj1 per_dmod_sym_all _ _ Hhh1) Hn1 Hnp) as (iR' & RR' & HaR' & Happs').
      assert (HnR' : RR' n n) by (apply (per_univ_elem_cross_irrel _ _ _ _ _ _ _ HaR HaR'); exact HnR).
      destruct (Happs' _ _ HnR') as (hc1 & Ehc1 & _).
      pose proof (Hhc _ Ehc1) as Hhcc.
      assert (Ehc'' : ⟦ me_app H[Wk]ᵐ #0 ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_value aB ↘ hc1)
        by (econstructor; [ exact Eh1 | econstructor | exact Ehc1 ]).
      (** The codomain's values *)
      destruct (Hcod _ _ Hnj) as (bC & b & EbC & Eb & HbCb).
      pose proof (HgC2 _ Hn _ Eb) as Hgb.
      destruct (eq_type_value_rel _ _ _ _ _ _ _ HCeq (type_sort_abs_kind _ _ (type_sort_universe lc)) HRΓb Hρ'' EbC)
        as (bK & iK & EbK & HbK).
      pose proof (per_univ_trans' _ _ _ _ _ HbK HbCb) as HbKb.
      assert (Hkb : domain_kind b = κc).
      { destruct (FunctionCases.rel_type_kind_of_sort_kind (sort_kind_abs_kind_sort _ _) (completeness_fundamental_exp _ _ _ HCt) _ HRΓb _ _ Hρ'')
          as (bC0 & EbC0 & HkbC).
        pose proof (functional_eval_exp _ _ _ _ EbC0 EbC) as ->.
        destruct HbCb as [Rbb Hbb]; rewrite <- (per_univ_elem_kind _ _ _ _ Hbb); exact HkbC. }
      (** The member of the application, from completeness *)
      destruct (mem_valid_at _ _ Hg _ _ _ _ _ _ _ HHapp Hmem' Hmty HRΓb Hρ'') as [hc0 b0 i0 R0 Ehc0 Eb0 HR0 Hhas _ _].
      pose proof (functional_eval_modexp _ _ _ _ Ehc0 Ehc'') as ->.
      pose proof (functional_eval_exp _ _ _ _ Eb0 EbK) as ->.
      assert (HevK : evaluated_kind (domain_kind bK))
        by (destruct HbKb as [Rkb Hkb']; rewrite (per_univ_elem_kind _ _ _ _ Hkb'), Hkb; exact Hev).
      destruct (Hhas HevK _ Hhcc) as [r r' Er _ _].
      (** The recursion, at the factorization through the identity *)
      pose proof (glu_sub_through_wk Hφ (glu_sub_through_id _ _ _ (wf_sub_sb_wk Hσ Hφ))) as Hstφ.
      assert (HmHφ : mdenote Θ Ξ Γ H[Id]ᵐ RH) by (rewrite modexp_sub_id; exact HmH).
      destruct (Hpar _ _ _ _ _ _ Hstφ HmHφ) as (TH' & BH' & T1H' & [HTH' HvH' HgluH']).
      rewrite HTH in HTH'; injection HTH' as <-; rewrite HvH in HvH'; injection HvH' as <- <-.
      destruct (HgluH' _ (sort_kind_type_sort _ _ Hsk) HBt) as (ib' & Pb & Elb & [Hgab HBφ]).
      (** The argument, glued at the value's next parameter *)
      assert (HB2a : Dom aB2 ≈ a ∈ per_univ ia)
        by (destruct Hab2 as [Rab Hab]; exists Rab; pose proof (@per_univ_PER _ ia Rab) as HP; symmetry; exact Hab).
      destruct (glu_elem_to_target HB2a HgaB2 Hgab HnlB2 HN HBφ) as [_ HNa].
      pose proof (Happ _ _ _ _ _ _ _ _ _ _ Hstφ HmHφ HTH HvH (sort_kind_type_sort _ _ Hsk) HBt N n hc ib' Pb Elb Hgab HBφ HNa Ehc) as IH.
      unfold glu_mem_goal in IH; rewrite modexp_sub_id in IH.
      destruct (IH x R' _ _ _ _ _ _ _ _ _ _ _ _ _
                  ltac:(intros; cbn [modexp_sub]; apply not_frame_former_of_none; reflexivity)
                  Hsrc' Hmem' Hmty (type_sort_abs_kind _ _ (type_sort_universe lc)) HCt' HxA'
                  HRΓb Hρ'' Ehc'' Hhcc EbK HbKb ltac:(rewrite Hkb; exact Hev) Er Hgb (HOP _ _ _ _ Hφ HN Hn))
        as [(lI & HIeq) HIglu].
      exists r; split; [ exact (selt_appm_comm _ _ Hnp _ _ Hsel _ _ _ Ehc Er) |].
      rewrite exp_sub_q_shift_var0_extend, Hkb in HIeq.
      split; [ exists lI; exact HIeq |].
      (** The member applied is the member of the application *)
      pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgab _ _ _ _ HNa) as HNt.
      assert (Hσφ : Δ' ⊢ˢ sb_wk σ φ,,N : Γ ▹{domain_kind a} BH)
        by (eapply wf_sub_extend; [ exact (wf_sub_sb_wk Hσ Hφ) | exact HBt | exact Hsk | exact HNt ]).
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Heq Hσφ) as HeqN.
      cbn [exp_sub] in HeqN.
      rewrite modexp_sub_shift_extend, exp_sub_q_shift_var0_extend in HeqN.
      cbn [exp_sub].
      eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hgb | exact HIglu |].
      apply wf_exp_eq_sym; exact (wf_exp_eq_conv_kind _ _ _ _ _ _ _ HeqN HIeq).
    }
    (** The type: its codomain at the variable is the glued [Π]'s *)
    pose proof (kripke_shift _ _ _ (presup_exp_ctx HOT)) as Hφv.
    pose proof (var0_glu_elem HgaB2 HnlB2 HITP) as Hv; rewrite EkB2 in Hv.
    pose proof (var_per_elem (length Δ) HaBk HnlB2) as Hvar.
    destruct (Hstep _ _ _ _ Hvar Hφv Hv) as (r0 & _ & (lv & Hceq) & _).
    rewrite <- exp_sub_q_extend_wk, <- !exp_sub_wk_q_extend in Hceq.
    pose proof (presup_exp_eq_left HBIT) as HBσt.
    assert (ESrt : SrtB[σ] = SrtB) by (destruct HSB; reflexivity).
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HBt Hσ) as HBσs; rewrite ESrt in HBσs.
    pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hσ HBt Hsk HBσs) as Hq.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCt Hq) as HCq; rewrite abs_kind_sort_sub in HCq; cbn [exp_sub] in HCq.
    pose proof (ctx_sub_extend_eq _ _ _ _ _ _ _ HBσt (presup_exp_eq_right HBIT) (sort_kind_abs_kind_sort _ _) HBIT) as Hsubctx.
    pose proof (ctxsub_exp _ _ _ _ _ _ (ctx_sub_escape _ _ _ _ Hsubctx) HCq) as HCq'.
    pose proof (codomain_wk_var0_eq _ _ _ _ _ _ HIT (sort_kind_abs_kind_sort _ _) (type_sort_abs_kind _ _ (type_sort_universe _)) HCq') as E1.
    pose proof (codomain_wk_var0_eq _ _ _ _ _ _ HIT (sort_kind_abs_kind_sort _ _) (type_sort_abs_kind _ _ (type_sort_universe _)) HOT) as E2.
    set (n0 := Nat.max lv (Nat.max lc (large_level k))).
    assert (HCOT : Δ ▹{domain_kind a} IT ⊢ C[q σ] ≈ OT : abs_kind_sort κc Typeω@n0).
    { eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact (abs_kind_sort_eq_lift _ _ _ _ lc n0 ltac:(unfold n0; lia) E1) |].
      eapply wf_exp_eq_trans; [ exact (abs_kind_sort_eq_lift _ _ _ _ lv n0 ltac:(unfold n0; lia) Hceq) |].
      exact (abs_kind_sort_eq_lift _ _ _ _ (large_level k) n0 ltac:(unfold n0; lia) E2). }
    pose proof (pi_eq_of_parts _ _ _ _ _ _ _ _ _ HBIT HCOT Hpk) as HΠ.
    set (n1 := Nat.max (Nat.max ld n0) (large_level k)).
    assert (Hout : Δ ⊢ (a_pi (domain_kind a) κc BH C)[σ] ≈ Tin : abs_kind_sort κc Typeω@n1).
    { cbn [exp_sub].
      eapply wf_exp_eq_trans; [ exact (abs_kind_sort_eq_lift _ _ _ _ (Nat.max ld n0) n1 ltac:(unfold n1; lia) HΠ) |].
      apply wf_exp_eq_sym; exact (abs_kind_sort_eq_lift _ _ _ _ (large_level k) n1 ltac:(unfold n1; lia) HTeq). }
    split; [ exists n1; exact Hout |].
    (** The member, glued at the [Π] by its values at glued arguments *)
    apply HEl2; econstructor.
    - exact (wf_exp_conv_kind _ _ _ _ _ _ (sub_preserves_exp _ _ _ _ _ _ _ HxA Hσ) Hout).
    - destruct (mem_value_facts _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ HH HmR HtR HRΓ Hρ Eh' Hhh' Ea2' (ex_intro _ Rj HRj) Hev Hsel)
        as (_ & _ & Hmm).
      exact (Hmm _ _ Hpel).
    - exact HTeq.
    - exact HIT.
    - exact HOT.
    - exact HIP.
    - intros Δ' φ N n Hφ HN equiv_n.
      destruct (Hstep _ _ _ _ equiv_n Hφ HN) as (r & Er & _ & Hr).
      exists r; split; [ exact Er | rewrite exp_wk_sub; exact Hr ].
  Qed.

  (** A term member of a glued module value is glued as the member, at
      every type glued at its type's value: by induction on the gluing,
      the application clause giving the recursion of [glu_mem_fun_case]. *)
  Lemma glu_mem_rec : forall Δ σ Γ H h, glu_dmod Δ σ Γ H h -> glu_mem_goal Δ σ Γ H h.
  Proof.
    enough (Hall : (forall Δ σ Γ H h, glu_dmod Δ σ Γ H h -> glu_mem_goal Δ σ Γ H h) /\
                   (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True)) by exact (proj1 Hall).
    apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
    - intros * Hσ HH Hl Hlen Hd Ha _; eapply glu_mem_global_case; eassumption.
    - intros * Hσ HH Hmem Hsubm _; apply glu_mem_body_case; econstructor; eassumption.
    - intros * Hσ HH Hnp Hpar _ IHapp; eapply glu_mem_fun_case; eassumption.
  Qed.

  (** The member of a module expression whose value is glued, in a context
      ([glu_modexp_at]), at a type glued there, is glued: at a proposition
      by its typing ([glu_rel_exp_proof]); at a type of an evaluated kind,
      at every glued environment, as the member of the module's value
      ([glu_mem_rec]), at the type at the environment, the member's value
      read off completeness ([mem_valid_at]). *)
  Lemma glu_rel_exp_mem_at : forall Γ H x R A Srt,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
      (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ -> not_frame_former H[ζ]ᵐ x) ->
      (forall RH Θ' p T Φ Ns, mdenote Θ Ξ Γ H RH -> mdesc_mod RH = Some (mdesc_closed Θ' p T Φ Ns) ->
         exists Γe Φs Φ0 E0 REs As, src_stored_member p T x Γe Φs Φ0 E0 REs As) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A ->
      type_sort Srt -> Γ ⊢ A : Srt -> Γ ⊢ a_mem H x : A ->
      glu_modexp_at Γ H -> Γ ⊩ A : Srt -> Γ ⊩ a_mem H x : A.
  Proof.
    intros * HH Hnf Hsrc Hm Ht HS HAt Hx HHg HAg.
    assert (HSk : Srt = Propₘ \/ exists κ (i : nat), evaluated_kind κ /\ Srt = abs_kind_sort κ Typeω@i)
      by (destruct HS; [ right; exists ak_relevant, i | left | right; exists ak_level, 0 ]; (split; [ constructor |]) || idtac; reflexivity).
    destruct HSk as [-> | (κ & i & Hκ & ->)]; [ exact (Soundness.UniverseCases.glu_rel_exp_proof HAg Hx) |].
    destruct (presup_ctx_glu_rel_exp HAg) as [Sb HSb].
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HSb |].
    intros Δ σ ρ Hσ.
    destruct (Soundness.UniverseCases.glu_rel_exp_kind_sort_large_inversion HSb HAg _ _ _ Hσ) as [HAσ (a & Ea & Ha & HaP)].
    destruct (per_univ_glu_univ_elem _ _ Ha) as (P & El & Hga).
    pose proof (HaP _ _ Hga) as HAP.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hga HAP HAσ) as [Hka _].
    assert (Hev : evaluated_kind (domain_kind a)) by (rewrite Hka; exact Hκ).
    destruct (HHg _ HSb _ _ _ Hσ) as (h & Eh & Hgd).
    destruct (glu_ctx_env_per_ctx_env HSb) as [RΓ HRΓ].
    pose proof (glu_ctx_env_per_env HSb HRΓ Hσ) as Hρ.
    destruct (Completeness.UnitCases.rel_modexp_at _ _ _ _ _ (proj2 (proj2 (@completeness_fundamental_modules GCt)) _ _ _ HH) HRΓ _ _ Hρ)
      as (h0 & h0' & Eh0 & Eh0' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ Eh0 Eh) as ->; pose proof (functional_eval_modexp _ _ _ _ Eh0' Eh) as ->.
    destruct (mem_valid_at _ _ Hg _ _ _ _ _ _ _ HH Hm Ht HRΓ Hρ) as [h1 a1 i1 R1 Eh1 Ea1 HR1 Hhas _ _].
    pose proof (functional_eval_modexp _ _ _ _ Eh1 Eh) as ->; pose proof (functional_eval_exp _ _ _ _ Ea1 Ea) as ->.
    destruct (Hhas Hev _ Hhh) as [m m' Em _ _].
    destruct (glu_mem_rec _ _ _ _ _ Hgd x R _ _ RΓ ρ h a a i m i P El _ Hnf Hsrc Hm Ht HS HAt Hx HRΓ Hρ Eh Hhh Ea Ha Hev Em Hga HAP)
      as [_ Hglu].
    econstructor; [ exact Ea | | exact Hga | exact Hglu ].
    unfold glu_term_value; destruct (domain_kind a) eqn:Ek; try (inversion Hev; fail); exact (eval_mem_of_sel _ _ _ _ _ Eh Em).
  Qed.

  (** The member [x] of the frame [F], a type former under declaration of
      the value [f0] ([d_ind pq k nil] or [d_record p nil]), at a module
      value given [args] of [F]'s telescope: it is glued as a term [Mm]
      equal to a term [Mr] glued at the former applied to [args], at its
      type's value [a], the value of [ctx_pi Trem S] for the parameters
      [Trem] still missing.  By induction on them: saturated, the member
      is the former applied ([sel_sat]); lacking one, it is a member
      closure, glued at the [Π] by its values at glued arguments, the
      members of the module given them, by induction, against the former
      applied to them. *)
  Lemma glu_frame_former_apps : forall F T Φ x f0,
      gc_loc Θ Ξ F = Some (T, Φ) ->
      (forall args r, List.length args = List.length T -> $*| f0 & args | Θ ⍮ Ξ ↘ r -> dm_global F args ·ₜ x Θ ⍮ Ξ ↘ r) ->
      forall n args Trem S ρT, List.length args + n = List.length T -> all_assumptions Trem -> List.length Trem = n ->
      forall Δ Mm Mr Tin rr a (i : nat) P El R,
        ⟦ ctx_pi Trem S ⟧ ρT ↘ a ->
        Δ ⊢ Mm ≈ Mr : Tin -> $*| f0 & args | Θ ⍮ Ξ ↘ rr ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ Mr : Tin ® rr ∈ El ->
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        (forall mm, dm_global F args ·ₜ x Θ ⍮ Ξ ↘ mm -> Dom mm ≈ mm ∈ R) ->
        exists mm, dm_global F args ·ₜ x Θ ⍮ Ξ ↘ mm /\ Δ ⊢ Mm : Tin ® mm ∈ El.
  Proof.
    intros * Hgl Hsat n; induction n as [| n IH]; intros * Hlen Ha HlT * Ea Heq Err Hga HMr HR Hself.
    - (** Saturated: the former applied *)
      exists rr; split; [ exact (Hsat args _ ltac:(lia) Err) |].
      eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hga | exact HMr | apply wf_exp_eq_sym; exact Heq ].
    - (** Lacking a parameter: a member closure, at a [Π] *)
      destruct (List.rev Trem) as [| e r0] eqn:Er;
        [ apply (f_equal (@List.length _)) in Er; rewrite List.length_rev in Er; cbn in Er; lia |].
      assert (ETrem : Trem = List.rev r0 ++ e :: nil) by (rewrite <- (List.rev_involutive Trem), Er; reflexivity).
      assert (Hin : List.In e Trem) by (rewrite ETrem; apply List.in_or_app; right; left; reflexivity).
      destruct (proj1 (List.Forall_forall _ _) Ha _ Hin) as (κ & B & ->).
      assert (Har : all_assumptions (List.rev r0)) by (rewrite ETrem in Ha; apply List.Forall_app in Ha; exact (proj1 Ha)).
      assert (Hlr : List.length (List.rev r0) = n) by (rewrite ETrem, List.length_app in HlT; cbn in HlT; lia).
      rewrite ETrem, ctx_pi_app in Ea; cbn [ctx_pi_at] in Ea.
      inversion Ea; subst.
      match goal with HB : ⟦ B ⟧ ρT ↘ ?b |- _ => rename HB into EaB; rename b into aB end.
      assert (Hmm : dm_global F args ·ₜ x Θ ⍮ Ξ ↘ d_member (dm_global F args) (x :: nil))
        by (eapply eval_sel_global_unsat; [ exact Hgl | lia ]).
      exists (d_member (dm_global F args) (x :: nil)); split; [ exact Hmm |].
      destruct (per_univ_pi_parts _ _ _ _ _ _ _ _ _ _ evaluated_kind_relevant HR) as (inr & HaB & Hcod).
      destruct (glu_univ_elem_pi_clean_inversion1 HaB evaluated_kind_relevant Hga)
        as (IP & IEl & OP & OEl & elr & HgaB & HgC & Hpel & HP & HEl).
      pose proof (proj1 (HEl _ _ _ _) HMr) as HMrP.
      inversion HMrP as [? ? ? ? IT OT HMrt Hrr HTeq HIT HOT HIP Happs]; subst; clear HMrP.
      apply HEl; econstructor.
      + exact (presup_exp_eq_left Heq).
      + apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR Hpel); exact (Hself _ Hmm).
      + exact HTeq.
      + exact HIT.
      + exact HOT.
      + exact HIP.
      + intros Δ' φ N n0 Hφ HN equiv.
        destruct (Happs _ _ _ _ Hφ HN equiv) as (rr' & Err' & HMr').
        destruct (Hcod _ _ equiv) as (b & b' & Eb & _ & _).
        pose proof (HgC _ equiv _ Eb) as Hgb.
        destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
        assert (Happm : $ᵐ| dm_global F args & n0 | Θ ⍮ Ξ ↘ dm_global F (args ++ n0 :: nil)) by constructor.
        (** The applications, equal *)
        pose proof (wf_exp_eq_conv_kind _ _ _ _ _ _ _ Heq HTeq) as Heq'.
        pose proof (kripke_preserves_exp_eq _ _ _ _ _ _ Heq' Hφ) as Heqφ; cbn [exp_wk] in Heqφ.
        pose proof (glu_univ_elem_trm_escape _ _ _ _ HgaB _ _ _ _ HN) as HNt.
        pose proof (wf_exp_eq_app_cong' _ _ _ _ _ _ _ _ _ _ _ Heqφ (wf_exp_eq_refl HNt)) as HeqN.
        rewrite exp_sub_wk_q_extend in HeqN.
        (** The former applied to one argument more *)
        assert (Err2 : $*| f0 & args ++ n0 :: nil | Θ ⍮ Ξ ↘ rr')
          by (apply (Evaluation.Modules.eval_apps_app Θ Ξ); exists rr; split; [ exact Err | econstructor; [ exact Err' | constructor ] ]).
        (** The member there is related to itself, as the member closure applied *)
        assert (Hself' : forall mm', dm_global F (args ++ n0 :: nil) ·ₜ x Θ ⍮ Ξ ↘ mm' -> Dom mm' ≈ mm' ∈ Rb).
        { intros mm' Hmm'.
          destruct (per_univ_elem_pi_clean_inversion evaluated_kind_relevant HaB Hpel) as (out_rel & Hout & Eel).
          pose proof (proj1 (Eel _ _) (proj1 (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR Hpel _ _) (Hself _ Hmm))) as [_ _ Hpa].
          destruct (Hpa _ _ equiv) as [fa fa' Efa Efa' Hfa].
          assert (Eapp : $| d_member (dm_global F args) (x :: nil) & n0 | Θ ⍮ Ξ ↘ mm')
            by (econstructor; [ exact Happm | constructor; exact Hmm' ]).
          rewrite (functional_eval_app _ _ _ _ Efa Eapp), (functional_eval_app _ _ _ _ Efa' Eapp) in Hfa.
          destruct (Hout _ _ equiv) as [b0 b0' Eb0 Eb0' HRo].
          pose proof (functional_eval_exp _ _ _ _ Eb0 Eb) as ->.
          apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRo HRb); exact Hfa. }
        destruct (IH (args ++ n0 :: nil) (List.rev r0) S (ρT ↦ n0 ⦂ entry_type_value aB)
                    ltac:(rewrite List.length_app; cbn; lia) Har eq_refl _ _ _ _ _ _ _ _ _ _
                    Eb HeqN Err2 Hgb HMr' HRb Hself') as (mm' & Hmm' & Hglu').
        exists mm'; split; [ econstructor; [ exact Happm | constructor; exact Hmm' ] | exact Hglu' ].
  Qed.

  (** A type former, read as the member [x] of a module expression naming
      the module [F] (stored, or a frame) as a definition with a module
      part whose term is [M0], closed, of the value [f0], at a closed type
      over [F]'s telescope, is glued at its type at every instance when
      [M0] is, provided that, saturated, the member is [f0] applied: the
      member is glued against [M0] ([glu_frame_former_apps]) from [F]'s
      value at no argument.  The type formers of a group member or of a
      record type, under declaration or filed, are of that form
      ([sel_global_ind_former], [sel_global_record_former]). *)
  Lemma glu_rel_exp_former_mem_under_sub : forall Γ H x F TF ΦF A1 M0 f0,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mod_qname H = Some F -> gc_loc Θ Ξ F = Some (TF, ΦF) ->
      (forall Γ', exists Rm Rmm, mdenote Θ Ξ Γ' (me_mem H x) (mdesc_dm nil (ctx_pi TF A1) M0 Rm) /\ mdesc_mod Rm = Some Rmm) ->
      (forall σ, (ctx_pi TF A1)[σ] = ctx_pi TF A1) -> (forall σ, M0[σ] = M0) ->
      (forall ρ r, ⟦ M0 ⟧ ρ ↘ r -> r = f0) ->
      (forall args r, List.length args = List.length TF -> $*| f0 & args | Θ ⍮ Ξ ↘ r -> dm_global F args ·ₜ x Θ ⍮ Ξ ↘ r) ->
      glu_rel_exp_under_sub Γ M0 (ctx_pi TF A1) ->
      glu_rel_exp_under_sub Γ (a_mem H x) (ctx_pi TF A1).
  Proof.
    intros * HH HqF HlF Hm EA EM Ef Hsat Hred.
    set (A := ctx_pi TF A1) in *.
    (** The parent's value, at no argument *)
    assert (EhF : forall ρ, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ dm_global F nil).
    { intros ρ; rewrite (mod_qname_inv _ _ HqF).
      apply (Evaluation.Modules.eval_path_mod Θ Ξ); intros m1 m2 Ec Hne.
      exact (path_prefix_loc _ _ Hg _ _ _ _ (gc_loc_loc _ _ _ _ _ HlF) _ Ec Hne). }
    constructor; [ exact (glu_rel_exp_under_sub_ctx _ _ _ Hred) |].
    intros Γ' τ Hτ.
    pose proof (glu_rel_sub_inst_typed _ _ _ Hτ) as Hτt.
    cbn [exp_sub]; rewrite (mod_qname_sub _ _ τ HqF), EA.
    pose proof (glu_rel_exp_under_sub_inst _ _ _ Hred _ _ Hτ) as HrA; rewrite EM, EA in HrA.
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH Hτt) as HHτ; rewrite (mod_qname_sub _ _ τ HqF) in HHτ.
    destruct (Hm Γ') as (Rm & Rmm & HmΓ & HRmm).
    pose proof (wf_exp_eq_mem_delta _ _ _ _ _ _ _ _ HHτ HmΓ eq_refl eq_refl) as Hδ.
    pose proof (mem_desc_ok _ _ _ _ _ _ _ (gctx_valid_syn _ _ Hg) HHτ HmΓ) as Hok.
    destruct (desc_ok_ty_mod _ _ _ _ _ _ Hok eq_refl HRmm) as [j HAj].
    destruct HrA as [Sb HSb lvl Hb].
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := lvl); [ exact HSb |].
    intros Δ σ ρ Hσ.
    destruct (Hb _ _ _ Hσ) as [a mr P El Ea Emr Hga Hmr].
    pose proof (glu_ctx_env_sub_escape HSb _ _ _ Hσ) as Hσt.
    (** Of the relevant kind: a type of a universe *)
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HAj Hσt) as HAjσ; cbn [exp_sub] in HAjσ.
    pose proof (glu_univ_elem_trm_typ _ _ _ _ Hga _ _ _ _ Hmr) as HAP.
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant _ Hga HAP HAjσ) as [Hka _].
    unfold glu_term_value in Emr; rewrite Hka in Emr; apply Ef in Emr; subst mr.
    (** The member at the environment, related to itself (completeness) *)
    destruct (glu_ctx_env_per_ctx_env HSb) as [RΓ HRΓ].
    pose proof (glu_ctx_env_per_env HSb HRΓ Hσ) as Hρ.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hga) as [Ra HRa].
    destruct (Completeness.UnitCases.rel_modexp_at _ _ _ _ _ (proj2 (proj2 (@completeness_fundamental_modules GCt)) _ _ _ HHτ) HRΓ _ _ Hρ)
      as (h0 & h0' & Eh0 & Eh0' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ Eh0 (EhF ρ)) as ->; pose proof (functional_eval_modexp _ _ _ _ Eh0' (EhF ρ)) as ->.
    destruct (mem_valid_at _ _ Hg _ _ _ _ _ _ _ HHτ HmΓ eq_refl HRΓ Hρ) as [h1 a1 i1 R1 Eh1 Ea1 HR1 Hhas _ _].
    pose proof (functional_eval_modexp _ _ _ _ Eh1 (EhF ρ)) as ->; pose proof (functional_eval_exp _ _ _ _ Ea1 Ea) as ->.
    assert (Hself : forall mm, dm_global F nil ·ₜ x Θ ⍮ Ξ ↘ mm -> Dom mm ≈ mm ∈ Ra).
    { intros mm Emm.
      destruct (Hhas ltac:(rewrite Hka; constructor) _ Hhh) as [m1 m1' Em1 Em1' Hm1].
      rewrite (functional_eval_sel _ _ _ _ Em1 Emm), (functional_eval_sel _ _ _ _ Em1' Emm) in Hm1.
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HRa); exact Hm1. }
    (** Glued against the former applied *)
    destruct (glu_frame_former_apps _ _ _ _ _ HlF Hsat (List.length TF) nil _ _ _ eq_refl
                (gc_loc_tele_all_assumptions _ _ Hg _ _ _ HlF) eq_refl _ _ _ _ _ _ _ _ _ _
                Ea (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hδ Hσt) ltac:(constructor) Hga Hmr HRa Hself)
      as (mm & Emm & Hglu).
    econstructor; [ exact Ea | | exact Hga | exact Hglu ].
    unfold glu_term_value; rewrite Hka; exact (eval_mem_of_sel _ _ _ _ _ (EhF ρ) Emm).
  Qed.

  (** The member rule at the target of a sound embedding, at every
      instance of the context: the member typed at the source, of a
      module expression whose instances are glued, at a type whose
      instances are glued.  At a proposition the instance is glued by its
      typing ([glu_rel_exp_proof]); at an evaluated kind by
      [glu_rel_exp_mem_at], the member stored at the source in every
      stored module the instance's description reads
      ([src_stored_member_of_mem]): substitution keeps the stored module
      ([mdesc_sub_closed_back]), and the target's description grows the
      source's ([mdenote_grow_all]). *)
  Lemma glu_rel_exp_mem_not_former_under_sub : forall Γ H x Rs A Srt,
      Θs ⍮ Ξs ⍮ Γ ⊢ᵐ H ≈ H -> @not_frame_former (gc_mk Θs Ξs) H x ->
      (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ -> not_frame_former H[ζ]ᵐ x) ->
      mdenote Θs Ξs Γ (me_mem H x) Rs -> mdesc_type Rs = Some A ->
      Θs ⍮ Ξs ⍮ Γ ⊢ A : Srt -> type_sort Srt -> Θs ⍮ Ξs ⍮ Γ ⊢ a_mem H x : A ->
      glu_rel_modexp_under_sub Γ H -> glu_rel_exp_under_sub Γ A Srt ->
      glu_rel_exp_under_sub Γ (a_mem H x) A.
  Proof.
    intros * HHs Hnfs Hnf HmRs HtRs HAs HS HxAs HHg HAg.
    pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
    pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hsub.
    destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & Hwe & _ & _ & _ & _ & Hwm & _).
    pose proof (Hwm _ _ _ HHs) as HH; pose proof (Hwe _ _ _ HAs) as HAt; pose proof (Hwe _ _ _ HxAs) as Hx.
    (** The descriptions at the target, grown *)
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmRs) as (R & HmR & Hgr).
    pose proof (mdesc_grows_ty _ _ _ _ _ _ _ Hgr HtRs) as HtR.
    assert (HkR : mdesc_kind R = mdesc_kind Rs)
      by (destruct Hgr; [ reflexivity | cbn in HtRs; discriminate | reflexivity ]).
    destruct (me_denotes _ _ _ _ _ HHs) as (RHs & Rms & HmHs & HRms).
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmHs) as (RH0 & HmH0 & HgrH).
    assert (ESrt : forall σ, Srt[σ] = Srt) by (intros; destruct HS; reflexivity).
    constructor; [ exact (glu_rel_modexp_under_sub_ctx _ _ HHg) |].
    intros Γ' τ Hτ.
    pose proof (glu_rel_sub_inst_typed _ _ _ Hτ) as Hτt.
    pose proof (glu_rel_exp_under_sub_inst _ _ _ HAg _ _ Hτ) as HAτ; rewrite ESrt in HAτ.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hx Hτt) as Hxτ.
    (** At a proposition, by its typing *)
    destruct HS as [i | | ]; [| exact (Soundness.UniverseCases.glu_rel_exp_proof HAτ Hxτ) |].
    all: cbn [exp_sub] in Hxτ |- *.
    all: pose proof (sub_preserves_exp _ _ _ _ _ _ _ HAt Hτt) as HAtτ; rewrite ESrt in HAtτ.
    (** At an evaluated kind: the member's kind, the sort's *)
    all: pose proof (mem_desc_ok _ _ _ _ _ _ _ (gctx_valid_syn _ _ Hg) HH HmR) as Hok;
      destruct (desc_ok_ty_at _ _ _ _ _ Hok HtR) as [i0 HAk].
    all: assert (Hk : evaluated_kind (mdesc_kind Rs))
           by (rewrite <- HkR; erewrite AnnotatedUpto.exp_eq_same_kind;
               [ | exact (wf_exp_eq_refl HAk) | exact (sort_kind_abs_kind_sort _ _) | exact HAt | econstructor ]; constructor).
    all: eapply glu_rel_exp_mem_at with (R := mdesc_sub R τ);
      [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hτt)
      | intros Γ1 ζ Hζ; rewrite modexp_sub_sub; apply (Hnf Γ1); eapply wf_sub_compose; [ exact Hτt | exact Hζ ]
      |
      | exact (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH HmR Hτt)
      | exact (mdesc_type_sub _ _ _ HtR)
      | constructor
      | exact HAtτ
      | exact Hxτ
      | exact (glu_rel_modexp_under_sub_inst _ _ HHg _ _ Hτ)
      | exact HAτ ].
    (** The member is stored at the source in every stored module the
        instance's description reads *)
    all: intros RH' Θ' p T Φ Ns HmH' HRH'.
    all: rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmH' _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HH HmH0 Hτt)) in HRH'.
    all: destruct (mdesc_sub_closed_back _ _ _ _ _ _ _ HRH') as (Θ'' & Ns' & HRH0).
    all: destruct (mdesc_grows_mod _ _ _ _ _ _ _ HgrH HRms) as (R2m & HR2m & Hgm); rewrite HRH0 in HR2m; injection HR2m as <-.
    all: inversion Hgm as [? Hc | ? ? Φ1 ? ? ? _ _ | ]; subst; [ cbn in Hc; discriminate |].
    all: destruct (src_stored_member_of_mem _ _ _ _ _ _ _ _ _ _ _ Hnfs HmHs HRms HmRs HtRs Hk) as (Γe & Φ0 & E0 & REs & As & Hsm).
    all: exists Γe, Φ1, Φ0, E0, REs, As; exact Hsm.
  Qed.

  (** The global facts a selection of [y] reads ([glu_sel_globals]) hold
      at the target for a module expression typed at the source reading a
      stored module [p] of which [y] is an entry: every description of its
      instances reads [p] (grown, [mdesc_grows_closed], and moved,
      [mdesc_sub_closed_back]); [p]'s telescope is glued by the embedding,
      the child stored at the target is stored at the source over the same
      telescope, glued by the embedding, and an alias child is the source's
      ([loc_child_grow]), glued by the embedding's deep field. *)
  Lemma glu_sel_globals_of_source : forall Γ H y RHs Θ0 p T Φs Ns0 E,
      Θs ⍮ Ξs ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θs Ξs Γ H RHs -> mdesc_mod RHs = Some (mdesc_closed Θ0 p T Φs Ns0) ->
      gm_entry Φs (y :: nil) = Some E ->
      forall Γ' τ, Γ' ⊢ˢ τ : Γ -> glu_sel_globals Γ' H[τ]ᵐ y.
  Proof.
    intros * HHs HmHs HRms He Γ' τ Hτ Γ1 ζ RH Θ' p' T' Φ' Ns Hζ HmH HRH.
    pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
    pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hsub.
    destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & _ & _ & _ & _ & _ & Hwm & _).
    pose proof (Hwm _ _ _ HHs) as HH.
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmHs) as (RH0 & HmH0 & HgrH).
    destruct (mdesc_grows_mod _ _ _ _ _ _ _ HgrH HRms) as (R2m & HR2m & Hgm).
    inversion Hgm as [? Hc | ? ? Φ1 Φ2 ? ? Hl1 Hl2 | ]; subst; [ cbn in Hc; discriminate |].
    (** The instance's description is the target's moved *)
    rewrite modexp_sub_sub in HmH.
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HH HmH0 (wf_sub_compose _ _ _ _ _ _ _ Hτ Hζ)) as HmH'.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmH _ HmH') in HRH.
    destruct (mdesc_sub_closed_back _ _ _ _ _ _ _ HRH) as (Θ'' & Ns' & HRH0).
    rewrite HR2m in HRH0; injection HRH0 as _ <- <- <- _.
    constructor.
    - intros T0 Φ0 Hl0; assert (Hl0' : gc_loc Θ Ξ p = Some (T0, Φ0)) by exact Hl0.
      rewrite (gc_loc_of_loc _ _ Hg _ _ _ Hl2) in Hl0'; injection Hl0' as <- <-.
      exact (glu_rel_ctx_types_ctx _ (glu_gctx_embedding_tele _ _ _ _ Hμ _ _ _ (gc_loc_of_loc _ _ Hgs _ _ _ Hl1))).
    - intros T1 Φ1' Hl'.
      destruct (proj1 (loc_child_grow _ _ _ _ Hgs Hg Hsub _ _ _ _ _ _ Hl1 Hl2 He) _ _ Hl') as (Φs' & Hls').
      exact (glu_rel_ctx_types_ctx _ (glu_gctx_embedding_tele _ _ _ _ Hμ _ _ _ Hls')).
    - intros U HU.
      pose proof (proj2 (loc_child_grow _ _ _ _ Hgs Hg Hsub _ _ _ _ _ _ Hl1 Hl2 He) _ HU) as HUs.
      exact (glu_gctx_embedding_alias_modexp _ _ _ _ _ _ _ _ _ Hμ (gc_loc_of_loc _ _ Hg _ _ _ Hl2) HUs HU).
  Qed.

  (** A selection typed at the source, read from an entry [y] of the
      stored module [p] the module expression reads, names no open frame at
      the target, at any instance: what it names is unchanged by the
      instance ([mod_qname_sub_eq]); were it an open frame, so would the
      module expression's path be ([frame_parent]), which the module
      expression then denotes as [p] ([mdenote_unit], [mdenote_ind_frame],
      [mdenote_record_frame]); but [p]'s child [y] is an entry at the
      source, so at the target ([gc_sub_entry_field]), and no entry is an
      open frame ([gc_entry_tele_nil]). *)
  Lemma names_no_frame_sel_of_source : forall Γ H y RHs Θ0 p T Φs Ns0 E,
      Θs ⍮ Ξs ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θs Ξs Γ H RHs -> mdesc_mod RHs = Some (mdesc_closed Θ0 p T Φs Ns0) ->
      gm_entry Φs (y :: nil) = Some E ->
      forall Γ' τ, Γ' ⊢ˢ τ : Γ -> names_no_frame (me_mem H y)[τ]ᵐ.
  Proof.
    intros * HHs HmHs HRms He Γ' τ Hτ pq Hq.
    pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
    pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hsub.
    destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & _ & _ & _ & _ & _ & Hwm & _).
    pose proof (Hwm _ _ _ HHs) as HH.
    cbn [modexp_sub mod_qname] in Hq.
    rewrite (mod_qname_sub_eq _ _ _ _ (wf_sub_mod_compat _ _ _ _ _ Hτ) (proj1 (modexp_eq_slot_root _ _ _ _ _ HH))) in Hq.
    destruct (mod_qname H) as [F |] eqn:HqF; [ injection Hq as <- | discriminate ].
    change (gc_frame Ξ (qname_in F y) = None).
    unfold gc_frame; destruct (gs_find_tele Ξ (qname_in F y)) as [[[[Δ [[|] Φ0 | E0]] [| ? ?]] T0] |] eqn:Ht;
      try reflexivity; exfalso.
    destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (TF & ΦF & HfF & _).
    (** The module expression then denotes its frame *)
    assert (HD : exists D, mdenote Θ Ξ Γ H D /\ mdesc_mod D = Some (mdesc_closed nil F TF ΦF nil)).
    { assert (HlF : gc_loc Θ Ξ F = Some (TF, ΦF)) by (unfold gc_loc; rewrite HfF; reflexivity).
      destruct (gs_find_ind Ξ F) as [[[pq k] D] |] eqn:Hk.
      - destruct (frame_ind_loc _ _ Hg _ _ _ _ Hk) as (U' & T1 & T' & Φ' & Mk & _ & Hfr & Hl' & HMk).
        rewrite HfF in Hfr; injection Hfr as <- <-.
        eexists; split; [ eapply mdenote_ind_frame; eassumption | reflexivity ].
      - destruct (gs_find_record Ξ F) as [R |] eqn:Hr.
        + eexists; split; [ eapply mdenote_record_frame; eassumption | reflexivity ].
        + eexists; split; [ eapply mdenote_unit; [ exact HqF | exact (gc_unit_frame _ _ _ _ _ _ HqF HfF Hk Hr) ] | reflexivity ]. }
    destruct HD as (D & HmD & HDm).
    (** So it reads [p] as its frame *)
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmHs) as (RH0 & HmH0 & HgrH).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmH0 _ HmD) in HgrH.
    destruct (mdesc_grows_mod _ _ _ _ _ _ _ HgrH HRms) as (R2m & HR2m & Hgm).
    rewrite HDm in HR2m; injection HR2m as <-.
    inversion Hgm as [? Hc | ? ? Φ1 Φ2 ? ? Hl1 Hl2 | ]; subst; [ cbn in Hc; discriminate |].
    (** whose child [y] is an entry, no frame *)
    pose proof (proj2 (loc_entry _ _ Hgs _ _ _ Hl1 _ _) He) as Hc1.
    destruct (gc_sub_entry_field _ _ _ _ Hsub _ _ Hc1) as (E' & Hc2 & _).
    rewrite (gc_entry_tele_nil _ _ _ _ _ Ht) in Hc2; discriminate.
  Qed.

  (** The member rule at the target of a sound embedding, at every
      instance of the context, for every member typed at the source whose
      δ-reduct, if any, is glued at the instances.  A type former under
      declaration at the target, or at the source and filed at the target,
      is glued against its reduct ([glu_rel_exp_former_mem_under_sub]):
      the source's description is the former's, which the target's grows,
      and its frame's parent, at the source a frame, is stored at the
      target with the same telescope ([gc_loc_grow]).  Any other member is
      read through the modules it is stored in
      ([glu_rel_exp_mem_not_former_under_sub]). *)
  Lemma glu_rel_exp_member_under_sub : forall Γ H x Rs A Srt,
      Θs ⍮ Ξs ⍮ Γ ⊢ᵐ H ≈ H ->
      mdenote Θs Ξs Γ (me_mem H x) Rs -> mdesc_type Rs = Some A ->
      Θs ⍮ Ξs ⍮ Γ ⊢ A : Srt -> type_sort Srt -> Θs ⍮ Ξs ⍮ Γ ⊢ a_mem H x : A ->
      glu_rel_modexp_under_sub Γ H -> glu_rel_exp_under_sub Γ A Srt ->
      (forall M, mdesc_reduct Rs = Some M -> glu_rel_exp_under_sub Γ M A) ->
      glu_rel_exp_under_sub Γ (a_mem H x) A.
  Proof.
    intros * HHs HmRs HtRs HAs HS HxAs HHg HAg HMg.
    pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
    pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hsub.
    destruct (gctx_embedding_preserves_wf _ _ _ _ Hem) as (_ & _ & _ & _ & _ & _ & Hwm & _).
    pose proof (Hwm _ _ _ HHs) as HH.
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmRs) as (R & HmR & Hgr).
    pose proof (mdesc_grows_ty _ _ _ _ _ _ _ Hgr HtRs) as HtR.
    apply (@frame_former_cases GCt H x).
    - (** No type former under declaration at the target *)
      intros Hnf.
      apply (@frame_former_cases (gc_mk Θs Ξs) H x).
      + intros Hnfs.
        exact (glu_rel_exp_mem_not_former_under_sub _ _ _ _ _ _ HHs Hnfs
                 (fun Γ1 ζ Hζ => not_frame_former_sub _ _ _ _ _ HH Hζ Hnf) HmRs HtRs HAs HS HxAs HHg HAg).
      + (** A group member's under declaration at the source, filed at the target *)
        intros p pq k D Mk Tm Φm Hq Hf HMk Hlp.
        pose proof (mdenote_ind_frame Θs Ξs Γ _ _ _ _ _ _ _ _ Hq Hf HMk Hlp) as Hm0.
        pose proof (proj1 (mdenote_functional_all _ _ Hgs) _ _ _ HmRs _ Hm0) as ->.
        cbn in HtRs; injection HtRs as <-.
        assert (Hq' := Hq); cbn [mod_qname] in Hq'.
        destruct (mod_qname H) as [F |] eqn:HqF; [ injection Hq' as Ep | discriminate ].
        assert (Ep' : p = qname_in F x) by (rewrite <- Ep; reflexivity); clear Ep; subst p.
        destruct (frame_ind_former_parent _ _ Hgs _ _ _ _ _ _ Hf HMk) as (TF & ΦF & A1 & HfrF & EA).
        destruct (gc_loc_grow _ _ _ _ Hg Hsub F TF ΦF ltac:(unfold gc_loc; rewrite HfrF; reflexivity)) as (ΦF' & HlF & _).
        pose proof (HMg _ eq_refl) as Hred.
        pose proof (fun σ => frame_ind_former_type_closed _ _ Hgs _ _ _ _ _ σ Hf HMk) as EAc.
        rewrite EA in Hred, EAc |- *.
        eapply (glu_rel_exp_former_mem_under_sub _ _ _ _ _ _ _ (a_ind pq k) (d_ind pq k nil) HH HqF HlF);
          [| exact EAc | reflexivity | intros ρ r E; inversion E; reflexivity
          | exact (sel_global_ind_former _ _ _ _ _ _ _ _ _ HlF (gc_sub_frame_ind _ _ _ _ _ _ Hsub Hf)) | exact Hred ].
        intros Γ'.
        destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ (mdenote_ind_frame Θs Ξs Γ' _ _ _ _ _ _ _ _ Hq Hf HMk Hlp))
          as (R' & HmR' & Hgr').
        unfold ind_former_desc in Hgr'; rewrite EA in Hgr'.
        inversion Hgr' as [? Hc | | ? ? ? ? ? Hgm]; subst; [ cbn in Hc; discriminate |].
        inversion Hgm; subst; (eexists _, _; split; [ exact HmR' | reflexivity ]).
      + (** A record type's under declaration at the source, filed at the target *)
        intros p Rr Tm Φm Hq Hf Hlp.
        pose proof (mdenote_record_frame Θs Ξs Γ _ _ _ _ _ Hq Hf Hlp) as Hm0.
        pose proof (proj1 (mdenote_functional_all _ _ Hgs) _ _ _ HmRs _ Hm0) as ->.
        cbn in HtRs; injection HtRs as <-.
        assert (Hq' := Hq); cbn [mod_qname] in Hq'.
        destruct (mod_qname H) as [F |] eqn:HqF; [ injection Hq' as Ep | discriminate ].
        assert (Ep' : p = qname_in F x) by (rewrite <- Ep; reflexivity); clear Ep; subst p.
        destruct (frame_record_former_parent _ _ Hgs _ _ _ Hf) as (TF & ΦF & A1 & HfrF & EA).
        destruct (gc_loc_grow _ _ _ _ Hg Hsub F TF ΦF ltac:(unfold gc_loc; rewrite HfrF; reflexivity)) as (ΦF' & HlF & _).
        pose proof (HMg _ eq_refl) as Hred.
        pose proof (fun σ => frame_record_former_type_closed _ _ Hgs _ _ σ Hf) as EAc.
        rewrite EA in Hred, EAc |- *.
        eapply (glu_rel_exp_former_mem_under_sub _ _ _ _ _ _ _ (a_record (qname_in F x)) (d_record (qname_in F x) nil) HH HqF HlF);
          [| exact EAc | reflexivity | intros ρ r E; inversion E; reflexivity
          | exact (sel_global_record_former _ _ _ _ _ _ _ HlF (gc_sub_frame_record _ _ _ _ _ _ Hsub Hf)) | exact Hred ].
        intros Γ'.
        destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ (mdenote_record_frame Θs Ξs Γ' _ _ _ _ _ Hq Hf Hlp))
          as (R' & HmR' & Hgr').
        unfold record_former_desc in Hgr'; rewrite EA in Hgr'.
        inversion Hgr' as [? Hc | | ? ? ? ? ? Hgm]; subst; [ cbn in Hc; discriminate |].
        inversion Hgm; subst; (eexists _, _; split; [ exact HmR' | reflexivity ]).
    - (** A group member's under declaration at the target *)
      intros p pq k D Mk Tm Φm Hq Hf HMk Hlp.
      pose proof (mdenote_ind_frame Θ Ξ Γ _ _ _ _ _ _ _ _ Hq Hf HMk Hlp) as Hm0.
      pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmR _ Hm0) as ->.
      assert (Hrs : mdesc_reduct Rs = Some (a_ind pq k)) by (inversion Hgr; subst; reflexivity).
      cbn in HtR; injection HtR as <-.
      assert (Hq' := Hq); cbn [mod_qname] in Hq'.
      destruct (mod_qname H) as [F |] eqn:HqF; [ injection Hq' as Ep | discriminate ].
      assert (Ep' : p = qname_in F x) by (rewrite <- Ep; reflexivity); clear Ep; subst p.
      destruct (frame_ind_former_parent _ _ Hg _ _ _ _ _ _ Hf HMk) as (TF & ΦF & A1 & HfrF & EA).
      assert (HlF : gc_loc Θ Ξ F = Some (TF, ΦF)) by (unfold gc_loc; rewrite HfrF; reflexivity).
      assert (Hfm : ind_mlookup Θ Ξ (qname_in F x) = Some (pq, k, D))
        by (rewrite ind_mlookup_unfold; replace (gs_find_ind Ξ (qname_in F x)) with (Some (pq, k, D)) by exact (eq_sym Hf); reflexivity).
      pose proof (HMg _ Hrs) as Hred.
      pose proof (fun σ => frame_ind_former_type_closed _ _ Hg _ _ _ _ _ σ Hf HMk) as EAc.
      rewrite EA in Hred, EAc |- *.
      eapply (glu_rel_exp_former_mem_under_sub _ _ _ _ _ _ _ (a_ind pq k) (d_ind pq k nil) HH HqF HlF);
        [| exact EAc | reflexivity | intros ρ r E; inversion E; reflexivity
        | exact (sel_global_ind_former _ _ _ _ _ _ _ _ _ HlF Hfm) | exact Hred ].
      intros Γ'; pose proof (mdenote_ind_frame Θ Ξ Γ' _ _ _ _ _ _ _ _ Hq Hf HMk Hlp) as Hm'.
      unfold ind_former_desc in Hm'; rewrite EA in Hm'.
      eexists _, _; split; [ exact Hm' | reflexivity ].
    - (** A record type's under declaration at the target *)
      intros p Rr Tm Φm Hq Hf Hlp.
      pose proof (mdenote_record_frame Θ Ξ Γ _ _ _ _ _ Hq Hf Hlp) as Hm0.
      pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmR _ Hm0) as ->.
      assert (Hrs : mdesc_reduct Rs = Some (a_record p)) by (inversion Hgr; subst; reflexivity).
      cbn in HtR; injection HtR as <-.
      assert (Hq' := Hq); cbn [mod_qname] in Hq'.
      destruct (mod_qname H) as [F |] eqn:HqF; [ injection Hq' as Ep | discriminate ].
      assert (Ep' : p = qname_in F x) by (rewrite <- Ep; reflexivity); clear Ep; subst p.
      destruct (frame_record_former_parent _ _ Hg _ _ _ Hf) as (TF & ΦF & A1 & HfrF & EA).
      assert (HlF : gc_loc Θ Ξ F = Some (TF, ΦF)) by (unfold gc_loc; rewrite HfrF; reflexivity).
      assert (Hfm : record_lookup Θ Ξ (qname_in F x) = Some Rr)
        by (unfold record_lookup; replace (gs_find_record Ξ (qname_in F x)) with (Some Rr) by exact (eq_sym Hf); reflexivity).
      pose proof (HMg _ Hrs) as Hred.
      pose proof (fun σ => frame_record_former_type_closed _ _ Hg _ _ σ Hf) as EAc.
      rewrite EA in Hred, EAc |- *.
      eapply (glu_rel_exp_former_mem_under_sub _ _ _ _ _ _ _ (a_record (qname_in F x)) (d_record (qname_in F x) nil) HH HqF HlF);
        [| exact EAc | reflexivity | intros ρ r E; inversion E; reflexivity
        | exact (sel_global_record_former _ _ _ _ _ _ _ HlF Hfm) | exact Hred ].
      intros Γ'; pose proof (mdenote_record_frame Θ Ξ Γ' _ _ _ _ _ Hq Hf Hlp) as Hm'.
      unfold record_former_desc in Hm'; rewrite EA in Hm'.
      eexists _, _; split; [ exact Hm' | reflexivity ].
  Qed.

End MembersFromSource.
