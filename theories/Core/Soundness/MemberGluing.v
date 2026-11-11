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
From Mctt.Core.Completeness.Consequences Require AnnotatedUpto.
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

(** ** Saturated global modules, from the source of a sound embedding *)

Section MembersFromSource.
  Variables (Θs : gdeps) (Ξs : gstack) (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hgs : ⊢ᵍ Θs ⍮ Ξs.
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis Hμ : glu_gctx_embedding Θs Ξs Θ Ξ.
  #[local] Instance GCt : GCtx := gc_mk Θ Ξ.
  Import Fixed_Notations.

  (** [glu_global_member_value_at], its stored member read from where the
      member is read at the source: the member read bare there is glued at
      the target ([glu_bare_member_at]) and read bare there as grown
      ([mdenote_grow_all]); its stored type is glued over the telescope
      ([stored_type_over_tele]). *)
  Lemma glu_global_member_src : forall p T Φs Φ x Γ1 H1 RHs RH Ns1 Rs R A' Δ σ1 args m a (i : nat) P El Tin,
      @names_no_frame (gc_mk Θs Ξs) H1 -> mdenote Θs Ξs Γ1 H1 RHs -> mdesc_mod RHs = Some (mdesc_closed nil p T Φs Ns1) ->
      mdenote Θs Ξs Γ1 (me_mem H1 x) Rs -> mdesc_type Rs = Some A' -> evaluated_kind (mdesc_kind Rs) ->
      gc_loc Θ Ξ p = Some (T, Φ) -> List.length args = List.length T ->
      Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H1 ≈ H1 -> names_no_frame H1 -> mdenote Θ Ξ Γ1 H1 RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
      mdenote Θ Ξ Γ1 (me_mem H1 x) R -> mdesc_type R = Some A' ->
      Δ ⊢ˢ σ1 : Γ1 ->
      glu_tele_args Δ (List.rev T) nil nil (List.map (fun N => N[σ1]) Ns1) args ->
      dm_global p args ·ₜ x Θ ⍮ Ξ ↘ m ->
      (forall h b, per_dmod h (dm_global p args) -> dmod_mem_type h x b -> exists j, Dom b ≈ a ∈ per_univ j) ->
      not_level_sort a -> DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ Tin ® P ->
      (exists l : nat, Δ ⊢ A'[σ1] ≈ Tin : abs_kind_sort (domain_kind a) Typeω@l) /\ Δ ⊢ (a_mem H1 x)[σ1] : Tin ® m ∈ El.
  Proof.
    intros * Hqs HmHs HRHs Hms Hts Hk Hgl Hlen HH1 Hq1 HmH HRH Hm Ht Hσ1 Hargs Hsel Hrel Hnl Hga HTin.
    (** The member's entry at the source *)
    apply (@mdenote_mem_no_frame (gc_mk Θs Ξs) _ _ _ _ _ Hgs Hqs Hms); intros S0 S0m Γy E rd REs Hs0 HS0m He Hed Hrd.
    rewrite (proj1 (mdenote_functional_all _ _ Hgs) _ _ _ Hs0 _ HmHs), HRHs in HS0m; injection HS0m as <-.
    pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgs HmHs) HRHs) as Hls; cbn in Hls.
    pose proof (loc_closed _ _ Hgs _ _ _ Hls) as HUs.
    destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HUs He) as (-> & HsE & ->).
    pose proof He as He1; cbn in He1.
    destruct (gm_prefix_upto Φs x) as [[| Φ0 z E0 | ] |] eqn:Hps; try discriminate.
    injection He1 as <-.
    destruct (gm_prefix_entry _ _ _ Hps) as (? & ? & Heq & _); injection Heq as <- -> <-.
    cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read REs Ns1) as [R1s |] eqn:Hats; cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
    rewrite mdesc_up_nil, mdesc_type_named in Hts; rewrite mdesc_up_nil, mdesc_kind_named in Hk.
    assert (Hdm : forall Θd A M Rm, REs = mdesc_dm Θd A M Rm -> Θd = nil).
    { intros * ->; inversion Hed; subst; try reflexivity;
        match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm; cbn in Hmm; contradiction end. }
    rewrite (mdesc_kind_ats_read _ _ _ Hdm Hats) in Hk.
    assert (HtRE : exists As, mdesc_type REs = Some As).
    { destruct REs as [r0 A0 om0 | Δ0 Φ1 Φx1 | Θ0 p0 T0 Φ1 Ns0 | Θd A0 M0 Rm0]; cbn; eauto; exfalso;
        rewrite mdesc_ats_read_mod in Hats by exact I;
        assert (Hmm : mdesc_is_mod R1s) by (eapply mdesc_ats_is_mod; [| exact Hats ]; exact I);
        destruct R1s; cbn in Hmm, Hts; first [ contradiction | discriminate ]. }
    destruct HtRE as (As & HtRE).
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
      the source and the target, at an environment [ρ] of [Γ] where [H]'s
      value is related to [h], is glued at every type [Tin] glued at a
      value [a2] related to its type's there, as [h]'s member, its type
      equal to [Tin]. *)
  #[local] Definition glu_mem_goal (Δ : ctx) (σ : sub) (Γ : ctx) (H : modexp) (h : dmod) : Prop :=
    forall x Rs A Srt RΓ ρ h' a2' a2 (j : universe_index) m (k : nat) P2 El2 Tin,
      (forall Γ1 ζ, Γ1 ⊢ˢ ζ : Γ -> names_no_frame H[ζ]ᵐ) ->
      (forall Γ1 ζ, Θs ⍮ Ξs ⍮ Γ1 ⊢ˢ ζ : Γ -> @names_no_frame (gc_mk Θs Ξs) H[ζ]ᵐ) ->
      Θs ⍮ Ξs ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θs Ξs Γ (me_mem H x) Rs -> mdesc_type Rs = Some A ->
      Θs ⍮ Ξs ⍮ Γ ⊢ a_mem H x : A ->
      type_sort Srt -> Γ ⊢ A : Srt -> Γ ⊢ a_mem H x : A ->
      EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h' -> per_dmod h h' ->
      ⟦ A ⟧ ρ ↘ a2' -> Dom a2' ≈ a2 ∈ per_univ j -> evaluated_kind (domain_kind a2) ->
      h ·ₜ x Θ ⍮ Ξ ↘ m ->
      DG a2 ∈ glu_univ_elem k ↘ P2 ↘ El2 -> Δ ⊢ Tin ® P2 ->
      (exists l : nat, Δ ⊢ A[σ] ≈ Tin : abs_kind_sort (domain_kind a2) Typeω@l) /\ Δ ⊢ (a_mem H x)[σ] : Tin ® m ∈ El2.

  (** A saturated global module value: its arguments read off the module
      part through the identity factorization, its member glued from the
      source's reading ([glu_global_member_src]), whose module part is the
      same stored module at the same arguments ([mdesc_grows_closed]). *)
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
    intros x Rs A Srt RΓ ρ h' a2' a2 j m k P2 El2 Tin Hnf Hnfs HHs HmRs HtRs HxAs HS HAt HxA HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel Hga2 HTin.
    pose proof (glu_gctx_embedding_embedding _ _ _ _ Hμ) as Hem.
    pose proof (gctx_embedding_resolution _ _ _ _ Hem) as Hsub.
    (** The member's description at the target, grown *)
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmRs) as (R & HmR & Hgr).
    pose proof (mdesc_grows_ty _ _ _ _ _ _ _ Hgr HtRs) as HtR.
    assert (HkR : mdesc_kind R = mdesc_kind Rs)
      by (destruct Hgr; [ reflexivity | cbn in HtRs; discriminate | reflexivity ]).
    (** The module's description at both, the same stored module at the
        same arguments *)
    destruct (me_denotes _ _ _ _ _ HHs) as (RHs & Rms & HmHs & HRms).
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmHs) as (RH & HmH & HgrH).
    pose proof (glu_sub_through_id _ _ _ Hσ) as Hst.
    assert (HmH' : mdenote Θ Ξ Γ H[Id]ᵐ RH) by (rewrite modexp_sub_id; exact HmH).
    destruct (Hd _ _ _ _ _ _ Hst HmH') as [Ns1 HNs1].
    pose proof (Ha _ _ _ _ _ _ _ Hst HmH' HNs1) as Hargs.
    destruct (mdesc_grows_mod _ _ _ _ _ _ _ HgrH HRms) as (R2m & HR2m & Hgm).
    rewrite HNs1 in HR2m; injection HR2m as <-.
    inversion Hgm as [? Hc | ? ? Φ1 ? ? ? _ _ | ]; subst; [ cbn in Hc; discriminate |].
    (** Naming no open frame, at both *)
    pose proof (Hnfs _ _ (wf_sub_id _ _ _ (presup_modexp_eq_ctx HHs))) as Hnfs0; rewrite modexp_sub_id in Hnfs0.
    pose proof (Hnf _ _ (wf_sub_id _ _ _ (presup_modexp_eq_ctx HH))) as Hnf0; rewrite modexp_sub_id in Hnf0.
    (** The completeness facts of the member *)
    pose proof (mem_type_value_kind _ _ Hg _ _ _ _ _ _ _ _ _ _ HH HmR HtR HRΓ Hρ Ea2' Ha2) as Hka.
    assert (Hk : evaluated_kind (mdesc_kind Rs)) by (rewrite <- HkR, <- Hka; exact Hev).
    destruct (mem_value_facts _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ HH HmR HtR HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel) as (_ & Hty & _).
    pose proof (type_value_not_level_sort _ _ _ _ _ _ _ _ _ _ HAt HS HRΓ Hρ Ea2' Ha2) as Hnl.
    exact (glu_global_member_src _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hnfs0 HmHs HRms HmRs HtRs Hk Hgl Hlen HH Hnf0 HmH HNs1 HmR HtR Hσ Hargs Hsel Hty Hnl Hga2 HTin).
  Qed.

  (** A saturated body value: its member is glued at the entry's type
      ([glu_mem_body_value_at]), with the completeness facts at the value
      ([mem_value_facts]). *)
  Lemma glu_mem_body_case : forall Δ σ Γ H sm Φ ρh,
      glu_dmod Δ σ Γ H (dm_local nil (md_body sm Φ) ρh) -> glu_mem_goal Δ σ Γ H (dm_local nil (md_body sm Φ) ρh).
  Proof.
    intros * Hgd; unfold glu_mem_goal.
    intros x Rs A Srt RΓ ρ h' a2' a2 j m k P2 El2 Tin Hnf Hnfs HHs HmRs HtRs HxAs HS HAt HxA HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel Hga2 HTin.
    assert (HH : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H) by (inversion Hgd; assumption).
    pose proof (gctx_embedding_resolution _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hsub.
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmRs) as (R & HmR & Hgr).
    pose proof (mdesc_grows_ty _ _ _ _ _ _ _ Hgr HtRs) as HtR.
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
    intros x Rs A Srt RΓ ρ h' a2' a2 j m k P2 El2 Tin Hnf Hnfs HHs HmRs HtRs HxAs HS HAt HxA HRΓ Hρ Eh' Hhh' Ea2' Ha2 Hev Hsel Hga2 HTin.
    pose proof (gctx_embedding_resolution _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hsub.
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmRs) as (R & HmR & Hgr).
    pose proof (mdesc_grows_ty _ _ _ _ _ _ _ Hgr HtRs) as HtR.
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
    (** The member of the module applied to the variable, at the source *)
    destruct (@me_mod_tele_exists (gc_mk Θs Ξs) _ _ _ HHs) as (RHs & TS & HmHs & HTS).
    destruct (proj1 (mdenote_grow_all _ _ _ _ Hgs Hg Hsub) _ _ _ HmHs) as (RH2 & HmH2 & HgrH).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmH2 _ HmH) in HgrH.
    pose proof (mdesc_grows_mtele _ _ _ _ _ _ _ HgrH HTS) as HTS'; rewrite HTH in HTS'; injection HTS' as <-.
    destruct (mod_next_param_typed _ _ Hgs _ _ _ _ _ _ HHs HmHs HTS HvH) as (SrtBs & HSBs & HBs).
    assert (Hsks : exists κs, sort_kind SrtBs κs) by (destruct HSBs; eexists; econstructor).
    destruct Hsks as [κs Hsks].
    pose proof (mem_desc_ok _ _ _ _ _ _ _ (gctx_valid_syn _ _ Hgs) HHs HmRs) as Hoks.
    destruct (desc_ok_ty_sorted _ _ (gctx_valid_syn _ _ Hgs) _ _ _ Hoks HtRs) as [(Sts & HSts & HAs) _].
    destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HAs) as [Sds lcs Hskds HBds _ _].
    pose proof (AnnotatedUpto.exp_eq_same_kind _ _ _ _ _ _ _ _ _ (wf_exp_eq_refl HBds) Hskds HBs Hsks) as Eks.
    subst κs.
    assert (HΓBs : ⊢ Θs ⍮ Ξs ⍮ Γ ▹{domain_kind a} BH) by (eapply wf_ctx_extend; eassumption).
    assert (HWks : Θs ⍮ Ξs ⍮ Γ ▹{domain_kind a} BH ⊢ˢ Wk : Γ) by (eapply wf_sub_shift; exact HΓBs).
    pose proof (@wf_me_app_shift (gc_mk Θs Ξs) _ _ _ _ _ _ _ _ HHs HmHs HTS HvH HBs HSBs Hsks) as HHapps.
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HHs HmRs HWks) as HmRws.
    pose proof (mdesc_type_sub _ _ Wk HtRs) as HtRws.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HxAs HWks) as HxAws; cbn [exp_sub] in HxAws.
    destruct (@wf_exp_eq_mem_app (gc_mk Θs Ξs) Hgs _ _ _ _ _ _ HHapps (Hnfs _ _ HWks) HmRws HtRws HxAws)
      as (B1s & C1s & Rs' & [_ Hpis Hmems Hmtys Heqs]).
    destruct Hpis as (κs1 & κcs & HApis); cbn in HApis; injection HApis as _ _ _ <-.
    pose proof (presup_exp_eq_right Heqs) as HxAs'.
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
      destruct (IH x Rs' _ _ _ _ _ _ _ _ _ _ _ _ _
                  ltac:(intros; cbn [modexp_sub]; apply names_no_frame_of_none; reflexivity)
                  ltac:(intros; cbn [modexp_sub]; apply names_no_frame_of_none; reflexivity)
                  HHapps Hmems Hmtys HxAs' (type_sort_abs_kind _ _ (type_sort_universe lc)) HCt' HxA'
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

End MembersFromSource.
