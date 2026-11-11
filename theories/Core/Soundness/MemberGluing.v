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
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation ModuleValues Selection MemberApp.
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

(** A term glued at its own type value is glued at a related type value,
    at any type glued there: the two types are equal
    ([glu_univ_elem_per_univ_typ_escape], at an index above both), and the
    term moves along the type values ([glu_univ_elem_exp_conv]). *)
Lemma glu_elem_to_target : forall {ie i : nat} {k : universe_index} {ae a Pe Ele P El Δ A T M m},
    Dom ae ≈ a ∈ per_univ k -> DG ae ∈ glu_univ_elem ie ↘ Pe ↘ Ele -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort ae -> Δ ⊢ M : A ® m ∈ Ele -> Δ ⊢ T ® P ->
    (exists l : nat, Δ ⊢ A ≈ T : abs_kind_sort (domain_kind a) Typeω@l) /\ Δ ⊢ M : T ® m ∈ El.
Proof.
  intros * [R HR] Hge Hga Hnl HM HT.
  set (n := Nat.max (Nat.max ie i) (large_level k)).
  destruct (glu_univ_elem_cumu_ge (i := ie) (j := n) ltac:(unfold n; lia) Hge) as (Pn & Eln & Hgn).
  destruct (glu_univ_elem_cumu_ge (i := i) (j := n) ltac:(unfold n; lia) Hga) as (Pn' & Eln' & Hgn').
  pose proof (glu_univ_elem_exp_cumu_ge (i := ie) (j := n) ltac:(unfold n; lia) Hge Hgn HM) as HMn.
  pose proof (glu_univ_elem_trm_typ _ _ _ _ Hgn _ _ _ _ HMn) as HAn.
  pose proof (glu_univ_elem_typ_cumu_ge (i := i) (j := n) ltac:(unfold n; lia) Hga Hgn' HT) as HTn.
  assert (HRn : Dom ae ≈ a ∈ per_univ n)
    by (exists R; eapply per_univ_elem_cumu_universe_index; [ exact HR | apply universe_index_le_ul_max; unfold n; lia ]).
  pose proof (glu_univ_elem_per_univ_typ_escape HRn Hgn Hgn' Hnl HAn HTn) as HAT.
  pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgn _ _ _ _ _ HMn HAT) as HMT.
  rewrite (per_univ_elem_kind _ _ _ _ HR) in HAT.
  split; [ eexists; exact HAT |].
  exact (glu_univ_elem_exp_conv HRn Hgn Hga HMT HT).
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

End Fixed_GCtx.
