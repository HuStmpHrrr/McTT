(** * Views Agree with their Containers in the Gluing Model

    An element of a view's type, glued at the type's container member, is
    an element of the view in the group's gluing ([glu_view_end_at]).  By
    induction on the container's gluing of the element: a constructor of
    the container's member is one of the group's member the view takes it
    to, with the view's own parameters and arguments, which are glued at the
    group's telescopes since the two telescopes are equal at the view's
    instance; a recursive argument of both is one of the group's by the
    induction; an argument the view nests through is one of the group's
    members the view nests through, of a lower rank.  By induction on the
    ranks of the views, every view agrees ([glu_views_ok_all]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes FiledViews ViewEquations ViewArgs.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup DescTyping.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Inductives Require Views.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Elements at Related Types

    A term glued at a type of a value is glued at an equal type of a related
    value, at any gluing of it where that type is glued. *)
Lemma glu_elem_conv : forall (i j : uidx) (k l : nat) a a' P El P' El' Γ T T' N x,
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' -> DG a ∈ glu_univ_elem j ↘ P ↘ El -> Dom a' ≈ a ∈ per_univ k ->
    Γ ⊢ T' ≈ T : Typeω@l -> Γ ⊢ T ® P -> Γ ⊢ N : T' ® x ∈ El' -> Γ ⊢ N : T ® x ∈ El.
Proof.
  intros * Hg' Hg [R HR] HTT HT HN.
  set (n := Nat.max (ulvl i) (Nat.max (ulvl j) (Nat.max k l))).
  assert (Hin : uidx_le i (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  assert (Hjn : uidx_le j (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_uidx Hin Hg') as (Pn & Eln & Hgn).
  pose proof (glu_univ_elem_exp_cumu_ge_uidx Hin Hg' Hgn HN) as HNn.
  pose proof (per_univ_elem_cumu_ge k n _ _ _ ltac:(unfold n; lia) HR) as HRn.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R HRn) Hgn) as Hgn'.
  pose proof (lift_exp_eq_ge _ _ _ _ _ l n ltac:(unfold n; lia) HTT) as HTTn.
  pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgn' _ _ _ _ _ HNn HTTn) as HNn'.
  exact (glu_univ_elem_exp_lower_uidx Hjn Hg Hgn' HT HNn').
Qed.

(** The view's instance commutes with weakening. *)
Lemma view_args_wk : forall Is Us φ, List.Forall (exp_scoped (List.length Us)) Is ->
    List.map (fun X => X[φ]ʷ) (List.map (fun I => I[sb_of_list Id Us]) Is)
    = List.map (fun I => I[sb_of_list Id (List.map (fun U => U[φ]ʷ) Us)]) Is.
Proof.
  intros * Hs; rewrite List.map_map; apply List.map_ext_in; intros I HI.
  rewrite List.Forall_forall in Hs.
  rewrite exp_wk_sub, (exp_sub_sb_eq _ _ _ (sb_wk_sb_of_list Us Id φ)).
  apply (exp_scoped_sub_agree _ (List.length Us)); [ exact (Hs _ HI) |].
  intros x Hx.
  rewrite (sb_of_list_nth _ _ x (a_var 0)), (sb_of_list_nth _ Id x (a_var 0)) by (rewrite List.length_map; exact Hx).
  reflexivity.
Qed.

(** ** From the Container's Gluing to the Group's *)

Section ToGroup.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := vgr_lookup _ _ Hg.
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hsu := vgr_sort _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Let Hdt := vgr_typed _ _ Hg.
  (** The group's clause. *)
  Variables (ups : list domain) (bu : domain) (u : uidx)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups)
    (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).
  (** The view and its container. *)
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Let HgQ := Hcv _ _ _ _ _ _ _ HMk Hh Hq.
  Let HcQ := vgr_closed _ _ HgQ.
  Let HassQ := vgr_ass _ _ HgQ.
  Let HPq := valid_groups_containers VP HVP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq.
  Let HcvQ := containers_valid_of_groups VP HVP qc Dq HPq.
  (** The container's clause, at the view's instance. *)
  Variables (cups : list domain).
  Hypothesis (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups).
  Variables (u' : uidx)
    (NP' : nat -> nat -> list domain -> glu_typ_pred) (NEl' : nat -> nat -> list domain -> glu_exp_pred)
    (AP' : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP' : nat -> list domain -> exp -> glu_typ_pred) (DEl' : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hf' : ind_fams_glu Dq cups u' NP' NEl' AP' AEl' DP' DEl').

  Let view_args (Us : list exp) : list exp := List.map (fun I => I[sb_of_list Id Us]) Is.

  Lemma length_view_args : forall Us, List.length (view_args Us) = ind_nu Dq.
  Proof. intros; unfold view_args; rewrite List.length_map; exact (view_is_length VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq). Qed.

  Lemma length_cups : List.length cups = ind_nu Dq.
  Proof. rewrite (eval_exps_length _ _ _ Ecups); exact (view_is_length VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq). Qed.

  (** *** At a Constructor of a Member of the Container *)

  Section AtCon.
    Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember) (c : String.string) (gs' gs : list carg).
    Hypotheses (HMi' : ind_member Dq i' = Some Mi') (HVM : view_member p D qc Dq vm i' Mi' v Mv)
      (Hcon' : ind_con Mi' c = Some gs') (Hcon : ind_con Mv c = Some gs) (Hcorr : cargs_corr vm gs' gs).
    Let Hv := vmb_v _ _ _ _ _ _ _ _ _ HVM.
    Let HMv := vmb_mem _ _ _ _ _ _ _ _ _ HVM.
    Variables (Γ : ctx) (Us Ns : list exp) (ns : list domain).
    Hypotheses (HΓ : ⊢ Γ) (HUs : glu_args Γ (ind_uparams D) Id nil Us ups)
      (Hns' : tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ns ns)
      (Hnp' : glu_nparams i' Mi' NEl' Γ (view_args Us) Ns ns).

    Lemma at_ns_g : tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mv)) ns ns.
    Proof. exact (view_nparams_transfer p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv _ _ Hns'). Qed.

    Lemma at_nparams_c : glu_args Γ (im_nparams Mi') (sb_of_list Id (view_args Us)) (env_args nil cups) Ns ns.
    Proof. exact (glu_args_of_nparams Dq cups u' NP' NEl' AP' AEl' DP' DEl' Hf' i' Mi' Γ (view_args Us) Ns ns HMi' Hnp' Hns'). Qed.

    Lemma at_nparams_glu : glu_args Γ (im_nparams Mv) (sb_of_list Id Us) (env_args nil ups) Ns ns.
    Proof. exact (view_nparams_glu_rev VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq Γ Us Ns ups ns cups i' Mi' v Mv HΓ Hu HUs HMi' Hv HMv at_nparams_c Ecups). Qed.

    Lemma at_comps : ind_glu_comps p D ups NP NEl AP AEl DP DEl Γ Us.
    Proof. exact (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Γ Us HΓ HUs). Qed.

    Lemma at_nparams : glu_nparams v Mv NEl Γ Us Ns ns.
    Proof. exact (nparams_of_glu_args p D Hass ups u NP NEl AP AEl DP DEl Hu Hf v Mv Γ Us Ns ns HMv at_comps at_nparams_glu at_ns_g). Qed.

    Lemma at_params : glu_args Γ (im_params D Mv) Id nil (Us ++ Ns) (ups ++ ns).
    Proof.
      destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
      unfold im_params; apply glu_args_app; [ exact (dc_ass _ Hc) | exact HUl | exact Hu |].
      split; [ exact HUs | exact at_nparams_glu ].
    Qed.

    Lemma at_params_c : glu_args Γ (im_params Dq Mi') Id nil (view_args Us ++ Ns) (cups ++ ns).
    Proof.
      unfold im_params; apply glu_args_app; [ exact (dc_ass _ HcQ) | exact (length_view_args Us) | exact length_cups |].
      split; [ exact (view_uparams_glu VP p D HVP HPD HG k Mk qc kc Is vm Dq HMk Hh Hq Γ Us ups cups HΓ HUs Ecups)
             | exact at_nparams_c ].
    Qed.
  End AtCon.
End ToGroup.

End Fixed_GCtx.
