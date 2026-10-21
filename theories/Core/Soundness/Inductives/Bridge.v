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

(** ** A View's Telescopes, Syntactically

    For a view [k] of a group [D], with the container's member [i'] taken
    to the group's member [v]: terms typed at the parameters and arguments
    of one of the two members (the container's at the view's instance) are
    typed at the other's, the types there being equal. *)
Section ViewSyn.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hdt : decl_typed gc_deps gc_stack D) (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hc : decl_closed D).
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq) (HcQ : decl_closed Dq).
  Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
  Hypotheses (HMi' : ind_member Dq i' = Some Mi') (Hv : List.nth_error vm i' = Some v) (HMv : ind_member D v = Some Mv).

  Lemma vs_is_length : List.length Is = ind_nu Dq.
  Proof.
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-; exact HIl.
  Qed.

  Lemma vs_nn : im_nn Mv = im_nn Mi'.
  Proof.
    destruct (dt_vwrap _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    destruct (vwo_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv' & HMv' & Hnn & _).
    rewrite HMv in HMv'; injection HMv' as <-; exact Hnn.
  Qed.

  Lemma vs_params_sub : forall Γ Ps, ⊢ Γ -> List.length Ps = im_np D Mv ->
      (forall j X T, List.nth_error Ps j = Some X -> List.nth_error (tele_insts (im_params D Mv) Id Ps) j = Some T -> Γ ⊢ X : T) ->
      Γ ⊢ˢ sb_of_list Id Ps : im_params D Mv.
  Proof.
    intros * HΓ HPl HPs; rewrite <- (List.app_nil_r (im_params D Mv)).
    eapply wf_sub_of_list; [ exact (decl_closed_params_ass D v Mv Hc HMv) | rewrite List.app_nil_r; exact (member_params_wf _ _ _ _ _ Hdt HMv)
                           | exact (wf_sub_to_nil _ _ _ HΓ) | rewrite length_im_params; exact HPl | exact HPs ].
  Qed.

  Lemma vs_insts_sub : forall X σ As, tele_insts (tele_sub X σ) Id As = tele_insts X σ As.
  Proof. intros; rewrite tele_insts_tele_sub; apply tele_insts_sb_eq, sb_compose_id_right. Qed.

  (** *** The Arguments *)

  Lemma vs_args_insts : forall Us Ns c gs' As, List.length Ns = im_nn Mv -> ind_con Mi' c = Some gs' ->
      tele_insts (tele_sub (tele_sub (cargs_ctx qc Dq Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id Is))) (sb_of_list Id (Us ++ Ns))) Id As
      = tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As.
  Proof.
    intros * HlNs Hcon'.
    rewrite !tele_insts_tele_sub.
    apply (tele_insts_agree _ (im_np Dq Mi')); [ apply cargs_ctx_aux_ass
                                               | exact (decl_closed_cargs_scoped Dq HcQ qc _ _ c gs' HMi' (cons_lookup_in _ _ _ Hcon')) |].
    intros x Hx; rewrite <- HlNs.
    apply sb_qn_list_agree; rewrite vs_is_length; unfold im_np in Hx; rewrite HlNs, vs_nn; lia.
  Qed.

  Lemma vs_args_ext : forall Γ Us Ns c gs' gs, ⊢ Γ -> List.length (Us ++ Ns) = im_np D Mv ->
      (forall j X T, List.nth_error (Us ++ Ns) j = Some X -> List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T) ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ tele_sub (tele_sub (cargs_ctx qc Dq Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id Is))) (sb_of_list Id (Us ++ Ns))
        ≈ tele_sub (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)).
  Proof.
    intros * HΓ HPl HPs Hcon' Hcon.
    pose proof (dt_view_args _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv Hcon' Hcon) as Hext.
    exact (sub_preserves_ext _ _ _ _ _ _ _ Hext (vs_params_sub Γ (Us ++ Ns) HΓ HPl HPs)).
  Qed.

  Lemma vs_args_eq_c : forall Γ Us Ns As c gs' gs, ⊢ Γ -> List.length Us = ind_nu D -> List.length Ns = im_nn Mv ->
      (forall j X T, List.nth_error (Us ++ Ns) j = Some X -> List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T) ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> List.length As = List.length gs' ->
      (forall j N T, List.nth_error As j = Some N ->
         List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) j = Some T ->
         Γ ⊢ N : T) ->
      forall j T' T, List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) j = Some T' ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T ->
        exists i, Γ ⊢ T' ≈ T : Typeω@i.
  Proof.
    intros * HΓ HUl HNl HPs Hcon' Hcon HAl HAs j T' T HT' HT.
    pose proof (vs_args_ext Γ Us Ns c gs' gs HΓ ltac:(rewrite List.length_app; unfold im_np; lia) HPs Hcon' Hcon) as He.
    rewrite <- (vs_insts_sub (cargs_ctx p D Mv gs)) in HT.
    rewrite <- (vs_args_insts Us Ns c gs' As HNl Hcon') in HT'.
    eapply (tele_insts_ext_eq Γ _ _ As He (tele_ass_sub _ _ (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _)))
              (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _))
              ltac:(rewrite !length_tele_sub, length_cargs_ctx; exact HAl)); [| exact HT' | exact HT ].
    intros j0 N T0 HN HT0; rewrite (vs_args_insts Us Ns c gs' As HNl Hcon') in HT0; exact (HAs _ _ _ HN HT0).
  Qed.

  Lemma vs_args_eq_g : forall Γ Us Ns As c gs' gs, ⊢ Γ -> List.length Us = ind_nu D -> List.length Ns = im_nn Mv ->
      (forall j X T, List.nth_error (Us ++ Ns) j = Some X -> List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T) ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> List.length As = List.length gs ->
      (forall j N T, List.nth_error As j = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T ->
         Γ ⊢ N : T) ->
      forall j T T', List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T ->
        List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) j = Some T' ->
        exists i, Γ ⊢ T ≈ T' : Typeω@i.
  Proof.
    intros * HΓ HUl HNl HPs Hcon' Hcon HAl HAs j T T' HT HT'.
    pose proof (vs_args_ext Γ Us Ns c gs' gs HΓ ltac:(rewrite List.length_app; unfold im_np; lia) HPs Hcon' Hcon) as He.
    apply Views.ext_eq_sym_ass in He; [| apply tele_ass_sub, tele_ass_sub, cargs_ctx_aux_ass ].
    rewrite <- (vs_insts_sub (cargs_ctx p D Mv gs)) in HT.
    rewrite <- (vs_args_insts Us Ns c gs' As HNl Hcon') in HT'.
    eapply (tele_insts_ext_eq Γ _ _ As He (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _))
              (tele_ass_sub _ _ (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _)))
              ltac:(rewrite length_tele_sub, length_cargs_ctx; exact HAl)); [| exact HT | exact HT' ].
    intros j0 N T0 HN HT0; rewrite vs_insts_sub in HT0; exact (HAs _ _ _ HN HT0).
  Qed.

  Lemma vs_args_typed_g : forall Γ Us Ns As c gs' gs, ⊢ Γ -> List.length Us = ind_nu D -> List.length Ns = im_nn Mv ->
      (forall j X T, List.nth_error (Us ++ Ns) j = Some X -> List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T) ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> List.length As = List.length gs' ->
      (forall j N T, List.nth_error As j = Some N ->
         List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) j = Some T ->
         Γ ⊢ N : T) ->
      forall j N T, List.nth_error As j = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T ->
        Γ ⊢ N : T.
  Proof.
    intros * HΓ HUl HNl HPs Hcon' Hcon HAl HAs j N T HN HT.
    assert (Hj : j < List.length As) by (apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) j)
      as [T' HT']; [ rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia |].
    destruct (vs_args_eq_c Γ Us Ns As c gs' gs HΓ HUl HNl HPs Hcon' Hcon HAl HAs j T' T HT' HT) as [i Hi].
    eapply wf_conv; [ exact (HAs _ _ _ HN HT') | | exact Hi ].
    gen_presups; eassumption.
  Qed.

  Lemma vs_args_typed_c : forall Γ Us Ns As c gs' gs, ⊢ Γ -> List.length Us = ind_nu D -> List.length Ns = im_nn Mv ->
      (forall j X T, List.nth_error (Us ++ Ns) j = Some X -> List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T) ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> List.length As = List.length gs ->
      (forall j N T, List.nth_error As j = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T ->
         Γ ⊢ N : T) ->
      forall j N T, List.nth_error As j = Some N ->
        List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) j = Some T ->
        Γ ⊢ N : T.
  Proof.
    intros * HΓ HUl HNl HPs Hcon' Hcon HAl HAs j N T HN HT.
    assert (Hj : j < List.length As) by (apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) j)
      as [T' HT']; [ rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia |].
    destruct (vs_args_eq_g Γ Us Ns As c gs' gs HΓ HUl HNl HPs Hcon' Hcon HAl HAs j T' T HT' HT) as [i Hi].
    eapply wf_conv; [ exact (HAs _ _ _ HN HT') | | exact Hi ].
    gen_presups; eassumption.
  Qed.

  (** *** The Parameters *)

  Lemma vs_nparams_insts : forall Us Ns, List.length Us = ind_nu D ->
      tele_insts (tele_sub (tele_sub (im_nparams Mi') (sb_of_list Id Is)) (sb_of_list Id Us)) Id Ns
      = tele_insts (im_nparams Mi') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)) Ns.
  Proof.
    intros * HUl.
    rewrite vs_insts_sub, tele_insts_tele_sub.
    apply (tele_insts_agree _ (ind_nu Dq)); [ exact (decl_closed_nparams_ass Dq HcQ _ _ HMi') | exact (decl_closed_nparams_scoped Dq HcQ _ _ HMi') |].
    intros x Hx; rewrite <- vs_is_length in Hx.
    exact (sb_of_list_map_nth Is (sb_of_list Id Us) x Hx).
  Qed.

  Lemma vs_nparams_ext : forall Γ Us, ⊢ Γ -> List.length Us = ind_nu D ->
      (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ tele_sub (im_nparams Mv) (sb_of_list Id Us)
        ≈ tele_sub (tele_sub (im_nparams Mi') (sb_of_list Id Is)) (sb_of_list Id Us).
  Proof.
    intros * HΓ HUl HUs.
    pose proof (dt_view_nparams _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv) as Hext.
    exact (sub_preserves_ext _ _ _ _ _ _ _ Hext (wf_uparams_sub _ _ _ _ _ Hdt HΓ HUl HUs)).
  Qed.

  Lemma vs_nparams_typed_c : forall Γ Us Ns, ⊢ Γ -> List.length Us = ind_nu D -> List.length Ns = im_nn Mv ->
      (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
      (forall j N T, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams Mv) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N : T) ->
      forall j N T, List.nth_error Ns j = Some N ->
        List.nth_error (tele_insts (im_nparams Mi') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)) Ns) j = Some T ->
        Γ ⊢ N : T.
  Proof.
    intros * HΓ HUl HNl HUs HNs j N T HN HT.
    pose proof (vs_nparams_ext Γ Us HΓ HUl HUs) as He.
    assert (Hj : j < List.length Ns) by (apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts (im_nparams Mv) (sb_of_list Id Us) Ns) j) as [T0 HT0];
      [ rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMv); rewrite length_im_nparams; lia |].
    rewrite <- vs_insts_sub in HT0; rewrite <- (vs_nparams_insts Us Ns HUl) in HT.
    destruct (tele_insts_ext_eq Γ _ _ Ns He (tele_ass_sub _ _ (decl_closed_nparams_ass D Hc _ _ HMv))
                (tele_ass_sub _ _ (tele_ass_sub _ _ (decl_closed_nparams_ass Dq HcQ _ _ HMi')))
                ltac:(rewrite length_tele_sub, length_im_nparams; lia)
                ltac:(intros j0 N0 T1 HN0 HT1; rewrite vs_insts_sub in HT1; exact (HNs _ _ _ HN0 HT1))
                j T0 T HT0 HT) as [i Hi].
    rewrite vs_insts_sub in HT0.
    eapply wf_conv; [ exact (HNs _ _ _ HN HT0) | | exact Hi ].
    gen_presups; eassumption.
  Qed.

  (** The parameters at the group's member, typed, are typed at the
      container's at the view's instance. *)
  Lemma vs_params_typed_c : forall Γ Us Ns, ⊢ Γ -> List.length Us = ind_nu D -> List.length Ns = im_nn Mv ->
      (forall j X T, List.nth_error (Us ++ Ns) j = Some X -> List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T) ->
      forall j X T, List.nth_error (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) j = Some X ->
        List.nth_error (tele_insts (im_params Dq Mi') Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) j = Some T -> Γ ⊢ X : T.
  Proof.
    intros * HΓ HUl HNl HPs.
    destruct (params_typed_split _ _ D Hc v Mv Γ (Us ++ Ns) HMv ltac:(rewrite List.length_app; unfold im_np; lia) HPs) as [HUs HNs].
    rewrite firstn_app_exact in HUs, HNs by exact HUl; rewrite skipn_app_exact in HNs by exact HUl.
    unfold im_params; apply Views.list_typed_app;
      [ exact (dc_ass _ HcQ) | rewrite List.length_map, vs_is_length; reflexivity
      | exact (Views.view_is_typed _ _ _ _ _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hl Hdt HcQ HMk Hh Hq HΓ HUl HUs)
      | exact (vs_nparams_typed_c Γ Us Ns HΓ HUl HNl HUs HNs) ].
  Qed.

  (** Parameters equal at the group's member are equal at the container's
      at the view's instance. *)
  Lemma vs_params_eq_transfer : forall Γ Us1 Us2 X Y, ⊢ Γ -> List.length Us1 = ind_nu D -> List.length X = im_nn Mv ->
      List.length Us2 = ind_nu D -> exps_eq_at Γ (im_params D Mv) (Us1 ++ X) (Us2 ++ Y) ->
      exps_eq_at Γ (im_params Dq Mi') (List.map (fun I => I[sb_of_list Id Us1]) Is ++ X) (List.map (fun I => I[sb_of_list Id Us2]) Is ++ Y).
  Proof.
    intros * HΓ HU1 HXl HU2 [HlE HE].
    rewrite !List.length_app in HlE.
    assert (HYl : List.length Y = im_nn Mv) by lia.
    pose proof (decl_closed_nparams_ass D Hc _ _ HMv) as HaV.
    assert (HtiG : forall Ws Zs, List.length Ws = ind_nu D ->
               tele_insts (im_params D Mv) Id (Ws ++ Zs) = tele_insts (ind_uparams D) Id Ws ++ tele_insts (im_nparams Mv) (sb_of_list Id Ws) Zs)
      by (intros; unfold im_params; apply tele_insts_app; [ exact (dc_ass _ Hc) | assumption ]).
    assert (HlU : forall Ws, List.length Ws = ind_nu D -> List.length (tele_insts (ind_uparams D) Id Ws) = ind_nu D)
      by (intros; rewrite length_tele_insts by exact (dc_ass _ Hc); unfold ind_nu in *; lia).
    (** Both sides typed. *)
    assert (HPs1 : forall j Z T, List.nth_error (Us1 ++ X) j = Some Z -> List.nth_error (tele_insts (im_params D Mv) Id (Us1 ++ X)) j = Some T ->
                     Γ ⊢ Z : T).
    { intros j Z T HZ HT.
      destruct (nth_error_lt_some (Us2 ++ Y) j) as [W HW];
        [ assert (j < List.length (Us1 ++ X)) by (apply List.nth_error_Some; congruence); rewrite List.length_app in *; lia |].
      pose proof (HE _ _ _ _ HZ HW HT) as H; gen_presups; eassumption. }
    destruct (params_typed_split _ _ D Hc v Mv Γ (Us1 ++ X) HMv ltac:(rewrite List.length_app; unfold im_np; lia) HPs1) as [HUs1 HXs].
    rewrite firstn_app_exact in HUs1, HXs by exact HU1; rewrite skipn_app_exact in HXs by exact HU1.
    assert (HEq : exps_eq_at Γ (im_params D Mv) (Us1 ++ X) (Us2 ++ Y)) by (split; [ rewrite !List.length_app; lia | exact HE ]).
    pose proof (exps_eq_at_typed_r p D v Mv Γ (Us1 ++ X) (Us2 ++ Y) Hl HMv HΓ ltac:(rewrite List.length_app; unfold im_np; lia) HEq)
      as HPs2.
    destruct (params_typed_split _ _ D Hc v Mv Γ (Us2 ++ Y) HMv ltac:(rewrite List.length_app; unfold im_np; lia) HPs2) as [HUs2 _].
    rewrite firstn_app_exact in HUs2 by exact HU2.
    (** The uniform parameters: an equal instance. *)
    assert (Hσ : Γ ⊢ˢ sb_of_list Id Us1 ≈ sb_of_list Id Us2 : ind_uparams D).
    { rewrite <- (List.app_nil_r (ind_uparams D)).
      apply Views.wf_sub_eq_of_list_conv;
        [ exact (dc_ass _ Hc) | rewrite List.app_nil_r; exact (dt_uparams _ _ _ Hdt) | apply wf_sub_eq_refl, wf_sub_to_nil, HΓ
        | exact HU1 | exact HU2 | exact HUs1 | exact HUs2 |].
      intros j Z W T HZ HW HT.
      assert (Hj1 : j < List.length Us1) by (apply List.nth_error_Some; congruence).
      apply (HE j); [ rewrite List.nth_error_app1 by lia; exact HZ | rewrite List.nth_error_app1 by lia; exact HW |].
      rewrite (HtiG Us1 X HU1), List.nth_error_app1 by (rewrite HlU by exact HU1; lia).
      exact HT. }
    pose proof (vs_is_length) as HIl.
    split; [ rewrite !List.length_app, !List.length_map; lia |].
    intros j Z W T HZ HW HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (first [ exact (dc_ass _ HcQ) | rewrite List.length_map, HIl; reflexivity ]).
    destruct (Nat.lt_ge_cases j (ind_nu Dq)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HZ, HW by (rewrite List.length_map; lia).
      rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (dc_ass _ HcQ); rewrite List.length_map; unfold ind_nu in *; lia).
      apply nth_error_map_inv in HZ as (I & HI & ->).
      rewrite List.nth_error_map, HI in HW; injection HW as <-.
      rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (sb_of_list Id Us1) Is (dc_ass _ HcQ) (dc_uparams _ HcQ) ltac:(intros; lia)) in HT.
      apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      exact (sub_eq_preserves_exp _ _ _ _ _ (dt_view_is _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HI HT0) _ _ _ Hσ).
    - rewrite List.nth_error_app2 in HZ, HW by (rewrite List.length_map; lia).
      rewrite List.length_map, HIl in HZ, HW.
      rewrite List.nth_error_app2 in HT by (rewrite length_tele_insts by exact (dc_ass _ HcQ); rewrite List.length_map; unfold ind_nu in *; lia).
      rewrite length_tele_insts, List.length_map, HIl in HT by exact (dc_ass _ HcQ).
      replace (Nat.min (List.length (ind_uparams Dq)) (ind_nu Dq)) with (ind_nu Dq) in HT by (unfold ind_nu; lia).
      set (j' := j - ind_nu Dq) in *.
      destruct (nth_error_lt_some (tele_insts (im_nparams Mv) (sb_of_list Id Us1) X) j') as [T' HT'];
        [ rewrite length_tele_insts by exact HaV; rewrite length_im_nparams;
          assert (j' < List.length X) by (apply List.nth_error_Some; congruence); lia |].
      assert (HZW : Γ ⊢ Z ≈ W : T').
      { apply (HE (ind_nu D + j')).
        - rewrite List.nth_error_app2 by lia; rewrite HU1; replace (ind_nu D + j' - ind_nu D) with j' by lia; exact HZ.
        - rewrite List.nth_error_app2 by lia; rewrite HU2; replace (ind_nu D + j' - ind_nu D) with j' by lia; exact HW.
        - rewrite (HtiG Us1 X HU1), List.nth_error_app2 by (rewrite HlU by exact HU1; lia).
          rewrite HlU by exact HU1; replace (ind_nu D + j' - ind_nu D) with j' by lia; exact HT'. }
      pose proof (vs_nparams_ext Γ Us1 HΓ HU1 HUs1) as He.
      rewrite <- vs_insts_sub in HT'; rewrite <- (vs_nparams_insts Us1 X HU1) in HT.
      destruct (tele_insts_ext_eq Γ _ _ X He (tele_ass_sub _ _ HaV) (tele_ass_sub _ _ (tele_ass_sub _ _ (decl_closed_nparams_ass Dq HcQ _ _ HMi')))
                  ltac:(rewrite length_tele_sub, length_im_nparams; lia)
                  ltac:(intros j0 N0 T1 HN0 HT1; rewrite vs_insts_sub in HT1; exact (HXs _ _ _ HN0 HT1))
                  j' T' T HT' HT) as [i Hi].
      eapply wf_exp_eq_conv; [ exact HZW | | exact Hi ].
      gen_presups; eassumption.
  Qed.
End ViewSyn.

(** A constructor of a view, applied to typed parameters and arguments, is
    the constructor of the container's member it views at the view's
    instance. *)
Lemma view_head_con_eq : forall g G j Mj qh kh Ih vmh Dh Mkh,
    decl_typed gc_deps gc_stack G -> ind_lookup gc_deps gc_stack g = Some G -> decl_closed G ->
    ind_member G j = Some Mj -> im_head Mj = mh_view qh kh Ih vmh -> ind_lookup gc_deps gc_stack qh = Some Dh ->
    ind_member Dh kh = Some Mkh ->
    forall Γ Us Ns As c gs gh, ⊢ Γ -> List.length Us = ind_nu G -> List.length Ns = im_nn Mj ->
      (forall i X T, List.nth_error (Us ++ Ns) i = Some X -> List.nth_error (tele_insts (im_params G Mj) Id (Us ++ Ns)) i = Some T -> Γ ⊢ X : T) ->
      ind_con Mkh c = Some gh -> ind_con Mj c = Some gs -> List.length As = List.length gs ->
      (forall i N T, List.nth_error As i = Some N -> List.nth_error (tele_insts (cargs_ctx g G Mj gs) (sb_of_list Id (Us ++ Ns)) As) i = Some T ->
         Γ ⊢ N : T) ->
      Γ ⊢ apps (a_con g j c) (Us ++ Ns ++ As) ≈ apps (a_con qh kh c) (List.map (fun I => I[sb_of_list Id Us]) Ih ++ Ns ++ As)
        : im_ty_at g j Mj Us Ns.
Proof.
  intros * Hdt Hl Hc HMj Hh Hq HMkh Γ Us Ns As c gs gh HΓ HUl HNl HPs Hcon' Hcon HAl HAs.
  destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dh' & Mkh' & Hq' & HMkh' & Hlt & _ & _ & Hvk & _ & Hcorr).
  rewrite Hq in Hq'; injection Hq' as <-; rewrite HMkh in HMkh'; injection HMkh' as <-.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hq) as [HdtH HcH].
  assert (Hdecl : im_is_decl Mkh = true) by (apply (dt_order _ _ _ HdtH _ _ HMkh); exact Hlt).
  pose proof (cargs_corr_length _ _ _ (Hcorr _ _ _ Hcon' Hcon)) as Hlg.
  pose proof (vs_is_length G Hdt j Mj qh kh Ih vmh Dh HMj Hh Hq) as HIl.
  pose proof (vs_nn G Hdt j Mj qh kh Ih vmh Dh HMj Hh Hq kh Mkh j Mj HMkh Hvk HMj) as Hnn.
  pose proof (vs_params_typed_c g G Hdt Hl Hc j Mj qh kh Ih vmh Dh HMj Hh Hq HcH kh Mkh j Mj HMkh Hvk HMj Γ Us Ns HΓ HUl HNl HPs)
    as HPs'.
  pose proof (vs_args_typed_c g G Hdt Hl Hc j Mj qh kh Ih vmh Dh HMj Hh Hq HcH kh Mkh j Mj HMkh Hvk HMj Γ Us Ns As c gh gs
                HΓ HUl HNl HPs Hcon' Hcon HAl HAs) as HAs'.
  set (Us' := List.map (fun I => I[sb_of_list Id Us]) Ih) in *.
  assert (HUl' : List.length Us' = ind_nu Dh) by (unfold Us'; rewrite List.length_map; exact HIl).
  pose proof (wf_exp_eq_con_apps_member Γ g G j Mj c gs (Us ++ Ns) (Us ++ Ns) As As Hl HMj Hcon HΓ
                ltac:(rewrite List.length_app; unfold im_np; lia) ltac:(rewrite List.length_app; unfold im_np; lia)
                ltac:(intros i0 P0 P0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HPs; eassumption)
                HAl HAl
                ltac:(intros i0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HAs; eassumption))
    as HL.
  rewrite firstn_app_exact, skipn_app_exact, <- List.app_assoc in HL by exact HUl.
  unfold ind_mty in HL; rewrite HMj in HL.
  pose proof (wf_exp_eq_con_apps_member Γ qh Dh kh Mkh c gh (Us' ++ Ns) (Us' ++ Ns) As As Hq HMkh Hcon' HΓ
                ltac:(rewrite List.length_app; unfold im_np; lia) ltac:(rewrite List.length_app; unfold im_np; lia)
                ltac:(intros i0 P0 P0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HPs'; eassumption)
                ltac:(lia) ltac:(lia)
                ltac:(intros i0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HAs'; eassumption))
    as HR.
  rewrite firstn_app_exact, skipn_app_exact, <- List.app_assoc in HR by exact HUl'.
  unfold ind_mty in HR; rewrite HMkh in HR.
  assert (ET : im_ty_at qh kh Mkh Us' Ns = im_ty_at g j Mj Us Ns).
  { unfold im_ty_at, im_ref, im_pre; rewrite Hh.
    unfold im_is_decl in Hdecl; destruct (im_head Mkh); [ reflexivity | discriminate ]. }
  rewrite ET in HR.
  replace (Us' ++ Ns ++ As) with (im_pre Mj Us ++ Ns ++ As) by (unfold im_pre; rewrite Hh; reflexivity).
  eapply wf_exp_eq_con_view; [ exact Hl | exact HMj | exact Hh | exact HUl | gen_presups; eassumption |].
  unfold im_pre; rewrite Hh; fold Us'; gen_presups; eassumption.
Qed.

(** ** The Heads of a View's Members

    The container's member [i'] and the group's member [v] the view takes
    it to have the same head: at the view's instance of typed parameters,
    the types of the two members are equal. *)
Section ViewHeads.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hdt : decl_typed gc_deps gc_stack D) (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hc : decl_closed D).
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
  Hypotheses (HMi' : ind_member Dq i' = Some Mi') (Hv : List.nth_error vm i' = Some v) (HMv : ind_member D v = Some Mv).
  Variables (Γ : ctx) (Us Ns : list exp).
  Hypotheses (HΓ : ⊢ Γ) (HUl : List.length Us = ind_nu D) (HNl : List.length Ns = im_nn Mv)
    (HPs : forall j X T, List.nth_error (Us ++ Ns) j = Some X ->
             List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T).

  Let HdtQ := proj1 (decl_of_lookup _ _ _ _ _ HΓ Hq).
  Let HcQ := proj2 (decl_of_lookup _ _ _ _ _ HΓ Hq).

  Lemma vh_vU_length : List.length (List.map (fun I => I[sb_of_list Id Us]) Is) = ind_nu Dq.
  Proof. rewrite List.length_map; exact (vs_is_length D Hdt k Mk qc kc Is vm Dq HMk Hh Hq). Qed.

  Lemma vh_ps_c : forall j X T, List.nth_error (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) j = Some X ->
      List.nth_error (tele_insts (im_params Dq Mi') Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) j = Some T -> Γ ⊢ X : T.
  Proof. exact (vs_params_typed_c p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq HcQ i' Mi' v Mv HMi' Hv HMv Γ Us Ns HΓ HUl HNl HPs). Qed.

  Lemma vh_uparams_typed : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T.
  Proof.
    destruct (params_typed_split _ _ D Hc v Mv Γ (Us ++ Ns) HMv ltac:(rewrite List.length_app; unfold im_np; lia) HPs) as [HUs _].
    rewrite firstn_app_exact in HUs by exact HUl; exact HUs.
  Qed.

  (** At a view of a view: the two instances of the uniform parameters of
      the head. *)
  Lemma vh_view_params_eq : forall qh kh Ihc vmc X vm' Dh Mkh, im_head Mi' = mh_view qh kh Ihc vmc -> im_head Mv = mh_view qh kh X vm' ->
      ind_lookup gc_deps gc_stack qh = Some Dh -> ind_member Dh kh = Some Mkh ->
      forall j Y Z T, List.nth_error (List.map (fun I => I[sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)]) Ihc ++ Ns) j = Some Y ->
        List.nth_error (List.map (fun I => I[sb_of_list Id Us]) X ++ Ns) j = Some Z ->
        List.nth_error (tele_insts (im_params Dh Mkh) Id
                          (List.map (fun I => I[sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)]) Ihc ++ Ns)) j = Some T ->
        Γ ⊢ Y ≈ Z : T.
  Proof.
    intros * Hhi Hhv HqH HMkh j Y Z T HY HZ HT.
    destruct (decl_of_lookup _ _ _ _ _ HΓ HqH) as [HdtH HcH].
    destruct (dt_view _ _ _ HdtQ _ _ _ _ _ _ HMi' Hhi) as (Dh' & Mkh' & HqH' & HMkh' & _ & _ & _ & Hvk & _).
    rewrite HqH in HqH'; injection HqH' as <-; rewrite HMkh in HMkh'; injection HMkh' as <-.
    pose proof (vs_is_length Dq HdtQ i' Mi' qh kh Ihc vmc Dh HMi' Hhi HqH) as HIcl.
    pose proof (vs_is_length D Hdt v Mv qh kh X vm' Dh HMv Hhv HqH) as HXl.
    pose proof (vs_nn D Hdt k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (vs_params_typed_c qc Dq HdtQ Hq HcQ i' Mi' qh kh Ihc vmc Dh HMi' Hhi HqH HcH kh Mkh i' Mi' HMkh Hvk HMi' Γ
                  (List.map (fun I => I[sb_of_list Id Us]) Is) Ns HΓ vh_vU_length ltac:(lia) vh_ps_c) as HPh.
    set (σU := sb_of_list Id Us) in *.
    set (vU := List.map (fun I => I[σU]) Is) in *.
    set (Pc := List.map (fun I => I[sb_of_list Id vU]) Ihc) in *.
    assert (HPcl : List.length Pc = ind_nu Dh) by (unfold Pc; rewrite List.length_map; exact HIcl).
    destruct (Nat.lt_ge_cases j (ind_nu Dh)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HY by lia.
      rewrite List.nth_error_app1 in HZ by (rewrite List.length_map; lia).
      unfold im_params in HT; rewrite tele_insts_app in HT by (first [ exact (dc_ass _ HcH) | exact HPcl ]).
      rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (dc_ass _ HcH); unfold ind_nu in *; lia).
      apply nth_error_map_inv in HZ as (Xj & HXj & ->).
      pose proof HY as HY0; unfold Pc in HY0; apply nth_error_map_inv in HY0 as (Ij & HIj & EY).
      destruct (nth_error_lt_some (tele_insts (ind_uparams Dh) Id Ihc) j) as [T0 HT0];
        [ rewrite length_tele_insts by exact (dc_ass _ HcH); unfold ind_nu in *; lia |].
      pose proof (dt_view_view_is _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v qh kh Ihc vmc Dh Mv X vm' j
                    Xj (Ij[sb_of_list Id Is]) T0 HMk Hh Hq HMi' Hhi HqH Hv HMv Hhv HXj
                    ltac:(rewrite List.nth_error_map, HIj; reflexivity) HT0) as HE.
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HE (wf_uparams_sub _ _ _ _ _ Hdt HΓ HUl vh_uparams_typed)) as HE'.
      fold σU in HE'.
      pose proof (Views.inst_sub_comm Ihc Is (ind_nu Dq) σU (decl_closed_head_scoped Dq HcQ _ _ _ _ _ _ HMi' Hhi)
                    (vs_is_length D Hdt k Mk qc kc Is vm Dq HMk Hh Hq)) as Ecomm.
      fold vU in Ecomm.
      assert (EY' : Y = Ij[sb_of_list Id Is][σU]).
      { rewrite EY; change (Ij[sb_of_list Id vU]) with ((fun I => I[sb_of_list Id vU]) Ij).
        apply (f_equal (fun l => List.nth_error l j)) in Ecomm.
        rewrite !List.nth_error_map, HIj in Ecomm; cbn in Ecomm; injection Ecomm as E; exact E. }
      assert (ET : T = T0[sb_of_list Id Is][σU]).
      { assert (EPc : Pc = List.map (fun M => M[σU]) (List.map (fun M => M[sb_of_list Id Is]) Ihc))
          by (unfold Pc; rewrite Ecomm, List.map_map; reflexivity).
        rewrite EPc in HT.
        rewrite <- (tele_insts_sub (ind_uparams Dh) 0 Id Id σU _ (dc_ass _ HcH) (dc_uparams _ HcH) ltac:(intros; lia)) in HT.
        rewrite <- (tele_insts_sub (ind_uparams Dh) 0 Id Id (sb_of_list Id Is) _ (dc_ass _ HcH) (dc_uparams _ HcH) ltac:(intros; lia)) in HT.
        rewrite !List.nth_error_map, HT0 in HT; cbn in HT; injection HT as <-; reflexivity. }
      rewrite EY', ET; symmetry; exact HE'.
    - rewrite List.nth_error_app2 in HY, HZ by (rewrite ?List.length_map; lia).
      rewrite List.length_map, HXl in HZ; rewrite HPcl in HY.
      rewrite HY in HZ; injection HZ as <-.
      apply wf_exp_eq_refl; eapply HPh; [| exact HT ].
      rewrite List.nth_error_app2 by lia; rewrite HPcl; exact HY.
  Qed.

  (** The types of the two members at the parameters. *)
  Lemma vh_ty_eq : exists i, Γ ⊢ im_ty_at qc i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) Ns ≈ im_ty_at p v Mv Us Ns : Typeω@i.
  Proof.
    pose proof (vs_nn D Hdt k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof vh_vU_length as HvUl.
    destruct (im_head Mi') as [pm | qh kh Ihc vmc] eqn:Hhi.
    - destruct (dt_view_decl _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & vm' & HMv' & Hhv).
      rewrite HMv in HMv'; injection HMv' as <-.
      assert (Hlt : i' < ind_ndecl Dq) by (apply (dt_order _ _ _ HdtQ _ _ HMi'); unfold im_is_decl; rewrite Hhi; reflexivity).
      assert (E : im_ty_at p v Mv Us Ns = im_ty_at qc i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) Ns)
        by (unfold im_ty_at, im_ref, im_pre; rewrite Hhv, Hhi; reflexivity).
      rewrite E.
      destruct (Views.ind_apps_conv_large _ _ Γ qc Dq i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)
                  (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ) Hq HMi' Hlt HΓ
                  ltac:(rewrite List.length_app, HvUl; unfold im_np, ind_nu in *; lia) ltac:(rewrite List.length_app, HvUl; unfold im_np, ind_nu in *; lia)
                  vh_ps_c vh_ps_c
                  ltac:(intros j0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply vh_ps_c; eassumption))
        as (i & _ & _ & H3).
      exists i; unfold im_ty_at, im_ref, im_pre; rewrite Hhi; cbn [fst snd]; exact H3.
    - destruct (dt_view_view _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & X & vm' & HMv' & Hhv & HXl).
      rewrite HMv in HMv'; injection HMv' as <-.
      destruct (dt_view _ _ _ HdtQ _ _ _ _ _ _ HMi' Hhi) as (Dh & Mkh & HqH & HMkh & Hlt & HIcl & _ & Hvk & _).
      destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMv Hhv) as (Dh' & Mkh' & HqH' & HMkh' & _ & _ & _ & Hvk' & _).
      rewrite HqH in HqH'; injection HqH' as <-; rewrite HMkh in HMkh'; injection HMkh' as <-.
      destruct (decl_of_lookup _ _ _ _ _ HΓ HqH) as [HdtH HcH].
      pose proof (vs_nn Dq HdtQ i' Mi' qh kh Ihc vmc Dh HMi' Hhi HqH kh Mkh i' Mi' HMkh Hvk HMi') as Hnn'.
      pose proof (vs_params_typed_c qc Dq HdtQ Hq HcQ i' Mi' qh kh Ihc vmc Dh HMi' Hhi HqH HcH kh Mkh i' Mi' HMkh Hvk HMi' Γ
                    (List.map (fun I => I[sb_of_list Id Us]) Is) Ns HΓ HvUl ltac:(lia) vh_ps_c) as HPc.
      pose proof (vs_params_typed_c p D Hdt Hl Hc v Mv qh kh X vm' Dh HMv Hhv HqH HcH kh Mkh v Mv HMkh Hvk' HMv Γ Us Ns HΓ HUl HNl HPs)
        as HPg.
      destruct (Views.ind_apps_conv_large _ _ Γ qh Dh kh Mkh
                  (List.map (fun I => I[sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)]) Ihc ++ Ns)
                  (List.map (fun I => I[sb_of_list Id Us]) X ++ Ns) (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ) HqH HMkh Hlt HΓ
                  ltac:(rewrite List.length_app, List.length_map, HIcl; unfold im_np, ind_nu in *; lia)
                  ltac:(rewrite List.length_app, List.length_map, HXl, HIcl; unfold im_np, ind_nu in *; lia)
                  HPc HPg (vh_view_params_eq qh kh Ihc vmc X vm' Dh Mkh Hhi Hhv HqH HMkh)) as (i & _ & _ & H3).
      exists i; unfold im_ty_at, im_ref, im_pre; rewrite Hhi, Hhv; cbn [fst snd]; exact H3.
  Qed.

  (** A term equal to the container's constructor applied to the view's
      instance, the parameters and typed arguments is equal to the group's
      constructor applied to the parameters and the arguments. *)
  Lemma vh_con_eq : forall As c gs' gs M, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs ->
      List.length As = List.length gs' ->
      (forall j N T, List.nth_error As j = Some N ->
         List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As) j = Some T ->
         Γ ⊢ N : T) ->
      Γ ⊢ M ≈ apps (a_con qc i' c) (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns ++ As)
        : im_ty_at qc i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) Ns ->
      Γ ⊢ M ≈ apps (a_con p v c) (Us ++ Ns ++ As) : im_ty_at p v Mv Us Ns.
  Proof.
    intros * Hcon' Hcon Hcorr HAl HAs HM.
    pose proof (vs_nn D Hdt k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof vh_vU_length as HvUl.
    pose proof (cargs_corr_length _ _ _ Hcorr) as Hlg.
    pose proof (vs_args_typed_g p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq HcQ i' Mi' v Mv HMi' Hv HMv Γ Us Ns As c gs' gs
                  HΓ HUl HNl HPs Hcon' Hcon HAl HAs) as HAg.
    destruct vh_ty_eq as [i Hi].
    assert (HTg : Γ ⊢ im_ty_at p v Mv Us Ns : Typeω@i) by (gen_presups; eassumption).
    pose proof (wf_exp_eq_conv _ _ _ _ _ _ _ _ HM HTg Hi) as HMg.
    destruct (im_head Mi') as [pm | qh kh Ihc vmc] eqn:Hhi.
    - destruct (dt_view_decl _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & vm' & HMv' & Hhv).
      rewrite HMv in HMv'; injection HMv' as <-.
      pose proof (view_head_con_eq p D v Mv qc i' Is vm' Dq Mi' Hdt Hl Hc HMv Hhv Hq HMi' Γ Us Ns As c gs gs'
                    HΓ HUl HNl HPs Hcon' Hcon ltac:(lia) HAg) as E1.
      etransitivity; [ exact HMg | symmetry; exact E1 ].
    - destruct (dt_view_view _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & X & vm' & HMv' & Hhv & HXl).
      rewrite HMv in HMv'; injection HMv' as <-.
      destruct (dt_view _ _ _ HdtQ _ _ _ _ _ _ HMi' Hhi) as (Dh & Mkh & HqH & HMkh & Hlt & HIcl & _ & Hvk & Hfst & Hcr).
      destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMv Hhv) as (Dh' & Mkh' & HqH' & HMkh' & _ & _ & _ & Hvk' & _).
      rewrite HqH in HqH'; injection HqH' as <-; rewrite HMkh in HMkh'; injection HMkh' as <-.
      destruct (decl_of_lookup _ _ _ _ _ HΓ HqH) as [HdtH HcH].
      pose proof (vs_nn Dq HdtQ i' Mi' qh kh Ihc vmc Dh HMi' Hhi HqH kh Mkh i' Mi' HMkh Hvk HMi') as Hnn'.
      (** The head's constructor. *)
      assert (Hgh : exists gh, ind_con Mkh c = Some gh).
      { pose proof (cons_lookup_in _ _ _ Hcon') as Hin.
        assert (Hc0 : List.In c (List.map fst (im_cons Mkh))) by (rewrite <- Hfst; apply List.in_map_iff; exists (c, gs'); split; [ reflexivity | exact Hin ]).
        apply List.in_map_iff in Hc0 as ([c0 gh] & Ec0 & Hin'); cbn in Ec0; subst c0.
        exact (cons_lookup_of_in _ _ _ Hin'). }
      destruct Hgh as [gh Hcon''].
      set (vU := List.map (fun I => I[sb_of_list Id Us]) Is) in *.
      set (Pc := List.map (fun I => I[sb_of_list Id vU]) Ihc) in *.
      set (Pg := List.map (fun I => I[sb_of_list Id Us]) X) in *.
      assert (HPcl : List.length Pc = ind_nu Dh) by (unfold Pc; rewrite List.length_map; exact HIcl).
      assert (HPgl : List.length Pg = ind_nu Dh) by (unfold Pg; rewrite List.length_map; lia).
      pose proof (vs_params_typed_c qc Dq HdtQ Hq HcQ i' Mi' qh kh Ihc vmc Dh HMi' Hhi HqH HcH kh Mkh i' Mi' HMkh Hvk HMi' Γ
                    vU Ns HΓ HvUl ltac:(lia) vh_ps_c) as HPc.
      pose proof (vs_params_typed_c p D Hdt Hl Hc v Mv qh kh X vm' Dh HMv Hhv HqH HcH kh Mkh v Mv HMkh Hvk' HMv Γ Us Ns HΓ HUl HNl HPs)
        as HPg.
      pose proof (vs_args_typed_c qc Dq HdtQ Hq HcQ i' Mi' qh kh Ihc vmc Dh HMi' Hhi HqH HcH kh Mkh i' Mi' HMkh Hvk HMi' Γ
                    vU Ns As c gh gs' HΓ HvUl ltac:(lia) vh_ps_c Hcon'' Hcon' HAl HAs) as HAc'.
      pose proof (vs_args_typed_c p D Hdt Hl Hc v Mv qh kh X vm' Dh HMv Hhv HqH HcH kh Mkh v Mv HMkh Hvk' HMv Γ
                    Us Ns As c gh gs HΓ HUl HNl HPs Hcon'' Hcon ltac:(lia) HAg) as HAg'.
      (** The two views' constructors, and the head's at the two instances. *)
      pose proof (view_head_con_eq p D v Mv qh kh X vm' Dh Mkh Hdt Hl Hc HMv Hhv HqH HMkh Γ Us Ns As c gs gh
                    HΓ HUl HNl HPs Hcon'' Hcon ltac:(lia) HAg) as E1.
      pose proof (view_head_con_eq qc Dq i' Mi' qh kh Ihc vmc Dh Mkh HdtQ Hq HcQ HMi' Hhi HqH HMkh Γ vU Ns As c gs' gh
                    HΓ HvUl ltac:(lia) vh_ps_c Hcon'' Hcon' HAl HAs) as E2.
      fold vU Pc in E2; fold Pg in E1.
      assert (HAlh : List.length As = List.length gh) by (rewrite (cargs_corr_length _ _ _ (Hcr _ _ _ Hcon'' Hcon')); exact HAl).
      pose proof (Views.con_apps_conv _ _ Γ qh Dh kh Mkh c gh (Pc ++ Ns) (Pg ++ Ns) As As (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ)
                    HqH HMkh Hlt Hcon'' HΓ
                    ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia) ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia)
                    HAlh HAlh HPc HPg (vh_view_params_eq qh kh Ihc vmc X vm' Dh Mkh Hhi Hhv HqH HMkh) HAc' HAg'
                    ltac:(intros j0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HAc'; eassumption))
        as E3.
      rewrite firstn_app_exact, skipn_app_exact, <- !List.app_assoc in E3 by exact HPcl.
      unfold ind_mty in E3; rewrite HMkh in E3.
      assert (ETc : im_ty_at qh kh Mkh Pc Ns = im_ty_at qc i' Mi' vU Ns).
      { unfold im_ty_at, im_ref, im_pre; rewrite Hhi.
        assert (Hdecl : im_is_decl Mkh = true) by (apply (dt_order _ _ _ HdtH _ _ HMkh); exact Hlt).
        unfold im_is_decl in Hdecl; destruct (im_head Mkh); [ reflexivity | discriminate ]. }
      rewrite ETc in E3.
      pose proof (wf_exp_eq_conv _ _ _ _ _ _ _ _ (wf_exp_eq_trans _ _ _ _ _ _ _ E2 E3) HTg Hi) as E23.
      etransitivity; [ exact HMg |].
      etransitivity; [ | symmetry; exact E1 ].
      exact E23.
  Qed.
End ViewHeads.

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
  (** The members the view nests through agree with their containers. *)
  Hypothesis (Hend : forall i' Mi' v Mv c gs1' A' gs2' gs1 t gs2, ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v ->
                 ind_member D v = Some Mv -> ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
                 cargs_corr vm gs1' gs1 -> glu_view_end_at p D ups NEl AEl DP DEl (ptyp_mem t)).

  Let view_args (Us : list exp) : list exp := List.map (fun I => I[sb_of_list Id Us]) Is.

  Lemma length_view_args : forall Us, List.length (view_args Us) = ind_nu Dq.
  Proof. intros; unfold view_args; rewrite List.length_map; exact (view_is_length VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq). Qed.

  Lemma length_cups : List.length cups = ind_nu Dq.
  Proof. rewrite (eval_exps_length _ _ _ Ecups); exact (view_is_length VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq). Qed.

  (** *** At a Neutral of a Member of the Container *)

  Section AtNeut.
    Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
    Hypotheses (HMi' : ind_member Dq i' = Some Mi') (HVM : view_member p D qc Dq vm i' Mi' v Mv).
    Let Hv := vmb_v _ _ _ _ _ _ _ _ _ HVM.
    Let HMv := vmb_mem _ _ _ _ _ _ _ _ _ HVM.
    Variables (Γ : ctx) (Us Ns : list exp).
    Hypotheses (HΓ : ⊢ Γ) (HUl : List.length Us = ind_nu D) (HNl : List.length Ns = im_nn Mv)
      (HPs : forall j X T, List.nth_error (Us ++ Ns) j = Some X ->
               List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T).

    Lemma at_neut : forall hd k' as' m M, im_ref qc i' Mi' = (hd, k') -> per_bot m m ->
        (forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M' ->
           Δ ⊢ M[φ]ʷ ≈ M' : (im_ty_at qc i' Mi' (view_args Us) Ns)[φ]ʷ) ->
        ind_glu_elem p D ups NEl AEl DP DEl v Γ Us Ns M (⇑ (d_ind hd k' as') m).
    Proof.
      intros * Href Hm HM.
      destruct (vh_ty_eq p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv Γ Us Ns HΓ HUl HNl HPs) as [i Hi].
      eapply ind_glu_elem_neut; [ exact HMv | rewrite (vmb_ref _ _ _ _ _ _ _ _ _ HVM); exact Href | exact Hm |].
      intros Δ φ M' Hφ HR.
      pose proof (kripke_preserves_typ_eq _ _ _ _ _ _ Hi Hφ) as Hiφ.
      eapply wf_exp_eq_conv; [ exact (HM Δ φ M' Hφ HR) | gen_presups; eassumption | exact Hiφ ].
    Qed.
  End AtNeut.

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

    Lemma at_lengths : List.length Us = ind_nu D /\ List.length Ns = im_nn Mv /\ List.length ns = im_nn Mv.
    Proof.
      destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
      destruct Hnp' as [L1 L2 _]; pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
      split; [ exact HUl | split; lia ].
    Qed.

    Lemma at_ps_typed : forall j X T, List.nth_error (Us ++ Ns) j = Some X ->
        List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T.
    Proof. intros; eapply glu_args_typed; [ exact (decl_closed_params_ass D v Mv Hc HMv) | exact at_params | eassumption | eassumption ]. Qed.

    Let VMP := view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv ns ns Hns'.

    (** The constructor's arguments and their values. *)
    Variables (As : list exp) (vs : list domain).
    Hypotheses (HAl : List.length As = List.length gs') (Hvl : List.length vs = List.length gs')
      (HAty' : forall j N A, List.nth_error As j = Some N ->
                 List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) j = Some A -> Γ ⊢ N : A)
      (Har' : tele_rel (canon_args_rel Dq cups i' ns c) (cargs_nonrec gs') (nonrec_arg_vals gs' vs) (nonrec_arg_vals gs' vs))
      (Harg' : forall gs1 A0 gs2 N A x, gs' = gs1 ++ ca_arg A0 :: gs2 -> List.nth_error As (List.length gs1) = Some N ->
                 List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) (List.length gs1) = Some A ->
                 List.nth_error vs (List.length gs1) = Some x ->
                 Γ ⊢ N : A ® x ∈ AEl' i' ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))).

    Lemma at_gs_length : List.length gs' = List.length gs.
    Proof. exact (cargs_corr_length _ _ _ Hcorr). Qed.

    Lemma at_args_typed : forall j N T, List.nth_error As j = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T -> Γ ⊢ N : T.
    Proof.
      destruct at_lengths as (HUl & HNl & _).
      exact (vs_args_typed_g p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq HcQ i' Mi' v Mv HMi' Hv HMv Γ Us Ns As c gs' gs
               HΓ HUl HNl at_ps_typed Hcon' Hcon HAl HAty').
    Qed.

    Lemma at_args_g : tele_rel (canon_args_rel D ups v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs).
    Proof.
      pose proof at_gs_length as Hlg.
      apply tele_rel_of_pre.
      exact (view_nonrec_prefix p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv c gs' gs
               Hcon' Hcon Hcorr ns (params_length _ _ _ _ _ _ _ _ _ VMP) (params_group_values _ _ _ _ _ _ _ _ _ VMP)
               (params_container_values _ _ _ _ _ _ _ _ _ VMP) Hns' gs gs' nil nil vs vs
               (eq_sym (List.app_nil_r gs')) (eq_sym (List.app_nil_r gs)) Hcorr ltac:(lia) ltac:(lia) (tele_rel_pre _ _ _ _ Har')).
    Qed.

    (** A non-recursive argument of the group's constructor: non-recursive
        in the container's, glued at the container's gluing of a type
        related to the group's, and equal to it. *)
    Lemma at_nonrec : forall gs1 A0 gs2 N A x, gs = gs1 ++ ca_arg A0 :: gs2 -> List.nth_error As (List.length gs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
        List.nth_error vs (List.length gs1) = Some x ->
        Γ ⊢ N : A ® x ∈ AEl v ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)).
    Proof.
      destruct at_lengths as (HUl & HNl & Hnl).
      pose proof at_gs_length as Hlg.
      pose proof (params_length _ _ _ _ _ _ _ _ _ VMP) as Hlms.
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
      assert (Hall : forall n gs1 A0 gs2 N A x, List.length gs1 < n -> gs = gs1 ++ ca_arg A0 :: gs2 ->
                 List.nth_error As (List.length gs1) = Some N ->
                 List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
                 List.nth_error vs (List.length gs1) = Some x ->
                 Γ ⊢ N : A ® x ∈ AEl v ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))).
      { induction n as [| n IH]; intros gs1 A0 gs2 N A x Hn Heq HN HA Hx; [ lia |].
        set (vp := List.firstn (List.length gs1) vs).
        assert (Hlgs1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
        assert (Hlvp : List.length vp = List.length gs1) by (unfold vp; rewrite List.length_firstn; lia).
        (** The container's argument at the position: non-recursive. *)
        destruct (nth_error_lt_some' gs' (List.length gs1) ltac:(lia)) as [g' Hg'].
        destruct (List.nth_error_split _ _ Hg') as (gs1' & gs2' & Heq' & Hl1).
        destruct (cargs_corr_split vm gs1' (g' :: gs2') gs1 (ca_arg A0 :: gs2) ltac:(rewrite <- Heq', <- Heq; exact Hcorr) Hl1)
          as [Hc1 Hc2].
        destruct g' as [A0' | t']; cbn in Hc2; [| contradiction ].
        destruct (nth_error_lt_some (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) (List.length gs1))
          as [A' HA']; [ rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia |].
        pose proof (Harg' gs1' A0' gs2' N A' x Heq' ltac:(rewrite Hl1; exact HN) ltac:(rewrite Hl1; exact HA')
                      ltac:(rewrite Hl1; exact Hx)) as HNc.
        rewrite Hl1 in HNc; fold vp in HNc.
        (** The two prefixes of the non-recursive arguments. *)
        pose proof (nonrec_prefix_pre _ gs' vs gs1' (ca_arg A0') gs2' Har' ltac:(lia) Heq') as Hpc.
        rewrite Hl1 in Hpc; fold vp in Hpc.
        pose proof (nonrec_prefix_pre _ gs vs gs1 (ca_arg A0) gs2 at_args_g ltac:(lia) Heq) as Hpg; fold vp in Hpg.
        assert (HnA' : List.nth_error (cargs_nonrec gs') (List.length (cargs_nonrec gs1')) = Some A0')
          by (rewrite Heq', cargs_nonrec_app; cbn [cargs_nonrec]; rewrite List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        assert (HnA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A0)
          by (rewrite Heq, cargs_nonrec_app; cbn [cargs_nonrec]; rewrite List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        (** The two types' values, glued. *)
        destruct (ifg_arg_eval _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ HMi' Hns' Hcon' HnA' Hpc) as [b' Eb'].
        pose proof (ifg_arg_glu _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ b' HMi' Hns' Hcon' HnA' Hpc Eb') as Hgb'.
        destruct (ifg_arg_eval _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs _ A0 _ HMv at_ns_g Hcon HnA Hpg) as [b Eb].
        pose proof (ifg_arg_glu _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs _ A0 _ b HMv at_ns_g Hcon HnA Hpg Eb) as Hgb.
        (** Related, through the arguments completed at both telescopes. *)
        destruct (view_args_complete p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                    c gs' gs Hcon' Hcon Hcorr ns Hlms (params_group_values _ _ _ _ _ _ _ _ _ VMP)
                    (params_container_values _ _ _ _ _ _ _ _ _ VMP) gs1 gs1' (ca_arg A0' :: gs2') (ca_arg A0 :: gs2) vp
                    Heq' Heq Hc1 Hlvp Hpc) as (vsX & [HlX HnX HnXg HgX HcX _]).
        destruct (vg_arg_types p D Hg Hcv v Mv c gs gs1 A0 gs2 ups ns vsX HMv Hcon Heq Hu Hlms HlX HgX)
          as (i1 & R1 & a1 & a1' & Ea1 & Ea1' & HR1).
        destruct (vg_arg_types qc Dq HgQ HcvQ i' Mi' c gs' gs1' A0' gs2' cups ns vsX HMi' Hcon' Heq' length_cups ltac:(lia) ltac:(lia) HcX)
          as (i2 & R2 & a2 & a2' & Ea2 & Ea2' & HR2).
        rewrite HnXg in Ea1'; rewrite HnX in Ea2'.
        pose proof (functional_eval_exp _ _ _ _ Ea1' Eb) as ->.
        pose proof (functional_eval_exp _ _ _ _ Ea2' Eb') as ->.
        pose proof (cargs_ctx_snoc qc Dq Mi' gs1' (ca_arg A0')) as ECc; pose proof (cargs_ctx_snoc p D Mv gs1 (ca_arg A0)) as ECg.
        cbn [cargs_ctx_aux List.app] in ECc, ECg.
        destruct (view_arg_link p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv c gs' gs
                    Hcon' Hcon Hcorr ns Hlms gs1' _ gs2' gs1 _ gs2 _ _ vsX Heq' Heq ltac:(lia) HlX ECc ECg HgX HcX)
          as [_ _ _ (i3 & R3 & b0 & a0 & Eb0 & Ea0 & HR3)].
        pose proof (functional_eval_exp _ _ _ _ Eb0 Ea1) as ->.
        pose proof (functional_eval_exp _ _ _ _ Ea0 Ea2) as ->.
        assert (Hrel : Dom b' ≈ b ∈ per_univ i2).
        { eapply per_univ_trans'; [ exact (per_univ_sym' _ _ _ (ex_intro _ R2 HR2)) |].
          eapply per_univ_trans'; [ exact (per_univ_sym' _ _ _ (ex_intro _ R3 HR3)) | exact (ex_intro _ R1 HR1) ]. }
        (** The two types: equal. *)
        destruct (vs_args_eq_c p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq HcQ i' Mi' v Mv HMi' Hv HMv Γ Us Ns As c gs' gs
                    HΓ HUl HNl at_ps_typed Hcon' Hcon HAl HAty' _ A' A HA' HA) as [l HAA].
        (** The group's type, glued, by the arguments before it. *)
        assert (HTP : Γ ⊢ A ® AP v ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp)).
        { eapply (igc_args _ _ _ _ _ _ _ _ _ _ _ at_comps v Mv c gs gs1 A0 gs2 Ns ns As vp A HMv Hcon Heq at_nparams at_ns_g Hlvp HA);
            [| exact Hpg ].
          intros hs1 B hs2 N0 T0 v0 Heq1 HN0 HT0 Hv0.
          assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
          unfold vp in Hv0 |- *; rewrite List.firstn_firstn, Nat.min_l by lia.
          rewrite List.nth_error_firstn in Hv0; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
          eapply (IH hs1 B (hs2 ++ ca_arg A0 :: gs2)); [ lia | rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN0 | exact HT0 | exact Hv0 ]. }
        exact (glu_elem_conv u' u i2 l b b' _ _ _ _ Γ A A' N x Hgb' Hgb Hrel HAA HTP HNc). }
      intros gs1 A0 gs2 N A x Heq HN HA Hx.
      exact (Hall (S (List.length gs1)) gs1 A0 gs2 N A x ltac:(lia) Heq HN HA Hx).
    Qed.

    (** The arguments before a position, glued on the side of the group's
        non-recursive ones. *)
    Lemma at_sub0 : forall gs1 g gs2 SbC0, gs = gs1 ++ g :: gs2 ->
        EG nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mv ∈ glu_ctx_env ↘ SbC0 ->
        Γ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))
          ® env_args nil ((ups ++ ns) ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) ∈ SbC0.
    Proof.
      intros gs1 g gs2 SbC0 Heq HSbC0.
      pose proof at_gs_length as Hlg.
      assert (Hl1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      eapply (nonrec_args_prefix_glu_sub p D Hc ups u NP NEl AP AEl DP DEl Hu Hf Γ Us HΓ HUs v Mv c gs gs1 g gs2 Ns ns As
                (List.firstn (List.length gs1) vs) SbC0
                HMv Hcon Heq at_nparams at_ns_g ltac:(rewrite List.length_firstn; lia) ltac:(lia)); [| | exact HSbC0 ].
      - intros hs1 B hs2 N0 T0 v0 Heq1 HN0 HT0 Hv0.
        assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
        rewrite List.firstn_firstn, Nat.min_l by lia.
        rewrite List.nth_error_firstn in Hv0; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
        eapply (at_nonrec hs1 B (hs2 ++ g :: gs2)); [ rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN0 | exact HT0 | exact Hv0 ].
      - exact (nonrec_prefix_pre _ gs vs gs1 g gs2 at_args_g ltac:(lia) Heq).
    Qed.

    (** An argument the view nests through: non-recursive in the
        container's constructor, of a shape in the group's, ending in a
        member that agrees with its container. *)
    Lemma at_nested : forall gs1 t gs2 gs1' A0' gs2' N A x, gs = gs1 ++ ca_rec t :: gs2 -> gs' = gs1' ++ ca_arg A0' :: gs2' ->
        List.length gs1' = List.length gs1 -> List.nth_error As (List.length gs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
        List.nth_error vs (List.length gs1) = Some x ->
        glu_rec p D ups NEl AEl DP DEl v Γ Us (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N x.
    Proof.
      intros gs1 t gs2 gs1' A0' gs2' N A x Heq Heq' Hl1 HN HA Hx.
      destruct at_lengths as (HUl & HNl & Hnl).
      pose proof at_gs_length as Hlg.
      pose proof (params_length _ _ _ _ _ _ _ _ _ VMP) as Hlms.
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
      set (vp := List.firstn (List.length gs1) vs).
      assert (Hlgs1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      assert (Hlvp : List.length vp = List.length gs1) by (unfold vp; rewrite List.length_firstn; lia).
      destruct (cargs_corr_split vm gs1' (ca_arg A0' :: gs2') gs1 (ca_rec t :: gs2) ltac:(rewrite <- Heq', <- Heq; exact Hcorr) Hl1)
        as [Hc1 _].
      (** The container's argument, glued. *)
      destruct (nth_error_lt_some (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) (List.length gs1))
        as [A' HA']; [ rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia |].
      pose proof (Harg' gs1' A0' gs2' N A' x Heq' ltac:(rewrite Hl1; exact HN) ltac:(rewrite Hl1; exact HA')
                    ltac:(rewrite Hl1; exact Hx)) as HNc.
      rewrite Hl1 in HNc; fold vp in HNc.
      pose proof (nonrec_prefix_pre _ gs' vs gs1' (ca_arg A0') gs2' Har' ltac:(lia) Heq') as Hpc.
      rewrite Hl1 in Hpc; fold vp in Hpc.
      pose proof (nonrec_prefix_pre _ gs vs gs1 (ca_rec t) gs2 at_args_g ltac:(lia) Heq) as Hpg; fold vp in Hpg.
      assert (HnA' : List.nth_error (cargs_nonrec gs') (List.length (cargs_nonrec gs1')) = Some A0')
        by (rewrite Heq', cargs_nonrec_app; cbn [cargs_nonrec]; rewrite List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      destruct (ifg_arg_eval _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ HMi' Hns' Hcon' HnA' Hpc) as [b' Eb'].
      pose proof (ifg_arg_glu _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ b' HMi' Hns' Hcon' HnA' Hpc Eb') as Hgb'.
      (** The arguments before, completed at both telescopes. *)
      destruct (view_args_complete p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                  c gs' gs Hcon' Hcon Hcorr ns Hlms (params_group_values _ _ _ _ _ _ _ _ _ VMP)
                  (params_container_values _ _ _ _ _ _ _ _ _ VMP) gs1 gs1' (ca_arg A0' :: gs2') (ca_rec t :: gs2) vp
                  Heq' Heq Hc1 Hlvp Hpc) as (vsX & [HlX HnX HnXg HgX HcX HaX]).
      destruct (vg_arg_types qc Dq HgQ HcvQ i' Mi' c gs' gs1' A0' gs2' cups ns vsX HMi' Hcon' Heq' length_cups ltac:(lia) ltac:(lia) HcX)
        as (i2 & R2 & a2 & a2' & Ea2 & Ea2' & HR2).
      rewrite HnX in Ea2'.
      pose proof (functional_eval_exp _ _ _ _ Ea2' Eb') as ->.
      pose proof (cargs_ctx_snoc qc Dq Mi' gs1' (ca_arg A0')) as ECc; pose proof (cargs_ctx_snoc p D Mv gs1 (ca_rec t)) as ECg.
      cbn [cargs_ctx_aux List.app] in ECc, ECg.
      destruct (view_arg_link p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv c gs' gs
                  Hcon' Hcon Hcorr ns Hlms gs1' _ gs2' gs1 _ gs2 _ _ vsX Heq' Heq ltac:(lia) HlX ECc ECg HgX HcX)
        as [_ _ _ (i3 & R3 & b0 & a0 & Eb0 & Ea0 & HR3)].
      pose proof (functional_eval_exp _ _ _ _ Ea0 Ea2) as ->.
      (** The container's gluing of the argument, moved to the group's type's
          value, at a level above both. *)
      set (n := Nat.max (ulvl u') (Nat.max i2 i3)).
      assert (Hun : uidx_le u' (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
      destruct (glu_univ_elem_cumu_ge_uidx Hun Hgb') as (Pn & Eln & Hgn).
      pose proof (glu_univ_elem_exp_cumu_ge_uidx Hun Hgb' Hgn HNc) as HNn.
      assert (Hrel : Dom b' ≈ b0 ∈ per_univ n).
      { destruct (per_univ_trans' _ _ _ _ _ (per_univ_sym' _ _ _ (ex_intro _ R2 HR2)) (per_univ_sym' _ _ _ (ex_intro _ R3 HR3)))
          as [R HR].
        exists R; exact (per_univ_elem_cumu_ge i2 n _ _ _ ltac:(unfold n; lia) HR). }
      pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ Hrel Hgn) as Hgn'.
      (** The group's side of the arguments before. *)
      destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gs HMv Hcon gs1 (ca_rec t :: gs2) Heq) as [HW1 _].
      assert (INV : forall R, EF cargs_ctx p D Mv gs1 ++ im_params D Mv ≈ cargs_ctx p D Mv gs1 ++ im_params D Mv ∈ per_ctx_env ↘ R ->
                R (env_args nil (ups ++ ns ++ vsX)) (env_args nil (ups ++ ns ++ vsX))).
      { intros R HR; apply (gargs_env_rel _ _ _ _ _ _ HR HW1); [| exact HgX ].
        rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
      destruct (gid_dctx _ HG _ _ _ _ _ _ _ 0 HMv Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
      pose proof HSbC0 as HSbC0'; cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0'.
      pose proof (at_sub0 gs1 (ca_rec t) gs2 SbC0 Heq HSbC0') as Hσ0; fold vp in Hσ0.
      set (As1 := List.firstn (List.length gs1) As) in *.
      assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      assert (HlNs' : List.length (Ns ++ nonrec_exps gs1 As1) = 0 + List.length (cargs_nonrec gs1) + im_nn Mv)
        by (rewrite List.length_app, length_nonrec_exps by exact HlAs1; lia).
      pose proof (con_rec_glu VP p D HVP HPD HG v Mv c gs HMv Hcon ups bu u NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf
                    gs1 t gs2 ns vsX Heq Hnl HlX at_ns_g HaX INV
                    (Hend i' Mi' v Mv c gs1' A0' gs2' gs1 t gs2 HMi' Hv HMv ltac:(rewrite <- Heq'; exact Hcon') ltac:(rewrite <- Heq; exact Hcon) Hc1)
                    t 0 nil Γ Id Us (Ns ++ nonrec_exps gs1 As1) SbC0 A' N x b0 (ul n) Pn Eln
                    eq_refl ltac:(lia) (tele_prefix_rel_nil _) ltac:(constructor) HΓ HUs HlNs' HSbC0
                    ltac:(rewrite HnXg, !List.app_nil_r, <- !List.app_assoc in *; exact Hσ0)
                    ltac:(cbn [List.repeat List.app]; rewrite List.app_nil_r; exact Eb0) Hgn' HNn) as Hfinal.
      rewrite List.app_nil_r, HnXg in Hfinal.
      pose proof (cargs_rec_type_sh p D Mv gs gs1 t gs2 (Us ++ Ns) As A Heq Hc ltac:(rewrite List.length_app; unfold im_np; lia) HA) as ETs.
      rewrite firstn_app_exact, <- List.app_assoc in ETs by exact HUl.
      rewrite ETs; exact Hfinal.
    Qed.

    (** The container's constructor is the group's, given its recursive
        arguments recursive in both as the group's. *)
    Lemma at_con : forall hd k' bs M, im_ref qc i' Mi' = (hd, k') -> List.length bs = (im_unu Dq Mi' + im_nn Mi')%nat ->
        List.skipn (im_unu Dq Mi') bs = ns ->
        Γ ⊢ M ≈ apps (a_con qc i' c) (view_args Us ++ Ns ++ As) : im_ty_at qc i' Mi' (view_args Us) Ns ->
        (forall gs1 t gs2 gs1' t' gs2' N A x, gs = gs1 ++ ca_rec t :: gs2 -> gs' = gs1' ++ ca_rec t' :: gs2' ->
           List.length gs1' = List.length gs1 -> List.nth_error As (List.length gs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
           List.nth_error vs (List.length gs1) = Some x ->
           glu_rec p D ups NEl AEl DP DEl v Γ Us (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N x) ->
        ind_glu_elem p D ups NEl AEl DP DEl v Γ Us Ns M (d_con hd k' c (bs ++ vs)).
    Proof.
      intros hd k' bs M Href Hbl Hns HM Hboth.
      destruct at_lengths as (HUl & HNl & Hnl).
      pose proof at_gs_length as Hlg.
      pose proof (vmb_unu _ _ _ _ _ _ _ _ _ HVM) as Hunu.
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
      eapply ind_glu_elem_con with (Mk := Mv) (gs := gs) (As := As);
        [ exact HMv | rewrite (vmb_ref _ _ _ _ _ _ _ _ _ HVM); exact Href | exact Hcon | exact HUl | exact HNl | lia | lia | lia
        | exact (vh_con_eq p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv Γ Us Ns HΓ HUl HNl at_ps_typed
                   As c gs' gs M Hcon' Hcon Hcorr HAl HAty' HM)
        | | | | exact at_args_typed | | ].
      all: rewrite ?Hunu, ?Hns.
      - exact at_ns_g.
      - exact at_args_g.
      - exact at_nparams.
      - exact at_nonrec.
      - intros gs1 t gs2 N A x Heq HN HA Hx.
        assert (Hlgs1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some' gs' (List.length gs1) ltac:(lia)) as [g' Hg'].
        destruct (List.nth_error_split _ _ Hg') as (gs1' & gs2' & Heq' & Hl1).
        destruct g' as [A0' | t'].
        + exact (at_nested gs1 t gs2 gs1' A0' gs2' N A x Heq Heq' Hl1 HN HA Hx).
        + exact (Hboth gs1 t gs2 gs1' t' gs2' N A x Heq Heq' Hl1 HN HA Hx).
    Qed.
  End AtCon.
End ToGroup.

End Fixed_GCtx.
