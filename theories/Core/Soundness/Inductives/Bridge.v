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

(** An instance of a context, moved along a weakening and extended by a
    term of a type over the context. *)
Lemma theta_step : forall Γ Δ Ψ A Ms τ φ b (i : nat), Γ ⊢ˢ sb_of_list τ Ms : Ψ -> Δ ⊢ᵏ φ : Γ -> Ψ ⊢ A : Typeω@i ->
    Δ ⊢ b : A[sb_of_list τ Ms][φ]ʷ ->
    Δ ⊢ˢ sb_of_list (sb_wk τ φ) (List.map (fun M => M[φ]ʷ) Ms ++ b :: nil) : ce_ass A :: Ψ.
Proof.
  intros * HΘ Hφ HA Hb.
  pose proof (wf_sub_compose _ _ _ _ _ _ _ HΘ (kripke_escape _ _ _ Hφ)) as H1.
  assert (Hb' : Δ ⊢ b : A[sb_of_list τ Ms ⨟ ι φ]) by (rewrite <- exp_sub_sub, exp_sub_of_wk; exact Hb).
  pose proof (wf_sub_extend _ _ _ _ _ _ _ _ H1 HA Hb') as H2.
  assert (E : sb_eq ((sb_of_list τ Ms ⨟ ι φ),,b) (sb_of_list (sb_wk τ φ) (List.map (fun M => M[φ]ʷ) Ms ++ b :: nil))).
  { rewrite sb_of_list_app; cbn [sb_of_list].
    apply sb_extend_cong; intros x; cbn [sb_compose]; rewrite sentry_sub_of_wk.
    exact (sb_wk_sb_of_list Ms τ φ x). }
  pose proof (wf_sub_eq_of_sb_eq _ _ _ _ _ _ H2 E) as H3.
  gen_presups; eassumption.
Qed.

(** The non-recursive arguments of moved terms. *)
Lemma nonrec_exps_map : forall gs As f, nonrec_exps gs (List.map f As) = List.map f (nonrec_exps gs As).
Proof. induction gs as [| [] gs IH]; intros [| A As] f; cbn; rewrite ?IH; reflexivity. Qed.

(** [wk_pat] after domains picks the non-recursive arguments out of an
    instance of all of them followed by the domains. *)
Lemma wk_pat_falses_sb_of_list : forall Ds gs1 σ As, List.length As = List.length gs1 ->
    sb_eq ((ι (wk_pat (List.repeat false (List.length Ds) ++ cargs_pat gs1))) ⨟ sb_of_list σ (As ++ Ds))
      (sb_of_list σ (nonrec_exps gs1 As ++ Ds)).
Proof.
  induction Ds as [| Y Ds IH] using List.rev_ind; intros gs1 σ As Hl.
  - rewrite !List.app_nil_r; exact (wk_pat_sb_of_list gs1 σ As Hl).
  - rewrite List.length_app, Nat.add_1_r; cbn [List.repeat List.app wk_pat].
    rewrite !List.app_assoc, !sb_of_list_app; cbn [sb_of_list].
    intros [| x]; [ reflexivity |].
    specialize (IH gs1 σ As Hl x); rewrite !sb_of_list_app in IH.
    cbn [sb_compose sb_of_wk sentry_sub wk_q sb_extend] in IH |- *; exact IH.
Qed.

Corollary exp_wk_pat_falses_sb_of_list : forall B Ds gs1 σ As, List.length As = List.length gs1 ->
    B[wk_pat (List.repeat false (List.length Ds) ++ cargs_pat gs1)]ʷ[sb_of_list σ (As ++ Ds)]
    = B[sb_of_list σ (nonrec_exps gs1 As ++ Ds)].
Proof.
  intros; rewrite <- exp_sub_of_wk, exp_sub_sub; apply exp_sub_sb_eq, wk_pat_falses_sb_of_list; assumption.
Qed.

(** The view's instance in a list instance, below the instance's
    variables. *)
Lemma sb_qn_view_agree : forall Is Us Ms τ x, List.Forall (exp_scoped (List.length Us)) Is ->
    x < List.length Ms + List.length Is ->
    (sb_qn (List.length Ms) (sb_of_list Id Is) ⨟ sb_of_list τ (Us ++ Ms)) x
    = sb_of_list τ (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ms) x.
Proof.
  intros * Hs Hx.
  rewrite (sb_of_list_app Us Ms τ), (sb_of_list_app _ Ms τ).
  rewrite (sb_qn_of_list Ms (sb_of_list Id Is) (sb_of_list τ Us) x).
  destruct (Nat.lt_ge_cases x (List.length Ms)) as [Hlt | Hge].
  - rewrite !(sb_of_list_nth Ms _ x (a_var 0) Hlt); reflexivity.
  - replace x with (List.length Ms + (x - List.length Ms)) by lia; rewrite !sb_of_list_ge.
    set (y := x - List.length Ms).
    assert (Hy : y < List.length Is) by (unfold y; lia).
    cbn [sb_compose].
    rewrite (sb_of_list_nth Is Id y (a_var 0) Hy), (sb_of_list_nth _ τ y (a_var 0)) by (rewrite List.length_map; exact Hy).
    cbn [sentry_sub]; rewrite List.length_map.
    rewrite (List.nth_indep (List.map (fun I : typ => I[sb_of_list Id Us]) Is) (a_var 0) ((a_var 0)[sb_of_list Id Us]))
      by (rewrite List.length_map; lia).
    rewrite (List.map_nth (fun I : typ => I[sb_of_list Id Us])); f_equal.
    rewrite List.Forall_forall in Hs.
    apply (exp_scoped_sub_agree _ (List.length Us)); [ apply Hs, List.nth_In; lia |].
    intros z Hz; apply Views.sb_of_list_agree; exact Hz.
Qed.

(** The domains and the parameters of a scoped shape are scoped. *)
Lemma ptyp_scoped_dom : forall t n d B, ptyp_scoped n t -> List.nth_error (ptyp_doms t) d = Some B -> exp_scoped (d + n) B.
Proof.
  induction t as [j Ps | B0 t IH]; intros n d B Hs HB; cbn in *; [ destruct d; discriminate |].
  destruct Hs as [HB0 Hs]; destruct d as [| d]; cbn in HB; [ injection HB as <-; exact HB0 |].
  replace (S d + n) with (d + S n) by lia; exact (IH _ _ _ Hs HB).
Qed.

Lemma ptyp_scoped_ps : forall t n, ptyp_scoped n t -> List.Forall (exp_scoped (ptyp_depth t + n)) (ptyp_ps t).
Proof.
  induction t as [j Ps | B0 t IH]; intros n Hs; cbn in *; [ exact Hs |].
  destruct Hs as [_ Hs]; unfold ptyp_depth in *; cbn.
  refine (List.Forall_impl _ _ (IH _ Hs)); intros; eapply exp_scoped_mono; [| eassumption ]; lia.
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

  (** *** The Shapes of Recursive Arguments *)

  (** A term of the container's telescope of the shape, under its
      weakening, followed by the view's instance and an instance of the
      group's, is the term at the container's instance of its own
      context. *)
  Lemma vs_wk_inst : forall X c gs' gs1' t' gs2' kk τ Us Ns As1 Ds, ind_con Mi' c = Some gs' -> gs' = gs1' ++ ca_rec t' :: gs2' ->
      List.length Us = ind_nu D -> List.length Ns = im_nn Mv -> List.length As1 = List.length gs1' -> List.length Ds = kk ->
      exp_scoped (kk + (List.length (cargs_strat gs1') + im_np Dq Mi')) X ->
      X[wk_pat (List.repeat false kk ++ cargs_pat gs1')]ʷ[sb_qn (kk + List.length gs1' + im_nn Mv) (sb_of_list Id Is)]
        [sb_of_list τ (Us ++ Ns ++ As1 ++ Ds)]
      = X[sb_of_list τ (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns ++ nonrec_exps gs1' As1 ++ Ds)].
  Proof.
    intros * Hcon' Heq' HUl HNl HAl HDl Hs.
    pose proof vs_nn as Hnn.
    rewrite exp_sub_sub.
    rewrite (exp_scoped_sub_agree _ (kk + List.length gs1' + im_nn Mv + ind_nu Dq) _
               (sb_of_list τ (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns ++ As1 ++ Ds))).
    - replace (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns ++ As1 ++ Ds)
        with ((List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) ++ (As1 ++ Ds)) by (rewrite <- !List.app_assoc; reflexivity).
      rewrite sb_of_list_app, <- HDl, exp_wk_pat_falses_sb_of_list by exact HAl.
      rewrite <- sb_of_list_app, <- !List.app_assoc; reflexivity.
    - eapply exp_scoped_wk; [ exact Hs |].
      intros x Hx.
      pose proof (wk_pat_bound (List.repeat false kk ++ cargs_pat gs1') (im_np Dq Mi') x) as Hb.
      rewrite pat_nargs_falses, pat_nargs_cargs_pat, List.length_app, List.repeat_length, length_cargs_pat in Hb.
      unfold im_np, ind_nu in *; specialize (Hb ltac:(lia)); lia.
    - intros x Hx.
      replace (kk + List.length gs1' + im_nn Mv) with (List.length (Ns ++ As1 ++ Ds)) by (rewrite !List.length_app; lia).
      apply sb_qn_view_agree; [ rewrite HUl; exact (decl_closed_head_scoped D Hc _ _ _ _ _ _ HMk Hh) |].
      rewrite !List.length_app, vs_is_length; lia.
  Qed.

  (** The domains of the two shapes of an argument recursive in both, at
      the two instances: equal. *)
  Lemma vs_dom_eq : forall Γ c gs' gs gs1' t' gs2' gs1 t gs2 kk B' B τ Us Ns As1 Ds,
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
      List.length gs1' = List.length gs1 ->
      List.nth_error (ptyp_doms t') kk = Some B' -> List.nth_error (ptyp_doms t) kk = Some B ->
      List.length Us = ind_nu D -> List.length Ns = im_nn Mv -> List.length As1 = List.length gs1 -> List.length Ds = kk -> ⊢ Γ ->
      Γ ⊢ˢ sb_of_list τ (Us ++ Ns ++ As1 ++ Ds) : sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv ->
      exists i, Γ ⊢ B'[sb_of_list τ (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns ++ nonrec_exps gs1' As1 ++ Ds)]
                ≈ B[sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)] : Typeω@i.
  Proof.
    intros * Hcon' Hcon Heq' Heq Hl1 HB' HB HUl HNl HAl HDl HΓ Hσ.
    assert (Hkk : kk < ptyp_depth t) by (unfold ptyp_depth; apply List.nth_error_Some; congruence).
    destruct (dt_view_doms _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 kk
                HMk Hh Hq HMi' Hv HMv Hcon' Hcon Heq' Heq Hl1 Hkk) as [i H].
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H Hσ) as H'.
    exists i; cbn [exp_sub] in H'.
    unfold ptyp_dom_at in H'.
    assert (EB : List.nth kk (ptyp_doms t) a_True = B) by (apply List.nth_error_nth; exact HB).
    assert (EB' : List.nth kk (ptyp_doms t') a_True = B') by (apply List.nth_error_nth; exact HB').
    rewrite EB, EB' in H'.
    rewrite <- Hl1 in H'.
    rewrite (vs_wk_inst B' c gs' gs1' t' gs2' kk τ Us Ns As1 Ds Hcon' Heq' HUl HNl ltac:(lia) HDl) in H'.
    - replace (Us ++ Ns ++ As1 ++ Ds) with ((Us ++ Ns) ++ (As1 ++ Ds)) in H' by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (sb_of_list_app (Us ++ Ns) (As1 ++ Ds) τ), <- HDl, exp_wk_pat_falses_sb_of_list in H' by exact HAl.
      rewrite <- (sb_of_list_app (Us ++ Ns) (nonrec_exps gs1 As1 ++ Ds) τ), <- !List.app_assoc in H'.
      exact H'.
    - pose proof (mc_recs _ _ (dc_members _ HcQ _ _ HMi') c gs' gs1' t' gs2' (cons_lookup_in _ _ _ Hcon') Heq') as Hst.
      exact (ptyp_scoped_dom _ _ _ _ Hst HB').
  Qed.

  (** The parameters the two shapes end in, at the two instances: equal at
      the telescope of the group's member the group's shape ends in. *)
  Lemma vs_ps_eq : forall Γ c gs' gs gs1' t' gs2' gs1 t gs2 Mj τ Us Ns As1 Ds,
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
      List.length gs1' = List.length gs1 -> ptyp_depth t' = ptyp_depth t -> ind_member D (ptyp_mem t) = Some Mj ->
      List.length Us = ind_nu D -> List.length Ns = im_nn Mv -> List.length As1 = List.length gs1 -> List.length Ds = ptyp_depth t -> ⊢ Γ ->
      Γ ⊢ˢ sb_of_list τ (Us ++ Ns ++ As1 ++ Ds) : sh_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv ->
      forall j X Y T,
        List.nth_error (List.map (fun P => P[sb_of_list τ (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns ++ nonrec_exps gs1' As1 ++ Ds)])
                          (ptyp_ps t')) j = Some X ->
        List.nth_error (List.map (fun P => P[sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)]) (ptyp_ps t)) j = Some Y ->
        List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id Us)
                          (List.map (fun P => P[sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)]) (ptyp_ps t))) j = Some T ->
        Γ ⊢ X ≈ Y : T.
  Proof.
    intros * Hcon' Hcon Heq' Heq Hl1 Hdp HMj HUl HNl HAl HDl HΓ Hσ j X Y T HX HY HT.
    apply nth_error_map_inv in HX as (P0' & HP0' & ->).
    apply nth_error_map_inv in HY as (P0 & HP0 & ->).
    set (wp := wk_pat (List.repeat false (ptyp_depth t) ++ cargs_pat gs1)).
    set (Pg := List.map (fun P => P[wp]ʷ) (ptyp_ps t)).
    assert (HPg : List.nth_error Pg j = Some P0[wp]ʷ) by (unfold Pg; rewrite List.nth_error_map, HP0; reflexivity).
    assert (HPc : List.nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P0'[wk_pat (List.repeat false (ptyp_depth t) ++ cargs_pat gs1')]ʷ)
      by (unfold ptyp_ps_at; rewrite List.nth_error_map, HP0', Hdp; reflexivity).
    assert (HassN : tele_ass (im_nparams Mj)) by exact (decl_closed_nparams_ass D Hc _ _ HMj).
    destruct (nth_error_lt_some (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1))) Pg) j)
      as [T0 HT0].
    { assert (Hj : j < List.length (tele_insts (im_nparams Mj) (sb_of_list Id Us)
                                      (List.map (fun P => P[sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)]) (ptyp_ps t))))
        by (apply List.nth_error_Some; congruence).
      rewrite length_tele_insts, List.length_map in Hj by exact HassN.
      rewrite length_tele_insts by exact HassN; unfold Pg; rewrite List.length_map; exact Hj. }
    destruct (dt_view_ps _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j
                _ _ T0 HMk Hh Hq HMi' Hv HMv Hcon' Hcon Heq' Heq Hl1 HMj HPc HPg HT0) as [_ H].
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H Hσ) as H'.
    rewrite <- Hl1, (vs_wk_inst P0' c gs' gs1' t' gs2' (ptyp_depth t) τ Us Ns As1 Ds Hcon' Heq' HUl HNl ltac:(lia) HDl) in H'.
    - unfold wp in H'.
      replace (Us ++ Ns ++ As1 ++ Ds) with ((Us ++ Ns) ++ (As1 ++ Ds)) in H' by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (sb_of_list_app (Us ++ Ns) (As1 ++ Ds) τ), <- HDl, exp_wk_pat_falses_sb_of_list in H' by exact HAl.
      rewrite <- (sb_of_list_app (Us ++ Ns) (nonrec_exps gs1 As1 ++ Ds) τ), <- !List.app_assoc in H'.
      rewrite <- (sb_of_list_app (Us ++ Ns) (As1 ++ Ds) τ), <- !List.app_assoc in H'.
      (** The type: the telescope's at the instance. *)
      set (Θ := sb_of_list τ (Us ++ Ns ++ As1 ++ Ds)) in *.
      set (uv := ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)) in *.
      assert (Hluv : List.length uv = ind_nu D) by (unfold uv, ind_uvars; apply length_vars_from).
      assert (Euv : List.map (fun M => M[Θ]) uv = Us).
      { unfold uv, ind_uvars, Θ.
        replace (ptyp_depth t + List.length gs1 + im_nn Mv) with (List.length (Ns ++ As1 ++ Ds)) by (rewrite !List.length_app; lia).
        rewrite <- HUl; exact (vars_from_sb_of_list_app Us (Ns ++ As1 ++ Ds) τ). }
      assert (Hag : forall x, x < ind_nu D -> sentry_sub (sb_of_list Id uv x) Θ = sb_of_list Id Us x).
      { intros x Hx.
        rewrite (sb_of_list_nth uv Id x (a_var 0)) by lia.
        rewrite <- Euv, (sb_of_list_nth (List.map (fun M => M[Θ]) uv) Id x (a_var 0)) by (rewrite List.length_map; lia).
        cbn [sentry_sub]; rewrite List.length_map.
        rewrite (List.nth_indep (List.map (fun M => M[Θ]) uv) (a_var 0) ((a_var 0)[Θ])) by (rewrite List.length_map; lia).
        rewrite (List.map_nth (fun M => M[Θ])); reflexivity. }
      pose proof (tele_insts_sub (im_nparams Mj) (ind_nu D) (sb_of_list Id uv) (sb_of_list Id Us) Θ Pg HassN
                    (decl_closed_nparams_scoped D Hc _ _ HMj) Hag) as Etel.
      assert (EPg : List.map (fun M => M[Θ]) Pg = List.map (fun P => P[sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)]) (ptyp_ps t)).
      { unfold Pg; rewrite List.map_map; apply List.map_ext; intros P.
        unfold wp, Θ.
        replace (Us ++ Ns ++ As1 ++ Ds) with ((Us ++ Ns) ++ (As1 ++ Ds)) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite (sb_of_list_app (Us ++ Ns) (As1 ++ Ds) τ), <- HDl, exp_wk_pat_falses_sb_of_list by exact HAl.
        rewrite <- (sb_of_list_app (Us ++ Ns) (nonrec_exps gs1 As1 ++ Ds) τ), <- !List.app_assoc; reflexivity. }
      rewrite EPg in Etel.
      rewrite <- Etel, List.nth_error_map, HT0 in HT; cbn in HT; injection HT as <-.
      exact H'.
    - pose proof (mc_recs _ _ (dc_members _ HcQ _ _ HMi') c gs' gs1' t' gs2' (cons_lookup_in _ _ _ Hcon') Heq') as Hst.
      pose proof (ptyp_scoped_ps _ _ Hst) as Hps; rewrite List.Forall_forall in Hps.
      rewrite <- Hdp; apply Hps, (List.nth_error_In _ _ HP0').
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

  (** *** Along an Argument Recursive in Both *)

  Section WalkCtx.
    Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember) (c : String.string) (gs' gs : list carg).
    Hypotheses (HMi' : ind_member Dq i' = Some Mi') (HVM : view_member p D qc Dq vm i' Mi' v Mv)
      (Hcon' : ind_con Mi' c = Some gs') (Hcon : ind_con Mv c = Some gs) (Hcorr : cargs_corr vm gs' gs).
    Let Hv := vmb_v _ _ _ _ _ _ _ _ _ HVM.
    Let HMv := vmb_mem _ _ _ _ _ _ _ _ _ HVM.
    Variables (gs1' : list carg) (t' : ptyp) (gs2' gs1 : list carg) (t : ptyp) (gs2 : list carg).
    Hypotheses (Heq' : gs' = gs1' ++ ca_rec t' :: gs2') (Heq : gs = gs1 ++ ca_rec t :: gs2) (Hl1 : List.length gs1' = List.length gs1).
    Variables (ns vp : list domain).
    Hypotheses (Hns' : tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ns ns) (Hlvp : List.length vp = List.length gs1)
      (Hpc : tele_prefix_rel (canon_args_rel Dq cups i' ns c) (List.length (cargs_nonrec gs1'))
               (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp)).
    Let VMP := view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv ns ns Hns'.

    Lemma wk_corr : cargs_corr vm gs1' gs1 /\ List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) /\ ptyp_depth t' = ptyp_depth t.
    Proof.
      destruct (cargs_corr_split vm gs1' (ca_rec t' :: gs2') gs1 (ca_rec t :: gs2) ltac:(rewrite <- Heq', <- Heq; exact Hcorr) Hl1)
        as [Hc1 Hc2].
      cbn in Hc2; destruct Hc2 as (Hm & Hd & _); exact (conj Hc1 (conj Hm Hd)).
    Qed.

    Lemma wk_lms : List.length ns = im_nn Mv.
    Proof. exact (params_length _ _ _ _ _ _ _ _ _ VMP). Qed.

    Lemma wk_inv : exists vsX, view_args_inv p D qc Dq ups cups Mi' v Mv c ns gs1' gs1 vp vsX.
    Proof.
      exact (view_args_complete p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
               c gs' gs Hcon' Hcon Hcorr ns wk_lms (params_group_values _ _ _ _ _ _ _ _ _ VMP)
               (params_container_values _ _ _ _ _ _ _ _ _ VMP) gs1 gs1' (ca_rec t' :: gs2') (ca_rec t :: gs2) vp
               Heq' Heq (proj1 wk_corr) Hlvp Hpc).
    Qed.

    Lemma wk_ns_g : tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mv)) ns ns.
    Proof. exact (view_nparams_transfer p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv _ _ Hns'). Qed.

    Lemma wk_pg : tele_prefix_rel (canon_args_rel D ups v ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp).
    Proof. destruct wk_inv as (vsX & [_ _ HnXg _ _ HaX]); rewrite HnXg in HaX; exact HaX. Qed.

    Lemma wk_doms_agree : forall kk B' B ys, List.nth_error (ptyp_doms t') kk = Some B' -> List.nth_error (ptyp_doms t) kk = Some B ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ns (nonrec_arg_vals gs1' vp) (ptyp_doms t')) kk ys ys ->
        (canon_doms_rel cups i' (ns ++ nonrec_arg_vals gs1' vp ++ ys) B' <~> canon_doms_rel ups v (ns ++ nonrec_arg_vals gs1 vp ++ ys) B).
    Proof.
      intros kk B' B ys HB' HB Hy'.
      exact (shape_doms_rel_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
               c gs' gs Hcon' Hcon Hcorr ns wk_lms (params_group_values _ _ _ _ _ _ _ _ _ VMP)
               (params_container_values _ _ _ _ _ _ _ _ _ VMP) gs1' t' gs2' gs1 t gs2 vp kk B' B ys
               Heq' Heq (proj1 wk_corr) Hlvp Hpc HB' HB Hy').
    Qed.

    (** The values of the two domains of the two shapes, after domains
        related at the container's: related. *)
    Lemma wk_dom_rel : forall kk ys B' B b0' b0, List.nth_error (ptyp_doms t') kk = Some B' -> List.nth_error (ptyp_doms t) kk = Some B ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ns (nonrec_arg_vals gs1' vp) (ptyp_doms t')) kk ys ys ->
        ⟦ B' ⟧ env_args nil (cups ++ ns ++ nonrec_arg_vals gs1' vp ++ ys) ↘ b0' ->
        ⟦ B ⟧ env_args nil (ups ++ ns ++ nonrec_arg_vals gs1 vp ++ ys) ↘ b0 ->
        exists i : nat, Dom b0' ≈ b0 ∈ per_univ i.
    Proof.
      intros kk ys B' B b0' b0 HB' HB Hy' Eb0' Eb0.
      destruct wk_corr as (Hc1 & _ & Hdp).
      pose proof wk_lms as Hlms.
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
      destruct wk_inv as (vsX & Hinv); pose proof Hinv as [HlX HnX HnXg HgX HcX _].
      assert (Hd : kk < List.length (ptyp_doms t)) by (unfold ptyp_depth in Hdp; rewrite <- Hdp; apply List.nth_error_Some; congruence).
      assert (Hd' : kk < List.length (ptyp_doms t')) by (apply List.nth_error_Some; congruence).
      destruct (view_shape_walk p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                  c gs' gs Hcon' Hcon Hcorr ns Hlms gs1' t' gs2' gs1 t gs2 vp vsX Heq' Heq Hc1 Hinv kk ys ltac:(lia) Hy')
        as [Hgd Hcd (i & R & ag & ac & Eag & Eac & HR)].
      pose proof Hy' as Hyl; rewrite tele_prefix_rel_iff in Hyl; destruct Hyl as (Hly & _ & _).
      destruct (vg_dom_types p D Hg Hcv v Mv c gs gs1 t gs2 kk B ups ns vsX ys HMv Hcon Heq HB Hu Hlms HlX Hly
                  (walk_group_prefix p D ups Hu Mv ns Hlms gs1 t vsX kk ys HlX HgX Hgd)) as (ig & Rg & bg & bg' & Ebg & Ebg' & HRg).
      destruct (vg_dom_types qc Dq HgQ HcvQ i' Mi' c gs' gs1' t' gs2' kk B' cups ns vsX ys HMi' Hcon' Heq' HB' length_cups
                  ltac:(lia) ltac:(lia) Hly
                  (walk_container_prefix p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hu Ecups i' Mi' v Mv HMi' Hv HMv ns Hlms
                     gs1' t' vsX kk ys ltac:(lia) HcX Hcd)) as (ic & Rc & bc & bc' & Ebc & Ebc' & HRc).
      rewrite HnXg in Ebg'; rewrite HnX in Ebc'.
      pose proof (functional_eval_exp _ _ _ _ Ebg' Eb0) as ->.
      pose proof (functional_eval_exp _ _ _ _ Ebc' Eb0') as ->.
      destruct (Tele.ptyp_skip_lt kk t Hd) as (B0 & HB0 & Hs); rewrite HB in HB0; injection HB0 as <-.
      destruct (Tele.ptyp_skip_lt kk t' Hd') as (B0' & HB0' & Hs'); rewrite HB' in HB0'; injection HB0' as <-.
      rewrite Hs in Eag; rewrite Hs' in Eac; cbn [ptyp_ty] in Eag, Eac.
      assert (Ag : ag = Πᵈ bg (env_args nil (ups ++ ns ++ vsX ++ ys))
                          (ptyp_ty p D (im_nn Mv) (false :: List.repeat false kk ++ cargs_pat gs1) (ptyp_skip (S kk) t)))
        by (eapply functional_eval_exp; [ exact Eag | econstructor; exact Ebg ]).
      assert (Ac : ac = Πᵈ bc (env_args nil (cups ++ ns ++ vsX ++ ys))
                          (ptyp_ty qc Dq (im_nn Mi') (false :: List.repeat false kk ++ cargs_pat gs1') (ptyp_skip (S kk) t')))
        by (eapply functional_eval_exp; [ exact Eac | econstructor; exact Ebc ]).
      subst ag ac; clear Eag Eac.
      basic_invert_per_univ_elem HR.
      match goal with H : per_univ_elem _ ?r bg bc |- _ => rename H into Hin end.
      exists ic.
      eapply per_univ_trans'; [ exact (per_univ_sym' _ _ _ (ex_intro _ Rc HRc)) |].
      eapply per_univ_trans'; [ exact (per_univ_sym' _ _ _ (ex_intro (fun R => per_univ_elem _ R bg bc) _ Hin)) | exact (ex_intro _ Rg HRg) ].
    Qed.
  End WalkCtx.

  (** A recursive argument of the container's member [i'], after domains
      of its shape: at an argument of a constructor recursive in both, a
      recursive argument of the group's member the view takes [i'] to, at
      the instance of the shape's context on the group's side. *)
  Definition rec_to_group (i' : nat) (Γ : ctx) (Us0 : list exp) (pre : list domain) (t0 : ptyp) (A' : typ) (N : exp) (x : domain)
    : Prop :=
    forall Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 ns vp kk ys τ Us Ns As1 Ds SbC,
      ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs ->
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
      tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ns ns -> List.length vp = List.length gs1 ->
      tele_prefix_rel (canon_args_rel Dq cups i' ns c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp) ->
      kk <= List.length (ptyp_doms t) -> t0 = ptyp_skip kk t' ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ns (nonrec_arg_vals gs1' vp) (ptyp_doms t')) kk ys ys ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel ups v) ns (nonrec_arg_vals gs1 vp) (ptyp_doms t)) kk ys ys ->
      Us0 = view_args Us -> pre = ns ++ nonrec_arg_vals gs1' vp ++ ys ->
      List.length Ns = im_nn Mv -> List.length As1 = List.length gs1 -> List.length Ds = kk ->
      A' = ptyp_ty_at qc Dq (view_args Us) (sb_of_list τ (view_args Us ++ Ns ++ nonrec_exps gs1' As1 ++ Ds)) t0 ->
      ⊢ Γ -> glu_args Γ (ind_uparams D) Id nil Us ups ->
      Γ ⊢ˢ sb_of_list τ (Us ++ Ns ++ As1 ++ Ds) : sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv ->
      EG doms_ctx (List.firstn kk (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mv
        ∈ glu_ctx_env ↘ SbC ->
      Γ ⊢ˢ sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds) ® env_args nil (ups ++ ns ++ nonrec_arg_vals gs1 vp ++ ys) ∈ SbC ->
      glu_rec p D ups NEl AEl DP DEl v Γ Us (ns ++ nonrec_arg_vals gs1 vp ++ ys) (ptyp_skip kk t)
        (ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)) (ptyp_skip kk t)) N x.

  (** A domain: an element of the group's gluing of the domain is one of
      the container's, the two domains being equal and their values
      related; applied to it, the argument is a recursive argument of the
      rest of the shape. *)
  Lemma walk_pi : forall i' Γ Us0 pre B' t0 A' N x,
      (forall IT OT, A' = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP' i' pre B') ->
      (forall IT OT, A' = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> canon_doms_rel cups i' pre B' c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl' i' pre B' -> exists fc, $| x & c | gc_deps ⍮ gc_stack ↘ fc) ->
      (forall IT OT, A' = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Γ -> canon_doms_rel cups i' pre B' c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl' i' pre B' -> $| x & c | gc_deps ⍮ gc_stack ↘ fc ->
         rec_to_group i' Δ (List.map (fun U => U[φ]ʷ) Us0) (pre ++ c :: nil) t0 OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
      rec_to_group i' Γ Us0 pre (pt_pi B' t0) A' N x.
  Proof.
    intros i' Γ Us0 pre B' t0 A' N x HP1' HP2' IH3.
    intros Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 ns vp kk ys τ Us Ns As1 Ds SbC
      HMi' HVM Hcon' Hcon Hcorr Heq' Heq Hl1 Hns' Hlvp Hpc Hkk Hsk Hy' Hy HUs0 Hpre HNl HAl HDl HA' HΓ HUs HΘ HSbC Hσ.
    pose proof (vmb_v _ _ _ _ _ _ _ _ _ HVM) as Hv; pose proof (vmb_mem _ _ _ _ _ _ _ _ _ HVM) as HMv.
    pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
    destruct (wk_corr gs' gs Hcorr gs1' t' gs2' gs1 t gs2 Heq' Heq Hl1) as (Hc1 & Hmem & Hdp).
    pose proof (wk_lms i' Mi' v Mv HMi' HVM ns Hns') as Hlms.
    pose proof (wk_ns_g i' Mi' v Mv HMi' HVM ns Hns') as Hnsd.
    pose proof (wk_pg i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr gs1' t' gs2' gs1 t gs2 Heq' Heq Hl1 ns vp Hns' Hlvp Hpc) as Hpg.
    symmetry in Hsk; destruct (Tele.ptyp_skip_pi _ _ _ _ Hsk) as [HB' Hs'].
    assert (Hd : kk < List.length (ptyp_doms t))
      by (unfold ptyp_depth in Hdp; rewrite <- Hdp; apply List.nth_error_Some; congruence).
    destruct (Tele.ptyp_skip_lt kk t Hd) as (B & HB & Hs).
    rewrite Hs; cbn [ptyp_ty_at].
    rewrite HA' in HP1', HP2', IH3; cbn [ptyp_ty_at] in HP1', HP2', IH3; clear A' HA'.
    subst pre.
    assert (Hlnv : List.length (nonrec_arg_vals gs1 vp) = List.length (cargs_nonrec gs1)) by (apply length_nonrec_arg_vals; exact Hlvp).
    (** The two domains' values, glued, related, and equal. *)
    destruct (ifg_dom_eval _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs gs1 t gs2 _ kk B ys HMv Hnsd Hcon Heq Hpg HB Hy) as [b0 Eb0].
    pose proof (ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs gs1 t gs2 _ kk B ys b0 HMv Hnsd Hcon Heq Hpg HB Hy Eb0) as Hgb0.
    destruct (ifg_dom_eval _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' gs1' t' gs2' _ kk B' ys HMi' Hns' Hcon' Heq' Hpc HB' Hy') as [b0' Eb0'].
    pose proof (ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' gs1' t' gs2' _ kk B' ys b0' HMi' Hns' Hcon' Heq' Hpc HB' Hy' Eb0')
      as Hgb0'.
    destruct (wk_dom_rel i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr gs1' t' gs2' gs1 t gs2 Heq' Heq Hl1 ns vp Hns' Hlvp Hpc
                kk ys B' B b0' b0 HB' HB Hy' Eb0' Eb0) as [n Hrel].
    pose proof (wk_doms_agree i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr gs1' t' gs2' gs1 t gs2 Heq' Heq Hl1 ns vp Hns' Hlvp Hpc
                  kk B' B ys HB' HB Hy') as Hag.
    destruct (vs_dom_eq p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq HcQ i' Mi' v Mv HMi' Hv HMv Γ c gs' gs gs1' t' gs2' gs1 t gs2
                kk B' B τ Us Ns As1 Ds Hcon' Hcon Heq' Heq Hl1 HB' HB HUl HNl HAl HDl HΓ HΘ) as [l HBB].
    (** The group's type, glued at the domains' gluings. *)
    pose proof (shape_typ_glu p D HG Hc Hdt Hsu ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf v Mv c gs gs1 t gs2 ns _ HMv Hcon Heq
                  Hnsd Hpg Hlms Hlnv (ptyp_skip kk t) kk ys Γ τ Us (Ns ++ nonrec_exps gs1 As1 ++ Ds) SbC eq_refl Hkk Hy HΓ HUl
                  ltac:(rewrite !List.length_app, length_nonrec_exps by exact HAl; lia) HSbC Hσ) as Hsh.
    rewrite Hs in Hsh; cbn [glu_shape_typ ptyp_ty_at] in Hsh.
    destruct (Hsh _ _ eq_refl) as [HshD _].
    (** An element of the group's domain is one of the container's. *)
    assert (Hconv : forall Δ φ b c', Δ ⊢ᵏ φ : Γ -> canon_doms_rel ups v (ns ++ nonrec_arg_vals gs1 vp ++ ys) B c' c' ->
              Δ ⊢ b : B[sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)][φ]ʷ ® c' ∈ DEl v (ns ++ nonrec_arg_vals gs1 vp ++ ys) B ->
              canon_doms_rel cups i' (ns ++ nonrec_arg_vals gs1' vp ++ ys) B' c' c' /\
              Δ ⊢ b : B'[sb_of_list τ (view_args Us ++ Ns ++ nonrec_exps gs1' As1 ++ Ds)][φ]ʷ ® c'
                ∈ DEl' i' (ns ++ nonrec_arg_vals gs1' vp ++ ys) B').
    { intros Δ φ b c' Hφ Hc' Hb.
      split; [ apply Hag; exact Hc' |].
      pose proof (kripke_preserves_typ_eq _ _ _ _ _ _ HBB Hφ) as HBBφ.
      exact (glu_elem_conv u u' n l b0' b0 _ _ _ _ Δ _ _ b c' Hgb0 Hgb0' (per_univ_sym' _ _ _ Hrel)
               (wf_exp_eq_sym _ _ _ _ _ _ HBBφ) (HP1' _ _ eq_refl Δ φ Hφ) Hb). }
    apply glu_rec_pi.
    - intros IT OT HA0 Δ φ Hφ; injection HA0 as <- <-; exact (HshD Δ φ Hφ).
    - intros IT OT HA0 Δ φ b c' Hφ Hc' Hb; injection HA0 as <- <-.
      destruct (Hconv Δ φ b c' Hφ Hc' Hb) as [Hc'c Hb'].
      exact (HP2' _ _ eq_refl Δ φ b c' Hφ Hc'c Hb').
    - intros IT OT HA0 Δ φ b c' fc Hφ Hc' Hb Hfc; injection HA0 as <- <-.
      destruct (Hconv Δ φ b c' Hφ Hc' Hb) as [Hc'c Hb'].
      pose proof (IH3 _ _ eq_refl Δ φ b c' fc Hφ Hc'c Hb' Hfc) as IHc.
      assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
      assert (Hd'' : kk < ptyp_depth t) by (unfold ptyp_depth; exact Hd).
      assert (HsIs : List.Forall (exp_scoped (List.length Us)) Is) by (rewrite HUl; exact (decl_closed_head_scoped D Hc _ _ _ _ _ _ HMk Hh)).
      (** The rest of the container's type. *)
      assert (EA : (ptyp_ty_at qc Dq (List.map (fun U => U[↑]ʷ) (view_args Us))
                      (q (sb_of_list τ (view_args Us ++ Ns ++ nonrec_exps gs1' As1 ++ Ds))) t0)[(ι φ),,b]
                   = ptyp_ty_at qc Dq (view_args (List.map (fun U => U[φ]ʷ) Us))
                     (sb_of_list (sb_wk τ φ) (view_args (List.map (fun U => U[φ]ʷ) Us) ++ List.map (fun U => U[φ]ʷ) Ns
                                               ++ nonrec_exps gs1' (List.map (fun U => U[φ]ʷ) As1) ++ (List.map (fun U => U[φ]ʷ) Ds ++ b :: nil))) t0).
      { rewrite (ptyp_ty_at_shape_step qc Dq t0 τ (view_args Us) (Ns ++ nonrec_exps gs1' As1 ++ Ds) φ b HcQ (length_view_args Us)).
        unfold view_args; rewrite (view_args_wk Is Us φ HsIs).
        rewrite !List.map_app, <- !List.app_assoc, <- nonrec_exps_map; reflexivity. }
      (** The instances, moved and extended by the argument. *)
      destruct (dt_view_doms _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 kk
                  HMk Hh Hq HMi' Hv HMv Hcon' Hcon Heq' Heq Hl1 Hd'') as [i0 Hdom].
      assert (HdomTy : sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv
                         ⊢ ptyp_dom_at (cargs_pat gs1) kk t : Typeω@i0) by (gen_presups; eassumption).
      assert (Edom : (ptyp_dom_at (cargs_pat gs1) kk t)[sb_of_list τ (Us ++ Ns ++ As1 ++ Ds)]
                     = B[sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)]).
      { unfold ptyp_dom_at; rewrite (List.nth_error_nth _ _ _ HB).
        replace (Us ++ Ns ++ As1 ++ Ds) with ((Us ++ Ns) ++ (As1 ++ Ds)) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite (sb_of_list_app (Us ++ Ns) (As1 ++ Ds) τ), <- HDl, exp_wk_pat_falses_sb_of_list by exact HAl.
        rewrite <- (sb_of_list_app (Us ++ Ns) (nonrec_exps gs1 As1 ++ Ds) τ), <- !List.app_assoc; reflexivity. }
      assert (Hbty : Δ ⊢ b : (ptyp_dom_at (cargs_pat gs1) kk t)[sb_of_list τ (Us ++ Ns ++ As1 ++ Ds)][φ]ʷ)
        by (rewrite Edom; exact (glu_univ_elem_trm_escape _ _ _ _ Hgb0 _ _ _ _ Hb)).
      pose proof (theta_step _ _ _ _ _ _ _ _ _ HΘ Hφ HdomTy Hbty) as HΘ'.
      replace (ce_ass (ptyp_dom_at (cargs_pat gs1) kk t) :: sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))
                 ++ cargs_ctx p D Mv gs1 ++ im_params D Mv)
        with (sh_ctx (cargs_pat gs1) (List.firstn (S kk) (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv) in HΘ'
        by (rewrite (Views.sh_ctx_firstn_S _ _ _ Hd''); reflexivity).
      rewrite !List.map_app, <- !List.app_assoc in HΘ'.
      destruct (gid_dctx _ HG _ _ _ _ _ _ _ (S kk) HMv Hcon Heq ltac:(lia)) as [SbC' HSbC'].
      pose proof (shape_sub_step D ups u DP DEl v Mv c gs gs1 t gs2 kk B ns (nonrec_arg_vals gs1 vp) ys Γ τ Us
                    (Ns ++ nonrec_exps gs1 As1 ++ Ds) SbC SbC' Δ φ b b0 c' HMv Hcon Heq HB HSbC HSbC' Hσ Hφ Eb0 Hgb0
                    (HshD Δ φ Hφ) Hb) as Hσ'.
      rewrite !List.map_app, <- !List.app_assoc, <- nonrec_exps_map in Hσ'.
      (** The group's type after the domain. *)
      change (match t with | pt_self _ _ => t | pt_pi _ t1 => ptyp_skip kk t1 end) with (ptyp_skip (S kk) t).
      rewrite (ptyp_ty_at_shape_step p D (ptyp_skip (S kk) t) τ Us (Ns ++ nonrec_exps gs1 As1 ++ Ds) φ b Hc HUl).
      rewrite !List.map_app, <- !List.app_assoc, <- nonrec_exps_map.
      exact (IHc Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 ns vp (S kk) (ys ++ c' :: nil) (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us)
               (List.map (fun U => U[φ]ʷ) Ns) (List.map (fun U => U[φ]ʷ) As1) (List.map (fun U => U[φ]ʷ) Ds ++ b :: nil) SbC'
               HMi' HVM Hcon' Hcon Hcorr Heq' Heq Hl1 Hns' Hlvp Hpc ltac:(lia) (eq_sym Hs')
               ltac:(apply tele_prefix_rel_snoc; [ exact Hy' | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB'); exact Hc'c ])
               ltac:(apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hc' ])
               ltac:(rewrite HUs0; unfold view_args; exact (view_args_wk Is Us φ HsIs))
               ltac:(rewrite <- !List.app_assoc; reflexivity)
               ltac:(rewrite List.length_map; exact HNl) ltac:(rewrite List.length_map; exact HAl)
               ltac:(rewrite List.length_app, List.length_map; cbn; lia)
               EA HΔ (glu_args_wk _ _ _ _ _ _ _ (dc_ass _ Hc) (dc_uparams _ Hc) Hφ HUs) HΘ' HSbC' Hσ').
  Qed.

  (** An element of the container's member [i'] at the view's instance of
      glued uniform parameters is an element of the group's member the
      view takes [i'] to, at parameters typed there. *)
  Definition elem_to_group (i' : nat) (Γ : ctx) (Us0 Ns : list exp) (M : exp) (x : domain) : Prop :=
    forall Mi' v Mv Us, ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv -> Us0 = view_args Us -> ⊢ Γ ->
      glu_args Γ (ind_uparams D) Id nil Us ups ->
      (forall j X T, List.nth_error (Us ++ Ns) j = Some X ->
         List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T) ->
      ind_glu_elem p D ups NEl AEl DP DEl v Γ Us Ns M x.

  (** The end of the shape: the group's parameters are glued as the
      shape's are, and an element of the container's member the shape ends
      in, at the view's instance of the group's parameters, is an element of
      the group's member. *)
  Lemma walk_self : forall i' Γ Us0 pre j' Ps' A' N x Mj', ind_member Dq j' = Some Mj' ->
      (forall bsr Q, ⟦ Ps' ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (cups ++ pre) ↘ bsr -> A' = im_ty_at qc j' Mj' Us0 Q ->
         forall Δ φ Us' Q', Δ ⊢ᵏ φ : Γ -> List.length Us' = ind_nu Dq ->
           exps_eq_at Δ (im_params Dq Mj') (List.map (fun P => P[φ]ʷ) (Us0 ++ Q)) (Us' ++ Q') ->
           elem_to_group j' Δ Us' Q' N[φ]ʷ x) ->
      rec_to_group i' Γ Us0 pre (pt_self j' Ps') A' N x.
  Proof.
    intros i' Γ Us0 pre j' Ps' A' N x Mj' HMj' IH2.
    intros Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 ns vp kk ys τ Us Ns As1 Ds SbC
      HMi' HVM Hcon' Hcon Hcorr Heq' Heq Hl1 Hns' Hlvp Hpc Hkk Hsk Hy' Hy HUs0 Hpre HNl HAl HDl HA' HΓ HUs HΘ HSbC Hσ.
    pose proof (vmb_v _ _ _ _ _ _ _ _ _ HVM) as Hv; pose proof (vmb_mem _ _ _ _ _ _ _ _ _ HVM) as HMv.
    pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
    destruct (wk_corr gs' gs Hcorr gs1' t' gs2' gs1 t gs2 Heq' Heq Hl1) as (Hc1 & Hmem & Hdp).
    pose proof (wk_lms i' Mi' v Mv HMi' HVM ns Hns') as Hlms.
    pose proof (wk_ns_g i' Mi' v Mv HMi' HVM ns Hns') as Hnsd.
    pose proof (wk_pg i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr gs1' t' gs2' gs1 t gs2 Heq' Heq Hl1 ns vp Hns' Hlvp Hpc) as Hpg.
    symmetry in Hsk; destruct (Tele.ptyp_skip_self _ _ _ _ Hsk) as (HkL & Ejm & EPs).
    assert (Hkd : kk = List.length (ptyp_doms t)) by (unfold ptyp_depth in Hdp; lia).
    subst j' Ps' pre.
    replace (ptyp_skip kk t) with (pt_self (ptyp_mem t) (ptyp_ps t)) by (rewrite Hkd; symmetry; exact (Views.ptyp_skip_depth t)).
    cbn [ptyp_ty_at].
    cbn [ptyp_ty_at] in HA'; unfold ind_mty in HA'; rewrite HMj' in HA'.
    destruct (length_rec_ps D HD v Mv HMv c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HPl).
    assert (Hlnv : List.length (nonrec_arg_vals gs1 vp) = List.length (cargs_nonrec gs1)) by (apply length_nonrec_arg_vals; exact Hlvp).
    (** The group's side of the arguments and the domains before. *)
    destruct (wk_inv i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr gs1' t' gs2' gs1 t gs2 Heq' Heq Hl1 ns vp Hns' Hlvp Hpc)
      as (vsX & Hinv).
    pose proof Hinv as [HlX HnX HnXg HgX HcX HaX].
    destruct (view_shape_walk p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                c gs' gs Hcon' Hcon Hcorr ns Hlms gs1' t' gs2' gs1 t gs2 vp vsX Heq' Heq Hc1 Hinv kk ys Hkk Hy') as [Hgd Hcd _].
    pose proof (walk_group_prefix p D ups Hu Mv ns Hlms gs1 t vsX kk ys HlX HgX Hgd) as Hgall_end.
    rewrite Hkd, List.firstn_all in Hgall_end.
    assert (Hy_full : tele_prefix_rel (shape_doms_rel (canon_doms_rel ups v) ns (nonrec_arg_vals gs1 vsX) (ptyp_doms t))
                        (List.length (ptyp_doms t)) ys ys) by (rewrite HnXg, <- Hkd; exact Hy).
    destruct (shape_end_params_link p D Hg v Mv c gs HMv Hcon (vg_cargs_sem p D Hg Hcv v Mv c gs HMv Hcon) gs1 t gs2 Heq
                ups ns vsX ys Hu Hlms HlX Hgu Hnsd HaX Hgall_end Hy_full) as [bs bs1 Ebs Ebs1 Hrel].
    rewrite HnXg in Ebs.
    unfold ntele_rel in Hrel; rewrite HMj in Hrel.
    pose proof Hy as Hyl; rewrite tele_prefix_rel_iff in Hyl; destruct Hyl as (Hly & _ & _).
    set (σ := sb_of_list τ (Us ++ Ns ++ nonrec_exps gs1 As1 ++ Ds)) in *.
    set (Qn := List.map (fun P => P[σ]) (ptyp_ps t)) in *.
    assert (HSbCt : EG ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mv ∈ glu_ctx_env ↘ SbC)
      by (rewrite Hkd, List.firstn_all in HSbC; exact HSbC).
    assert (HQn : glu_args Γ (im_nparams Mj) (sb_of_list Id Us) (env_args nil ups) Qn bs).
    { unfold Qn, σ.
      eapply (rec_params_args VP p D HVP HPD HG v Mv c gs HMv Hcon ups Hu Γ gs1 t gs2 Mj τ Us (Ns ++ nonrec_exps gs1 As1 ++ Ds)
                ns (nonrec_arg_vals gs1 vp) ys SbC bs Heq HMj HUl); try eassumption;
        [ rewrite !List.length_app, length_nonrec_exps by exact HAl; unfold ptyp_depth; lia | unfold ptyp_depth; lia ]. }
    pose proof (decl_closed_params_ass D (ptyp_mem t) Mj Hc HMj) as HassPj.
    pose proof (decl_closed_params D (ptyp_mem t) Mj Hc HMj) as HsPj.
    assert (HQp : glu_args Γ (im_params D Mj) Id nil (Us ++ Qn) (ups ++ bs)).
    { unfold im_params; apply glu_args_app; [ exact (dc_ass _ Hc) | exact HUl | exact Hu |].
      split; [ exact HUs | exact HQn ]. }
    pose proof (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Γ Us HΓ HUs) as Hcomps.
    pose proof (Con.con_canon VP p D HVP HPD ups Hu Hgu) as Hcp.
    assert (H01 : tele_rel (canon_nparams_rel D ups (ptyp_mem t)) (List.rev (im_nparams Mj)) bs bs)
      by exact (canon_nparams_rel_trans p D ups Hass Hcp _ _ _ _ _ HMj Hrel (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hrel)).
    pose proof (nparams_of_glu_args p D Hass ups u NP NEl AP AEl DP DEl Hu Hf _ _ Γ Us Qn bs HMj Hcomps HQn H01) as HnQ.
    assert (HQl : List.length Qn = im_nn Mj) by (unfold Qn; rewrite List.length_map; exact HPl).
    assert (EQ : forall Q, ind_mty p D (ptyp_mem t) Us Qn = im_ty_at p (ptyp_mem t) Mj Us Q -> Q = Qn).
    { intros Q HQ; unfold ind_mty in HQ; rewrite HMj in HQ; unfold im_ty_at in HQ.
      apply apps_ind_inj, List.app_inv_head in HQ; congruence. }
    apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
    - intros bsr Q Hbsr HQ.
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      pose proof (EQ _ HQ) as ->.
      split; [ exact HQl | split; [ exact H01 |] ].
      intros bsr' Hb'.
      split; [ exact (glu_nparams_resp_per D ups NEl (nel_resp_per VP p D HVP HPD ups bu u NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf)
                        _ _ _ _ _ _ _ HMj Hb' HnQ) |].
      intros Δ0 φ Hφ.
      pose proof (glu_args_params_top _ _ _ _ _ HassPj HsPj (glu_args_wk _ _ _ _ _ _ _ HassPj HsPj Hφ HQp)) as Ht.
      exact (glu_params_top_resp_per_top_ps _ _ _ _ _ _ (canon_params_per_top VP p D HVP HPD ups bu Hu Hgu Hbu _ _ _ _ HMj Hb') Ht).
    - intros bsr Q Hbsr HQ Δ φ Us' Q' Hφ HUl' HQ'.
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      pose proof (EQ _ HQ) as ->.
      subst Us0.
      assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
      assert (HsIs : List.Forall (exp_scoped (List.length Us)) Is) by (rewrite HUl; exact (decl_closed_head_scoped D Hc _ _ _ _ _ _ HMk Hh)).
      set (σ' := sb_of_list τ (view_args Us ++ Ns ++ nonrec_exps gs1' As1 ++ Ds)) in *.
      set (Qc := List.map (fun P => P[σ']) (ptyp_ps t')) in *.
      (** The container's member the shape ends in, and the group's. *)
      destruct (view_agree_members p D k Mk qc kc Is vm Dq Hass HMk Hh Hq (ptyp_mem t') Mj' HMj') as (v0 & Mv0 & HVM0).
      pose proof (vmb_v _ _ _ _ _ _ _ _ _ HVM0) as Hv0; rewrite Hmem in Hv0; injection Hv0 as <-.
      pose proof (vmb_mem _ _ _ _ _ _ _ _ _ HVM0) as HMv0; rewrite HMj in HMv0; injection HMv0 as <-.
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ HVM0) as Hnnj.
      destruct (length_rec_ps Dq (vgr_valid _ _ HgQ) i' Mi' HMi' c gs' gs1' t' gs2' Hcon' Heq') as (Mj'' & HMj'' & HPl').
      rewrite HMj' in HMj''; injection HMj'' as <-.
      assert (HQcl : List.length Qc = List.length Qn) by (unfold Qc, Qn; rewrite !List.length_map; lia).
      (** The values of the container's parameters. *)
      pose proof (view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv ns ns Hns')
        as VMP0.
      assert (Hy'_full : tele_rel (shape_doms_rel (canon_doms_rel cups i') ns (nonrec_arg_vals gs1' vp) (ptyp_doms t')) (ptyp_doms t') ys ys).
      { apply tele_rel_of_pre; unfold ptyp_depth in Hdp; replace (List.length (ptyp_doms t')) with kk by lia; exact Hy'. }
      destruct (shape_params_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                  c gs' gs Hcon' Hcon Hcorr ns Hlms (params_group_values _ _ _ _ _ _ _ _ _ VMP0)
                  (params_container_values _ _ _ _ _ _ _ _ _ VMP0) Hnsd Hns' gs1' t' gs2' gs1 t gs2 vp ys
                  Heq' Heq Hc1 Hlvp Hpc Hy'_full) as [bsc bsg Ebsc _ _].
      (** The container's parameters are the group's at the view's
          instance. *)
      assert (HΘd : Γ ⊢ˢ sb_of_list τ (Us ++ Ns ++ As1 ++ Ds) : sh_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv)
        by (rewrite Hkd, List.firstn_all in HΘ; exact HΘ).
      assert (E0 : exps_eq_at Γ (im_params D Mj) (Us ++ Qn) (Us ++ Qc)).
      { split; [ rewrite !List.length_app; lia |].
        intros j0 X Y T HX HY HT.
        unfold im_params in HT; rewrite tele_insts_app in HT by (first [ exact (dc_ass _ Hc) | exact HUl ]).
        destruct (Nat.lt_ge_cases j0 (List.length Us)) as [Hj | Hj].
        - rewrite List.nth_error_app1 in HX, HY by exact Hj.
          rewrite HX in HY; injection HY as <-.
          rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (dc_ass _ Hc); unfold ind_nu in *; lia).
          apply wf_exp_eq_refl; eapply glu_args_typed; [ exact (dc_ass _ Hc) | exact HUs | eassumption | eassumption ].
        - rewrite List.nth_error_app2 in HX, HY by exact Hj.
          rewrite List.nth_error_app2 in HT by (rewrite length_tele_insts by exact (dc_ass _ Hc); unfold ind_nu in *; lia).
          rewrite length_tele_insts in HT by exact (dc_ass _ Hc).
          replace (j0 - Nat.min (List.length (ind_uparams D)) (List.length Us)) with (j0 - List.length Us) in HT by (unfold ind_nu in *; lia).
          symmetry.
          exact (vs_ps_eq p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq HcQ i' Mi' v Mv HMi' Hv HMv Γ c gs' gs gs1' t' gs2' gs1 t gs2 Mj
                   τ Us Ns As1 Ds Hcon' Hcon Heq' Heq Hl1 Hdp HMj HUl HNl HAl ltac:(unfold ptyp_depth; lia) HΓ HΘd _ _ _ _ HY HX HT). }
      assert (E1 : exps_eq_at Γ (im_params D Mj) (Us ++ Qc) (Us ++ Qn)).
      { split; [ rewrite !List.length_app; lia |].
        exact (params_eq_sym Γ p D (ptyp_mem t) Mj (Us ++ Qn) (Us ++ Qc) Hl HMj HΓ
                 ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia) ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia)
                 (proj2 E0)). }
      pose proof (exps_eq_at_params_wk p D (ptyp_mem t) Mj Γ Δ φ (Us ++ Qc) (Us ++ Qn) Hl HMj Hφ E1) as E1φ.
      assert (E2 : exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) Us ++ List.map (fun P => P[φ]ʷ) Qc) (Us' ++ Q')).
      { destruct HQ' as [HlQ' HQ'2].
        rewrite !List.length_map, !List.length_app in HlQ'.
        rewrite <- List.map_app.
        split; [ rewrite List.length_map, !List.length_app; lia |].
        exact (params_eq_trans Δ p D (ptyp_mem t) Mj (List.map (fun P => P[φ]ʷ) (Us ++ Qc)) (List.map (fun P => P[φ]ʷ) (Us ++ Qn))
                 (Us' ++ Q') Hl HMj HΔ
                 ltac:(rewrite List.length_map, List.length_app; unfold im_np, ind_nu in *; lia)
                 ltac:(rewrite List.length_map, List.length_app; unfold im_np, ind_nu in *; lia)
                 ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia)
                 (proj2 E1φ) HQ'2). }
      pose proof (vs_params_eq_transfer p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq HcQ (ptyp_mem t') Mj' (ptyp_mem t) Mj HMj' Hmem HMj
                    Δ (List.map (fun P => P[φ]ʷ) Us) Us' (List.map (fun P => P[φ]ʷ) Qc) Q' HΔ
                    ltac:(rewrite List.length_map; exact HUl) ltac:(rewrite List.length_map; lia) HUl' E2) as E3.
      assert (E3' : exps_eq_at Δ (im_params Dq Mj') (List.map (fun P => P[φ]ʷ) (view_args Us ++ Qc)) (view_args Us' ++ Q')).
      { rewrite List.map_app; unfold view_args; rewrite (view_args_wk Is Us φ HsIs); exact E3. }
      (** The group's uniform parameters there, glued, and its parameters
          typed. *)
      pose proof (exps_eq_at_uparams_of_params D Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Qn)) (Us' ++ Q') Hc
                    ltac:(rewrite List.length_map, List.length_app; unfold im_np, ind_nu in *; lia) HQ') as HU'.
      rewrite List.map_app, !firstn_app_exact in HU' by (rewrite ?List.length_map; unfold ind_nu in *; lia).
      pose proof (glu_args_resp_eq Δ (ind_uparams D) nil _ Us' ups (dc_ass _ Hc) (dt_uparams _ _ _ Hdt) HΔ HU'
                    (glu_args_wk _ _ _ _ _ _ _ (dc_ass _ Hc) (dc_uparams _ Hc) Hφ HUs)) as HUs'.
      pose proof (exps_eq_at_typed_r p D (ptyp_mem t) Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Qn)) (Us' ++ Q') Hl HMj HΔ
                    ltac:(rewrite List.length_map, List.length_app; unfold im_np, ind_nu in *; lia) HQ') as HPs'.
      exact (IH2 bsc Qc Ebsc HA' Δ φ (view_args Us') Q' Hφ (length_view_args Us') E3' Mj' (ptyp_mem t) Mj Us' HMj' HVM0 eq_refl HΔ HUs' HPs').
  Qed.
End ToGroup.

End Fixed_GCtx.
