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
From Mctt.Core.Completeness.Inductives Require Con RviewEnds.
From Mctt.Core.Completeness.Records Require Model.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence ViewCount.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup DescTyping.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Inductives Require Views.
From Mctt.Core.Syntactic Require Import Records.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Records Require Model.
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Elements at Related Types

    A term glued at a type of a value is glued at an equal type of a related
    value, at any gluing of it where that type is glued. *)
Lemma glu_elem_conv : forall (i j : universe_index) (k l : nat) a a' P El P' El' Γ T T' N x,
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' -> DG a ∈ glu_univ_elem j ↘ P ↘ El -> Dom a' ≈ a ∈ per_univ k ->
    Γ ⊢ T' ≈ T : Typeω@l -> Γ ⊢ T ® P -> Γ ⊢ N : T' ® x ∈ El' -> Γ ⊢ N : T ® x ∈ El.
Proof.
  intros * Hg' Hg [R HR] HTT HT HN.
  set (n := Nat.max (large_level i) (Nat.max (large_level j) (Nat.max k l))).
  assert (Hin : universe_index_le i (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
  assert (Hjn : universe_index_le j (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_universe_index Hin Hg') as (Pn & Eln & Hgn).
  pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hin Hg' Hgn HN) as HNn.
  pose proof (per_univ_elem_cumu_ge k n _ _ _ ltac:(unfold n; lia) HR) as HRn.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R HRn) Hgn) as Hgn'.
  pose proof (lift_exp_eq_ge _ _ _ _ _ l n ltac:(unfold n; lia) HTT) as HTTn.
  pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgn' _ _ _ _ _ HNn HTTn) as HNn'.
  exact (glu_univ_elem_exp_lower_universe_index Hjn Hg Hgn' HT HNn').
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
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-; exact HIl.
  Qed.

  Lemma vs_nn : im_nn Mv = im_nn Mi'.
  Proof.
    destruct (decl_typed_view_wrap _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv' & HMv' & Hnn & _).
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
    pose proof (decl_typed_view_args _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv Hcon' Hcon) as Hext.
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
    pose proof (decl_typed_view_nparams _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv) as Hext.
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
      [ exact (decl_closed_ass _ HcQ) | rewrite List.length_map, vs_is_length; reflexivity
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
    destruct (decl_typed_view_doms _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 kk
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
    - pose proof (member_closed_recs _ _ (decl_closed_members _ HcQ _ _ HMi') c gs' gs1' t' gs2' (cons_lookup_in _ _ _ Hcon') Heq') as Hst.
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
    destruct (decl_typed_view_ps _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j
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
    - pose proof (member_closed_recs _ _ (decl_closed_members _ HcQ _ _ HMi') c gs' gs1' t' gs2' (cons_lookup_in _ _ _ Hcon') Heq') as Hst.
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
      by (intros; unfold im_params; apply tele_insts_app; [ exact (decl_closed_ass _ Hc) | assumption ]).
    assert (HlU : forall Ws, List.length Ws = ind_nu D -> List.length (tele_insts (ind_uparams D) Id Ws) = ind_nu D)
      by (intros; rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in *; lia).
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
        [ exact (decl_closed_ass _ Hc) | rewrite List.app_nil_r; exact (decl_typed_uparams_field _ _ _ Hdt) | apply wf_sub_eq_refl, wf_sub_to_nil, HΓ
        | exact HU1 | exact HU2 | exact HUs1 | exact HUs2 |].
      intros j Z W T HZ HW HT.
      assert (Hj1 : j < List.length Us1) by (apply List.nth_error_Some; congruence).
      apply (HE j); [ rewrite List.nth_error_app1 by lia; exact HZ | rewrite List.nth_error_app1 by lia; exact HW |].
      rewrite (HtiG Us1 X HU1), List.nth_error_app1 by (rewrite HlU by exact HU1; lia).
      exact HT. }
    pose proof (vs_is_length) as HIl.
    split; [ rewrite !List.length_app, !List.length_map; lia |].
    intros j Z W T HZ HW HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (first [ exact (decl_closed_ass _ HcQ) | rewrite List.length_map, HIl; reflexivity ]).
    destruct (Nat.lt_ge_cases j (ind_nu Dq)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HZ, HW by (rewrite List.length_map; lia).
      rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (decl_closed_ass _ HcQ); rewrite List.length_map; unfold ind_nu in *; lia).
      apply nth_error_map_inv in HZ as (I & HI & ->).
      rewrite List.nth_error_map, HI in HW; injection HW as <-.
      rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (sb_of_list Id Us1) Is (decl_closed_ass _ HcQ) (decl_closed_uparams _ HcQ) ltac:(intros; lia)) in HT.
      apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      exact (sub_eq_preserves_exp _ _ _ _ _ (decl_typed_view_is _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HI HT0) _ _ _ Hσ).
    - rewrite List.nth_error_app2 in HZ, HW by (rewrite List.length_map; lia).
      rewrite List.length_map, HIl in HZ, HW.
      rewrite List.nth_error_app2 in HT by (rewrite length_tele_insts by exact (decl_closed_ass _ HcQ); rewrite List.length_map; unfold ind_nu in *; lia).
      rewrite length_tele_insts, List.length_map, HIl in HT by exact (decl_closed_ass _ HcQ).
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
  destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dh' & Mkh' & Hq' & HMkh' & Hlt & _ & _ & Hvk & _ & Hcorr).
  rewrite Hq in Hq'; injection Hq' as <-; rewrite HMkh in HMkh'; injection HMkh' as <-.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hq) as [HdtH HcH].
  assert (Hdecl : im_is_decl Mkh = true) by (apply (decl_typed_order _ _ _ HdtH _ _ HMkh); exact Hlt).
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
    unfold im_is_decl in Hdecl; destruct (im_head Mkh); [ reflexivity | discriminate | discriminate ]. }
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
    destruct (decl_typed_view _ _ _ HdtQ _ _ _ _ _ _ HMi' Hhi) as (Dh' & Mkh' & HqH' & HMkh' & _ & _ & _ & Hvk & _).
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
      unfold im_params in HT; rewrite tele_insts_app in HT by (first [ exact (decl_closed_ass _ HcH) | exact HPcl ]).
      rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (decl_closed_ass _ HcH); unfold ind_nu in *; lia).
      apply nth_error_map_inv in HZ as (Xj & HXj & ->).
      pose proof HY as HY0; unfold Pc in HY0; apply nth_error_map_inv in HY0 as (Ij & HIj & EY).
      destruct (nth_error_lt_some (tele_insts (ind_uparams Dh) Id Ihc) j) as [T0 HT0];
        [ rewrite length_tele_insts by exact (decl_closed_ass _ HcH); unfold ind_nu in *; lia |].
      pose proof (decl_typed_view_view_is _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v qh kh Ihc vmc Dh Mv X vm' j
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
        rewrite <- (tele_insts_sub (ind_uparams Dh) 0 Id Id σU _ (decl_closed_ass _ HcH) (decl_closed_uparams _ HcH) ltac:(intros; lia)) in HT.
        rewrite <- (tele_insts_sub (ind_uparams Dh) 0 Id Id (sb_of_list Id Is) _ (decl_closed_ass _ HcH) (decl_closed_uparams _ HcH) ltac:(intros; lia)) in HT.
        rewrite !List.nth_error_map, HT0 in HT; cbn in HT; injection HT as <-; reflexivity. }
      rewrite EY', ET; symmetry; exact HE'.
    - rewrite List.nth_error_app2 in HY, HZ by (rewrite ?List.length_map; lia).
      rewrite List.length_map, HXl in HZ; rewrite HPcl in HY.
      rewrite HY in HZ; injection HZ as <-.
      apply wf_exp_eq_refl; eapply HPh; [| exact HT ].
      rewrite List.nth_error_app2 by lia; rewrite HPcl; exact HY.
  Qed.

  (** At a record view of the container: the two members are record views
      of the same record, at instances equal at the view's
      ([decl_typed_view_rview_is]). *)
  Lemma vh_rview_ty_eq : forall q'' Is'' fl'', im_head Mi' = mh_record q'' Is'' fl'' ->
      exists i, Γ ⊢ im_ty_at qc i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) Ns ≈ im_ty_at p v Mv Us Ns : Typeω@i.
  Proof.
    intros * Hhi.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgc.
    destruct (decl_typed_view_rview _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & X & HMv' & Hhv & HXl).
    rewrite HMv in HMv'; injection HMv' as <-.
    destruct (rview_struct_record _ _ _ (decl_typed_rstruct _ _ _ HdtQ) _ _ _ _ _ HMi' Hhi) as [R HR].
    pose proof (rview_record_lookup _ _ _ _ _ _ HR) as HlR.
    pose proof (rview_record_count _ _ _ _ _ _ HR) as HIl.
    pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hgc) HlR) as HcR.
    pose proof (record_lookup_typed _ _ Hgc (gctx_valid_syn _ _ Hgc) _ _ HlR) as HRt.
    assert (HNs : Ns = nil).
    { destruct Ns; [ reflexivity |].
      unfold im_nn in HNl; rewrite (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMv Hhv) in HNl; discriminate HNl. }
    pose proof (wf_uparams_sub _ _ _ _ _ Hdt HΓ HUl vh_uparams_typed) as HσU.
    rewrite HNs.
    set (σU := sb_of_list Id Us) in *.
    set (vU := List.map (fun I => I[σU]) Is) in *.
    unfold im_ty_at, im_pre; rewrite Hhi, Hhv, !List.app_nil_r.
    assert (HsIs'' : List.Forall (exp_scoped (List.length Is)) Is'')
      by (rewrite (vs_is_length D Hdt k Mk qc kc Is vm Dq HMk Hh Hq); exact (decl_closed_rhead_scoped _ HcQ _ _ _ _ _ HMi' Hhi)).
    pose proof (Views.inst_sub_comm Is'' Is (List.length Is) σU HsIs'' eq_refl) as Ecomm.
    fold vU in Ecomm.
    set (Xs := List.map (fun I => I[sb_of_list Id vU]) Is'') in *.
    set (Ys := List.map (fun I => I[σU]) X) in *.
    assert (HXl' : List.length Xs = List.length (record_params R)) by (unfold Xs; rewrite List.length_map; exact HIl).
    assert (HYl' : List.length Ys = List.length (record_params R)) by (unfold Ys; rewrite List.length_map; lia).
    (** The two instances, pointwise equal. *)
    assert (HXY : forall j0 Y Z T, List.nth_error Xs j0 = Some Y -> List.nth_error Ys j0 = Some Z ->
               List.nth_error (tele_insts (record_params R) Id Xs) j0 = Some T -> Γ ⊢ Y ≈ Z : T).
    { intros j0 Y Z T HY HZ HT.
      rewrite Ecomm in HY, HT.
      apply nth_error_map_inv in HY as (I'' & HI'' & ->).
      unfold Ys in HZ; apply nth_error_map_inv in HZ as (C0 & HC0 & ->).
      rewrite <- (List.map_map (fun I => I[sb_of_list Id Is]) (fun I => I[σU])), <- (record_params_insts_sub R _ σU HcR),
        <- (record_params_insts_sub R Is'' (sb_of_list Id Is) HcR), List.map_map in HT.
      apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      assert (HC' : List.nth_error (List.map (fun I => I[sb_of_list Id Is]) Is'') j0 = Some I''[sb_of_list Id Is])
        by (rewrite List.nth_error_map, HI''; reflexivity).
      pose proof (decl_typed_view_rview_is _ _ _ _ Hgc Hdt Hl k Mk qc kc Is vm Dq i' Mi' v q'' Is'' fl'' R Mv X fl'' j0 C0
                    I''[sb_of_list Id Is] T0 HMk Hh Hq HMi' Hhi HlR Hv HMv Hhv HC0 HC' HT0) as HE.
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HE HσU) as HE'.
      symmetry; exact HE'. }
    pose proof (record_typed_former _ _ _ _ _ HRt HlR HΓ) as Hrt.
    pose proof (wf_exp_eq_record_apps _ _ _ _ _ Xs Ys Hrt HlR HXl' HYl' HXY) as HTT.
    assert (HXt : forall j0 Y T, List.nth_error Xs j0 = Some Y -> List.nth_error (tele_insts (record_params R) Id Xs) j0 = Some T ->
               Γ ⊢ Y : T).
    { intros j0 Y T HY HT.
      destruct (nth_error_lt_some' Ys j0 ltac:(assert (j0 < List.length Xs) by (apply List.nth_error_Some; congruence); lia))
        as [Z HZ].
      pose proof (HXY _ _ _ _ HY HZ HT) as H; gen_presups; assumption. }
    destruct (wf_record_inversion Hrt) as [R0 Hl0 _ _ _ _ _ HS _ _].
    rewrite HlR in Hl0; injection Hl0 as <-.
    assert (HPw : ⊢ gc_deps ⍮ gc_stack ⍮ record_params R) by (eapply presup_is_univ_ctx; eassumption).
    assert (HSs : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ (record_sort R)[sb_of_list Id Xs]).
    { eapply (proj1 (proj2 (proj2 (proj2 sub_preserves_wf)))); [ exact HS |].
      rewrite <- (List.app_nil_r (record_params R)).
      eapply wf_sub_of_list; [ exact (typed_params_ass _ _ _ HRt) | rewrite List.app_nil_r; exact HPw
                             | exact (wf_sub_to_nil _ _ _ HΓ) | exact HXl' | exact HXt ]. }
    exact (wf_exp_eq_is_univ_large HSs HTT).
  Qed.

  (** The types of the two members at the parameters. *)
  Lemma vh_ty_eq : exists i, Γ ⊢ im_ty_at qc i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) Ns ≈ im_ty_at p v Mv Us Ns : Typeω@i.
  Proof.
    pose proof (vs_nn D Hdt k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof vh_vU_length as HvUl.
    destruct (im_head Mi') as [pm | qh kh Ihc vmc | q'' Is'' fl''] eqn:Hhi; [| | exact (vh_rview_ty_eq _ _ _ Hhi) ].
    - destruct (decl_typed_view_decl _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & vm' & HMv' & Hhv).
      rewrite HMv in HMv'; injection HMv' as <-.
      assert (Hlt : i' < ind_ndecl Dq) by (apply (decl_typed_order _ _ _ HdtQ _ _ HMi'); unfold im_is_decl; rewrite Hhi; reflexivity).
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
    - destruct (decl_typed_view_view _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & X & vm' & HMv' & Hhv & HXl).
      rewrite HMv in HMv'; injection HMv' as <-.
      destruct (decl_typed_view _ _ _ HdtQ _ _ _ _ _ _ HMi' Hhi) as (Dh & Mkh & HqH & HMkh & Hlt & HIcl & _ & Hvk & _).
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMv Hhv) as (Dh' & Mkh' & HqH' & HMkh' & _ & _ & _ & Hvk' & _).
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
    destruct (im_head Mi') as [pm | qh kh Ihc vmc | q'' Is'' fl''] eqn:Hhi.
    3:{ (** A record view: both constructors are the tuple of the fields,
            at equal record types. *)
        destruct (decl_typed_view_rview _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & X & HMv' & Hhv & HXl).
        rewrite HMv in HMv'; injection HMv' as <-.
        assert (HNs : Ns = nil).
        { destruct Ns; [ reflexivity |].
          unfold im_nn in HNl; rewrite (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMv Hhv) in HNl; discriminate HNl. }
        rewrite HNs in HAs, HAg, HMg, HM, Hi |- *.
        assert (Hcs1 : forall G j0 Mj0 q0 Is0 fl0 c0 g0, ind_member G j0 = Some Mj0 -> im_head Mj0 = mh_record q0 Is0 fl0 ->
                  decl_typed gc_deps gc_stack G -> ind_con Mj0 c0 = Some g0 -> im_cons Mj0 = (c0, g0) :: nil).
        { intros * HM0 Hh0 Hdt0 Hc0.
          destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt0) _ _ _ _ _ HM0 Hh0) as (gs0 & Hcs0 & _).
          unfold ind_con in Hc0; rewrite Hcs0 in Hc0 |- *; cbn in Hc0.
          destruct (String.eqb c0 rview_con) eqn:E; [ injection Hc0 as -> | discriminate Hc0 ].
          apply String.eqb_eq in E; rewrite E; reflexivity. }
        pose proof (Hcs1 _ _ _ _ _ _ _ _ HMi' Hhi HdtQ Hcon') as Hcs'.
        pose proof (Hcs1 _ _ _ _ _ _ _ _ HMv Hhv Hdt Hcon) as Hcs.
        rewrite List.app_nil_r in HAs, HAg.
        assert (HvUt : forall j U T, List.nth_error (List.map (fun I => I[sb_of_list Id Us]) Is) j = Some U ->
                  List.nth_error (tele_insts (ind_uparams Dq) Id (List.map (fun I => I[sb_of_list Id Us]) Is)) j = Some T -> Γ ⊢ U : T).
        { intros j U T HU HT; eapply vh_ps_c; [ rewrite HNs, List.app_nil_r; exact HU |].
          rewrite HNs, List.app_nil_r.
          unfold im_params; rewrite (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ HdtQ) _ _ _ _ _ HMi' Hhi); exact HT. }
        pose proof (rview_con_tuple Γ qc Dq i' Mi' q'' Is'' fl'' c gs' _ As Hq HMi' Hhi Hcs' HΓ HvUl HvUt HAl HAs) as E1.
        pose proof (rview_con_tuple Γ p D v Mv q'' X fl'' c gs Us As Hl HMv Hhv Hcs HΓ HUl vh_uparams_typed ltac:(lia) HAg) as E2.
        assert (HTc : Γ ⊢ a_tuple (apps_exp (a_record q'') (im_pre Mi' (List.map (fun I => I[sb_of_list Id Us]) Is)))
                          (List.combine fl'' As) : im_ty_at qc i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) nil)
          by (gen_presups; eassumption).
        assert (HTg' : Γ ⊢ a_tuple (apps_exp (a_record q'') (im_pre Mv Us)) (List.combine fl'' As) : im_ty_at p v Mv Us nil)
          by (gen_presups; eassumption).
        pose proof HTc as HTc0.
        assert (ETc : im_ty_at qc i' Mi' (List.map (fun I => I[sb_of_list Id Us]) Is) nil
                      = apps_exp (a_record q'') (im_pre Mi' (List.map (fun I => I[sb_of_list Id Us]) Is)))
          by (unfold im_ty_at; rewrite Hhi, List.app_nil_r; reflexivity).
        rewrite ETc in HTc0.
        destruct (wf_tuple_inversion HTc0) as [qt Rt Nt lt HTt HTe Hrt HlRt HNtl HNtt Hnm Hfs _].
        set (n := Nat.max i lt).
        pose proof (lift_exp_eq_ge _ _ _ _ _ i n ltac:(unfold n; lia) Hi) as Hin.
        pose proof (lift_exp_eq_ge _ _ _ _ _ lt n ltac:(unfold n; lia) HTe) as HTen.
        rewrite ETc in Hin.
        assert (ETg : im_ty_at p v Mv Us nil = apps_exp (a_record q'') (im_pre Mv Us))
          by (unfold im_ty_at; rewrite Hhv, List.app_nil_r; reflexivity).
        rewrite ETg in Hin, HTg'.
        assert (Htg : Γ ⊢ a_tuple (apps_exp (a_record q'') (im_pre Mv Us)) (List.combine fl'' As)
                        : apps_exp (a_record q'') (im_pre Mi' (List.map (fun I => I[sb_of_list Id Us]) Is))).
        { eapply wf_conv'; [ exact HTg' |]; symmetry; exact Hin. }
        pose proof (wf_exp_eq_tuple_cong _ _ _ _ _ _ _ _ _ _ _ HTc0 Hin HTen HlRt HNtl HNtt Hnm eq_refl
                      ltac:(intros k0 f0 M0 M0' U0 H0 H0' HU0; rewrite H0 in H0'; injection H0' as <-;
                            apply wf_exp_eq_refl; eapply Hfs; eassumption)
                      Htg) as E3.
        rewrite ETc in E1, Hi.
        assert (HT0 : Γ ⊢ im_ty_at p v Mv Us nil : Typeω@i) by (gen_presups; eassumption).
        pose proof (wf_exp_eq_conv _ _ _ _ _ _ _ _ (wf_exp_eq_trans _ _ _ _ _ _ _ E1 E3) HT0 Hi) as E13.
        etransitivity; [ exact HMg |].
        etransitivity; [ exact E13 | symmetry; exact E2 ]. }
    - destruct (decl_typed_view_decl _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & vm' & HMv' & Hhv).
      rewrite HMv in HMv'; injection HMv' as <-.
      pose proof (view_head_con_eq p D v Mv qc i' Is vm' Dq Mi' Hdt Hl Hc HMv Hhv Hq HMi' Γ Us Ns As c gs gs'
                    HΓ HUl HNl HPs Hcon' Hcon ltac:(lia) HAg) as E1.
      etransitivity; [ exact HMg | symmetry; exact E1 ].
    - destruct (decl_typed_view_view _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hhi Hv) as (Mv' & X & vm' & HMv' & Hhv & HXl).
      rewrite HMv in HMv'; injection HMv' as <-.
      destruct (decl_typed_view _ _ _ HdtQ _ _ _ _ _ _ HMi' Hhi) as (Dh & Mkh & HqH & HMkh & Hlt & HIcl & _ & Hvk & Hfst & Hcr).
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMv Hhv) as (Dh' & Mkh' & HqH' & HMkh' & _ & _ & _ & Hvk' & _).
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
        assert (Hdecl : im_is_decl Mkh = true) by (apply (decl_typed_order _ _ _ HdtH _ _ HMkh); exact Hlt).
        unfold im_is_decl in Hdecl; destruct (im_head Mkh); [ reflexivity | discriminate | discriminate ]. }
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
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  (** The group's clause. *)
  Variables (ups : list domain) (bu : domain) (u : universe_index)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups)
    (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).
  (** The view and its container. *)
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Let HgQ := Hcv _ _ _ _ _ _ _ HMk Hh Hq.
  Let HcQ := valid_group_closed _ _ HgQ.
  Let HassQ := valid_group_ass _ _ HgQ.
  Let HPq := valid_groups_containers VP HVP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq.
  Let HcvQ := containers_valid_of_groups VP HVP qc Dq HPq.
  (** The container's clause, at the view's instance. *)
  Variables (cups : list domain).
  Hypothesis (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups).
  Variables (u' : universe_index)
    (NP' : nat -> nat -> list domain -> glu_typ_pred) (NEl' : nat -> nat -> list domain -> glu_exp_pred)
    (AP' : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP' : nat -> list domain -> exp -> glu_typ_pred) (DEl' : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hf' : ind_fams_glu Dq cups u' NP' NEl' AP' AEl' DP' DEl').
  (** The members the view nests through agree with their containers. *)
  Hypothesis (Hend : forall i' Mi' v Mv c gs1' A' gs2' gs1 t gs2, ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v ->
                 ind_member D v = Some Mv -> ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
                 cargs_corr vm gs1' gs1 -> glu_end_at p D ups NEl AEl DP DEl (ptyp_mem t)).

  Let view_args (Us : list exp) : list exp := List.map (fun I => I[sb_of_list Id Us]) Is.

  Lemma length_view_args : forall Us, List.length (view_args Us) = ind_nu Dq.
  Proof. intros; unfold view_args; rewrite List.length_map; exact (view_is_length VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq). Qed.

  Lemma length_cups : List.length cups = ind_nu Dq.
  Proof. rewrite (eval_exps_length _ _ _ Ecups); exact (view_is_length VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq). Qed.

  (** *** At a Neutral of a Member of the Container *)

  Section AtNeut.
    Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
    Hypotheses (HMi' : ind_member Dq i' = Some Mi') (HVM : view_member p D qc Dq vm i' Mi' v Mv).
    Let Hv := view_member_v _ _ _ _ _ _ _ _ _ HVM.
    Let HMv := view_member_mem _ _ _ _ _ _ _ _ _ HVM.
    Variables (Γ : ctx) (Us Ns : list exp).
    Hypotheses (HΓ : ⊢ Γ) (HUl : List.length Us = ind_nu D) (HNl : List.length Ns = im_nn Mv)
      (HPs : forall j X T, List.nth_error (Us ++ Ns) j = Some X ->
               List.nth_error (tele_insts (im_params D Mv) Id (Us ++ Ns)) j = Some T -> Γ ⊢ X : T).

    Lemma at_neut : forall hd k' as' m M, im_is_rview Mi' = false -> im_ref qc i' Mi' = (hd, k') -> per_bot m m ->
        (forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M' ->
           Δ ⊢ M[φ]ʷ ≈ M' : (im_ty_at qc i' Mi' (view_args Us) Ns)[φ]ʷ) ->
        ind_glu_elem p D ups NEl AEl DP DEl v Γ Us Ns M (⇑ (d_ind hd k' as') m).
    Proof.
      intros * Hrv Href Hm HM.
      destruct (vh_ty_eq p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv Γ Us Ns HΓ HUl HNl HPs) as [i Hi].
      eapply ind_glu_elem_neut; [ exact HMv | rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ HVM); exact Hrv
                                | rewrite (view_member_ref _ _ _ _ _ _ _ _ _ HVM Hrv); exact Href | exact Hm |].
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
    Let Hv := view_member_v _ _ _ _ _ _ _ _ _ HVM.
    Let HMv := view_member_mem _ _ _ _ _ _ _ _ _ HVM.
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
      unfold im_params; apply glu_args_app; [ exact (decl_closed_ass _ Hc) | exact HUl | exact Hu |].
      split; [ exact HUs | exact at_nparams_glu ].
    Qed.

    Lemma at_params_c : glu_args Γ (im_params Dq Mi') Id nil (view_args Us ++ Ns) (cups ++ ns).
    Proof.
      unfold im_params; apply glu_args_app; [ exact (decl_closed_ass _ HcQ) | exact (length_view_args Us) | exact length_cups |].
      split; [ exact (view_uparams_glu VP p D HVP HPD HG k Mk qc kc Is vm Dq HMk Hh Hq Γ Us ups cups HΓ HUs Ecups)
             | exact at_nparams_c ].
    Qed.

    Lemma at_lengths : List.length Us = ind_nu D /\ List.length Ns = im_nn Mv /\ List.length ns = im_nn Mv.
    Proof.
      destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
      destruct Hnp' as [L1 L2 _]; pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
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
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
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
        destruct (ind_fams_glu_arg_eval _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ HMi' Hns' Hcon' HnA' Hpc) as [b' Eb'].
        pose proof (ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ b' HMi' Hns' Hcon' HnA' Hpc Eb') as Hgb'.
        destruct (ind_fams_glu_arg_eval _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs _ A0 _ HMv at_ns_g Hcon HnA Hpg) as [b Eb].
        pose proof (ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs _ A0 _ b HMv at_ns_g Hcon HnA Hpg Eb) as Hgb.
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
        { eapply (ind_glu_comps_args _ _ _ _ _ _ _ _ _ _ _ at_comps v Mv c gs gs1 A0 gs2 Ns ns As vp A HMv Hcon Heq at_nparams at_ns_g Hlvp HA);
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
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
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
      destruct (ind_fams_glu_arg_eval _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ HMi' Hns' Hcon' HnA' Hpc) as [b' Eb'].
      pose proof (ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' _ A0' _ b' HMi' Hns' Hcon' HnA' Hpc Eb') as Hgb'.
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
      set (n := Nat.max (large_level u') (Nat.max i2 i3)).
      assert (Hun : universe_index_le u' (ul n)) by (apply universe_index_le_ul_max; unfold n; lia).
      destruct (glu_univ_elem_cumu_ge_universe_index Hun Hgb') as (Pn & Eln & Hgn).
      pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hun Hgb' Hgn HNc) as HNn.
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
      destruct (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ 0 HMv Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
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

    (** The instance of the context of the arguments before a position,
        typed. *)
    Lemma at_theta0 : forall gs1 g gs2, gs = gs1 ++ g :: gs2 ->
        Γ ⊢ˢ sb_of_list Id (Us ++ Ns ++ List.firstn (List.length gs1) As) : cargs_ctx p D Mv gs1 ++ im_params D Mv.
    Proof.
      intros gs1 g gs2 Heq.
      destruct at_lengths as (HUl & HNl & _).
      pose proof at_gs_length as Hlg.
      assert (Hl1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      set (As1 := List.firstn (List.length gs1) As).
      assert (HlA1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      assert (HassC : tele_ass (cargs_ctx p D Mv gs1 ++ im_params D Mv))
        by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_params_ass D v Mv Hc HMv) ]).
      destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ) Hl HMv (cons_lookup_in _ _ _ Hcon)
                  gs1 (g :: gs2) Heq) as (HW & _ & _).
      assert (HA1 : forall j N T, List.nth_error As1 j = Some N ->
                List.nth_error (tele_insts (cargs_ctx p D Mv gs1) (sb_of_list Id (Us ++ Ns)) As1) j = Some T -> Γ ⊢ N : T).
      { intros j N0 T0 HN0 HT0.
        assert (Hj : j < List.length As1) by (apply List.nth_error_Some; congruence).
        apply (at_args_typed j N0 T0).
        - rewrite <- (List.firstn_skipn (List.length gs1) As), List.nth_error_app1 by (fold As1; exact Hj); exact HN0.
        - rewrite (cargs_split_aux p D Mv gs gs1 g gs2 Heq), <- (List.firstn_skipn (List.length gs1) As).
          rewrite tele_insts_app by (first [ apply cargs_ctx_aux_ass | fold As1; rewrite length_cargs_ctx; exact HlA1 ]).
          rewrite List.nth_error_app1 by (rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; fold As1; lia).
          exact HT0. }
      rewrite <- (List.app_nil_r (cargs_ctx p D Mv gs1 ++ im_params D Mv)), List.app_assoc.
      eapply wf_sub_of_list; [ exact HassC | rewrite List.app_nil_r; exact HW | exact (wf_sub_to_nil _ _ _ HΓ)
                             | rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia |].
      apply (Views.list_typed_app _ _ _ (cargs_ctx p D Mv gs1) (im_params D Mv) Id (Us ++ Ns) As1 (decl_closed_params_ass D v Mv Hc HMv)
               ltac:(rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia) at_ps_typed HA1).
    Qed.

    (** The container's constructor is the group's, given its recursive
        arguments recursive in both as the group's. *)
    Lemma at_con : forall hd k' bs M, im_is_rview Mi' = false -> im_ref qc i' Mi' = (hd, k') ->
        List.length bs = (im_unu Dq Mi' + im_nn Mi')%nat ->
        List.skipn (im_unu Dq Mi') bs = ns ->
        Γ ⊢ M ≈ apps (a_con qc i' c) (view_args Us ++ Ns ++ As) : im_ty_at qc i' Mi' (view_args Us) Ns ->
        (forall gs1 t gs2 gs1' t' gs2' N A x, gs = gs1 ++ ca_rec t :: gs2 -> gs' = gs1' ++ ca_rec t' :: gs2' ->
           List.length gs1' = List.length gs1 -> List.nth_error As (List.length gs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
           List.nth_error vs (List.length gs1) = Some x ->
           glu_rec p D ups NEl AEl DP DEl v Γ Us (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N x) ->
        ind_glu_elem p D ups NEl AEl DP DEl v Γ Us Ns M (d_con hd k' c (bs ++ vs)).
    Proof.
      intros hd k' bs M Hrv Href Hbl Hns HM Hboth.
      destruct at_lengths as (HUl & HNl & Hnl).
      pose proof at_gs_length as Hlg.
      pose proof (view_member_unu _ _ _ _ _ _ _ _ _ HVM Hrv) as Hunu.
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
      eapply ind_glu_elem_con with (Mk := Mv) (gs := gs) (As := As);
        [ exact HMv | rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ HVM); exact Hrv
        | rewrite (view_member_ref _ _ _ _ _ _ _ _ _ HVM Hrv); exact Href | exact Hcon | exact HUl | exact HNl | lia | lia | lia
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

    (** At a record view of the container: an element of it is one of the
        group's record view the view takes it to, at the same fields,
        given its recursive fields recursive in both as the group's. *)
    Lemma at_record : forall q'' Is'' fl'' M m, im_head Mi' = mh_record q'' Is'' fl'' -> ns = nil ->
        ⟦projs fl'' of m ⟧ gc_deps ⍮ gc_stack ↘ vs ->
        Γ ⊢ M ≈ apps (a_con qc i' c) (view_args Us ++ Ns ++ As) : im_ty_at qc i' Mi' (view_args Us) Ns ->
        (forall gs1 t gs2 gs1' t' gs2' N A x, gs = gs1 ++ ca_rec t :: gs2 -> gs' = gs1' ++ ca_rec t' :: gs2' ->
           List.length gs1' = List.length gs1 -> List.nth_error As (List.length gs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
           List.nth_error vs (List.length gs1) = Some x ->
           glu_rec p D ups NEl AEl DP DEl v Γ Us (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N x) ->
        ind_glu_elem p D ups NEl AEl DP DEl v Γ Us Ns M m.
    Proof.
      intros q'' Is'' fl'' M m Hhi Hns0 Hps HM Hboth.
      destruct at_lengths as (HUl & HNl & Hnl).
      pose proof at_gs_length as Hlg.
      destruct (view_member_rview _ _ _ _ _ _ _ _ _ HVM _ _ _ Hhi) as [X Hhv].
      destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMv Hhv) as (gs0 & Hcs0 & _).
      assert (Hcs : im_cons Mv = (c, gs) :: nil).
      { pose proof Hcon as Hc0; unfold ind_con in Hc0; rewrite Hcs0 in Hc0 |- *; cbn in Hc0.
        destruct (String.eqb c rview_con) eqn:E; [ injection Hc0 as -> | discriminate Hc0 ].
        apply String.eqb_eq in E; rewrite E; reflexivity. }
      eapply ind_glu_elem_record with (Mk := Mv) (gs := gs) (As := As);
        [ exact HMv | exact Hhv | exact Hcs | exact HUl | exact HNl | lia | exact Hps
        | exact (vh_con_eq p D Hdt Hl Hc k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv Γ Us Ns HΓ HUl HNl at_ps_typed
                   As c gs' gs M Hcon' Hcon Hcorr HAl HAty' HM)
        | rewrite <- Hns0; exact at_args_g | exact at_args_typed | |].
      - intros * Heq HN HA Hx; rewrite <- Hns0; exact (at_nonrec _ _ _ _ _ _ Heq HN HA Hx).
      - intros gs1 t gs2 N A x Heq HN HA Hx.
        assert (Hlgs1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some' gs' (List.length gs1) ltac:(lia)) as [g' Hg'].
        destruct (List.nth_error_split _ _ Hg') as (gs1' & gs2' & Heq' & Hl1).
        replace (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
          with (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) by (rewrite Hns0; reflexivity).
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
    Let Hv := view_member_v _ _ _ _ _ _ _ _ _ HVM.
    Let HMv := view_member_mem _ _ _ _ _ _ _ _ _ HVM.
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
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
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
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ HVM) as Hv; pose proof (view_member_mem _ _ _ _ _ _ _ _ _ HVM) as HMv.
    pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
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
    destruct (ind_fams_glu_dom_eval _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs gs1 t gs2 _ kk B ys HMv Hnsd Hcon Heq Hpg HB Hy) as [b0 Eb0].
    pose proof (ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf v Mv ns c gs gs1 t gs2 _ kk B ys b0 HMv Hnsd Hcon Heq Hpg HB Hy Eb0) as Hgb0.
    destruct (ind_fams_glu_dom_eval _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' gs1' t' gs2' _ kk B' ys HMi' Hns' Hcon' Heq' Hpc HB' Hy') as [b0' Eb0'].
    pose proof (ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf' i' Mi' ns c gs' gs1' t' gs2' _ kk B' ys b0' HMi' Hns' Hcon' Heq' Hpc HB' Hy' Eb0')
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
      destruct (decl_typed_view_doms _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) Hdt Hl k Mk qc kc Is vm Dq i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 kk
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
      destruct (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ (S kk) HMv Hcon Heq ltac:(lia)) as [SbC' HSbC'].
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
               EA HΔ (glu_args_wk _ _ _ _ _ _ _ (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) Hφ HUs) HΘ' HSbC' Hσ').
  Qed.

  (** An element of the container's member [i'] at the view's instance of
      glued uniform parameters is an element of the group's member the
      view takes [i'] to, at parameters typed there. *)
  Definition elem_to_group (i' : nat) (Γ : ctx) (Us0 Ns : list exp) (M : exp) (x : domain) : Prop :=
    forall Mi' v Mv Us, ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv -> Us0 = view_args Us -> ⊢ Γ ->
      glu_args Γ (ind_uparams D) Id nil Us ups -> List.length Ns = im_nn Mv ->
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
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ HVM) as Hv; pose proof (view_member_mem _ _ _ _ _ _ _ _ _ HVM) as HMv.
    pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM) as Hnn.
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
    { unfold im_params; apply glu_args_app; [ exact (decl_closed_ass _ Hc) | exact HUl | exact Hu |].
      split; [ exact HUs | exact HQn ]. }
    pose proof (comps_of_uparams p D HG Hc Hdt Hsu Hass ups bu u NP NEl AP AEl DP DEl Hu Hbu Hule Hf Γ Us HΓ HUs) as Hcomps.
    pose proof (Con.con_canon VP p D HVP HPD ups Hu Hgu) as Hcp.
    assert (H01 : tele_rel (canon_nparams_rel D ups (ptyp_mem t)) (List.rev (im_nparams Mj)) bs bs)
      by exact (canon_nparams_rel_trans p D ups Hass Hcp _ _ _ _ _ HMj Hrel (canon_nparams_rel_sym p D ups Hass Hcp _ _ _ _ HMj Hrel)).
    pose proof (nparams_of_glu_args p D Hass ups u NP NEl AP AEl DP DEl Hu Hf _ _ Γ Us Qn bs HMj Hcomps HQn H01) as HnQ.
    assert (HQl : List.length Qn = im_nn Mj) by (unfold Qn; rewrite List.length_map; exact HPl).
    assert (EQ : forall Q, ind_mty p D (ptyp_mem t) Us Qn = im_ty_at p (ptyp_mem t) Mj Us Q -> Q = Qn).
    { intros Q HQ; unfold ind_mty in HQ; rewrite HMj in HQ; unfold im_ty_at in HQ.
      destruct (im_head Mj);
        first [ apply apps_ind_inj, List.app_inv_head in HQ | apply apps_record_inj, List.app_inv_head in HQ ]; congruence. }
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
      pose proof (view_member_v _ _ _ _ _ _ _ _ _ HVM0) as Hv0; rewrite Hmem in Hv0; injection Hv0 as <-.
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ HVM0) as HMv0; rewrite HMj in HMv0; injection HMv0 as <-.
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVM0) as Hnnj.
      destruct (length_rec_ps Dq (valid_group_valid _ _ HgQ) i' Mi' HMi' c gs' gs1' t' gs2' Hcon' Heq') as (Mj'' & HMj'' & HPl').
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
        unfold im_params in HT; rewrite tele_insts_app in HT by (first [ exact (decl_closed_ass _ Hc) | exact HUl ]).
        destruct (Nat.lt_ge_cases j0 (List.length Us)) as [Hj | Hj].
        - rewrite List.nth_error_app1 in HX, HY by exact Hj.
          rewrite HX in HY; injection HY as <-.
          rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in *; lia).
          apply wf_exp_eq_refl; eapply glu_args_typed; [ exact (decl_closed_ass _ Hc) | exact HUs | eassumption | eassumption ].
        - rewrite List.nth_error_app2 in HX, HY by exact Hj.
          rewrite List.nth_error_app2 in HT by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in *; lia).
          rewrite length_tele_insts in HT by exact (decl_closed_ass _ Hc).
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
      pose proof (glu_args_resp_eq Δ (ind_uparams D) nil _ Us' ups (decl_closed_ass _ Hc) (decl_typed_uparams_field _ _ _ Hdt) HΔ HU'
                    (glu_args_wk _ _ _ _ _ _ _ (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) Hφ HUs)) as HUs'.
      pose proof (exps_eq_at_typed_r p D (ptyp_mem t) Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Qn)) (Us' ++ Q') Hl HMj HΔ
                    ltac:(rewrite List.length_map, List.length_app; unfold im_np, ind_nu in *; lia) HQ') as HPs'.
      assert (HQ'l : List.length Q' = im_nn Mj)
        by (destruct HQ' as [HlQ' _]; rewrite List.length_map, !List.length_app in HlQ'; unfold ind_nu in *; lia).
      exact (IH2 bsc Qc Ebsc HA' Δ φ (view_args Us') Q' Hφ (length_view_args Us') E3' Mj' (ptyp_mem t) Mj Us' HMj' HVM0 eq_refl HΔ HUs'
               HQ'l HPs').
  Qed.

  (** The recursive arguments recursive in both of a constructor of the
      container's member [i'], each a recursive argument of the
      container's shape that is the group's ([rec_to_group]), are
      recursive arguments of the group's shapes. *)
  Lemma con_recs_to_group : forall i' Mi' v Mv c gs' gs Γ Us Ns ns As vs,
      ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs -> ⊢ Γ ->
      glu_args Γ (ind_uparams D) Id nil Us ups ->
      tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ns ns ->
      glu_nparams i' Mi' NEl' Γ (view_args Us) Ns ns ->
      List.length As = List.length gs' -> List.length vs = List.length gs' ->
      (forall j N A, List.nth_error As j = Some N ->
         List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) j = Some A -> Γ ⊢ N : A) ->
      tele_rel (canon_args_rel Dq cups i' ns c) (cargs_nonrec gs') (nonrec_arg_vals gs' vs) (nonrec_arg_vals gs' vs) ->
      (forall gs1 A0 gs2 N A x, gs' = gs1 ++ ca_arg A0 :: gs2 -> List.nth_error As (List.length gs1) = Some N ->
         List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) (List.length gs1) = Some A ->
         List.nth_error vs (List.length gs1) = Some x ->
         Γ ⊢ N : A ® x ∈ AEl' i' ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))) ->
      List.length Ns = im_nn Mv ->
      (forall gs1 t gs2 N A x, gs' = gs1 ++ ca_rec t :: gs2 -> List.nth_error As (List.length gs1) = Some N ->
         List.nth_error (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) (List.length gs1) = Some A ->
         List.nth_error vs (List.length gs1) = Some x ->
         rec_to_group i' Γ (view_args Us) (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N x) ->
      forall gs1 t gs2 gs1' t' gs2' N A x, gs = gs1 ++ ca_rec t :: gs2 -> gs' = gs1' ++ ca_rec t' :: gs2' ->
        List.length gs1' = List.length gs1 -> List.nth_error As (List.length gs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
        List.nth_error vs (List.length gs1) = Some x ->
        glu_rec p D ups NEl AEl DP DEl v Γ Us (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N x.
  Proof.
      intros i' Mi' v Mv c gs' gs Γ Us Ns ns As vs HMi' HVM Hcon' Hcon Hcorr HΓ HUs Hns' Hnp' HAl Hvl HAty' Har' Harg' HNl IHrec.
      destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
      pose proof (cargs_corr_length _ _ _ Hcorr) as Hlg.
      intros gs1 t gs2 gs1' t' gs2' N A x Heq Heq' Hl1 HN HA Hx.
      assert (Hlgs1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some (tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (view_args Us ++ Ns)) As) (List.length gs1'))
        as [A' HA']; [ rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia |].
      pose proof (IHrec gs1' t' gs2' N A' x Heq' ltac:(rewrite Hl1; exact HN) HA' ltac:(rewrite Hl1; exact Hx)) as IH.
      set (vp := List.firstn (List.length gs1) vs) in *.
      set (As1 := List.firstn (List.length gs1) As) in *.
      assert (Hlvp : List.length vp = List.length gs1) by (unfold vp; rewrite List.length_firstn; lia).
      assert (HlA1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      pose proof (nonrec_prefix_pre _ gs' vs gs1' (ca_rec t') gs2' Har' ltac:(lia) Heq') as Hpc.
      rewrite Hl1 in Hpc; fold vp in Hpc.
      (** The two types, at the start of the shapes. *)
      pose proof (cargs_rec_type_sh qc Dq Mi' gs' gs1' t' gs2' (view_args Us ++ Ns) As A' Heq' HcQ
                    ltac:(rewrite List.length_app, length_view_args, (view_member_nn _ _ _ _ _ _ _ _ _ HVM) in *; unfold im_np, ind_nu in *; lia)
                    HA') as ETc.
      rewrite firstn_app_exact, <- List.app_assoc in ETc by exact (length_view_args Us).
      rewrite Hl1 in ETc; fold As1 in ETc.
      pose proof (cargs_rec_type_sh p D Mv gs gs1 t gs2 (Us ++ Ns) As A Heq Hc
                    ltac:(rewrite List.length_app; unfold im_np, ind_nu in *; lia) HA) as ETg.
      rewrite firstn_app_exact, <- List.app_assoc in ETg by exact HUl.
      fold As1 in ETg.
      (** The instances of the context of the arguments before. *)
      pose proof (at_theta0 i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr Γ Us Ns ns HΓ HUs Hns' Hnp' As vs HAl Hvl HAty'
                    gs1 (ca_rec t) gs2 Heq) as HΘ0.
      fold As1 in HΘ0.
      destruct (glu_ind_decl_dctx _ HG _ _ _ _ _ _ _ 0 (view_member_mem _ _ _ _ _ _ _ _ _ HVM) Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
      pose proof HSbC0 as HSbC0'; cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0'.
      pose proof (at_sub0 i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr Γ Us Ns ns HΓ HUs Hns' Hnp' As vs HAl Hvl HAty' Har' Harg'
                    gs1 (ca_rec t) gs2 SbC0 Heq HSbC0') as Hσ0.
      fold vp As1 in Hσ0.
      pose proof (IH Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 ns vp 0 nil Id Us Ns As1 nil SbC0
                    HMi' HVM Hcon' Hcon Hcorr Heq' Heq Hl1 Hns' Hlvp Hpc ltac:(lia) eq_refl
                    (tele_prefix_rel_nil _) (tele_prefix_rel_nil _) eq_refl
                    ltac:(rewrite Hl1, List.app_nil_r; reflexivity) HNl HlA1 eq_refl
                    ltac:(rewrite List.app_nil_r; exact ETc) HΓ HUs
                    ltac:(rewrite List.app_nil_r; exact HΘ0) HSbC0
                    ltac:(rewrite !List.app_nil_r, <- !List.app_assoc in *; exact Hσ0)) as Hg0.
      cbn [ptyp_skip] in Hg0; rewrite !List.app_nil_r in Hg0.
      rewrite ETg; exact Hg0.
  Qed.

  (** By induction on the container's gluing. *)
  Lemma to_group_all :
    (forall i' Γ Us0 Ns M x, ind_glu_elem qc Dq cups NEl' AEl' DP' DEl' i' Γ Us0 Ns M x -> elem_to_group i' Γ Us0 Ns M x) /\
    (forall i' Γ Us0 pre t0 A' N x, glu_rec qc Dq cups NEl' AEl' DP' DEl' i' Γ Us0 pre t0 A' N x -> rec_to_group i' Γ Us0 pre t0 A' N x).
  Proof.
    apply (ind_glu_elem_mut_ind_all qc Dq cups NEl' AEl' DP' DEl' (fun i' Γ Us0 Ns M x _ => elem_to_group i' Γ Us0 Ns M x)
             (fun i' Γ Us0 pre t0 A' N x _ => rec_to_group i' Γ Us0 pre t0 A' N x)).
    - intros i' Mi' hd k' c gs' Us0 Ns bs vs As Γ M HMi' Hrv Href Hcon' HUl0 HNl0 Hbl Hvl HAl HM Hns' Har' Hnp' HAty' Harg' _ IHrec.
      intros Mi0 v Mv Us HMi0 HVM HUs0 HΓ HUs HNl HPs.
      rewrite HMi' in HMi0; injection HMi0 as <-; subst Us0.
      destruct (view_member_cons _ _ _ _ _ _ _ _ _ HVM c gs' Hcon') as (gs & Hcon & Hcorr).
      set (ns := List.skipn (im_unu Dq Mi') bs) in *.
      apply (at_con i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr Γ Us Ns ns HΓ HUs Hns' Hnp' As vs HAl Hvl HAty' Har' Harg'
               hd k' bs M Hrv Href Hbl eq_refl HM).
      exact (con_recs_to_group i' Mi' v Mv c gs' gs Γ Us Ns ns As vs HMi' HVM Hcon' Hcon Hcorr HΓ HUs Hns' Hnp' HAl Hvl HAty'
               Har' Harg' HNl IHrec).
    - intros i' Mi' hd k' m Γ Us0 Ns M as' HMi' Hrv Href Hm HM.
      intros Mi0 v Mv Us HMi0 HVM HUs0 HΓ HUs HNl HPs.
      rewrite HMi' in HMi0; injection HMi0 as <-; subst Us0.
      destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
      exact (at_neut i' Mi' v Mv HMi' HVM Γ Us Ns HΓ HUl HNl HPs hd k' as' m M Hrv Href Hm HM).
    - (** A record view: by its fields, as a constructor's arguments. *)
      intros i' Mi' qr Is'' fl'' c gs' Us0 Ns As m vs Γ M HMi' Hhi Hcs' HUl0 HNl0 HAl Hps HM Har' HAty' Harg' _ IHrec.
      intros Mi0 v Mv Us HMi0 HVM HUs0 HΓ HUs HNl HPs.
      rewrite HMi' in HMi0; injection HMi0 as <-; subst Us0.
      pose proof (ind_con_single _ _ _ Hcs') as Hcon'.
      destruct (view_member_cons _ _ _ _ _ _ _ _ _ HVM c gs' Hcon') as (gs & Hcon & Hcorr).
      pose proof (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ (valid_group_typed _ _ HgQ)) _ _ _ _ _ HMi' Hhi) as Hnp0.
      assert (Hns' : tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) nil nil)
        by (rewrite Hnp0; split; reflexivity + exact I).
      assert (Hnp' : glu_nparams i' Mi' NEl' Γ (view_args Us) Ns nil).
      { constructor; [ exact HNl0 | unfold im_nn; rewrite Hnp0; reflexivity | intros [] ? ? ? _ _ Hn; discriminate Hn ]. }
      assert (Hvl : List.length vs = List.length gs').
      { rewrite (eval_projs_length _ _ _ Hps).
        destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ (valid_group_typed _ _ HgQ)) _ _ _ _ _ HMi' Hhi) as (gs0 & Hcs0 & Hl0).
        rewrite Hcs' in Hcs0; injection Hcs0 as _ <-; lia. }
      apply (at_record i' Mi' v Mv c gs' gs HMi' HVM Hcon' Hcon Hcorr Γ Us Ns nil HΓ HUs Hns' Hnp' As vs HAl Hvl HAty' Har' Harg'
               qr Is'' fl'' M m Hhi eq_refl Hps HM).
      exact (con_recs_to_group i' Mi' v Mv c gs' gs Γ Us Ns nil As vs HMi' HVM Hcon' Hcon Hcorr HΓ HUs Hns' Hnp' HAl Hvl HAty'
               Har' Harg' HNl IHrec).
    - intros j' Mj' Ps' pre A' Us0 Γ N x i' HMj' _ _ IH2.
      exact (walk_self i' Γ Us0 pre j' Ps' A' N x Mj' HMj' IH2).
    - intros A' Γ i' pre B' x Us0 t0 N HP1' HP2' _ IH3.
      exact (walk_pi i' Γ Us0 pre B' t0 A' N x HP1' HP2' IH3).
  Qed.
End ToGroup.

(** ** The Fields of an Element of a Record, Glued

    An element glued at a record type, at a weakening and glued
    parameters of the record: its type there is the record type at them,
    and the projections of its fields are glued, along the record's
    fields at them, to its value's projections ([record_elem_fields]). *)

(** What an element [M] of type [W], of value [v], is at the parameters
    [Ns] of the record [R] glued to [cups]: [W] is the record type at
    them, and [M]'s projections are glued along the record's fields at
    them to [v]'s. *)
#[warnings="-cannot-define-projection"]
Record record_elem_fields (qr : qname) (R : record_decl) (cups : list domain) (Δ : ctx) (W M : exp) (v : domain)
    (Ns : list exp) : Prop := mk_record_elem_fields
  { (** The projections of [v] *)
    elem_field_projs : list domain
    (** The universe level of the type equation *)
  ; elem_field_lvl : nat
    (** They are [v]'s fields *)
  ; elem_field_projs_eval : record_projs R v elem_field_projs
    (** [W] is the record type at [Ns] *)
  ; elem_field_typ_eq : Δ ⊢ W ≈ apps_exp (a_record qr) Ns : Typeω@elem_field_lvl
    (** [M]'s projections are glued to them along the record's fields *)
  ; elem_field_args : glu_args Δ (record_fctx R (List.length (record_fields R))) (sb_of_list Id Ns) (env_args nil cups)
      (record_pre R (List.length (record_fields R)) M) elem_field_projs }.

(** An element glued at the record type, at a weakening and glued
    parameters [Ns]: what it is there. *)
Lemma record_elem_fields_glu : forall qr R cups (i : universe_index) P El Δ W N v,
    record_lookup gc_deps gc_stack qr = Some R ->
    DG d_record qr cups ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ N : W ® v ∈ El ->
    forall Δ' φ Ns, Δ' ⊢ᵏ φ : Δ -> glu_args Δ' (record_params R) Id nil Ns cups ->
      record_elem_fields qr R cups Δ' W[φ]ʷ N[φ]ʷ v Ns.
Proof.
  intros * HlR Hgl HN Δ' φ Ns Hφ HNs.
  invert_glu_univ_elem Hgl.
  match goal with H : record_lookup _ _ qr = Some ?R0 |- _ => assert_fails constr_eq R0 R; rewrite HlR in H; injection H as <- end.
  match goal with H0 : per_univ_elem _ _ (d_record qr cups) (d_record qr cups) |- _ => rename H0 into Hper end.
  match goal with HEl : _ <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ => apply HEl in HN end.
  match goal with H : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename H into HgF end.
  match goal with H : forall k f T vs, _ -> _ -> exists b, _ |- _ => rename H into HeF end.
  destruct HN as [HNt Hm Ns0 HNs0 ws Hws Hk].
  destruct (per_univ_elem_record_facts _ _ _ _ _ _ HlR Hper) as [_ _ _ Htop _ _ _ HE].
  pose proof (proj1 (HE _ _) Hm) as HrelM.
  pose proof (record_projs_length _ _ _ Hws) as Lw.
  assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
  pose proof (ctx_wf_gctx _ _ _ HΔ') as Hg.
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR) as Ht.
  pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) HlR) as Hc.
  pose proof (typed_params_ass _ _ _ Ht) as Hass.
  assert (HCw : ⊢ record_params R ++ Δ').
  { pose proof (record_fctx_app_wf _ _ R 0 Δ' ltac:(lia) Hc Hass (record_typed_fctx_wf _ _ _ Ht _ (le_n _)) HΔ') as H.
    change (record_fctx R 0) with (@nil centry) in H; exact H. }
  (** The parameters of the element's type, at the weakening, are the
      given ones: both are glued to [cups]. *)
  destruct (record_typ_at_facts _ _ _ _ _ _ HlR _ _ _ _ _ HNs0 Hφ) as (HWφ & Hrt & HNl0 & _ & HS0).
  pose proof HNs0 as [_ Hwk0]; destruct (Hwk0 Δ' φ Hφ) as [Htop0 _ Hfields].
  pose proof (Mctt.Core.Soundness.Records.Model.glu_args_params_glu_top _ _ _ _ Hass (closed_params _ Hc) HNs) as HtopN.
  assert (Heq : exps_eq_at Δ' (record_params R) (List.map (fun N0 => N0[φ]ʷ) Ns0) Ns).
  { eapply record_params_glu_eq; [ exact Hass | exact HCw | | exact Htop0 | exact HtopN ].
    destruct (Htop (length Δ')) as (Cs & HCs & _); exists Cs; exact HCs. }
  apply (mk_record_elem_fields _ _ _ _ _ _ _ _ ws (large_level i) Hws).
  - eapply wf_exp_eq_trans; [ exact HWφ |].
    destruct Heq as [HlE HE1].
    eapply wf_exp_eq_subtyp; [ eapply wf_exp_eq_record_apps; [ exact Hrt | exact HlR | exact HNl0 | lia | exact HE1 ]
                             | mauto 3 | exact HS0 ].
  - (** Each field's projection, glued at its type after the projections
        before it. *)
    set (n := List.length (record_fields R)).
    assert (Epre : forall k M, k <= n -> List.firstn k (record_pre R n M) = record_pre R k M)
      by (intros; unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
    constructor.
    + rewrite length_record_pre, length_record_fctx by lia; reflexivity.
    + rewrite length_record_fctx by lia; exact Lw.
    + intros k M T r A HM HT Hr HA.
      destruct (tele_insts_nth _ _ _ _ _ HT) as (A1 & HA1 & ->).
      rewrite HA in HA1; injection HA1 as <-.
      rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA
        by (rewrite Completeness.Records.Model.length_field_tele; lia).
      destruct (Completeness.Records.Model.field_tele_nth _ _ _ HA) as [f Hf].
      assert (Hkn : k < n) by (apply List.nth_error_Some; congruence).
      unfold record_pre in HM; rewrite List.firstn_all2 in HM by lia.
      rewrite List.nth_error_map, Hf in HM; cbn in HM; injection HM as <-.
      rewrite <- sb_of_list_app, Epre by lia.
      pose proof (record_projs_prefix_diag R cups v ws k HrelM Hws ltac:(lia)) as Hpre.
      destruct (HeF k f A (List.firstn k ws) Hf Hpre) as [b Eb].
      pose proof (HgF k f A (List.firstn k ws) b Hf Hpre Eb) as Hgb.
      pose proof (Hk Δ' φ Ns Hφ Heq k f A r Hf Hr) as HMg.
      econstructor; [ rewrite <- env_args_app; exact Eb | exact Hgb | | exact HMg ].
      refine (Hfields Ns Heq k f A (record_pre R k N[φ]ʷ) (List.firstn k ws) Hf
                ltac:(apply length_record_pre; lia) ltac:(rewrite List.length_firstn; lia) _ Hpre).
      intros j' g T' M' m HfJ HMJ HmJ.
      assert (Hjk : j' < k)
        by (assert (j' < List.length (record_pre R k N[φ]ʷ)) by (apply List.nth_error_Some; congruence);
            rewrite length_record_pre in * by lia; lia).
      unfold record_pre in HMJ; rewrite List.nth_error_map, List.nth_error_firstn in HMJ.
      destruct (Nat.ltb_spec j' k); [| lia ].
      rewrite HfJ in HMJ; cbn in HMJ; injection HMJ as <-.
      rewrite List.nth_error_firstn in HmJ; destruct (Nat.ltb_spec j' k); [| lia ].
      rewrite List.firstn_firstn, Nat.min_l by lia.
      replace (List.firstn j' (record_pre R k N[φ]ʷ)) with (record_pre R j' N[φ]ʷ)
        by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
      exact (Hk Δ' φ Ns Hφ Heq j' g T' m HfJ HmJ).
Qed.

(** Glued arguments of a telescope scoped below [k] are glued over any
    base agreeing below [k]. *)
Lemma glu_args_base_agree : forall Δ C k τ τ' ρ Ms vs, tele_ass C -> ctx_scoped k C ->
    (forall x, x < k -> τ x = τ' x) -> glu_args Δ C τ ρ Ms vs -> glu_args Δ C τ' ρ Ms vs.
Proof.
  intros * Hass Hs Hτ [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
  pose proof (tele_insts_sub C k τ τ' Id Ms Hass Hs ltac:(intros x Hx; rewrite sentry_sub_id; exact (Hτ x Hx))) as E.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in E.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in E.
  rewrite <- E; exact H.
Qed.

(** The fields of the η-expansion of [M] are the record's field names
    paired with [M]'s projections. *)
Lemma record_eta_fields_combine : forall R M,
    record_eta_fields R M = List.combine (List.map fst (record_fields R)) (record_pre R (List.length (record_fields R)) M).
Proof.
  intros R M; unfold record_eta_fields, record_pre; rewrite List.firstn_all.
  induction (record_fields R) as [| [f T] fs IH]; cbn; [ reflexivity | f_equal; exact IH ].
Qed.

(** ** The Fields of a Record View, Glued

    Terms glued along the record's fields at the record view's instance
    are glued along the view's constructor's telescope: position by
    position, the two types have related values ([rview_arg_link]) and
    equal instances (the record view equation,
    [decl_typed_rview_fields]). *)
Section RviewFields.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Let Hl := valid_group_lookup _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (j : nat) (Mj : imember) (qr : qname) (Is : list exp) (fl : list String.string) (R : record_decl)
    (c : String.string) (gs : list carg).
  Hypotheses (HMj : ind_member D j = Some Mj) (Hh : im_head Mj = mh_record qr Is fl) (HR : valid_rview_record qr R)
    (Hcs : im_cons Mj = (c, gs) :: nil).
  Variables (ups cups : list domain).
  Hypotheses (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
    (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups).
  Let HlR := valid_rview_record_lookup _ _ HR.

  (** Terms glued along the record's fields, over the record view's
      instance at [Us], are glued along the view's constructor's telescope
      at [Us]. *)
  Lemma rview_fields_to_cargs : forall Δ Us Ms ws, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      glu_args Δ (record_fctx R (List.length (record_fields R))) (sb_of_list Id Is ⨟ sb_of_list Id Us) (env_args nil cups) Ms ws ->
      glu_args Δ (cargs_ctx p D Mj gs) (sb_of_list Id Us) (env_args nil ups) Ms ws.
  Proof.
    intros * HΔ HUs HgF.
    pose proof (RviewEnds.rv_len p D Hg j Mj qr Is fl R c gs HMj Hh HR Hcs) as Hlg.
    assert (HlF : List.length (record_fctx R (List.length (record_fields R))) = List.length gs)
      by (rewrite length_record_fctx by lia; lia).
    destruct (glu_args_length _ _ _ _ _ _ HgF) as [LM Lw].
    apply (glu_args_transfer Δ (record_fctx R (List.length (record_fields R))) (cargs_ctx p D Mj gs) _ _ _ _ Ms ws
             (record_fctx_ass _ _) (cargs_ctx_aux_ass _ _ _ _ _) ltac:(rewrite HlF, length_cargs_ctx; reflexivity) HgF).
    - (** The types' values are related: the record view's link at the
          position. *)
      intros k A A' a HA HA' Hk Ea Hp.
      rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA
        by (rewrite Completeness.Records.Model.length_field_tele; lia).
      destruct (Completeness.Records.Model.field_tele_nth _ _ _ HA) as [f Hf].
      assert (Hkg : k < List.length gs) by (rewrite HlF in Lw; lia).
      destruct (nth_error_lt_some' gs k Hkg) as [g Hg0].
      assert (Heq : gs = List.firstn k gs ++ g :: List.skipn (S k) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg0), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn k gs) = k) by (rewrite List.length_firstn; lia).
      destruct (RviewEnds.cargs_ctx_single p D (im_nn Mj) (cargs_pat (List.firstn k gs)) g) as [G HG1].
      assert (HG : cargs_ctx p D Mj (List.firstn k gs ++ g :: nil) = ce_ass G :: cargs_ctx p D Mj (List.firstn k gs))
        by (rewrite cargs_ctx_snoc, HG1; reflexivity).
      assert (Eg : List.rev (cargs_ctx p D Mj gs) = List.rev (cargs_ctx p D Mj (List.firstn k gs)) ++ ce_ass G ::
                     List.rev (cargs_ctx_aux p D (im_nn Mj) (cargs_pat (List.firstn k gs ++ g :: nil) ++ nil) (List.skipn (S k) gs))).
      { rewrite Heq at 1.
        replace (List.firstn k gs ++ g :: List.skipn (S k) gs) with ((List.firstn k gs ++ g :: nil) ++ List.skipn (S k) gs)
          by (rewrite <- List.app_assoc; reflexivity).
        unfold cargs_ctx at 1; rewrite cargs_ctx_aux_app.
        change (cargs_ctx_aux p D (im_nn Mj) nil (List.firstn k gs ++ g :: nil)) with (cargs_ctx p D Mj (List.firstn k gs ++ g :: nil)).
        rewrite HG, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity. }
      assert (Lr : List.length (List.rev (cargs_ctx p D Mj (List.firstn k gs))) = k)
        by (rewrite List.length_rev, length_cargs_ctx; exact Lk).
      rewrite Eg, List.nth_error_app2, Lr, Nat.sub_diag in HA' by lia; cbn in HA'; injection HA' as <-.
      rewrite Eg, List.firstn_app, Lr, Nat.sub_diag, List.firstn_all2 in Hp by lia; cbn [List.firstn] in Hp.
      rewrite List.app_nil_r in Hp.
      set (zs := List.firstn k ws) in *.
      assert (Lz : List.length zs = k) by (unfold zs; rewrite List.length_firstn; lia).
      pose proof (proj2 (RviewEnds.rview_tele_link p D Hg Hcv j Mj qr Is fl R c gs HMj Hh HR Hcs ups cups Hgu Hu Ecups
                           k zs zs ltac:(lia) Lz Lz) Hp) as HpR.
      pose proof (RviewEnds.rv_cups_len p D Hg j Mj qr Is fl R HMj Hh HR ups cups Ecups) as Hlc.
      assert (Hg1 : per_gargs (List.rev (cargs_ctx p D Mj (List.firstn k gs) ++ ind_uparams D)) nil nil (ups ++ zs) (ups ++ zs)).
      { rewrite List.rev_app_distr; apply Decl.per_gargs_app_intro;
          [ rewrite List.length_rev; unfold ind_nu in *; lia | exact Hgu | exact Hp ]. }
      assert (Hg2 : per_gargs (List.rev (record_fctx R k ++ record_params R)) nil nil (cups ++ zs) (cups ++ zs)).
      { rewrite List.rev_app_distr, Completeness.Records.Model.rev_record_fctx; apply Decl.per_gargs_app_intro;
          [ rewrite List.length_rev; exact Hlc
          | exact (RviewEnds.rv_cups_rel p D Hg j Mj qr Is fl R HMj Hh HR ups cups Hgu Hu Ecups) | exact HpR ]. }
      pose proof (RviewEnds.rview_arg_link p D Hg Hcv j Mj qr Is fl R c gs HMj Hh HR Hcs ups cups Hgu Hu Ecups
                    k f A (List.firstn k gs) g (List.skipn (S k) gs) G zs Hf Heq Lk Lz HG Hg1 Hg2) as Hlk.
      destruct (RviewEnds.rtl_types _ _ _ _ Hlk) as (i & R0 & [a1 b Ea1 Eb HR0]).
      rewrite env_args_app in Ea1, Eb.
      pose proof (functional_eval_exp _ _ _ _ Ea1 Ea) as ->.
      exists b, i; split; [ exact Eb | exists R0; exact HR0 ].
    - (** The instances are equal: the record view equation at [Us]. *)
      intros k T T' HT HT'.
      pose proof (ctx_wf_gctx _ _ _ HΔ) as Hgc.
      pose proof (decl_typed_rview_fields _ _ _ _ Hgc Hdt Hl _ _ _ _ _ _ _ _ HMj Hh HlR Hcs) as HE.
      destruct (decl_typed_uparams _ _ _ Hdt) as [HUw HUa].
      assert (Hσ : Δ ⊢ˢ sb_of_list Id Us : ind_uparams D).
      { rewrite <- (List.app_nil_r (ind_uparams D)); eapply wf_sub_of_list;
          [ exact HUa | rewrite List.app_nil_r; exact HUw | exact (wf_sub_to_nil _ _ _ HΔ)
          | destruct (glu_args_length _ _ _ _ _ _ HUs) as [L _]; exact L | exact (glu_args_typed _ _ _ _ _ _ HUa HUs) ]. }
      pose proof (sub_preserves_ext _ _ _ _ _ _ _ HE Hσ) as HE'.
      assert (Ei : forall X σ, tele_insts (tele_sub X σ) Id Ms = tele_insts X σ Ms)
        by (intros; rewrite tele_insts_tele_sub; apply tele_insts_sb_eq, sb_compose_id_right).
      assert (HassF : tele_ass (tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id Is)))
        by (apply tele_ass_sub, record_fctx_ass).
      eapply (tele_insts_ext_eq Δ _ _ Ms HE');
        [ apply tele_ass_sub; exact HassF | apply tele_ass_sub, cargs_ctx_aux_ass | rewrite !length_tele_sub; exact LM
        | | rewrite !Ei, tele_insts_tele_sub; exact HT | rewrite Ei; exact HT' ].
      intros k0 N T0 HN HT0; rewrite !Ei, tele_insts_tele_sub in HT0.
      exact (glu_args_typed _ _ _ _ _ _ (record_fctx_ass _ _) HgF _ _ _ HN HT0).
  Qed.

  (** Conversely, terms glued along the view's constructor's telescope at
      [Us] are glued along the record's fields over the record view's
      instance at [Us]. *)
  Lemma rview_cargs_to_fields : forall Δ Us Ms ws, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      glu_args Δ (cargs_ctx p D Mj gs) (sb_of_list Id Us) (env_args nil ups) Ms ws ->
      glu_args Δ (record_fctx R (List.length (record_fields R))) (sb_of_list Id Is ⨟ sb_of_list Id Us) (env_args nil cups) Ms ws.
  Proof.
    intros * HΔ HUs HgA.
    pose proof (RviewEnds.rv_len p D Hg j Mj qr Is fl R c gs HMj Hh HR Hcs) as Hlg.
    assert (HlF : List.length (record_fctx R (List.length (record_fields R))) = List.length gs)
      by (rewrite length_record_fctx by lia; lia).
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LM Lw]; rewrite length_cargs_ctx in LM, Lw.
    apply (glu_args_transfer Δ (cargs_ctx p D Mj gs) (record_fctx R (List.length (record_fields R))) _ _ _ _ Ms ws
             (cargs_ctx_aux_ass _ _ _ _ _) (record_fctx_ass _ _) ltac:(rewrite HlF, length_cargs_ctx; reflexivity) HgA).
    - (** The types' values are related: the record view's link at the
          position, read the other way. *)
      intros k G0 A a HA' HA Hk Ea Hp.
      rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA
        by (rewrite Completeness.Records.Model.length_field_tele; lia).
      destruct (Completeness.Records.Model.field_tele_nth _ _ _ HA) as [f Hf].
      assert (Hkg : k < List.length gs) by lia.
      destruct (nth_error_lt_some' gs k Hkg) as [g Hg0].
      assert (Heq : gs = List.firstn k gs ++ g :: List.skipn (S k) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg0), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn k gs) = k) by (rewrite List.length_firstn; lia).
      destruct (RviewEnds.cargs_ctx_single p D (im_nn Mj) (cargs_pat (List.firstn k gs)) g) as [G HG1].
      assert (HG : cargs_ctx p D Mj (List.firstn k gs ++ g :: nil) = ce_ass G :: cargs_ctx p D Mj (List.firstn k gs))
        by (rewrite cargs_ctx_snoc, HG1; reflexivity).
      assert (Eg : List.rev (cargs_ctx p D Mj gs) = List.rev (cargs_ctx p D Mj (List.firstn k gs)) ++ ce_ass G ::
                     List.rev (cargs_ctx_aux p D (im_nn Mj) (cargs_pat (List.firstn k gs ++ g :: nil) ++ nil) (List.skipn (S k) gs))).
      { rewrite Heq at 1.
        replace (List.firstn k gs ++ g :: List.skipn (S k) gs) with ((List.firstn k gs ++ g :: nil) ++ List.skipn (S k) gs)
          by (rewrite <- List.app_assoc; reflexivity).
        unfold cargs_ctx at 1; rewrite cargs_ctx_aux_app.
        change (cargs_ctx_aux p D (im_nn Mj) nil (List.firstn k gs ++ g :: nil)) with (cargs_ctx p D Mj (List.firstn k gs ++ g :: nil)).
        rewrite HG, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity. }
      assert (Lr : List.length (List.rev (cargs_ctx p D Mj (List.firstn k gs))) = k)
        by (rewrite List.length_rev, length_cargs_ctx; exact Lk).
      rewrite Eg, List.nth_error_app2, Lr, Nat.sub_diag in HA' by lia; cbn in HA'; injection HA' as <-.
      rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_firstn, Nat.min_l in Hp by lia.
      set (zs := List.firstn k ws) in *.
      assert (Lz : List.length zs = k) by (unfold zs; rewrite List.length_firstn; lia).
      pose proof (proj1 (RviewEnds.rview_tele_link p D Hg Hcv j Mj qr Is fl R c gs HMj Hh HR Hcs ups cups Hgu Hu Ecups
                           k zs zs ltac:(lia) Lz Lz) Hp) as HpC.
      pose proof (RviewEnds.rv_cups_len p D Hg j Mj qr Is fl R HMj Hh HR ups cups Ecups) as Hlc.
      assert (Hg1 : per_gargs (List.rev (cargs_ctx p D Mj (List.firstn k gs) ++ ind_uparams D)) nil nil (ups ++ zs) (ups ++ zs)).
      { rewrite List.rev_app_distr; apply Decl.per_gargs_app_intro;
          [ rewrite List.length_rev; unfold ind_nu in *; lia | exact Hgu | exact HpC ]. }
      assert (Hg2 : per_gargs (List.rev (record_fctx R k ++ record_params R)) nil nil (cups ++ zs) (cups ++ zs)).
      { rewrite List.rev_app_distr, Completeness.Records.Model.rev_record_fctx; apply Decl.per_gargs_app_intro;
          [ rewrite List.length_rev; exact Hlc
          | exact (RviewEnds.rv_cups_rel p D Hg j Mj qr Is fl R HMj Hh HR ups cups Hgu Hu Ecups) | exact Hp ]. }
      pose proof (RviewEnds.rview_arg_link p D Hg Hcv j Mj qr Is fl R c gs HMj Hh HR Hcs ups cups Hgu Hu Ecups
                    k f A (List.firstn k gs) g (List.skipn (S k) gs) G zs Hf Heq Lk Lz HG Hg1 Hg2) as Hlk.
      destruct (RviewEnds.rtl_types _ _ _ _ Hlk) as (i & R0 & [a1 b Ea1 Eb HR0]).
      rewrite env_args_app in Ea1, Eb.
      pose proof (functional_eval_exp _ _ _ _ Eb Ea) as ->.
      exists a1, i; split; [ exact Ea1 | apply per_univ_sym'; exists R0; exact HR0 ].
    - (** The instances are equal: the record view equation at [Us]. *)
      intros k T T' HT HT'.
      pose proof (ctx_wf_gctx _ _ _ HΔ) as Hgc.
      pose proof (decl_typed_rview_fields _ _ _ _ Hgc Hdt Hl _ _ _ _ _ _ _ _ HMj Hh HlR Hcs) as HE.
      destruct (decl_typed_uparams _ _ _ Hdt) as [HUw HUa].
      assert (Hσ : Δ ⊢ˢ sb_of_list Id Us : ind_uparams D).
      { rewrite <- (List.app_nil_r (ind_uparams D)); eapply wf_sub_of_list;
          [ exact HUa | rewrite List.app_nil_r; exact HUw | exact (wf_sub_to_nil _ _ _ HΔ)
          | destruct (glu_args_length _ _ _ _ _ _ HUs) as [L _]; exact L | exact (glu_args_typed _ _ _ _ _ _ HUa HUs) ]. }
      assert (HassF : tele_ass (tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id Is)))
        by (apply tele_ass_sub, record_fctx_ass).
      pose proof (sub_preserves_ext _ _ _ _ _ _ _ (Views.ext_eq_sym_ass _ _ _ _ _ HassF HE) Hσ) as HE'.
      assert (Ei : forall X σ, tele_insts (tele_sub X σ) Id Ms = tele_insts X σ Ms)
        by (intros; rewrite tele_insts_tele_sub; apply tele_insts_sb_eq, sb_compose_id_right).
      eapply (tele_insts_ext_eq Δ _ _ Ms HE');
        [ apply tele_ass_sub, cargs_ctx_aux_ass | apply tele_ass_sub; exact HassF | rewrite !length_tele_sub, length_cargs_ctx; exact LM
        | | rewrite Ei; exact HT | rewrite !Ei, tele_insts_tele_sub; exact HT' ].
      intros k0 N T0 HN HT0; rewrite Ei in HT0.
      exact (glu_args_typed _ _ _ _ _ _ (cargs_ctx_aux_ass _ _ _ _ _) HgA _ _ _ HN HT0).
  Qed.
End RviewFields.

(** ** A View Agrees with its Container

    An element of the view's type, glued at the type's container member at
    uniform parameters related to the view's instance and non-uniform ones
    related to the group's, is an element of the container's member at the
    instance's values and the families of its clause there, hence one of
    the group's member. *)
Section Root.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := valid_group_lookup _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (ups : list domain) (bu : domain) (u : universe_index)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups)
    (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : universe_index_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).

  (** Non-uniform parameters related at the group's member are related at
      the container's member it views. *)
  Lemma nparams_rel_to_container : forall k Mk qc kc Is vm Dq cups i' Mi' v Mv, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
      ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups ->
      ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      forall a b, tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mv)) a b ->
        tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) a b.
  Proof.
    intros * HMk Hh Hq Ecups HMi' Hv HMv a b Hab.
    pose proof (vs_nn D Hdt k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    assert (Hab' : tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mi')) a b)
      by (destruct Hab as [Hla Hab]; split; [ rewrite Hla, !List.length_rev, !length_im_nparams; lia | exact Hab ]).
    apply (tele_rel_map _ (canon_nparams_rel D ups v)); [| exact Hab' ].
    intros j pa pb x y Hj _ Hp2 Hxy.
    rewrite List.length_rev, length_im_nparams in Hj.
    apply (view_nparams_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
             j pa pb ltac:(lia) Hp2); exact Hxy.
  Qed.

  Lemma glu_view_end_root : forall k,
      (forall Mk qc kc Is vm Dq i' Mi' v Mv c gs1' A' gs2' gs1 t gs2, ind_member D k = Some Mk ->
         im_head Mk = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
         List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
         ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
         cargs_corr vm gs1' gs1 -> glu_end_at p D ups NEl AEl DP DEl (ptyp_mem t)) ->
      glu_view_end_at p D ups NEl AEl DP DEl k.
  Proof.
    intros k Hend Mj qc kc Is vm Dq cups cs bs bs1 Δ Us Q W N x i P El HMj Hh Hq Ecups Hgc Hrel Hgl HN _ HQp Δ' φ Us' Q' Hφ HUl' HE.
    pose proof (Hcv _ _ _ _ _ _ _ HMj Hh Hq) as HgQ.
    pose proof (valid_group_closed _ _ HgQ) as HcQ; pose proof (valid_group_valid _ _ HgQ) as HDQ; pose proof (valid_group_sort _ _ HgQ) as HsuQ.
    pose proof (valid_group_lookup _ _ HgQ) as HlQ; pose proof (valid_group_ass _ _ HgQ) as HassQ.
    pose proof (valid_groups_containers VP HVP p D k Mj qc kc Is vm Dq HPD HMj Hh Hq) as HPq.
    pose proof (containers_valid_of_groups VP HVP qc Dq HPq) as HcvQ.
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dq' & Mkc & Hq' & HMkc & Hlt & HIl & _ & Hvk & _).
    rewrite Hq in Hq'; injection Hq' as <-.
    assert (Hdecl : im_is_decl Mkc = true) by (apply (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMkc); exact Hlt).
    destruct (im_head Mkc) as [pmc | ? ? ? ? | ? ? ?] eqn:Hhc;
      [| unfold im_is_decl in Hdecl; rewrite Hhc in Hdecl; discriminate | unfold im_is_decl in Hdecl; rewrite Hhc in Hdecl; discriminate ].
    (** The view's member of the container, and its image. *)
    destruct (view_agree_members p D k Mj qc kc Is vm Dq Hass HMj Hh Hq kc Mkc HMkc) as (v0 & Mv0 & HVMk).
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ HVMk) as Hv0; rewrite Hvk in Hv0; injection Hv0 as <-.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ HVMk) as HMv0; rewrite HMj in HMv0; injection HMv0 as <-.
    pose proof (view_member_nn _ _ _ _ _ _ _ _ _ HVMk) as Hnn.
    assert (Hlc : List.length cups = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ Ecups); exact HIl).
    pose proof (view_cups_rel p D Hg Hcv k Mj qc kc Is vm Dq HMj Hh Hq ups cups Hgu Hu Ecups) as Hgcups.
    (** The parameters of the element's type, split at the uniform ones. *)
    destruct (glu_args_length _ _ _ _ _ _ HQp) as [HlP Hlp].
    rewrite length_im_params in HlP, Hlp.
    set (Us0 := List.firstn (ind_nu D) (Us ++ Q)) in *; set (Q0 := List.skipn (ind_nu D) (Us ++ Q)) in *.
    assert (EP : Us ++ Q = Us0 ++ Q0) by (symmetry; apply List.firstn_skipn).
    assert (HUl0 : List.length Us0 = ind_nu D) by (unfold Us0; rewrite List.length_firstn; unfold im_np in HlP; lia).
    assert (HQl0 : List.length Q0 = im_nn Mj) by (unfold Q0; rewrite List.length_skipn; unfold im_np in HlP; lia).
    assert (Hlbs : List.length bs = im_nn Mj) by (rewrite List.length_app in Hlp; unfold im_np, ind_nu in *; lia).
    rewrite EP in HQp, HE; clearbody Us0 Q0; clear EP HlP Hlp.
    (** The container's relations of the values. *)
    pose proof (nparams_rel_to_container k Mj qc kc Is vm Dq cups kc Mkc k Mj HMj Hh Hq Ecups HMkc Hvk HMj bs bs1 Hrel) as Hrel'.
    pose proof (Con.con_canon VP qc Dq HVP HPq cups Hlc Hgcups) as HcpQ.
    assert (Hbb' : tele_rel (canon_nparams_rel Dq cups kc) (List.rev (im_nparams Mkc)) bs bs)
      by exact (canon_nparams_rel_trans qc Dq cups HassQ HcpQ _ _ _ _ _ HMkc Hrel'
                  (canon_nparams_rel_sym qc Dq cups HassQ HcpQ _ _ _ _ HMkc Hrel')).
    destruct (sort_value Dq HDQ cups Hgcups Hlc) as [bq Ebq].
    pose proof (ind_relate Dq HDQ HcQ HsuQ qc HlQ HassQ kc Mkc pmc cups cs bs bs1 bq HMkc Hhc Hgc Hlc Ebq Hrel') as HR0.
    pose proof (ind_relate Dq HDQ HcQ HsuQ qc HlQ HassQ kc Mkc pmc cups cups bs bs bq HMkc Hhc Hgcups Hlc Ebq Hbb') as HRq0.
    (** At a universe above both. *)
    set (n := ul (Nat.max (large_level i) (large_level (Completeness.Inductives.Decl.univ_idx bq)))).
    assert (Hin : universe_index_le i n) by (apply universe_index_le_ul_max; unfold n; lia).
    assert (Hbn : universe_index_le (Completeness.Inductives.Decl.univ_idx bq) n) by (apply universe_index_le_ul_max; unfold n; lia).
    destruct (glu_univ_elem_cumu_ge_universe_index Hin Hgl) as (Pn & Eln & Hgn).
    pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hin Hgl Hgn HN) as HNn.
    pose proof (per_univ_elem_cumu_universe_index _ _ _ _ HR0 _ Hbn) as HR0n.
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (per_univ_sym' _ _ _ (per_univ_of_elem _ _ _ _ HR0n)) Hgn) as Hgn'.
    pose proof (per_univ_elem_cumu_universe_index _ _ _ _ HRq0 _ Hbn) as HRqn.
    destruct (ind_glu_of_per qc Dq HlQ n _ kc Mkc pmc cups bs HMkc Hhc HRqn Hlc)
      as [NP2 NEl2 AP2 AEl2 DP2 DEl2 P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf2].
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hgn' Hg2) as [_ EEl].
    apply EEl, HEl2 in HNn; destruct HNn as [HNty _ Ps2 HPs2 Hk2].
    assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    (** The view's parameters, at the container's member. *)
    pose proof HQp as HQp'; unfold im_params in HQp'.
    apply glu_args_app in HQp' as [HUs HNs]; [| exact (decl_closed_ass _ Hc) | exact HUl0 | exact Hu ].
    pose proof (view_uparams_glu VP p D HVP HPD HG k Mj qc kc Is vm Dq HMj Hh Hq Δ Us0 ups cups HΔ HUs Ecups) as HUc.
    pose proof (view_nparams_glu VP p D HVP HPD k Mj qc kc Is vm Dq HMj Hh Hq Δ Us0 Q0 ups bs cups kc Mkc k Mj HΔ Hu HUs
                  HMkc Hvk HMj HNs Ecups) as HNc.
    assert (HQpc : glu_args Δ (im_params Dq Mkc) Id nil (List.map (fun I => I[sb_of_list Id Us0]) Is ++ Q0) (cups ++ bs)).
    { unfold im_params; apply glu_args_app;
        [ exact (decl_closed_ass _ HcQ) | rewrite List.length_map; exact HIl | exact Hlc |].
      split; [ exact HUc | exact HNc ]. }
    pose proof (decl_closed_params_ass Dq kc Mkc HcQ HMkc) as HassPc.
    pose proof (decl_closed_params Dq kc Mkc HcQ HMkc) as HsPc.
    pose proof (glu_args_params_top _ _ _ _ _ HassPc HsPc (glu_args_wk _ _ _ _ _ _ _ HassPc HsPc Hφ HQpc)) as Ht.
    destruct (proj2 HPs2 _ _ Hφ) as (HPt2 & _ & _).
    pose proof (glu_params_top_eq qc Dq kc Mkc Δ' _ _ _ HlQ HMkc HΔ' (ind_rps_of_per _ _ _ _ _ _ _ _ HRqn HlQ HMkc _) HPt2 Ht) as Heqq.
    (** The group's parameters there are the container's at the view's
        instance. *)
    assert (HsIs : List.Forall (exp_scoped (List.length Us0)) Is) by (rewrite HUl0; exact (decl_closed_head_scoped D Hc _ _ _ _ _ _ HMj Hh)).
    assert (HlE : List.length Us' + List.length Q' = ind_nu D + im_nn Mj)
      by (destruct HE as [HlE _]; rewrite List.length_map, !List.length_app in HlE; lia).
    pose proof (vs_params_eq_transfer p D Hdt Hl Hc k Mj qc kc Is vm Dq HMj Hh Hq HcQ kc Mkc k Mj HMkc Hvk HMj
                  Δ' (List.map (fun P => P[φ]ʷ) Us0) Us' (List.map (fun P => P[φ]ʷ) Q0) Q' HΔ'
                  ltac:(rewrite List.length_map; exact HUl0) ltac:(rewrite List.length_map; exact HQl0) HUl'
                  ltac:(rewrite <- List.map_app; exact HE)) as HEc.
    rewrite <- (view_args_wk Is Us0 φ HsIs), <- List.map_app in HEc.
    assert (Heqq' : exps_eq_at Δ' (im_params Dq Mkc) (List.map (fun P => P[φ]ʷ) Ps2)
                      (List.map (fun I => I[sb_of_list Id Us']) Is ++ Q')).
    { destruct Heqq as [HlE1 HE1]; destruct HEc as [HlE2 HE2]; split; [ rewrite ?List.length_map in *; lia |].
      destruct HPt2 as [HPl2 _ _]; destruct Ht as [HQl2 _ _].
      eapply (params_eq_trans _ qc Dq kc Mkc _ _ _ HlQ HMkc HΔ' HPl2 HQl2); [| exact HE1 | exact HE2 ].
      rewrite List.length_app, List.length_map, HIl; unfold im_np, ind_nu in *; lia. }
    pose proof (Hk2 Δ' φ _ Hφ Heqq') as Hgi.
    rewrite firstn_app_exact, skipn_app_exact in Hgi by (rewrite List.length_map; exact HIl).
    (** The container's element is the group's. *)
    pose proof (exps_eq_at_uparams_of_params D Mj Δ' (List.map (fun P => P[φ]ʷ) (Us0 ++ Q0)) (Us' ++ Q') Hc
                  ltac:(rewrite List.length_map, List.length_app; unfold im_np, ind_nu in *; lia) HE) as HU'.
    rewrite List.map_app, !firstn_app_exact in HU' by (rewrite ?List.length_map; unfold ind_nu in *; lia).
    pose proof (glu_args_resp_eq Δ' (ind_uparams D) nil _ Us' ups (decl_closed_ass _ Hc) (decl_typed_uparams_field _ _ _ Hdt) HΔ' HU'
                  (glu_args_wk _ _ _ _ _ _ _ (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) Hφ HUs)) as HUs'.
    pose proof (exps_eq_at_typed_r p D k Mj Δ' (List.map (fun P => P[φ]ʷ) (Us0 ++ Q0)) (Us' ++ Q') Hl HMj HΔ'
                  ltac:(rewrite List.length_map, List.length_app; unfold im_np, ind_nu in *; lia) HE) as HPs'.
    pose proof (to_group_all VP p D HVP HPD HG ups bu u NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf k Mj qc kc Is vm Dq HMj Hh Hq
                  cups Ecups n NP2 NEl2 AP2 AEl2 DP2 DEl2 Hf2
                  (fun i' Mi' v Mv c gs1' A' gs2' gs1 t gs2 HMi' Hv HMv Hc' Hc0 Hcr =>
                     Hend Mj qc kc Is vm Dq i' Mi' v Mv c gs1' A' gs2' gs1 t gs2 HMj Hh Hq HMi' Hv HMv Hc' Hc0 Hcr)) as [TG _].
    exact (TG kc Δ' _ Q' N[φ]ʷ x Hgi Mkc k Mj Us' HMkc HVMk eq_refl HΔ' HUs' ltac:(unfold ind_nu in *; lia) HPs').
  Qed.

  (** A record view agrees with its record, given that the members its
      recursive fields end in agree: the record's gluing of an element
      gives its projections glued along the record's fields at the view's
      instance, so along the view's constructor's telescope (the record
      view equation), and the element is that constructor at them. *)
  Lemma glu_rview_end_root : forall j,
      (forall Mj qr Is fl c gs gs1 t gs2, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
         im_cons Mj = (c, gs) :: nil -> gs = gs1 ++ ca_rec t :: gs2 -> glu_end_at p D ups NEl AEl DP DEl (ptyp_mem t)) ->
      glu_rview_end_at p D ups NEl AEl DP DEl j.
  Proof.
    intros j Hend Mj qr Is fl R cups cs Δ Us W N v i P El HMj Hh HlR Ecups Hgc Hgl HN _ HUs Δ' φ Us' Hφ HUl' HE.
    destruct (valid_group_records _ _ Hg _ _ _ _ _ HMj Hh) as [R0 HR].
    rewrite (valid_rview_record_lookup _ _ HR) in HlR; injection HlR as <-.
    pose proof (valid_rview_record_lookup _ _ HR) as HlR.
    destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gs & Hcs & _).
    (** The record's gluing, at the instance's values. *)
    pose proof (RviewEnds.rv_cups_len p D Hg j Mj qr Is fl R0 HMj Hh HR ups cups Ecups) as Hlc.
    destruct (vrr_type_rel qr R0 cups cs HR Hgc Hlc) as [i1 HR1].
    pose proof (glu_univ_elem_per_univ _ _ _ _ Hgl) as Hss.
    assert (Hcc : per_univ i1 (d_record qr cups) (d_record qr cs)) by (eexists; exact HR1).
    pose proof (per_univ_trans' _ _ _ _ _ Hss (per_univ_sym' _ _ _ Hcc)) as Hsc.
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ Hsc Hgl) as Hgl'.
    (** The uniform parameters at the weakening, and the instance there. *)
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    pose proof (RviewEnds.rv_params p D Hg j Mj qr Is fl HMj Hh) as EP.
    rewrite EP in HUs, HE.
    pose proof (glu_args_resp_eq Δ' (ind_uparams D) nil _ Us' ups (decl_closed_ass _ Hc) (decl_typed_uparams_field _ _ _ Hdt) HΔ' HE
                  (glu_args_wk _ _ _ _ _ _ _ (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) Hφ HUs)) as HUs'.
    set (Ns' := List.map (fun I => I[sb_of_list Id Us']) Is).
    pose proof (rview_uparams_glu VP p D HVP HPD HG j Mj qr Is fl R0 HMj Hh HR Δ' Us' ups cups HΔ' HUs' Ecups) as HNs'.
    (** The element's projections, glued along the record's fields, so
        along the view's constructor's telescope. *)
    destruct (record_elem_fields_glu qr R0 cups i P El Δ W N v HlR Hgl' HN Δ' φ Ns' Hφ HNs') as [ws l Hws HWeq HgF].
    set (n := List.length (record_fields R0)) in *.
    set (Ms := record_pre R0 n N[φ]ʷ) in *.
    pose proof (valid_rview_record_closed _ _ HR) as HcR.
    pose proof (rview_record_len p D Hg j Mj qr Is fl R0 HMj Hh HR) as HIl.
    assert (HsF : ctx_scoped (List.length (record_params R0)) (record_fctx R0 n)).
    { apply ctx_scoped_app_iff, (record_fctx_scoped R0 n (le_n _)); [| exact (closed_params _ HcR) ].
      intros k f T HfT _; exact (closed_fields _ HcR _ _ _ HfT). }
    pose proof (glu_args_base_agree _ _ _ _ (sb_of_list Id Is ⨟ sb_of_list Id Us') _ _ _ (record_fctx_ass _ _) HsF
                  ltac:(intros x Hx; cbn [sb_compose]; symmetry; apply sb_of_list_lt_compose; lia) HgF) as HgF'.
    pose proof (rview_fields_to_cargs p D Hg Hcv j Mj qr Is fl R0 rview_con gs HMj Hh HR Hcs ups cups Hgu Hu Ecups
                  Δ' Us' Ms ws HΔ' HUs' HgF') as HgA.
    (** The element is the constructor at its projections: record η, and
        the constructor is the tuple of its arguments. *)
    pose proof (RviewEnds.rv_names p D Hg j Mj qr Is fl R0 HMj Hh HR) as Hfl.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LMs _]; rewrite length_cargs_ctx in LMs.
    destruct (decl_typed_uparams _ _ _ Hdt) as [_ HUa].
    pose proof (rview_con_tuple Δ' p D j Mj qr Is fl rview_con gs Us' Ms Hl HMj Hh Hcs HΔ' HUl'
                  (glu_args_typed _ _ _ _ _ _ HUa HUs') LMs (glu_args_typed _ _ _ _ _ _ (cargs_ctx_aux_ass _ _ _ _ _) HgA)) as Hct.
    assert (Hpre : im_pre Mj Us' = Ns') by (unfold im_pre; rewrite Hh; reflexivity).
    assert (HTy : im_ty_at p j Mj Us' nil = apps_exp (a_record qr) Ns')
      by (unfold im_ty_at, im_pre; rewrite Hh, List.app_nil_r; reflexivity).
    rewrite Hpre, HTy in Hct.
    assert (HNt : Δ' ⊢ N[φ]ʷ : apps_exp (a_record qr) Ns').
    { pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgl' _ _ _ _ (glu_univ_elem_exp_monotone _ _ _ _ Hgl' _ _ _ _ _ _ HN Hφ)) as H.
      eapply wf_conv; [ exact H | gen_presups; eassumption | exact HWeq ]. }
    assert (HNl : List.length Ns' = List.length (record_params R0)) by (unfold Ns'; rewrite List.length_map; exact HIl).
    assert (Htup : Δ' ⊢ a_tuple (apps_exp (a_record qr) Ns') (record_eta_fields R0 N[φ]ʷ) : apps_exp (a_record qr) Ns')
      by (rewrite record_eta_fields_combine, <- Hfl; gen_presups; eassumption).
    pose proof (wf_exp_eq_record_eta _ _ _ qr Ns' N[φ]ʷ R0 HNt HlR HNl Htup) as Heta.
    assert (Heqn : Δ' ⊢ N[φ]ʷ ≈ apps_exp (a_con p j rview_con) (Us' ++ nil ++ Ms) : im_ty_at p j Mj Us' nil).
    { rewrite HTy; cbn [List.app]; eapply wf_exp_eq_trans; [ exact Heta |].
      rewrite record_eta_fields_combine, <- Hfl; apply wf_exp_eq_sym; exact Hct. }
    apply (con_rview_ind_glu_elem VP p D HVP HPD HG j Mj rview_con gs HMj (ind_con_single _ _ _ Hcs) ups bu u NP NEl AP AEl DP DEl
             Hu Hgu Hbu Hule Hf qr Is fl Δ' Us' nil Ms nil ws N[φ]ʷ v Hh HΔ' HUl').
    - rewrite !List.app_nil_r, EP; exact HUs'.
    - rewrite !List.app_nil_r; exact HgA.
    - apply (RviewEnds.record_projs_iff R0 fl v ws Hfl); exact Hws.
    - exact Heqn.
    - intros gs1 t gs2 Heq; exact (Hend Mj qr Is fl rview_con gs gs1 t gs2 HMj Hh Hcs Heq).
  Qed.

  (** By induction on the ranks of the views and the record views: the
      members a view nests through, and those a record view's recursive
      fields end in, are of lower rank. *)
  Lemma glu_view_end_all : glu_view_end_ok p D ups NEl AEl DP DEl.
  Proof.
    destruct (decl_typed_rank _ _ _ Hdt) as [rk Hrk].
    assert (Hall : forall n j, rk j < n -> glu_end_at p D ups NEl AEl DP DEl j).
    { induction n as [| n IH]; intros j Hj; [ lia |].
      split.
      - apply glu_view_end_root.
        intros * HMj Hh Hq HMi' Hv HMv Hc' Hc0 Hcr.
        pose proof (view_rank_ok_nest _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hq HMi' Hv HMv Hc' Hc0) as Hn.
        pose proof (cargs_nest_ok_at _ _ _ _ _ _ _ _ _ _ (cargs_corr_len _ _ _ Hcr) Hn) as Hlt.
        exact (IH (ptyp_mem t) ltac:(lia)).
      - apply glu_rview_end_root.
        intros * HMj Hh Hcs Heq.
        pose proof (view_rank_ok_rview _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ HMj Hh ltac:(rewrite Hcs; left; reflexivity) Heq) as Hlt.
        exact (IH (ptyp_mem t) ltac:(lia)). }
    intros j; exact (Hall (S (rk j)) j ltac:(lia)).
  Qed.
End Root.

(** Every view of a group whose declaration is glued agrees with its
    container. *)
Theorem glu_views_ok_all : forall VP p D, valid_groups VP -> VP p D -> glu_ind_decl D -> glu_views_ok p D.
Proof.
  intros VP p D HVP HPD HG ups bu u NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf.
  exact (glu_view_end_all VP p D HVP HPD HG ups bu u NP NEl AP AEl DP DEl Hu Hgu Hbu Hule Hf).
Qed.

End Fixed_GCtx.
