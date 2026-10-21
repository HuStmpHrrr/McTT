(** * The Group's Gluing of an Element Is its Type's

    An element of a member [k] of a group, glued in the group
    ([ind_glu_elem]), is glued at its type: the group's own clause of
    [d_ind] at a declared member, the container's at a view.  This is the
    converse of [Inductives/Bridge.v].  By induction on the group's gluing:
    a constructor's arguments are glued at the closed telescope of its
    arguments, the non-recursive ones by the clause's families, the
    recursive ones by the induction, and the constructor applied to them is
    glued at its type ([con_base], [con_view_base]); a neutral is
    ([realize_glu_elem_bot]).  The eliminator glues the arguments of a
    constructor this way at the types of its branch's context. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes FiledViews ViewEquations ViewArgs.
From Mctt.Core.Completeness.Inductives Require Con ViewReadback.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon IndElim ViewCoherence.
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
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon Bridge ElimBase.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Section AtType.
  Variable (VP : qname -> ind_decl -> Prop).
  Hypotheses (HVP : valid_groups VP) (HGall : forall qn G, VP qn G -> glu_ind_decl G)
    (Hviewsall : forall qn G, VP qn G -> glu_views_ok qn G).
  Variables (p : qname) (D : ind_decl).
  Hypothesis (HPD : VP p D).
  Let HG := HGall _ _ HPD.
  Let Hvg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := vgr_lookup _ _ Hvg.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hsu := vgr_sort _ _ Hvg.
  Let Hass := vgr_ass _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.

  Variables (ups : list domain) (bu : domain) (u : uidx)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypotheses (Hu : List.length ups = ind_nu D) (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups)
    (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).

  #[local] Abbreviation nr := (canon_nparams_rel D ups).
  #[local] Abbreviation ar := (canon_args_rel D ups).
  #[local] Abbreviation dr := (canon_doms_rel ups).
  #[local] Abbreviation G := (grp_rel p D ups nr ar dr).

  (** ** The Statements

      An element [M'] of the member [k] at the uniform parameters [Us']
      and the non-uniform ones [Ns'], glued in the group: at any gluing of
      its type's value at which its type is glued, it is glued. *)
  Definition elem_glu_at_type (k : nat) (Δ' : ctx) (Us' Ns' : list exp) (M' : exp) (mv : domain) : Prop :=
    forall Mk ns hd k' pre (i : nat) P El, ind_member D k = Some Mk ->
      ⟦mref k of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      glu_args Δ' (ind_uparams D) Id nil Us' ups -> Δ' ⊢ M' : im_ty_at p k Mk Us' Ns' ->
      glu_nparams k Mk NEl Δ' Us' Ns' ns -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns ->
      G k ups ups ns ns mv mv ->
      DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El -> Δ' ⊢ im_ty_at p k Mk Us' Ns' ® P ->
      Δ' ⊢ M' : im_ty_at p k Mk Us' Ns' ® mv ∈ El.

  (** A recursive argument [N] of shape [t] of a constructor [c0] of the
      member [k], after [d] domains of the shape, glued in the group: at
      any gluing of the value of its shape's type at which its type is
      glued, it is glued. *)
  Definition rec_glu_at_type (k : nat) (Δ' : ctx) (Us' : list exp) (pre : list domain) (t : ptyp) (A : typ) (N : exp) (v : domain) : Prop :=
    forall Mk ms c0 gs1 t0 gs2 ws d ys σs a (i : nat) P El,
      ind_member D k = Some Mk -> ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) -> pre = ms ++ ws ++ ys ->
      tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
      tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
      ptyp_skip d t0 = t -> tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) d ys ys ->
      glu_args Δ' (ind_uparams D) Id nil Us' ups -> A = ptyp_ty_at p D Us' σs t -> Δ' ⊢ N : A ->
      rec_arg_rel p D (okr_at D ups nr) nr ar dr k ups ups pre pre t v v ->
      ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ a ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ' ⊢ A ® P -> Δ' ⊢ N : A ® v ∈ El.

  (** ** The Relation of a Member's Type

      The relation of the value of a member's type, as [mref] reads its
      head and uniform parameters, is the group's at the member. *)
  Lemma mref_rel : forall k Mk hd k' pre ns (i : uidx) R, ind_member D k = Some Mk ->
      ⟦mref k of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      DF d_ind hd k' (pre ++ ns) ≈ d_ind hd k' (pre ++ ns) ∈ per_univ_elem i ↘ R ->
      (R <~> G k ups ups ns ns).
  Proof.
    intros * HMk Hr HR.
    destruct (im_head Mk) as [pm | qc kc Is vm] eqn:Hh.
    - pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMk Hh Hr) as E; injection E as -> -> ->.
      exact (proj1 (vg_type_rel_base p D Hvg k Mk pm ups ups ups ups ns ns i R HMk Hh Hgu Hu Hgu Hgu HR)).
    - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMk Hh Hr) as (py & E & Epy); injection E as -> -> <-.
      destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mk' & Hq & _).
      destruct (vg_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMk Hh Hq ups ups Hgu Hu) as (c0 & c0' & E0 & E0' & Hc0).
      pose proof (functional_eval_exps' _ _ _ _ E0 Epy) as ->; pose proof (functional_eval_exps' _ _ _ _ E0' Epy) as ->.
      exact (Completeness.Inductives.Con.view_end_rel_all VP p D HVP HPD ups ups Hgu Hu k Mk qc kc Is vm Dq pre pre HMk Hh Hq Epy Epy pre pre ns ns i R Hc0 Hc0 HR).
  Qed.

  (** ** Neutrals *)
  Lemma elem_at_neut : forall k Mk hd k' m Δ' Us' Ns' M' as', ind_member D k = Some Mk -> im_ref p k Mk = (hd, k') ->
      Dom m ≈ m ∈ per_bot ->
      (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (im_ty_at p k Mk Us' Ns')[φ]ʷ) ->
      elem_glu_at_type k Δ' Us' Ns' M' (⇑ (d_ind hd k' as') m).
  Proof.
    intros * HMk Href Hm Hrb Mk0 ns hd0 k0 pre i P El HMk0 Hr _ HM' _ Hns HGm Hglu HT.
    rewrite HMk in HMk0; injection HMk0 as <-.
    destruct (ViewReadback.mref_ref_len p D k Mk ups hd0 k0 pre Hl HMk Hu Hr) as [Href0 Lpre].
    rewrite Href in Href0; injection Href0 as <- <-.
    pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
    rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (realize_glu_elem_bot _ _ _ _ Hglu Δ' _ M' m
                  (glu_elem_bot_make _ _ _ _ _ _ P El HM' Hglu HT Hm Hrb)) as HEl.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    eapply glu_univ_elem_trm_resp_per_elem; [ exact Hglu | exact HR | exact HEl |].
    apply (mref_rel k Mk hd k' pre ns i R HMk Hr HR).
    inversion HGm as [| ? ? ? ? ? ? as1 as2 ? ? ? ? HM1 Hr1 Hn1 L1 L2 Hs1 Hs2 He]; subst.
    rewrite HMk in HM1; injection HM1 as <-.
    eapply ind_rel_neut; [ exact HMk | exact Href | exact Hns | rewrite List.length_app, Lpre; lia | exact L2
                         | rewrite skipn_app_exact by exact Lpre; exact Hns | exact Hs2 | exact He ].
  Qed.

  (** ** Types of Members at Glued Parameters

      A level [nb] above the clause's index and the sorts of the
      containers of the views: at it and above, the type of a member at
      glued parameters is glued at its value's gluing. *)
  Variable (nb : nat).
  Hypotheses (Hnbu : uidx_le u (ul nb))
    (Hnbq : forall j Mj qc kc Is vm Dq, ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
              ind_lookup gc_deps gc_stack qc = Some Dq -> forall ρ bq, ⟦ ind_sort Dq ⟧ ρ ↘ bq ->
              uidx_le (Completeness.Inductives.Decl.univ_idx bq) (ul nb)).

  Lemma ul_mono : forall a b, a <= b -> uidx_le (ul a) (ul b).
  Proof. intros a b Hab; apply uidx_le_ul_max; cbn; exact Hab. Qed.

  Lemma mty_glu : forall j Mj hd k' pre Δ Us' Q bs (i : nat) P El, nb <= i -> ind_member D j = Some Mj ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) -> ⊢ Δ ->
      glu_args Δ (ind_uparams D) Id nil Us' ups -> glu_nparams j Mj NEl Δ Us' Q bs ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs ->
      DG d_ind hd k' (pre ++ bs) ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ im_ty_at p j Mj Us' Q ® P.
  Proof.
    intros * Hi HMj Hr HΔ HUs Hgn Hbs Hglu.
    pose proof (gnp_len _ _ _ _ _ _ _ Hgn) as LQ.
    pose proof (gnp_vals_len _ _ _ _ _ _ _ Hgn) as Lbs.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf j Mj Δ Us' Q bs HMj Hgn Hbs) as HNs.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh.
    - pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMj Hh Hr) as E; injection E as -> -> ->.
      assert (Hlt : j < ind_ndecl D) by (eapply decl_member_lt; eassumption).
      assert (HgP : glu_args Δ (im_params D Mj) Id nil (Us' ++ Q) (ups ++ bs)).
      { unfold im_params; apply glu_args_app; [ exact (dc_ass _ Hc) | exact LU | rewrite Hu; reflexivity |].
        split; [ exact HUs | exact HNs ]. }
      destruct (ind_glu_of_per p D Hl (ul i) R j Mj pm ups bs HMj Hh HR Hu)
        as [NP2 NEl2 AP2 AEl2 DP2 DEl2 P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf2].
      assert (Hle' : uidx_le (Completeness.Inductives.Decl.univ_idx bu) (ul i))
        by (eapply uidx_le_trans; [ exact Hule | eapply uidx_le_trans; [ exact Hnbu | exact (ul_mono _ _ Hi) ] ]).
      assert (HT2 : Δ ⊢ im_ty_at p j Mj Us' Q ® P2).
      { apply HP2; exists (Us' ++ Q).
        unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
        exact (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Hass j Mj Δ (Us' ++ Q) ups bs bu (ul i) NP2 NEl2 AP2 AEl2 DP2 DEl2
                 HMj Hlt HΔ HgP Hu Hbu Hle' Hf2). }
      destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hg2) as [EP _].
      apply EP; exact HT2.
    - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMj Hh Hr) as (py & E & Epy); injection E as -> -> <-.
      destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dq & Mkc & Hq & HMkc & Hkd & HIl & _ & Hvm & _).
      pose proof (valid_groups_containers VP HVP p D j Mj qc kc Is vm Dq HPD HMj Hh Hq) as HPq.
      pose proof (valid_groups_valid VP HVP qc Dq HPq) as HgQ.
      pose proof (HGall _ _ HPq) as HGq.
      assert (Hhc : exists pmc, im_head Mkc = mh_decl pmc).
      { pose proof (proj2 (dt_order _ _ _ (vgr_typed _ _ HgQ) _ _ HMkc) Hkd) as Hd.
        unfold im_is_decl in Hd; destruct (im_head Mkc); [ eauto | discriminate ]. }
      destruct Hhc as [pmc Hhc].
      assert (Hlpre : List.length pre = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ Epy); exact HIl).
      pose proof (view_uparams_glu VP p D HVP HPD HG j Mj qc kc Is vm Dq HMj Hh Hq Δ Us' ups pre HΔ HUs Epy) as HUc.
      pose proof (view_nparams_glu VP p D HVP HPD j Mj qc kc Is vm Dq HMj Hh Hq Δ Us' Q ups bs pre kc Mkc j Mj HΔ Hu HUs
                    HMkc Hvm HMj HNs Epy) as HNc.
      assert (HPc : glu_args Δ (im_params Dq Mkc) Id nil (List.map (fun I => I[sb_of_list Id Us']) Is ++ Q) (pre ++ bs)).
      { unfold im_params; apply glu_args_app; [ exact (dc_ass _ (vgr_closed _ _ HgQ)) | rewrite List.length_map; exact HIl
                                              | exact Hlpre |].
        split; [ exact HUc | exact HNc ]. }
      destruct (ind_glu_of_per qc Dq (vgr_lookup _ _ HgQ) (ul i) R kc Mkc pmc pre bs HMkc Hhc HR Hlpre)
        as [NP2 NEl2 AP2 AEl2 DP2 DEl2 P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf2].
      destruct (vg_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMj Hh Hq ups ups Hgu Hu) as (c0 & c0' & E0 & _ & Hc0).
      pose proof (functional_eval_exps' _ _ _ _ E0 Epy) as ->.
      destruct (sort_value Dq (vgr_valid _ _ HgQ) pre ltac:(eapply uparams_refl_l; [ exact (vgr_valid _ _ HgQ)
                                                                                     | exact (vgr_closed _ _ HgQ) | exact Hc0 ]) Hlpre)
        as [bq Ebq].
      assert (Hle' : uidx_le (Completeness.Inductives.Decl.univ_idx bq) (ul i))
        by (eapply uidx_le_trans; [ exact (Hnbq _ _ _ _ _ _ _ HMj Hh Hq _ _ Ebq) | exact (ul_mono _ _ Hi) ]).
      assert (HT2 : Δ ⊢ im_ty_at p j Mj Us' Q ® P2).
      { apply HP2; exists (List.map (fun I => I[sb_of_list Id Us']) Is ++ Q).
        unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
        exact (ind_typ_at_of_args qc Dq (vgr_lookup _ _ HgQ) HGq (vgr_closed _ _ HgQ) (vgr_typed _ _ HgQ) (vgr_sort _ _ HgQ)
                 (vgr_ass _ _ HgQ) kc Mkc Δ _ pre bs bq (ul i) NP2 NEl2 AP2 AEl2 DP2 DEl2 HMkc Hkd HΔ HPc Hlpre Ebq Hle' Hf2). }
      destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hg2) as [EP _].
      apply EP; exact HT2.
  Qed.

  (** ** Types of Recursive Arguments

      The type of a recursive argument glued in the group, at a universe
      above [nb] and its type's: glued at the gluing of the value of its
      shape's type. *)
  Lemma ptyp_skip_pi : forall d t0 B t, ptyp_skip d t0 = pt_pi B t ->
      List.nth_error (ptyp_doms t0) d = Some B /\ ptyp_skip (S d) t0 = t.
  Proof.
    induction d as [| d IH]; intros [j Ps | B0 t0] B t H; cbn in H |- *; try discriminate.
    - injection H as -> ->; split; reflexivity.
    - exact (IH _ _ _ H).
  Qed.

  (** A domain value's relation is the canonical family's at it. *)
  Lemma rel_dr : forall k pre B b (j : uidx) R c, ⟦ B ⟧ env_args nil (ups ++ pre) ↘ b ->
      DF b ≈ b ∈ per_univ_elem j ↘ R -> R c c -> dr k pre B c c.
  Proof.
    intros * Eb HR Hcc; unfold canon_doms_rel; intros i2 R1 b2 b2' Eb2 Eb2' HR1.
    assert (b2 = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (b2' = b) as -> by (eapply functional_eval_exp; eassumption).
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HR1); exact Hcc.
  Qed.

  Lemma shape_ty_step : forall t Us' σs φ b, List.length Us' = ind_nu D ->
      (ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us') (q σs) t)[(ι φ),,b]
      = ptyp_ty_at p D (List.map (fun U => U[φ]ʷ) Us') (q σs ⨟ ((ι φ),,b)) t.
  Proof.
    intros * HUl; rewrite ptyp_ty_at_sub by (try exact Hc; rewrite List.length_map; exact HUl).
    rewrite List.map_map; f_equal; apply List.map_ext; intros U; apply exp_shift_extend_wk.
  Qed.

  (** The premises of [glu_rec] at each shape. *)
  Lemma glu_rec_self_inv : forall k Γ Us pre j Ps A N v, glu_rec p D ups NEl AEl DP DEl k Γ Us pre (pt_self j Ps) A N v ->
      exists Mj, ind_member D j = Some Mj /\
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr ->
         A = im_ty_at p j Mj Us Q ->
         List.length Q = im_nn Mj /\ tele_rel (nr j) (List.rev (im_nparams Mj)) bsr bsr /\
         (forall bsr', tele_rel (nr j) (List.rev (im_nparams Mj)) bsr bsr' ->
            glu_nparams j Mj NEl Γ Us Q bsr' /\
            forall Δ φ, Δ ⊢ᵏ φ : Γ -> glu_params_top D Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (ups ++ bsr'))) /\
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr ->
         A = im_ty_at p j Mj Us Q ->
         forall Δ φ Us' Q', Δ ⊢ᵏ φ : Γ -> List.length Us' = ind_nu D ->
           exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
           ind_glu_elem p D ups NEl AEl DP DEl j Δ Us' Q' N[φ]ʷ v).
  Proof. intros * H; inversion H; subst; eauto. Qed.

  Lemma glu_rec_pi_inv : forall k Γ Us pre B t A N v, glu_rec p D ups NEl AEl DP DEl k Γ Us pre (pt_pi B t) A N v ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP k pre B) /\
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) /\
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Γ -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
         glu_rec p D ups NEl AEl DP DEl k Δ (List.map (fun U => U[φ]ʷ) Us) (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc).
  Proof. intros * H; inversion H; subst; eauto. Qed.

  Lemma eval_shty_pi_inv : forall B t ρ a, ⟦shty pt_pi B t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a ->
      exists b, ⟦ B ⟧ ρ ↘ b /\ a = Πᵈ b (nil ↦ d_shfam p ups ρ t) fam_cod.
  Proof. intros * H; inversion H; subst; eauto. Qed.

  Lemma eval_shty_self_inv : forall j Ps ρ a, ⟦shty pt_self j Ps of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a ->
      exists bs pc kc pre, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ bs /\ ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (pc, kc, pre) /\
        a = d_ind pc kc (pre ++ bs).
  Proof. intros * H; inversion H; subst; eauto 10. Qed.

  Lemma rec_typ_glu : forall t k Δ' Us' pre A N v, glu_rec p D ups NEl AEl DP DEl k Δ' Us' pre t A N v ->
      forall Mk ms c0 gs1 t0 gs2 ws d ys σs a (j0 i : nat) P El,
      ind_member D k = Some Mk -> ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) -> pre = ms ++ ws ++ ys ->
      tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
      tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
      ptyp_skip d t0 = t -> tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) d ys ys ->
      glu_args Δ' (ind_uparams D) Id nil Us' ups -> A = ptyp_ty_at p D Us' σs t -> Δ' ⊢ A : Typeω@j0 ->
      ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ a -> j0 <= i -> nb <= i ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ' ⊢ A ® P.
  Proof.
    induction t as [j Ps | B t IH]; intros * Hgr * HMk Hc0 Hpre Hms Hws Hsk Hys HUs HA HAt Ea Hj0 Hi Hglu.
    all: assert (HΔ' : ⊢ Δ') by (gen_presups; assumption).
    all: destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    - subst; destruct (glu_rec_self_inv _ _ _ _ _ _ _ _ _ Hgr) as (Mj & HMj & Hs1 & _).
      destruct (eval_shty_self_inv _ _ _ _ Ea) as (bs & pc & kc & pre' & Ebs & Hr & ->).
      destruct (Hs1 _ (List.map (fun P0 => P0[σs]) Ps) Ebs ltac:(cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity))
        as (_ & Hbs & Hgn).
      cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj.
      exact (mty_glu j Mj _ _ _ Δ' Us' _ _ i P El Hi HMj Hr HΔ' HUs (proj1 (Hgn _ Hbs)) Hbs Hglu).
    - subst pre A; destruct (glu_rec_pi_inv _ _ _ _ _ _ _ _ _ Hgr) as (Hq1 & Hq2 & Hq3).
      destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hsk'].
      cbn [ptyp_ty_at] in HAt, Hq1, Hq2, Hq3 |- *.
      set (IT := B[σs]) in *.
      set (OTy := ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us') (q σs) t) in *.
      specialize (Hq1 _ _ eq_refl); specialize (Hq2 _ _ eq_refl); specialize (Hq3 _ _ eq_refl).
      destruct (eval_shty_pi_inv _ _ _ _ Ea) as (b1 & Eb1 & ->).
      destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Ra HRa].
      basic_invert_per_univ_elem HRa.
      match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
      destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' Hglu) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & _).
      pose proof (ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hms Hc0 eq_refl Hws HB Hys Eb1) as HgD.
      destruct (wf_pi_inversion' HAt) as [HITt HOTt].
      assert (Hui : uidx_le u (ul i)) by (eapply uidx_le_trans; [ exact Hnbu | exact (ul_mono _ _ Hi) ]).
      apply HPeq; econstructor.
      + apply wf_exp_eq_refl; exact (lift_exp_ge _ _ _ _ j0 i Hj0 HAt).
      + exact (lift_exp_ge _ _ _ _ j0 i Hj0 HITt).
      + exact (lift_exp_ge _ _ _ _ j0 i Hj0 HOTt).
      + intros Δ φ Hφ.
        eapply (glu_typ_transfer u (ul i) (ul i)); [ exact Hui | apply uidx_le_refl | eexists; exact equiv_a_a' | exact HgD
                                                   | exact Hgb1 | exact (Hq1 _ _ Hφ) ].
      + intros Δ φ M m Hφ HM equiv_m.
        pose proof (rel_dr k (ms ++ ws ++ ys) B b1 i in_rel m Eb1 equiv_a_a' equiv_m) as Hdr.
        assert (HbD : Δ ⊢ M : IT[φ]ʷ ® m ∈ DEl k (ms ++ ws ++ ys) B).
        { eapply glu_elem_retype; [ exact Hgb1 | exact HgD | exact (glu_univ_elem_trm_typ _ _ _ _ Hgb1 _ _ _ _ HM) | exact HM
                                  | exact (Hq1 _ _ Hφ) ]. }
        destruct (Hq2 _ _ _ _ Hφ Hdr HbD) as [fc Efc].
        pose proof (Hq3 _ _ _ _ _ Hφ Hdr HbD Efc) as Hgr'.
        destruct (Hcod _ _ equiv_m) as [a2 a2' Ea2 Ea2' _].
        pose proof (Hcodg _ equiv_m _ Ea2) as Hga2.
        pose proof (eval_fam_cod_shfam_inv _ _ _ _ _ _ Ea2) as Ea2s.
        assert (HΔ : ⊢ Δ) by (eapply kripke_dom; exact Hφ).
        pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ HM) as HMt.
        rewrite <- !List.app_assoc in Hgr'; cbn [List.app] in Hgr'.
        eapply (IH k Δ (List.map (fun U => U[φ]ʷ) Us') _ _ _ fc Hgr' Mk ms c0 gs1 t0 gs2 ws (S d) (ys ++ m :: nil)
                  (q σs ⨟ ((ι φ),,M)) a2 j0 i); try eassumption.
        * reflexivity.
        * apply tele_prefix_rel_snoc; [ exact Hys |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hdr.
        * exact (glu_args_wk _ _ _ _ _ _ _ (dc_ass _ Hc) (dc_uparams _ Hc) Hφ HUs).
        * unfold OTy; apply shape_ty_step; rewrite LU; reflexivity.
        * exact (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ HMt).
        * replace (ups ++ ms ++ ws ++ ys ++ m :: nil) with ((ups ++ ms ++ ws ++ ys) ++ m :: nil)
            by (rewrite <- !List.app_assoc; reflexivity).
          rewrite env_args_snoc; exact Ea2s.
  Qed.

End AtType.

End Fixed_GCtx.
