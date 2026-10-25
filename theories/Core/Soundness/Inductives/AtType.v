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
From Mctt.Core.Completeness.Inductives Require Con ViewReadback Elim.
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
  Let Hl := valid_group_lookup _ _ Hvg.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hsu := valid_group_sort _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.

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
      ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ a ->
      (forall R, DF a ≈ a ∈ per_univ_elem i ↘ R -> R v v) ->
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
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mk' & Hq & _).
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

  (** ** The Value of a Member's Type over a Closed Telescope

      The member [j]'s type at the uniform parameters as variables, after
      values [X ++ ws] of a closed telescope [Z] over them related to
      themselves ([X] its non-uniform parameters): related to the type's
      value at the uniform parameters [pre] [mref] gives and non-uniform
      parameters related to [X]. *)
  Lemma mty_val_rel : forall j Mj hd k' pre Z RZ X ws L b ns, ind_member D j = Some Mj ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
      List.length (X ++ ws) = List.length Z -> List.length X = im_nn Mj -> List.length ws = L ->
      RZ (env_args nil (ups ++ X ++ ws)) (env_args nil (ups ++ X ++ ws)) ->
      ⟦ ind_mty p D j (ind_uvars D (im_nn Mj) L) (vars_from L (im_nn Mj)) ⟧ env_args nil (ups ++ X ++ ws) ↘ b ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns X ->
      exists (i0 : uidx) R0, DF d_ind hd k' (pre ++ ns) ≈ b ∈ per_univ_elem i0 ↘ R0.
  Proof.
    intros * HMj Hr HZ HRZ Lz LX Lw HE Eb Hns.
    destruct (ViewReadback.mref_ref_len p D j Mj ups hd k' pre Hl HMj Hu Hr) as [Href _].
    destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMj Eb) as (cs & xs & Ecs & Exs & ->).
    rewrite Href; cbn [fst snd].
    assert (EX : ⟦ vars_from L (im_nn Mj) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ X ++ ws) ↘ X).
    { rewrite env_args_app, <- LX, <- Lw; apply Decl.eval_vars_from_args. }
    pose proof (functional_eval_exps' _ _ _ _ Exs EX) as ->.
    destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh.
    - pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMj Hh Hr) as E; injection E as -> -> ->.
      assert (cs = ups) as ->.
      { unfold im_pre in Ecs; rewrite Hh in Ecs.
        assert (HU : ⟦ ind_uvars D (im_nn Mj) L ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ X ++ ws) ↘ ups).
        { unfold ind_uvars.
          replace (L + im_nn Mj) with (List.length (X ++ ws)) by (rewrite List.length_app; lia).
          rewrite <- Hu; apply Decl.eval_vars_from_args. }
        exact (functional_eval_exps' _ _ _ _ Ecs HU). }
      destruct (vg_relate p D Hvg j Mj pm ups ups ns X HMj Hh Hgu Hu Hns) as [i0 Hi0]; eauto.
    - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMj Hh Hr) as (py & E & Epy); injection E as -> -> <-.
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dq & Mkc & Hq & _).
      destruct (view_pre_values p D Hvg Hcv j Mj qc kc Is vm Dq ups Z RZ (X ++ ws) (im_nn Mj) L cs HMj Hh Hq Hu Hgu
                  HZ HRZ ltac:(lia) ltac:(rewrite List.length_app; lia) HE Ecs) as (cups & Ecups & Hgc).
      pose proof (functional_eval_exps' _ _ _ _ Ecups Epy) as ->.
      destruct (ViewReadback.view_end_type VP HVP p D HPD ups Hgu Hu j Mj qc kc Is vm Dq pre cs ns X HMj Hh Hq Epy Hgc
                  ltac:(unfold ntele_rel; rewrite HMj; exact Hns)) as (i0 & R0 & H0); eauto.
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
    pose proof (glu_nparams_len _ _ _ _ _ _ _ Hgn) as LQ.
    pose proof (glu_nparams_vals_len _ _ _ _ _ _ _ Hgn) as Lbs.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf j Mj Δ Us' Q bs HMj Hgn Hbs) as HNs.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh.
    - pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMj Hh Hr) as E; injection E as -> -> ->.
      assert (Hlt : j < ind_ndecl D) by (eapply decl_member_lt; eassumption).
      assert (HgP : glu_args Δ (im_params D Mj) Id nil (Us' ++ Q) (ups ++ bs)).
      { unfold im_params; apply glu_args_app; [ exact (decl_closed_ass _ Hc) | exact LU | rewrite Hu; reflexivity |].
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
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dq & Mkc & Hq & HMkc & Hkd & HIl & _ & Hvm & _).
      pose proof (valid_groups_containers VP HVP p D j Mj qc kc Is vm Dq HPD HMj Hh Hq) as HPq.
      pose proof (valid_groups_valid VP HVP qc Dq HPq) as HgQ.
      pose proof (HGall _ _ HPq) as HGq.
      assert (Hhc : exists pmc, im_head Mkc = mh_decl pmc).
      { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMkc) Hkd) as Hd.
        unfold im_is_decl in Hd; destruct (im_head Mkc); [ eauto | discriminate ]. }
      destruct Hhc as [pmc Hhc].
      assert (Hlpre : List.length pre = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ Epy); exact HIl).
      pose proof (view_uparams_glu VP p D HVP HPD HG j Mj qc kc Is vm Dq HMj Hh Hq Δ Us' ups pre HΔ HUs Epy) as HUc.
      pose proof (view_nparams_glu VP p D HVP HPD j Mj qc kc Is vm Dq HMj Hh Hq Δ Us' Q ups bs pre kc Mkc j Mj HΔ Hu HUs
                    HMkc Hvm HMj HNs Epy) as HNc.
      assert (HPc : glu_args Δ (im_params Dq Mkc) Id nil (List.map (fun I => I[sb_of_list Id Us']) Is ++ Q) (pre ++ bs)).
      { unfold im_params; apply glu_args_app; [ exact (decl_closed_ass _ (valid_group_closed _ _ HgQ)) | rewrite List.length_map; exact HIl
                                              | exact Hlpre |].
        split; [ exact HUc | exact HNc ]. }
      destruct (ind_glu_of_per qc Dq (valid_group_lookup _ _ HgQ) (ul i) R kc Mkc pmc pre bs HMkc Hhc HR Hlpre)
        as [NP2 NEl2 AP2 AEl2 DP2 DEl2 P2 El2 R2 Hg2 HP2 HEl2 HR2 Hf2].
      destruct (vg_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMj Hh Hq ups ups Hgu Hu) as (c0 & c0' & E0 & _ & Hc0).
      pose proof (functional_eval_exps' _ _ _ _ E0 Epy) as ->.
      destruct (sort_value Dq (valid_group_valid _ _ HgQ) pre ltac:(eapply uparams_refl_l; [ exact (valid_group_valid _ _ HgQ)
                                                                                     | exact (valid_group_closed _ _ HgQ) | exact Hc0 ]) Hlpre)
        as [bq Ebq].
      assert (Hle' : uidx_le (Completeness.Inductives.Decl.univ_idx bq) (ul i))
        by (eapply uidx_le_trans; [ exact (Hnbq _ _ _ _ _ _ _ HMj Hh Hq _ _ Ebq) | exact (ul_mono _ _ Hi) ]).
      assert (HT2 : Δ ⊢ im_ty_at p j Mj Us' Q ® P2).
      { apply HP2; exists (List.map (fun I => I[sb_of_list Id Us']) Is ++ Q).
        unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
        exact (ind_typ_at_of_args qc Dq (valid_group_lookup _ _ HgQ) HGq (valid_group_closed _ _ HgQ) (valid_group_typed _ _ HgQ) (valid_group_sort _ _ HgQ)
                 (valid_group_ass _ _ HgQ) kc Mkc Δ _ pre bs bq (ul i) NP2 NEl2 AP2 AEl2 DP2 DEl2 HMkc Hkd HΔ HPc Hlpre Ebq Hle' Hf2). }
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
      pose proof (ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hms Hc0 eq_refl Hws HB Hys Eb1) as HgD.
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
        * exact (glu_args_wk _ _ _ _ _ _ _ (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) Hφ HUs).
        * unfold OTy; apply shape_ty_step; rewrite LU; reflexivity.
        * exact (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ HMt).
        * replace (ups ++ ms ++ ws ++ ys ++ m :: nil) with ((ups ++ ms ++ ws ++ ys) ++ m :: nil)
            by (rewrite <- !List.app_assoc; reflexivity).
          rewrite env_args_snoc; exact Ea2s.
  Qed.

  (** ** Recursive Arguments

      At the end of a shape, the argument is an element of the member the
      shape ends in, glued at its type by the induction. *)
  Lemma rec_at_self : forall j Mj Ps pre A Us Γ N v k, ind_member D j = Some Mj ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr -> A = im_ty_at p j Mj Us Q ->
         List.length Q = im_nn Mj /\ tele_rel (nr j) (List.rev (im_nparams Mj)) bsr bsr /\
         (forall bsr', tele_rel (nr j) (List.rev (im_nparams Mj)) bsr bsr' ->
            glu_nparams j Mj NEl Γ Us Q bsr' /\
            forall Δ φ, Δ ⊢ᵏ φ : Γ -> glu_params_top D Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (ups ++ bsr'))) ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr -> A = im_ty_at p j Mj Us Q ->
         forall Δ φ Us' Q', Δ ⊢ᵏ φ : Γ -> List.length Us' = ind_nu D ->
           exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
           elem_glu_at_type j Δ Us' Q' N[φ]ʷ v) ->
      rec_glu_at_type k Γ Us pre (pt_self j Ps) A N v.
  Proof.
    intros * HMj Hs1 IH; unfold rec_glu_at_type.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σs a i P El HMk Hc0 Hpre Hms Hws Hsk Hys HUs HA HN Ea HRv Hglu HAP.
    destruct (eval_shty_self_inv _ _ _ _ Ea) as (bs & pc & kc & pre' & Ebs & Hr & ->).
    assert (HAQ : A = im_ty_at p j Mj Us (List.map (fun P0 => P0[σs]) Ps))
      by (rewrite HA; cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
    destruct (Hs1 _ _ Ebs HAQ) as (_ & Hbs & Hgn).
    destruct (Hgn _ Hbs) as [Hgn' Htop].
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    pose proof (kripke_id _ HΓ) as Hid.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof (IH _ _ Ebs HAQ Γ wk_id Us (List.map (fun P0 => P0[σs]) Ps) Hid LU
                  ltac:(pose proof (glu_params_top_refl _ _ _ _ _ (Htop _ _ Hid)) as H; rewrite map_wk_id in H;
                        rewrite map_wk_id; exact H)) as He.
    rewrite exp_wk_id in He.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    pose proof (proj1 (mref_rel j Mj pc kc pre' bs i R HMj Hr HR v v) (HRv _ HR)) as HGv.
    rewrite HAQ in HN, HAP |- *.
    exact (He Mj bs pc kc pre' i P El HMj Hr HUs HN Hgn' Hbs HGv Hglu HAP).
  Qed.

  (** At a domain of a shape, the argument is a function of the domain,
      glued at the [Π] by the induction at the rest of the shape. *)
  Lemma rec_at_pi : forall A Γ k pre B v Us t N,
      (forall IT OT, A = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP k pre B) ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Γ -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
         glu_rec p D ups NEl AEl DP DEl k Δ (List.map (fun U => U[φ]ʷ) Us) (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Γ -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
         rec_glu_at_type k Δ (List.map (fun U => U[φ]ʷ) Us) (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
      rec_glu_at_type k Γ Us pre (pt_pi B t) A N v.
  Proof.
    intros * Hq1 Hq2 Hq3 IH; unfold rec_glu_at_type.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σs a i P El HMk Hc0 Hpre Hms Hws Hsk Hys HUs HA HN Ea HRv Hglu HAP.
    subst pre A.
    destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hsk'].
    cbn [ptyp_ty_at] in Hq1, Hq2, Hq3, IH, HN, HAP |- *.
    set (IT := B[σs]) in *.
    set (OTy := ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us) (q σs) t) in *.
    specialize (Hq1 _ _ eq_refl); specialize (Hq2 _ _ eq_refl); specialize (Hq3 _ _ eq_refl); specialize (IH _ _ eq_refl).
    destruct (eval_shty_pi_inv _ _ _ _ Ea) as (b1 & Eb1 & ->).
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    (** At a universe above the clause's and [nb]. *)
    set (L := Nat.max i nb).
    assert (HiL : uidx_le i (ul L)) by (apply uidx_le_ul_max; unfold L; cbn; lia).
    assert (HuL : uidx_le u (ul L)) by (eapply uidx_le_trans; [ exact Hnbu | apply ul_mono; unfold L; lia ]).
    destruct (glu_univ_elem_cumu_ge_uidx HiL Hglu) as (PL & ElL & HgL).
    pose proof (glu_univ_elem_typ_cumu_ge_uidx HiL Hglu HgL HAP) as HAPL.
    enough (HNL : Γ ⊢ N : Π IT OTy ® v ∈ ElL)
      by (eapply glu_elem_retype; [ exact HgL | exact Hglu | exact HAPL | exact HNL | exact HAP ]).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R0 HR0].
    destruct (glu_univ_elem_per_univ _ _ _ _ HgL) as [RL HRL].
    assert (HRvL : RL v v).
    { apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ (per_univ_elem_cumu_uidx _ _ _ _ HR0 _ HiL) HRL).
      exact (HRv _ HR0). }
    pose proof HRL as HRsave.
    basic_invert_per_univ_elem HRL.
    match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
    match goal with H : _ <~> (fun _ _ => forall _ _ _, rel_mod_app _ _ _ _ _) |- _ => rename H into HRE end.
    destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' HgL) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & HEleq).
    pose proof (ind_fams_glu_dom_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hms Hc0 eq_refl Hws HB Hys Eb1) as HgD.
    pose proof (glu_univ_elem_univ_lvl_gen _ _ _ _ HgL _ _ HAPL) as HTyt; cbn [ulvl] in HTyt.
    destruct (wf_pi_inversion' HTyt) as [HITt HOTt].
    assert (HIT : forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® IP).
    { intros Δ φ Hφ.
      eapply (glu_typ_transfer u (ul L) (ul L)); [ exact HuL | apply uidx_le_refl | eexists; exact equiv_a_a' | exact HgD
                                                 | exact Hgb1 | exact (Hq1 _ _ Hφ) ]. }
    apply HEleq; eapply mk_pi_glu_exp_pred with (IT := IT) (OT := OTy);
      [ exact HN | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRsave Hper); exact HRvL
      | apply wf_exp_eq_refl; exact HTyt | exact HITt | exact HOTt | exact HIT |].
    intros Δ φ N0 n Hφ HN0 equiv_n.
    pose proof (rel_dr k (ms ++ ws ++ ys) B b1 (ul L) in_rel n Eb1 equiv_a_a' equiv_n) as Hdr.
    assert (HbD : Δ ⊢ N0 : IT[φ]ʷ ® n ∈ DEl k (ms ++ ws ++ ys) B).
    { eapply glu_elem_retype; [ exact Hgb1 | exact HgD | exact (glu_univ_elem_trm_typ _ _ _ _ Hgb1 _ _ _ _ HN0) | exact HN0
                              | exact (Hq1 _ _ Hφ) ]. }
    destruct (Hq2 _ _ _ _ Hφ Hdr HbD) as [fc Efc].
    pose proof (Hq3 _ _ _ _ _ Hφ Hdr HbD Efc) as Hgr'.
    pose proof (IH _ _ _ _ _ Hφ Hdr HbD Efc) as IH'.
    destruct (Hcod _ _ equiv_n) as [a2 a2' Ea2 Ea2' Ha22].
    assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (Hcodg _ equiv_n _ Ea2) as Hga2.
    pose proof (eval_fam_cod_shfam_inv _ _ _ _ _ _ Ea2) as Ea2s.
    assert (Ea2s' : ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ (ms ++ ws ++ ys) ++ n :: nil) ↘ a2)
      by (replace (ups ++ (ms ++ ws ++ ys) ++ n :: nil) with ((ups ++ ms ++ ws ++ ys) ++ n :: nil)
            by (rewrite <- !List.app_assoc; reflexivity); rewrite env_args_snoc; exact Ea2s).
    destruct (proj1 (HRE v v) HRvL _ _ equiv_n) as [fc1 fc2 Efc1 Efc2 Hfc].
    assert (fc1 = fc) as -> by (eapply functional_eval_app; eassumption).
    assert (fc2 = fc) as -> by (eapply functional_eval_app; eassumption).
    assert (HΔ : ⊢ Δ) by (eapply kripke_dom; exact Hφ).
    pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ HN0) as HN0t.
    pose proof (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ HN0t) as HOTt'.
    assert (Hys' : tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) (S d) (ys ++ n :: nil) (ys ++ n :: nil))
      by (apply tele_prefix_rel_snoc; [ exact Hys |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hdr).
    assert (HUs' : glu_args Δ (ind_uparams D) Id nil (List.map (fun U => U[φ]ʷ) Us) ups)
      by exact (glu_args_wk _ _ _ _ _ _ _ (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) Hφ HUs).
    assert (HOTe : OTy[(ι φ),,N0] = ptyp_ty_at p D (List.map (fun U => U[φ]ʷ) Us) (q σs ⨟ ((ι φ),,N0)) t)
      by (unfold OTy; apply shape_ty_step; rewrite LU; reflexivity).
    exists fc; split; [ exact Efc |].
    eapply (IH' Mk ms c0 gs1 t0 gs2 ws (S d) (ys ++ n :: nil) (q σs ⨟ ((ι φ),,N0)) a2 L); try eassumption.
    - rewrite <- !List.app_assoc; reflexivity.
    - exact (app_wk_typed _ _ _ _ _ _ _ HN Hφ HN0t).
    - intros R' HR'; apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha22 HR'); exact Hfc.
    - eapply (rec_typ_glu t k Δ (List.map (fun U => U[φ]ʷ) Us) _ _ _ fc Hgr' Mk ms c0 gs1 t0 gs2 ws (S d) (ys ++ n :: nil)
                (q σs ⨟ ((ι φ),,N0)) a2 L L); try eassumption; [ rewrite <- !List.app_assoc; reflexivity | lia | unfold L; lia ].
  Qed.

  (** ** Constructors

      The parameters and the arguments of a constructor of the member [k],
      glued in the group, are glued at the closed telescope of its
      arguments: the non-recursive ones at the clause's families, the
      recursive ones by the induction, both against the telescope's types
      at the values before them, which the arguments before them relate. *)
  Section AtCon.
    Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg)
      (Us' Ns' : list exp) (bs vs : list domain) (As : list exp) (Δ' : ctx).
    Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs)
      (HNl' : List.length Ns' = im_nn Mk) (Hbl : List.length bs = (im_unu D Mk + im_nn Mk)%nat)
      (Hvl : List.length vs = List.length gs) (HAl : List.length As = List.length gs)
      (Hb : tele_rel (nr k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs))
      (Hv : tele_rel (ar k (List.skipn (im_unu D Mk) bs) c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs))
      (Hnp : glu_nparams k Mk NEl Δ' Us' Ns' (List.skipn (im_unu D Mk) bs))
      (HAs : forall j N A, List.nth_error As j = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) j = Some A -> Δ' ⊢ N : A)
      (Harg : forall gs1 A0 gs2 N A v, gs = gs1 ++ ca_arg A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Δ' ⊢ N : A ® v ∈ AEl k (List.skipn (im_unu D Mk) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)))
      (Hrec : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec p D ups NEl AEl DP DEl k Δ' Us' (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N v)
      (IH : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          rec_glu_at_type k Δ' Us' (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N v).
    Hypotheses (HΔ' : ⊢ Δ') (HUs : glu_args Δ' (ind_uparams D) Id nil Us' ups)
      (Hia : con_args_rel p D (okr_at D ups nr) nr ar dr k ups ups
               (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs) gs vs vs).
    #[local] Abbreviation X := (List.skipn (im_unu D Mk) bs).

    Lemma ac_lens : List.length Us' = ind_nu D /\ List.length X = im_nn Mk.
    Proof.
      destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
      split; [ exact LU | rewrite List.length_skipn; lia ].
    Qed.

    Lemma ac_params : glu_args Δ' (im_params D Mk) Id nil (Us' ++ Ns') (ups ++ X).
    Proof.
      unfold im_params; apply glu_args_app; [ exact (decl_closed_ass _ Hc) | exact (proj1 ac_lens) | rewrite Hu; reflexivity |].
      split; [ exact HUs | exact (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf k Mk Δ' Us' Ns' X HMk Hnp Hb) ].
    Qed.

    Lemma ac_HΨ : ⊨ cargs_ctx p D Mk gs ++ im_params D Mk.
    Proof.
      pose proof (vg_cargs_sem_all p D Hvg Hcv k Mk c gs HMk Hcon gs nil (eq_sym (List.app_nil_r gs))) as [H _]; exact H.
    Qed.

    (** The instance of the telescope's type at a position. *)
    Lemma ac_inst : forall n g, List.nth_error gs n = Some g ->
        exists A T, List.nth_error (List.rev (cargs_ctx p D Mk gs)) n = Some (ce_ass A) /\
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) n = Some T /\
          T = A[sb_of_list (sb_of_list Id (Us' ++ Ns')) (List.firstn n As)].
    Proof.
      intros n g Hg.
      assert (Hn : n < List.length gs) by (apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) n) as [T HT].
      { rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. }
      destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ET).
      exists A, T; auto.
    Qed.

    Lemma ac_args_prefix : forall n, n <= List.length gs ->
        glu_args Δ' (cargs_ctx p D Mk (List.firstn n gs)) (sb_of_list Id (Us' ++ Ns')) (env_args nil (ups ++ X))
          (List.firstn n As) (List.firstn n vs).
    Proof.
      destruct ac_lens as [LU LX].
      induction n as [| n IHn]; intros Hn; [ cbn; apply glu_args_nil |].
      destruct (nth_error_lt_some' gs n ltac:(lia)) as [g Hg].
      destruct (nth_error_lt_some' As n ltac:(lia)) as [N HN].
      destruct (nth_error_lt_some' vs n ltac:(lia)) as [v Hvn].
      pose proof (IHn ltac:(lia)) as Hpre_g.
      assert (Heq : gs = List.firstn n gs ++ g :: List.skipn (S n) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg), List.firstn_skipn; reflexivity).
      assert (Lgs1 : List.length (List.firstn n gs) = n) by (rewrite List.length_firstn; lia).
      assert (LAs1 : List.length (List.firstn n As) = n) by (rewrite List.length_firstn; lia).
      assert (Lvs1 : List.length (List.firstn n vs) = n) by (rewrite List.length_firstn; lia).
      set (gs1 := List.firstn n gs) in *; set (gs2 := List.skipn (S n) gs) in *.
      set (fa := List.firstn n vs) in *.
      rewrite (firstn_S_snoc _ _ _ Hg), (firstn_S_snoc _ _ _ HN), (firstn_S_snoc _ _ _ Hvn); fold gs1 fa.
      rewrite cargs_ctx_snoc.
      apply glu_args_app; [ apply cargs_ctx_aux_ass | rewrite length_cargs_ctx; lia | rewrite length_cargs_ctx; lia |].
      split; [ exact Hpre_g |].
      destruct (ac_inst n g Hg) as (A & T & HA & HT & ET).
      (** The closed telescope before the argument, related at itself. *)
      assert (HgPA : glu_args Δ' (cargs_ctx p D Mk gs1 ++ im_params D Mk) Id nil ((Us' ++ Ns') ++ List.firstn n As) ((ups ++ X) ++ fa)).
      { destruct (glu_args_length _ _ _ _ _ _ ac_params) as [LP' LB'].
        apply glu_args_app; [ exact (decl_closed_params_ass D k Mk Hc HMk) | exact LP' | exact LB' |].
        split; [ exact ac_params | exact Hpre_g ]. }
      pose proof (glu_args_per_gargs _ _ _ _ _ _ ltac:(apply List.Forall_app; split; [ apply cargs_ctx_aux_ass
                                                                                   | exact (decl_closed_params_ass D k Mk Hc HMk) ])
                    HgPA) as Hpg.
      rewrite <- List.app_assoc in Hpg.
      destruct g as [A0 | t].
      - (** A non-recursive argument. *)
        cbn [cargs_ctx_aux List.app].
        pose proof (cargs_rev_nth_arg p D Mk gs gs1 A0 gs2 Heq) as HA0; rewrite Lgs1, HA in HA0; injection HA0 as ->.
        apply (proj2 (glu_args_snoc Δ' nil _ _ _ _ _ _ _)); split; [| apply glu_args_nil ].
        destruct (vg_arg_types p D Hvg Hcv k Mk c gs gs1 A0 gs2 ups X fa HMk Hcon Heq Hu LX ltac:(lia) Hpg)
          as (i0 & R0 & a & a' & Ea & Ea' & HR0).
        rewrite <- Lgs1 in HN, HT, Hvn.
        rewrite ET in HT.
        pose proof (Harg gs1 A0 gs2 N _ v Heq HN HT Hvn) as HNg.
        set (K := List.length (cargs_nonrec gs1)) in *.
        assert (HBk : List.nth_error (cargs_nonrec gs) K = Some A0)
          by (unfold K; rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        assert (Hpk : tele_prefix_rel (ar k X c) K (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                        (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)))
          by (eapply nonrec_prefix_pre; [ exact Hv | exact Hvl | exact Heq ]).
        rewrite Lgs1 in Hpk; fold fa in Hpk.
        pose proof (ind_fams_glu_arg_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ HMk Hb Hcon HBk Hpk Ea') as Hgb.
        rewrite Lgs1 in HNg; fold fa in HNg.
        destruct (glu_transfer_per_elem u i0 a' a _ _ Δ' _ N v Hgb (per_univ_sym' _ _ _ (ex_intro _ R0 HR0))
                    (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HNg) HNg) as (k' & P' & El' & Hg' & HT' & HM').
        refine (mk_glu_arg _ _ _ _ _ _ k' a P' El' _ Hg' HT' HM').
        rewrite <- env_args_app, <- List.app_assoc; exact Ea.
      - (** A recursive argument. *)
        cbn [cargs_ctx_aux List.app].
        pose proof (cargs_rev_nth_rec p D Mk gs gs1 t gs2 Heq) as HA0; rewrite Lgs1, HA in HA0; injection HA0 as ->.
        apply (proj2 (glu_args_snoc Δ' nil _ _ _ _ _ _ _)); split; [| apply glu_args_nil ].
        rewrite <- Lgs1 in HN, HT, Hvn.
        pose proof HT as HT0; rewrite ET in HT.
        set (K := List.length (cargs_nonrec gs1)) in *.
        set (nv := nonrec_arg_vals gs1 fa) in *.
        assert (Hpk : tele_prefix_rel (ar k X c) K nv nv)
          by (unfold nv, fa; rewrite <- Lgs1; eapply nonrec_prefix_pre; [ exact Hv | exact Hvl | exact Heq ]).
        (** The closed type at the values before, and its relation. *)
        destruct (vg_cargs_sem_all p D Hvg Hcv k Mk c gs HMk Hcon (gs1 ++ ca_rec t :: nil) gs2
                    ltac:(rewrite <- List.app_assoc; exact Heq)) as [HW1 _].
        rewrite cargs_ctx_snoc in HW1; cbn [cargs_ctx_aux List.app] in HW1.
        destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HW1) as [jc HAc].
        pose proof (rel_ctx_wf_tail HW1) as HW0.
        destruct (rel_ctx_wf_per_ctx_env HW0) as [R0 HR0].
        assert (HE0 : R0 (env_args nil (ups ++ X ++ fa)) (env_args nil (ups ++ X ++ fa))).
        { apply (gargs_env_rel _ _ _ _ _ _ HR0 HW0);
            [ rewrite !List.length_app, length_cargs_ctx, length_im_params, LX; unfold im_np, ind_nu in *; lia |].
          exact Hpg. }
        destruct (rel_exp_of_typ_inversion_simple_at HR0 HAc _ _ HE0) as (acl & acl' & Eacl & Eacl' & [Rcl HRcl]).
        assert (acl' = acl) as -> by (eapply functional_eval_exp; eassumption).
        assert (Hpre_env : forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk
                                        ∈ per_ctx_env ↘ R ->
                             R (env_args nil (ups ++ X ++ fa)) (env_args nil (ups ++ X ++ fa))).
        { intros R HR; apply (per_ctx_env_right_irrel _ _ _ _ _ HR0 HR); exact HE0. }
        pose proof (fun Mj qc kc Is vm Dq cups cs bs0 bs0' =>
                      ViewReadback.view_end_type VP HVP p D HPD ups Hgu Hu (ptyp_mem t) Mj qc kc Is vm Dq cups cs bs0 bs0') as Hend.
        destruct (shty_link p D Hvg Hcv k Mk c gs HMk Hcon ac_HΨ gs1 t gs2 Heq ups X fa Hu LX ltac:(lia) Hgu Hb Hpk Hpre_env Hend
                    (List.length (ptyp_doms t)) 0 nil acl jc Rcl ltac:(lia) (tele_prefix_rel_nil _) ltac:(cbn; apply per_gargs_nil)
                    ltac:(cbn [List.repeat List.app ptyp_skip]; rewrite List.app_nil_r; exact Eacl) HRcl)
          as (bsh & Ebsh & Hab).
        cbn [ptyp_skip] in Ebsh; rewrite List.app_nil_r in Ebsh; fold nv in Ebsh.
        pose proof (shape_char p D Hvg Hcv k Mk c gs HMk Hcon ac_HΨ gs1 t gs2 Heq ups X fa Hu LX ltac:(lia) Hgu Hb Hpk Hpre_env
                      (Completeness.Inductives.Con.view_end_rel_all VP p D HVP HPD ups ups Hgu Hu (ptyp_mem t))
                      (List.length (ptyp_doms t)) 0 nil acl jc Rcl ltac:(lia) (tele_prefix_rel_nil _)
                      ltac:(cbn; apply per_gargs_nil)
                      ltac:(cbn [List.repeat List.app ptyp_skip]; rewrite List.app_nil_r; exact Eacl) HRcl) as ERcl.
        destruct (Elim.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & x' & Hx & Hx' & Hra).
        rewrite Hvn in Hx; injection Hx as <-; rewrite Hvn in Hx'; injection Hx' as <-.
        assert (HRv : Rcl v v).
        { apply ERcl; cbn [ptyp_skip]; rewrite List.app_nil_r; unfold nv, fa; rewrite <- Lgs1; exact Hra. }
        (** At a universe above the type's, [nb] and the closed type's. *)
        destruct (presup_exp (HAs _ _ _ HN HT0)) as [_ [jT HjT]].
        set (L := Nat.max (Nat.max jc nb) jT).
        destruct Hab as [Rab HRab].
        pose proof (per_univ_elem_cumu_ge jc L _ _ _ ltac:(unfold L; lia) HRab) as HRabL.
        pose proof (per_univ_elem_cumu_ge jc L _ _ _ ltac:(unfold L; lia) HRcl) as HRclL.
        destruct (per_univ_glu_univ_elem L _ (ex_intro _ Rcl HRclL)) as (PL & ElL & HgL).
        pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ Rab HRabL) HgL) as HgLs.
        assert (HUl0 : List.length (Us' ++ Ns') = im_np D Mk) by (rewrite List.length_app, LU, HNl'; unfold im_np; lia).
        pose proof (cargs_rec_type_sh p D Mk gs gs1 t gs2 (Us' ++ Ns') As _ Heq Hc HUl0 HT0) as HTeq.
        rewrite firstn_app_exact in HTeq by exact LU.
        assert (Hc0 : ind_con Mk c = Some (gs1 ++ ca_rec t :: gs2)) by (rewrite <- Heq; exact Hcon).
        assert (Hpre_eq : X ++ nv = X ++ nv ++ nil) by (rewrite List.app_nil_r; reflexivity).
        pose proof (Hrec gs1 t gs2 N _ v Heq HN HT0 Hvn) as Hr0.
        pose proof (IH gs1 t gs2 N _ v Heq HN HT0 Hvn) as HI0.
        rewrite Lgs1 in Hr0, HI0; fold fa nv in Hr0, HI0.
        pose proof (rec_typ_glu t k Δ' Us' (X ++ nv) _ N v Hr0
                      Mk X c gs1 t gs2 nv 0 nil _ bsh jT L PL ElL HMk Hc0 Hpre_eq Hb Hpk eq_refl (tele_prefix_rel_nil _)
                      HUs HTeq HjT Ebsh ltac:(unfold L; lia) ltac:(unfold L; lia) HgLs) as HTP.
        assert (HRvs : forall R', DF bsh ≈ bsh ∈ per_univ_elem L ↘ R' -> R' v v).
        { intros R' HR'.
          apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRabL HR').
          apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRclL HRabL); exact HRv. }
        pose proof (HI0 Mk X c gs1 t gs2 nv 0 nil _ bsh L PL ElL HMk Hc0 Hpre_eq Hb Hpk eq_refl
                      (tele_prefix_rel_nil _) HUs HTeq (HAs _ _ _ HN HT0) Ebsh HRvs HgLs HTP) as HNg.
        rewrite <- ET.
        refine (mk_glu_arg _ _ _ _ _ _ (ul L) acl PL ElL _ HgL HTP HNg).
        rewrite <- env_args_app, <- List.app_assoc; exact Eacl.
    Qed.

    (** The type of the constructor's application at the parameters and
        arguments: the member's type at the parameters. *)
    Lemma ac_ty : (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))
                    [sb_of_list Id ((Us' ++ Ns') ++ As)] = im_ty_at p k Mk Us' Ns'.
    Proof.
      destruct ac_lens as [LU _].
      destruct (im_head Mk) as [pm | qc kc Is vm] eqn:Hh.
      - rewrite (con_codomain_inst p D k Mk pm gs HMk Hh) by (rewrite !List.length_app; unfold im_np; lia).
        rewrite firstn_app_exact by (rewrite List.length_app; unfold im_np; lia).
        symmetry; exact (im_ty_at_decl p k Mk pm Us' Ns' Hh).
      - rewrite <- List.app_assoc, <- HAl.
        rewrite (view_ty_inst p D k Mk qc kc Is vm Id Us' Ns' As Hc HMk Hh LU HNl').
        unfold im_ty_at, im_ref, im_pre; rewrite Hh; reflexivity.
    Qed.

    (** The constructor, glued at its type's gluing at any level: through
        [con_base] (declared) or [con_view_base] (view) at the value of the
        constructor's codomain, which is related to the type's value, and
        at the stored uniform parameters [pre] the type is at. *)
    Lemma elem_at_con : forall hd k' M', im_ref p k Mk = (hd, k') ->
        Δ' ⊢ M' ≈ apps (a_con p k c) (Us' ++ Ns' ++ As) : im_ty_at p k Mk Us' Ns' ->
        elem_glu_at_type k Δ' Us' Ns' M' (d_con hd k' c (bs ++ vs)).
    Proof.
      intros hd k' M' Href HMeq Mk0 ns hd0 k0 pre i P El HMk0 Hr _ _ _ Hns HGm Hglu HT.
      rewrite HMk in HMk0; injection HMk0 as <-.
      destruct (ViewReadback.mref_ref_len p D k Mk ups hd0 k0 pre Hl HMk Hu Hr) as [Href0 Lpre].
      rewrite Href in Href0; injection Href0 as <- <-.
      destruct ac_lens as [LU LX].
      pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
      assert (HassC : tele_ass (cargs_ctx p D Mk gs ++ im_params D Mk))
        by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
      (** All the parameters and arguments, glued. *)
      pose proof (ac_args_prefix (List.length gs) (le_n _)) as HgA.
      rewrite (List.firstn_all2 (n := List.length gs) gs), (List.firstn_all2 (n := List.length gs) As),
        (List.firstn_all2 (n := List.length gs) vs) in HgA by lia.
      assert (HgAll : glu_args Δ' (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil ((Us' ++ Ns') ++ As) ((ups ++ X) ++ vs)).
      { apply glu_args_app; [ exact HassP | rewrite length_im_params, List.length_app; unfold im_np; lia
                            | rewrite length_im_params, List.length_app; unfold im_np; lia |].
        split; [ exact ac_params | exact HgA ]. }
      pose proof (glu_args_per_gargs _ _ _ _ _ _ HassC HgAll) as Hpg.
      destruct (rel_ctx_wf_per_ctx_env ac_HΨ) as [RΨ HRΨ].
      assert (HE : RΨ (env_args nil ((ups ++ X) ++ vs)) (env_args nil ((ups ++ X) ++ vs))).
      { apply (gargs_env_rel _ _ _ _ _ _ HRΨ ac_HΨ); [| exact Hpg ].
        rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
      (** The value of the constructor's codomain there. *)
      destruct (Completeness.Inductives.Elim.mty_vars_valid_at p D Hvg Hcv k Mk (cargs_ctx p D Mk gs) HMk ac_HΨ) as [jb Hjb].
      rewrite length_cargs_ctx in Hjb.
      destruct (rel_exp_of_typ_inversion_simple_at HRΨ Hjb _ _ HE) as (b & b' & Eb & Eb' & [Rb HRb]).
      assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
      rewrite <- List.app_assoc in Eb.
      (** The scrutinee's parameters, related to the stored ones. *)
      assert (Hns' : tele_rel (nr k) (List.rev (im_nparams Mk)) ns X).
      { unfold grp_rel in HGm; inversion HGm; subst.
        match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HMk in H1; injection H1 as <- end.
        match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => apply app_split_eq in E; [| lia ]; destruct E as [-> ->] end.
        assumption. }
      (** The type's value, related to the codomain's. *)
      assert (HZ : ⊨ (cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D) by (rewrite <- List.app_assoc; exact ac_HΨ).
      assert (HRZ : EF (cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D
                      ≈ (cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D ∈ per_ctx_env ↘ RΨ)
        by (rewrite <- List.app_assoc; exact HRΨ).
      pose proof HE as HE0; rewrite <- List.app_assoc in HE0.
      destruct (mty_val_rel k Mk hd k' pre _ RΨ X vs (List.length gs) b ns HMk Hr HZ HRZ
                  ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia) LX Hvl HE0 Eb Hns')
        as (i0 & R0 & Hab).
      pose proof (per_univ_elem_cumu_uidx _ _ _ _ Hab (ul (ulvl i0)) ltac:(apply uidx_le_ul_max; lia)) as Hab'.
      (** The constructor's value, related to the scrutinee. *)
      destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
      pose proof (mref_rel k Mk hd k' pre ns i R HMk Hr HR) as ER.
      assert (Ebs : bs ++ vs = List.firstn (im_unu D Mk) bs ++ (X ++ vs)) by (rewrite List.app_assoc, List.firstn_skipn; reflexivity).
      assert (Hwm : G k ups ups ns ns (d_con hd k' c (pre ++ X ++ vs)) (d_con hd k' c (bs ++ vs))).
      { rewrite Ebs in HGm |- *; unfold grp_rel in *.
        eapply Completeness.Inductives.Elim.ind_rel_con_prefix_l;
          [ exact HMk | | | exact HGm ]; rewrite ?List.length_firstn; lia. }
      assert (Hww : G k ups ups ns ns (d_con hd k' c (pre ++ X ++ vs)) (d_con hd k' c (pre ++ X ++ vs))).
      { rewrite Ebs in Hwm; unfold grp_rel in *.
        eapply Completeness.Inductives.Elim.ind_rel_con_prefix_r;
          [ exact HMk | | | exact Hwm ]; rewrite ?List.length_firstn; lia. }
      assert (HRw : Rb (d_con hd k' c (pre ++ X ++ vs)) (d_con hd k' c (pre ++ X ++ vs))).
      { apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hab HRb).
        apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR Hab).
        apply ER; exact Hww. }
      (** The constructor, glued at the codomain's value. *)
      destruct (sort_bound VP p D HVP HPD) as [n0 Hn0].
      set (ib := Nat.max (Nat.max jb nb) n0).
      pose proof (per_univ_elem_cumu_ge jb ib _ _ _ ltac:(unfold ib; lia) HRb) as HRbL.
      destruct (per_univ_glu_univ_elem ib _ (ex_intro _ Rb HRbL)) as (Pb & Elb & Hgb).
      assert (Hper : forall R', DF b ≈ b ∈ per_univ_elem ib ↘ R' ->
                       R' (d_con hd k' c (pre ++ X ++ vs)) (d_con hd k' c (pre ++ X ++ vs))).
      { intros R' HR'; apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRbL HR'); exact HRw. }
      assert (Hcb : Δ' ⊢ apps (a_con p k c) ((Us' ++ Ns') ++ As)
                      : (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))
                          [sb_of_list Id ((Us' ++ Ns') ++ As)]
                      ® d_con hd k' c (pre ++ X ++ vs) ∈ Elb).
      { destruct (im_head Mk) as [pm | qc kc Is vm] eqn:Hh.
        - pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMk Hh Hr) as E; injection E as Ehd Ek Epre.
          assert (Hw : Completeness.Inductives.Con.con_value p D k Mk c ((ups ++ X) ++ vs) (d_con hd k' c (pre ++ X ++ vs))).
          { rewrite Ehd, Ek, Epre, List.app_assoc; exact (Completeness.Inductives.Con.con_value_decl p D k Mk c pm _ Hh). }
          eapply (con_base VP p D HVP HPD HG (Hviewsall _ _ HPD) k Mk pm c gs HMk Hh Hcon);
            [ exact HΔ' | intros ρ0 b0 Eb0; exact (Hn0 _ _ Eb0 ib ltac:(unfold ib; lia)) | exact HgAll | exact Hw | exact Eb'
            | exact Hgb | exact Hper ].
        - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMk Hh Hr) as (py & E & Epy); injection E as Ehd Ek Epre.
          destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mkc & Hq & HMkc & Hkd & _ & _ & Hvm & _).
          pose proof (valid_groups_containers VP HVP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq) as HPq.
          pose proof (valid_groups_valid VP HVP qc Dq HPq) as HgQ.
          assert (Hhd : exists pmc, im_head Mkc = mh_decl pmc).
          { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMkc) Hkd) as Hd0.
            unfold im_is_decl in Hd0; destruct (im_head Mkc); [ eauto | discriminate ]. }
          destruct Hhd as [pmc Hhc].
          destruct (Completeness.Inductives.Con.view_con_container p D Hass Hdt k Mk qc kc Is vm Dq Mkc c gs HMk Hh Hq HMkc Hcon)
            as (gs' & Hcon' & Hcorr).
          assert (Hw : Completeness.Inductives.Con.con_value p D k Mk c ((ups ++ X) ++ vs) (d_con hd k' c (pre ++ X ++ vs))).
          { rewrite Ehd, Ek.
            replace (pre ++ X ++ vs) with (pre ++ List.skipn (ind_nu D) ((ups ++ X) ++ vs))
              by (rewrite <- List.app_assoc, skipn_app_exact by exact Hu; reflexivity).
            eapply Completeness.Inductives.Con.con_value_view; [ exact Hh | rewrite !List.length_app; lia |].
            rewrite <- List.app_assoc, firstn_app_exact by exact Hu; rewrite Epre; exact Epy. }
          eapply (con_view_base VP HVP HGall Hviewsall p D HPD k Mk qc kc Is vm c gs HMk Hh Hcon Dq Mkc pmc gs' ib);
            [ exact Hq | exact HMkc | exact Hhc | exact Hvm | exact Hcon' | exact Hcorr | exact HΔ'
            | intros ρ0 b0 Eb0; eapply uidx_le_trans; [ exact (Hnbq _ _ _ _ _ _ _ HMk Hh Hq _ _ Eb0) | apply ul_mono; unfold ib; lia ]
            | exact HgAll | exact Hw | exact Eb' | exact Hgb | exact Hper ]. }
      rewrite ac_ty in Hcb.
      (** At the type's gluing, then at the scrutinee's value and term. *)
      pose proof (glu_univ_elem_univ_lvl_gen _ _ _ _ Hglu _ _ HT) as HTy.
      pose proof (glu_elem_conv ib i (ulvl i0) (ulvl i) _ _ _ _ _ _ Δ' _ _ _ _ Hgb Hglu
                    (per_univ_sym' _ _ _ (ex_intro _ R0 Hab')) (wf_exp_eq_refl HTy) HT Hcb) as Hc1.
      pose proof (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hglu _ HR _ _ _ _ _ Hc1 ltac:(apply ER; exact Hwm)) as Hc2.
      rewrite <- List.app_assoc in Hc2.
      exact (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hglu _ _ _ _ _ Hc2 (wf_exp_eq_sym _ _ _ _ _ _ HMeq)).
    Qed.

  End AtCon.

  (** ** The Bridge

      Every element glued in the group, and every recursive argument, is
      glued at its type's own gluing, by induction on the group's gluing. *)
  Theorem glu_at_type_all :
    (forall k Γ Us Ns M mv, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M mv -> elem_glu_at_type k Γ Us Ns M mv) /\
    (forall k Γ Us pre t A N v, glu_rec p D ups NEl AEl DP DEl k Γ Us pre t A N v -> rec_glu_at_type k Γ Us pre t A N v).
  Proof.
    apply (ind_glu_elem_mut_ind_all p D ups NEl AEl DP DEl
             (fun k Γ Us Ns M mv _ => elem_glu_at_type k Γ Us Ns M mv)
             (fun k Γ Us pre t A N v _ => rec_glu_at_type k Γ Us pre t A N v)).
    - intros k Mk hd k' c gs Us Ns bs vs As Γ M HMk Href Hcon HUl HNl Hbl Hvl HAl HMeq Hb Hv Hnp HAs Harg Hrec IH.
      intros Mk0 ns hd0 k0 pre i P El HMk0 Hr HUs HM' Hgn Hns HGm Hglu HT.
      assert (Hia : con_args_rel p D (okr_at D ups nr) nr ar dr k ups ups
                      (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs) gs vs vs).
      { unfold grp_rel in HGm; inversion HGm; subst.
        match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HMk in H1; injection H1 as <- end.
        match goal with H1 : ind_con Mk c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
        repeat match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => apply app_split_eq in E; [| lia ]; destruct E as [-> ->] end.
        assumption. }
      assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
      exact (elem_at_con k Mk c gs Us Ns bs vs As Γ HMk Hcon HNl Hbl Hvl HAl Hb Hv Hnp HAs Harg Hrec IH HΓ HUs Hia
               hd k' M Href HMeq Mk0 ns hd0 k0 pre i P El HMk0 Hr HUs HM' Hgn Hns HGm Hglu HT).
    - intros k Mk hd k' m Γ Us Ns M as' HMk Href Hm Hrb.
      exact (elem_at_neut k Mk hd k' m Γ Us Ns M as' HMk Href Hm Hrb).
    - intros j Mj Ps pre A Us Γ N v k HMj Hs1 _ IH.
      exact (rec_at_self j Mj Ps pre A Us Γ N v k HMj Hs1 IH).
    - intros A Γ k pre B v Us t N Hq1 Hq2 Hq3 IH.
      exact (rec_at_pi A Γ k pre B v Us t N Hq1 Hq2 Hq3 IH).
  Qed.

End AtType.

(** ** A Level Above the Containers' Sorts

    A group of a valid family has finitely many views, each of a valid
    container, whose sort is bounded ([sort_bound]): a level above all of
    them and a given index, as [AtType]'s [nb] needs. *)
Lemma views_sort_bound : forall VP p D, valid_groups VP -> VP p D ->
    forall l, (forall Mj, In Mj l -> exists j, ind_member D j = Some Mj) ->
    exists n, forall Mj qc kc Is vm Dq, In Mj l -> im_head Mj = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
      forall ρ bq, ⟦ ind_sort Dq ⟧ ρ ↘ bq -> uidx_le (Completeness.Inductives.Decl.univ_idx bq) (ul n).
Proof.
  intros VP p D HVP HPD; induction l as [| M l IH]; intros Hin.
  - exists 0; intros * [].
  - destruct (IH (fun Mj H => Hin Mj (or_intror H))) as [n Hn].
    destruct (im_head M) as [pm | qc kc Is vm] eqn:Hh.
    + exists n; intros * [<- | H] Hh' Hq; [ rewrite Hh in Hh'; discriminate | exact (Hn _ _ _ _ _ _ H Hh' Hq) ].
    + destruct (Hin M (or_introl eq_refl)) as [j Hj].
      destruct (decl_typed_view _ _ _ (valid_group_typed _ _ (valid_groups_valid VP HVP p D HPD)) _ _ _ _ _ _ Hj Hh) as (Dq0 & _ & Hq0 & _).
      destruct (sort_bound VP qc Dq0 HVP (valid_groups_containers VP HVP p D j M qc kc Is vm Dq0 HPD Hj Hh Hq0)) as [m Hm].
      exists (Nat.max n m); intros * [<- | H] Hh' Hq ρ bq Eb.
      * rewrite Hh in Hh'; injection Hh' as <- <- <- <-; rewrite Hq0 in Hq; injection Hq as <-.
        exact (Hm _ _ Eb (Nat.max n m) ltac:(lia)).
      * eapply uidx_le_trans; [ exact (Hn _ _ _ _ _ _ H Hh' Hq _ _ Eb) | apply uidx_le_ul_max; cbn; lia ].
Qed.

Lemma nb_exists : forall VP p D, valid_groups VP -> VP p D -> forall u : uidx,
    exists nb : nat, uidx_le u (ul nb) /\
      forall j Mj qc kc Is vm Dq, ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
        ind_lookup gc_deps gc_stack qc = Some Dq -> forall ρ bq, ⟦ ind_sort Dq ⟧ ρ ↘ bq ->
        uidx_le (Completeness.Inductives.Decl.univ_idx bq) (ul nb).
Proof.
  intros VP p D HVP HPD u.
  destruct (views_sort_bound VP p D HVP HPD (ind_members D) (fun Mj H => List.In_nth_error _ _ H)) as [n Hn].
  exists (Nat.max n (ulvl u)); split; [ apply uidx_le_ul_max; lia |].
  intros * HMj Hh Hq ρ bq Eb.
  eapply uidx_le_trans; [ exact (Hn _ _ _ _ _ _ (List.nth_error_In _ _ HMj) Hh Hq _ _ Eb) | apply uidx_le_ul_max; cbn; lia ].
Qed.

End Fixed_GCtx.
