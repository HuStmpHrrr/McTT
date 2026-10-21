(** * The Eliminator of a Group in the Gluing Model

    The soundness counterpart of [Core/Completeness/Inductives/Elim.v]: an
    elimination of a member of a group, by its blocks, is glued at the
    motive's instance, by induction on the gluing of the scrutinee in the
    group.  On a constructor, the branch of its member's block is glued at
    the substitution of the constructor's non-uniform parameters, its
    arguments and the recursive results, and the type of the motive is the
    branch's through the equation [ι] gives.  On a neutral, the eliminator
    reads back as the stuck one: at a declared member the group's, at a
    view the container's (E1′), whose branches the view's read at fresh
    variables and, where the view nests through an argument, at the
    eliminator stuck at a member of lower rank.  The values the gluings are
    at are related to those the evaluation reaches through the PER model,
    as [Core/Completeness/Inductives/Elim.v] and
    [Core/Semantic/Inductives/IndElim.v] relate them. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes ViewBranch.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.Inductives Require Elim.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.LogicalRelation Require Instance.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
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
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon ElimBase.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Blocks, Glued

    The gluing premises of an eliminator's blocks at uniform parameters
    [Us]: each block's motive in its member's context, and each branch at
    its type in its context. *)
#[warnings="-cannot-define-projection"]
Record glu_blocks (Γ : ctx) (p : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock) (i : nat) : Prop := mk_glu_blocks
  { gbk_motive : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      elim_mctx p D k Mk Us ++ Γ ⊩ eb_motive b : Typeω@i
  ; gbk_branch : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
      elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ⊩ B : elim_bty p k Mk c gs (eb_motive b) Us }.

(** ** The Eliminator, at an Environment

    The group [D] at [p], valid; the context [Γ] of the eliminator, the
    uniform parameters [Us] and the blocks [Bks] there; an environment [ρ]
    of [Γ], at which [Us] are [ups]; and the gluings of the clause of
    [d_ind] at [ups]. *)
Section ElimGlu.
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hvg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := vgr_lookup _ _ Hvg.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hsu := vgr_sort _ _ Hvg.
  Let Hass := vgr_ass _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := dc_ass _ Hc.
  Let Usem : ⊨ ind_uparams D := vid_uparams _ HD.

  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (SbΓ : glu_sub_pred).
  Hypothesis (HSbΓ : EG Γ ∈ glu_ctx_env ↘ SbΓ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).

  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUt : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊢ N : T)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T)
    (HUg : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊩ N : T).
  Let τU := sb_of_list Id Us.

  Variable (Bks : list eblock) (iA : nat).
  Hypotheses (HBt : blocks_typed gc_deps gc_stack Γ p D Us Bks iA) (HBv : valid_blocks p D Γ Us Bks iA)
    (HBg : glu_blocks Γ p D Us Bks iA).
  Let HBks := vbs_has _ _ _ _ _ _ HBv.
  Let HMall := vbs_mctx _ _ _ _ _ _ HBv.
  Let HAv := vbs_motive _ _ _ _ _ _ HBv.

  Variable (ρ : env) (ups : list domain).
  Hypotheses (Hρ : RΓ ρ ρ) (HUv : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ups).

  Variable (bu : domain) (u : uidx)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypotheses (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).

  #[local] Abbreviation nr := (canon_nparams_rel D ups).
  #[local] Abbreviation ar := (canon_args_rel D ups).
  #[local] Abbreviation dr := (canon_doms_rel ups).
  #[local] Abbreviation G := (grp_rel p D ups nr ar dr).
  #[local] Abbreviation EB f := (f VP p D HVP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ρ ups Hρ HUv).

  (** ** What an Elimination Yields

      An element [mv] of the member [k], its type's non-uniform parameters
      [ns]: the value of the eliminator at it, the value of the motive of
      [k]'s block at it, and the elimination of a term [M'] of it, at the
      instance of the blocks by [σ'], glued at the motive there.  The
      motive is [List.nth k (blocks_motives Bks) a_True]: every member has
      its block ([bt_len]), so the default is never taken. *)
  #[warnings="-cannot-define-projection"]
  Record elim_out (k : nat) (Mk : imember) (Δ' : ctx) (σ' : sub) (oq' : option qname) (Ns' : list exp) (M' : exp)
      (mv : domain) (ns : list domain) : Prop := mk_elim_out
    { eo_val : domain
    ; eo_motive : domain
    ; eo_eval : ⟦elim mv at k of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ eo_val
    ; eo_eval_motive : ⟦ List.nth k (blocks_motives Bks) a_True ⟧ env_args ρ (ns ++ mv :: nil) ↘ eo_motive
    ; eo_per : Dom eo_motive ≈ eo_motive ∈ per_univ iA
    ; eo_glu : forall P El, DG eo_motive ∈ glu_univ_elem iA ↘ P ↘ El ->
        Δ' ⊢ a_elim oq' (List.map (fun U => U[σ']) Us) k (blocks_sub Bks σ') M'
          : (List.nth k (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mk)) σ'][sb_of_list Id (Ns' ++ M' :: nil)] ® eo_val ∈ El }.

  (** The motive of the induction on the gluing of an element of the member
      [k] at the uniform parameters [Us'] and non-uniform ones [Ns']: at a
      substitution [σ'] glued to [ρ] that sends [Us] to [Us'], the
      elimination of the element is glued. *)
  Definition elim_prop (k : nat) (Δ' : ctx) (Us' Ns' : list exp) (M' : exp) (mv : domain) : Prop :=
    forall Mk σ' oq' ns, ind_member D k = Some Mk -> elim_grp D oq' p k ->
      Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> Us' = List.map (fun U => U[σ']) Us -> Δ' ⊢ M' : im_ty_at p k Mk Us' Ns' ->
      glu_nparams k Mk NEl Δ' Us' Ns' ns -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns ->
      G k ups ups ns ns mv mv ->
      elim_out k Mk Δ' σ' oq' Ns' M' mv ns.

  (** The motive at a recursive argument [N] of shape [t], of a constructor
      [c0] of the member [k], after [d] domains of the shape of the
      argument at the uniform parameters [Us'], the values [pre] of the
      shape's components: its recursive result is glued at the type of the
      recursive result. *)
  Definition rec_prop (k : nat) (Δ' : ctx) (Us' : list exp) (pre : list domain) (t : ptyp) (A : typ) (N : exp) (v : domain) : Prop :=
    forall Mk ms c0 gs1 t0 gs2 ws d ys σ' oq' σs r a (j : nat) R P El,
      ind_member D k = Some Mk -> ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) -> pre = ms ++ ws ++ ys ->
      tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
      tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
      ptyp_skip d t0 = t -> tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) d ys ys ->
      (oq' = Some p \/ oq' = None) -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> Us' = List.map (fun U => U[σ']) Us ->
      A = ptyp_ty_at p D Us' σs t -> Δ' ⊢ N : A ->
      rec_arg_rel p D (okr_at D ups nr) nr ar dr k ups ups pre pre t v v ->
      ⟦ih v of t under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
      ⟦ihty v of t under ρ (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ a ->
      DF a ≈ a ∈ per_univ_elem j ↘ R -> R r r -> uidx_le u (ul j) -> iA <= j -> DG a ∈ glu_univ_elem j ↘ P ↘ El ->
      Δ' ⊢ ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σs N t : Typeω@j ->
      Δ' ⊢ ptyp_ih p D oq' Us' (blocks_sub Bks σ') σs N t : ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σs N t ® r ∈ El.

  (** The neutral case at the member [j], which the induction on the ranks
      of the members proves. *)
  Definition neut_ok (j : nat) : Prop :=
    forall Mj hd k' as' e Δ' Us' Ns' M', ind_member D j = Some Mj -> im_ref p j Mj = (hd, k') -> Dom e ≈ e ∈ per_bot ->
      (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (im_ty_at p j Mj Us' Ns')[φ]ʷ) ->
      elim_prop j Δ' Us' Ns' M' (⇑ (d_ind hd k' as') e).

  (** ** The Uniform Parameters *)

  Lemma ups_len : List.length ups = ind_nu D.
  Proof. rewrite (Completeness.Inductives.Model.eval_exps_length _ _ _ HUv); exact HUl. Qed.

  Lemma ups_gargs : per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof. exact (EB Elim.u0_gargs). Qed.

  Lemma ups_RU : RU (env_args nil ups) (env_args nil ups).
  Proof. exact (EB Elim.u0_env). Qed.

  (** The uniform parameters at a substitution glued to [ρ], glued at
      their telescope at [ups]. *)
  Lemma us_glu_args : forall Δ σ, Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
      glu_args Δ (ind_uparams D) Id nil (List.map (fun U => U[σ]) Us) ups.
  Proof.
    intros * Hσ.
    eapply params_glu_args; [ exact Ua | exact (dc_uparams _ Hc) | exact Usem | exact HΓ | exact HRΓ | exact HSbΓ | exact Hσ
                            | rewrite HUl; reflexivity | exact HUs | exact HUg | exact HUv ].
  Qed.

  (** ** The PER Model at [ρ]

      The canonical relations at [ups], and the family of the motives at
      [ρ] on both sides: the eliminator at related elements, and its
      recursive results, are related at it ([per_ind_elim_all]). *)
  Let Hcp := vg_canon p D Hvg ups ups_gargs ups_len.
  #[local] Abbreviation HnP := (icp_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (icp_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (icp_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (icp_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (icp_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (icp_dom_iff _ _ Hcp).
  Let Had := vg_adm p D Hvg ups ups ups_gargs ups_len ups_gargs.
  Let Hups := EB Elim.ups_ok ups ups ups_RU ups_RU ups_len ups_len.
  Let Hnm : blocks_nm_ok D Bks := vbs_nm _ _ _ _ _ _ HBv.
  Let Hna := vbs_names _ _ _ _ _ _ HBv.
  Let Har := vbs_arity _ _ _ _ _ _ HBv.
  Let Hnd := dt_nodup _ _ _ Hdt.
  #[local] Abbreviation Rel := (fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args ρ (ns ++ m :: nil)) (env_args ρ (ns' ++ m' :: nil))).

  Lemma mot_rel : forall j Mj ba bb u u' ns ns' m m', ind_member D j = Some Mj ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> G j u u' ns ns' m m' ->
      exists a a', ⟦ eb_motive ba ⟧ env_args ρ (ns ++ m :: nil) ↘ a /\ ⟦ eb_motive bb ⟧ env_args ρ (ns' ++ m' :: nil) ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns m ns' m'.
  Proof.
    intros * HMj Hba Hbb Hm; rewrite Hba in Hbb; injection Hbb as <-.
    exact (EB Elim.mot_mid ρ Hρ Bks iA HMall j Mj ba (eb_motive ba) HMj Hba (HAv _ _ _ HMj Hba) _ _ _ _ _ _ Hm).
  Qed.

  Lemma br_rel : forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k', ind_member D j = Some Mj ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> ind_con Mj c = Some gs ->
      brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
      G j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
      rec_results_rel dr Rel j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') gs vs vs' ihs ihs' ->
      exists r r', ⟦ Ba ⟧ env_args ρ (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ↘ r /\
        ⟦ Bb ⟧ env_args ρ (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ↘ r' /\
        Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs)) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r'.
  Proof.
    refine (EB Elim.br_mid ρ Hρ Bks iA HBks HMall HAv (vbs_bctx _ _ _ _ _ _ HBv) Bks _).
    intros * HMj Hb Hb' Hcon HlB HlB'; rewrite Hb in Hb'; injection Hb' as <-.
    rewrite HlB in HlB'; injection HlB' as <-.
    exact (vbs_branch _ _ _ _ _ _ HBv _ _ _ _ _ _ _ HMj Hb Hcon (brs_lookup_in _ _ _ _ HlB)).
  Qed.

  #[local] Abbreviation ER f := (f p D ups nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had (ul iA) ρ ρ Bks Bks ups ups Hups Rel
     HBks HBks Hnm Hnm Hna Hna Har Har Hnd mot_rel br_rel).
  Let pelim := ER per_ind_elim_all.

  (** ** Instances of Closed Telescopes at [ρ]

      A type of a closed telescope over the uniform parameters, at its
      instance at [τU] in [ρ] extended by values related at the telescope
      at [ups], against the type at [ups] and those values. *)
  Lemma inst_link : forall Pre X (j : nat) zs, tele_ass (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
      ⊨ tele_sub Pre τU ++ Γ -> Pre ++ ind_uparams D ⊨ X : Typeω@j ->
      per_gargs (List.rev Pre) (env_args nil ups) (env_args nil ups) zs zs -> List.length zs = List.length Pre ->
      exists a b, ⟦ X[sb_qn (List.length Pre) τU] ⟧ env_args ρ zs ↘ a /\ ⟦ X ⟧ env_args nil (ups ++ zs) ↘ b /\
        Dom a ≈ b ∈ per_univ j.
  Proof.
    intros * HKa HK HS HX Hg Hlz.
    pose proof (EB Elim.cv_gen Pre HKa HK HS ρ ρ ups ups Hρ HUv HUv ups_RU ups_RU zs zs Hg Hlz) as Hg'.
    destruct (rel_ctx_wf_per_ctx_env HS) as [RS HRS].
    pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS HS Hρ ltac:(rewrite length_tele_sub; exact Hlz) Hg') as HE.
    destruct (rel_ctx_wf_per_ctx_env HK) as [RK HRK].
    pose proof (EB Elim.closed_pre_base Pre RK HKa HK HRK ρ ups zs ups_RU ups_len Hg Hlz) as HF.
    exact (closed_typ_inst Pre (ind_uparams D) Γ X j τU RΓ RK RS ρ zs (env_args ρ ups) (env_args nil (ups ++ zs))
             HKa HK Ua Usem HΓ HRΓ HRK HRS HX
             (Instance.gsub_valid (Elim.gsub_U VP p D HVP HPD Γ HΓ Us HUl HUs)) HE Hlz
             (Decl.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) HUv) HF).
  Qed.

  (** The type of an entry of the instance at [τU] of a closed telescope,
      against the entry's type at [ups]. *)
  Lemma inst_entry_link : forall C, tele_ass (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D -> ⊨ tele_sub C τU ++ Γ ->
      forall zs, per_gargs (List.rev C) (env_args nil ups) (env_args nil ups) zs zs -> List.length zs = List.length C ->
      forall k A' a, List.nth_error (List.rev (tele_sub C τU)) k = Some (ce_ass A') -> ⟦ A' ⟧ env_args ρ (List.firstn k zs) ↘ a ->
        exists A b (j : nat), List.nth_error (List.rev C) k = Some (ce_ass A) /\
          ⟦ A ⟧ env_args nil (ups ++ List.firstn k zs) ↘ b /\ Dom a ≈ b ∈ per_univ j.
  Proof.
    intros C HCa HCs HCS zs Hpg Hlz k A' a HA' Ea.
    assert (HCa' : tele_ass C) by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
    assert (HeA : exists A, e = ce_ass A).
    { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
      unfold tele_ass in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
    destruct HeA as [A ->].
    pose proof He as He0.
    destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
    rewrite <- HPl in HA'; rewrite nth_rev_tele_sub in HA'; injection HA' as <-.
    rewrite <- List.app_assoc in HCa, HCs; cbn [List.app] in HCa, HCs.
    assert (HKa : tele_ass (Pre ++ ind_uparams D))
      by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [_ H]; inversion H; assumption).
    pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCs) as HK1.
    destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HK1) as [j HX].
    pose proof (rel_ctx_wf_tail HK1) as HK.
    rewrite tele_sub_app, <- List.app_assoc in HCS; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HCS) as HS1.
    cbn [tele_sub List.app] in HS1; pose proof (rel_ctx_wf_tail HS1) as HS.
    rewrite List.rev_app_distr in Hpg; cbn [List.rev] in Hpg; rewrite <- List.app_assoc in Hpg.
    rewrite <- (List.firstn_skipn k zs) in Hpg.
    rewrite !List.length_app in Hlz; cbn in Hlz.
    assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_firstn, List.length_rev; lia).
    destruct (Decl.per_gargs_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
      as [Hg1 _].
    destruct (inst_link Pre A j (List.firstn k zs) HKa HK HS HX Hg1 ltac:(rewrite List.length_firstn; lia)) as (a1 & b & Ea1 & Eb & Hab).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    exists A, b, j; split; [ exact He0 | split; [ exact Eb | exact Hab ] ].
  Qed.

End ElimGlu.

End Fixed_GCtx.
