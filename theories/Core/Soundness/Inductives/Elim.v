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
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con ViewCon Bridge ElimBase AtType.
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
  Hypotheses (HVP : valid_groups VP) (HGall : forall qn G, VP qn G -> glu_ind_decl G)
    (Hviewsall : forall qn G, VP qn G -> glu_views_ok qn G) (HPD : VP p D).
  Let HG := HGall _ _ HPD.
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
  (** A level above [u] and the sorts of the containers of the views, as
      [AtType] needs ([nb_exists] gives one). *)
  Variable (nb : nat).
  Hypotheses (Hnbu : uidx_le u (ul nb))
    (Hnbq : forall j Mj qc kc Is vm Dq, ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
              ind_lookup gc_deps gc_stack qc = Some Dq -> forall ρ bq, ⟦ ind_sort Dq ⟧ ρ ↘ bq ->
              uidx_le (Completeness.Inductives.Decl.univ_idx bq) (ul nb)).

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
  (** The eliminator's PER facts at [ρ] and [ups] ([per_ind_elim_all]); a
      definition, so that its statement stays out of proof contexts. *)
  Definition per_elim_at_ups := ER per_ind_elim_all.

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

  (** Glued arguments of a closed telescope over the uniform parameters,
      at its types at [ups], are glued arguments of its instance at [τU],
      over a substitution glued to [ρ]. *)
  Lemma tele_inst_args : forall C, tele_ass (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D ->
      ⊨ tele_sub C τU ++ Γ -> ctx_scoped (ind_nu D) C ->
      forall Δ' σ' Ms zs, glu_args Δ' C (sb_of_list Id (List.map (fun U => U[σ']) Us)) (env_args nil ups) Ms zs ->
        per_gargs (List.rev C) (env_args nil ups) (env_args nil ups) zs zs ->
        glu_args Δ' (tele_sub C τU) σ' ρ Ms zs.
  Proof.
    intros C HCa HCs HCS HCsc Δ' σ' Ms zs Hg Hpg.
    assert (HCa' : tele_ass C) by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [LM Lz].
    apply (glu_args_link Δ' C (tele_sub C τU) (sb_of_list Id (List.map (fun U => U[σ']) Us)) σ' (env_args nil ups) ρ Ms zs);
      [ rewrite length_tele_sub; reflexivity | | exact Hg | |].
    - rewrite tele_insts_tele_sub; symmetry; apply (tele_insts_base_agree _ (ind_nu D)); [ exact HCa' | exact HCsc |].
      intros x Hx; cbn [sb_compose]; unfold τU; apply sb_of_list_lt_compose; lia.
    - intros k A A' a HA HA' Hk Ea.
      destruct (ctx_rev_split C k _ HA) as (C1 & Pre & -> & HPl).
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
      assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_rev, List.length_firstn; lia).
      destruct (Decl.per_gargs_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
        as [Hg1 _].
      destruct (inst_link Pre A j (List.firstn k zs) HKa HK HS HX Hg1 ltac:(rewrite List.length_firstn; lia)) as (a1 & b & Ea1 & Eb & Hab).
      rewrite <- env_args_app in Ea.
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      exists a1, j; split; assumption.
    - intros k e' He'.
      assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
      assert (HeA : exists A, e = ce_ass A).
      { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
        unfold tele_ass in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
      destruct HeA as [A ->].
      destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
      rewrite <- HPl in He'; rewrite nth_rev_tele_sub in He'; injection He' as <-.
      exists A; split; [ exact He | eexists; reflexivity ].
  Qed.

  (** ** The Motive's Context, Glued

      The instance of the member [j]'s type at a substitution [σ'] glued
      to [ρ] and non-uniform parameters [Ns']. *)
  Lemma mty_inst : forall j Mj σ' Ns', ind_member D j = Some Mj -> List.length Ns' = im_nn Mj ->
      (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))[sb_of_list σ' Ns']
      = im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns'.
  Proof.
    intros * HMj HNl.
    rewrite ind_mty_sub by (try exact Hc; rewrite List.length_map; exact HUl).
    rewrite List.map_map, <- HNl, map_shift_sb_of_list, vars_from_sb_of_list.
    unfold ind_mty; rewrite HMj; reflexivity.
  Qed.

  (** The substitution of the motive's context at glued non-uniform
      parameters and a scrutinee glued at its type's value. *)
  Lemma mctx_glu_sub : forall j Mj SbM, ind_member D j = Some Mj -> EG elim_mctx p D j Mj Us ++ Γ ∈ glu_ctx_env ↘ SbM ->
      forall Δ' σ' Ns' ns M' m hd k' pre, Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      glu_nparams j Mj NEl Δ' (List.map (fun U => U[σ']) Us) Ns' ns ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      (forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
         Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
         Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® m ∈ El) ->
      Δ' ⊢ˢ sb_of_list σ' (Ns' ++ M' :: nil) ® env_args ρ (ns ++ m :: nil) ∈ SbM.
  Proof.
    intros j Mj SbM HMj HSbM * Hσ' Hgn Hns Hr Hgl.
    pose proof (HMall _ _ HMj) as HMm.
    pose proof (rel_ctx_wf_tail HMm) as HNt.
    pose proof (member_params_ass D Hc _ _ HMj) as HPa.
    pose proof (vid_params _ HD _ _ HMj) as HPs.
    pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf j Mj Δ' _ Ns' ns HMj Hgn Hns) as Hg0.
    pose proof (EB Completeness.Inductives.Elim.nparams_closed_of_canon j Mj HMj ns ns Hns) as Hpg.
    pose proof (tele_inst_args (im_nparams Mj) HPa HPs HNt (decl_closed_nparams_scoped D Hc j Mj HMj) Δ' σ' Ns' ns Hg0 Hpg) as Hg1.
    destruct (glu_args_length _ _ _ _ _ _ Hg1) as [LN Ln]; rewrite length_tele_sub, length_im_nparams in LN, Ln.
    assert (HassN : tele_ass (tele_sub (im_nparams Mj) τU)) by (apply tele_ass_sub, (decl_closed_nparams_ass D Hc _ _ HMj)).
    eapply glu_sub_of_list; [ exact (elim_mctx_ass p D j Mj Us Hc HMj) | exact HSbM | exact HSbΓ | exact Hσ' |].
    unfold elim_mctx; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R).
    apply glu_args_app; [ exact HassN | rewrite length_tele_sub, length_im_nparams; exact LN
                        | rewrite length_tele_sub, length_im_nparams; exact Ln |].
    split; [ exact Hg1 |].
    change (ce_ass ?H0 :: nil) with (nil ++ ce_ass H0 :: nil).
    apply (proj2 (glu_args_snoc _ nil _ _ _ _ _ _ _)); split; [| apply glu_args_nil ].
    rewrite (mty_inst j Mj σ' Ns' HMj LN).
    (** The type's value at [ρ] and [ns], against the scrutinee's. *)
    destruct (Completeness.Inductives.Elim.mty_vars_valid p D Hvg Hcv j Mj HMj) as [jx HX].
    destruct (inst_link (im_nparams Mj) _ jx ns HPa HPs HNt HX Hpg ltac:(rewrite length_im_nparams; exact Ln))
      as (a & b & Ea & Eb & Hab).
    unfold τU in Ea; rewrite length_im_nparams, (Completeness.Inductives.Elim.mty_vars_inst p D j Mj Us Hc HUl) in Ea.
    destruct (rel_ctx_wf_per_ctx_env HPs) as [RK HRK].
    assert (HKE : RK (env_args nil (ups ++ ns ++ nil)) (env_args nil (ups ++ ns ++ nil))).
    { rewrite List.app_nil_r.
      apply (gargs_env_rel _ _ _ _ _ _ HRK HPs); [ rewrite !List.length_app, length_im_params, ups_len; unfold im_np, ind_nu in *; lia |].
      exact (Completeness.Inductives.Model.params_gargs D HD Hc Hsu j Mj HMj ups ups bu ns ns ups_gargs ups_len Hbu Hns). }
    replace (ups ++ ns) with (ups ++ ns ++ nil) in Eb by (rewrite List.app_nil_r; reflexivity).
    destruct (mty_val_rel VP HVP p D HPD ups ups_len ups_gargs j Mj hd k' pre (im_nparams Mj) RK ns nil 0 b ns HMj Hr HPs HRK
                ltac:(rewrite List.app_nil_r, length_im_nparams; exact Ln) Ln eq_refl HKE Eb Hns) as (i0 & R0 & H0).
    destruct (Decl.per_univ_elem_to_nat _ _ _ _ H0) as [n0 Hn0].
    assert (Hda : Dom d_ind hd k' (pre ++ ns) ≈ a ∈ per_univ n0)
      by (eapply per_univ_trans'; [ exists R0; exact Hn0 | apply per_univ_sym'; exact Hab ]).
    (** The scrutinee, glued at a gluing of its type's value above [nb]. *)
    assert (Hdd : Dom d_ind hd k' (pre ++ ns) ≈ d_ind hd k' (pre ++ ns) ∈ per_univ n0)
      by (eapply per_univ_trans'; [ exact Hda | apply per_univ_sym'; exact Hda ]).
    set (i := Nat.max n0 nb).
    destruct Hdd as [Rd HRd]; pose proof (per_univ_elem_cumu_ge n0 i _ _ _ ltac:(unfold i; lia) HRd) as HRdi.
    destruct (per_univ_glu_univ_elem i _ (ex_intro _ Rd HRdi)) as (P & El & Hglu).
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    pose proof (mty_glu VP HVP HGall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf nb Hnbu Hnbq
                  j Mj hd k' pre Δ' _ Ns' ns i P El ltac:(unfold i; lia) HMj Hr HΔ' (us_glu_args Δ' σ' Hσ') Hgn Hns Hglu) as HTP.
    pose proof (Hgl i P El ltac:(unfold i; lia) Hglu HTP) as HMg.
    destruct (glu_transfer_per_elem i n0 _ _ P El Δ' _ M' m Hglu Hda HTP HMg) as (k1 & P1 & El1 & Hg1' & HP1 & HM1).
    exact (mk_glu_arg _ _ _ _ _ _ k1 a P1 El1 Ea Hg1' HP1 HM1).
  Qed.

  (** The motive of the member [j]'s block at glued non-uniform parameters
      and scrutinee: its value, and its instance glued at any gluing of
      it. *)
  Lemma motive_glu : forall j Mj Δ' σ' Ns' ns M' m hd k' pre, ind_member D j = Some Mj -> Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      glu_nparams j Mj NEl Δ' (List.map (fun U => U[σ']) Us) Ns' ns ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pre) ->
      (forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
         Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
         Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® m ∈ El) ->
      exists a, ⟦ List.nth j (blocks_motives Bks) a_True ⟧ env_args ρ (ns ++ m :: nil) ↘ a /\ Dom a ≈ a ∈ per_univ iA /\
        forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
          Δ' ⊢ (List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)] ® P.
  Proof.
    intros * HMj Hσ' Hgn Hns Hr Hgl.
    destruct (HBks _ _ HMj) as [b Hb]; rewrite (blocks_motives_nth _ _ _ Hb).
    pose proof (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMj Hb) as HAg.
    destruct HAg as [SbM HSbM iM HAg'].
    pose proof (mctx_glu_sub j Mj SbM HMj HSbM Δ' σ' Ns' ns M' m hd k' pre Hσ' Hgn Hns Hr Hgl) as Hτ.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMj Hb) Hτ) as (_ & a & Ea & Hpa & HPa).
    exists a; split; [ exact Ea | split; [ exact Hpa |] ].
    intros P El Hg; pose proof (HPa P El Hg) as H.
    rewrite <- exp_sub_qn_of_list in H.
    pose proof (gnp_len _ _ _ _ _ _ _ Hgn) as LN.
    replace (List.length (Ns' ++ M' :: nil)) with (S (im_nn Mj)) in H by (rewrite List.length_app, LN; cbn; lia).
    exact H.
  Qed.

End ElimGlu.

End Fixed_GCtx.
