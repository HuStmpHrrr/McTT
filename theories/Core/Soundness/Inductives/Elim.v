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

  (** ** Recursive Results

      The group of the eliminator at a member, as [elim_at] writes it. *)
  Lemma elim_at_grp' : forall oq j Mj, (oq = Some p \/ oq = None) -> ind_member D j = Some Mj ->
      elim_grp D (if ind_has_views D then Some p else oq) p j.
  Proof.
    intros oq j Mj Hoq HMj.
    destruct (ind_has_views D) eqn:Hv; [ left; reflexivity |].
    destruct Hoq as [-> | ->]; [ left; reflexivity | right; split; [ reflexivity |] ].
    apply (dt_order _ _ _ Hdt _ _ HMj); exact (no_views_decl _ _ _ Hv HMj).
  Qed.

  (** At the end of a shape, the recursive result is the eliminator at the
      argument, an element of the member the shape ends in. *)
  Lemma rec_self_case : forall k Δ' Us' pre j0 Mj Ps A N v, ind_member D j0 = Some Mj ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr -> A = im_ty_at p j0 Mj Us' Q ->
         List.length Q = im_nn Mj /\ tele_rel (nr j0) (List.rev (im_nparams Mj)) bsr bsr /\
         (forall bsr', tele_rel (nr j0) (List.rev (im_nparams Mj)) bsr bsr' ->
            glu_nparams j0 Mj NEl Δ' Us' Q bsr' /\
            forall Δ φ, Δ ⊢ᵏ φ : Δ' -> glu_params_top D Mj Δ (List.map (fun P => P[φ]ʷ) (Us' ++ Q)) (ups ++ bsr'))) ->
      (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr -> A = im_ty_at p j0 Mj Us' Q ->
         forall Δ φ Us'' Q', Δ ⊢ᵏ φ : Δ' -> List.length Us'' = ind_nu D ->
           exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us' ++ Q)) (Us'' ++ Q') ->
           elim_prop j0 Δ Us'' Q' N[φ]ʷ v) ->
      rec_prop k Δ' Us' pre (pt_self j0 Ps) A N v.
  Proof.
    intros * HMj Hs1 IH; unfold rec_prop.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σ' oq' σs r a j R P El HMk Hc0 Hpre Hms Hws Hsk Hys Hoq Hσ' HUs' HA HN Hsh Er Ea HR Hr
           Huj HiAj Hg HIT.
    destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs0 & Ebs & Ebs0 & _ & _ & Hir).
    pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->.
    inversion Er; subst.
    match goal with H : ⟦elim v at j0 of _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H into Er' end.
    inversion Ea; subst.
    match goal with H : ⟦ List.nth j0 _ _ ⟧ _ ⍮ _ ⍮ env_args ρ (?b0 ++ v :: nil) ↘ a |- _ => rename H into Ea'; rename b0 into bs' end.
    match goal with H : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ bs' |- _ => pose proof (functional_eval_exps' _ _ _ _ H Ebs) as -> end.
    set (Q := List.map (fun P0 => P0[σs]) Ps) in *.
    assert (HAQ : ptyp_ty_at p D (List.map (fun U => U[σ']) Us) σs (pt_self j0 Ps) = im_ty_at p j0 Mj (List.map (fun U => U[σ']) Us) Q)
      by (cbn [ptyp_ty_at]; unfold ind_mty; rewrite HMj; reflexivity).
    pose proof HN as HN'; rewrite HAQ in HN'.
    destruct (Hs1 _ Q Ebs HAQ) as (HQl & Hbs & Hgn).
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    pose proof (kripke_id _ HΔ') as Hid.
    destruct (Hgn bs Hbs) as [Hgn' Htop].
    assert (HUl' : List.length (List.map (fun U => U[σ']) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
    pose proof (IH _ Q Ebs HAQ Δ' wk_id _ Q Hid HUl'
                  ltac:(pose proof (glu_params_top_refl _ _ _ _ _ (Htop _ _ Hid)) as H; rewrite map_wk_id in H; rewrite map_wk_id; exact H)) as HE.
    rewrite exp_wk_id in HE.
    destruct (HE Mj σ' _ bs HMj (elim_at_grp' oq' j0 Mj Hoq HMj) Hσ' eq_refl HN' Hgn' Hbs Hir) as [r' a' Er'' Ea'' Haa Hgl].
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Er'' Er') as ->.
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Haa) as (P0 & El0 & Hg0).
    pose proof (Hgl P0 El0 Hg0) as HE0.
    cbn [ptyp_ih ptyp_ihty]; unfold elim_at; rewrite (blocks_motives_sub D Bks σ' j0 Mj Hnm HMj).
    eapply glu_univ_elem_exp_cumu_ge; [ exact HiAj | exact Hg0 | exact Hg | exact HE0 ].
  Qed.

  (** The recursive result of a function shape and its type, under the
      binder, at a weakening and an argument. *)
  Lemma ih_body_inst : forall oq σ' σs N t φ e,
      (ptyp_ih p D oq (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (blocks_wk (blocks_sub Bks σ') ↑)
         (q σs) (a_app N[↑]ʷ (a_var 0)) t)[sb_extend (ι φ) e]
      = ptyp_ih p D oq (List.map (fun U => U[sb_wk σ' φ]) Us) (blocks_sub Bks (sb_wk σ' φ))
          (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) t.
  Proof.
    intros; rewrite ptyp_ih_sub
      by (first [ exact Hc | rewrite !List.length_map; exact HUl | apply blocks_nm_ok_wk, blocks_nm_ok_sub, Hnm ]).
    f_equal.
    - rewrite !List.map_map; apply List.map_ext; intros U; rewrite exp_shift_extend_wk_e, exp_wk_sub; reflexivity.
    - apply blocks_step.
    - cbn [exp_sub]; rewrite exp_shift_extend_wk_e; reflexivity.
  Qed.

  Lemma ih_cod_inst : forall σ' σs N t φ e Mm, ind_member D (ptyp_mem t) = Some Mm ->
      List.length (ptyp_ps t) = im_nn Mm ->
      (ptyp_ihty (blocks_motives (blocks_sub Bks σ')) (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t)[sb_extend (ι φ) e]
      = ptyp_ihty (blocks_motives (blocks_sub Bks (sb_wk σ' φ))) Id (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) t.
  Proof.
    intros * HMm HPl; rewrite ptyp_ihty_sub; cbn [exp_sub]; rewrite exp_shift_extend_wk_e.
    rewrite (ptyp_ihty_sb_eq _ _ _ (ι φ ⨟ Id) _ _ _ (fun z => eq_refl) (fun z => eq_refl)).
    apply ptyp_ihty_base.
    rewrite HPl, !(blocks_motives_sub D Bks _ _ Mm Hnm HMm).
    symmetry; apply exp_sub_sub_ext, sb_qn_compose_ext; symmetry; apply sb_wk_compose.
  Qed.

  (** The member a recursive argument's shape ends in, and the shape's
      terms' freedom from module variables. *)
  Lemma rec_shape_facts : forall k Mk c0 gs1 t0 gs2 d, ind_member D k = Some Mk ->
      ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
      (exists Mj, ind_member D (ptyp_mem (ptyp_skip d t0)) = Some Mj /\ List.length (ptyp_ps (ptyp_skip d t0)) = im_nn Mj) /\
      List.Forall (exp_mvc 0) (ptyp_doms (ptyp_skip d t0)) /\ List.Forall (exp_mvc 0) (ptyp_ps (ptyp_skip d t0)).
  Proof.
    intros * HMk Hc0.
    rewrite ptyp_mem_skip, ptyp_ps_skip, ptyp_doms_skip.
    split; [ exact (vid_plen _ HD k Mk c0 _ HMk Hc0 gs1 t0 gs2 eq_refl) |].
    destruct (dmv_members _ (dt_mvc _ _ _ Hdt) _ _ HMk) as (_ & _ & Hcm).
    pose proof (Hcm _ _ (cons_lookup_in _ _ _ Hc0)) as Hf0.
    apply List.Forall_app in Hf0 as [_ Hf0]; inversion Hf0 as [| ? ? Hct _]; subst; cbn in Hct; destruct Hct as [Hd Hp].
    split; [| exact Hp ].
    rewrite <- (List.firstn_skipn d (ptyp_doms t0)) in Hd; apply List.Forall_app in Hd as [_ Hd]; exact Hd.
  Qed.

  (** At a domain of a shape, the recursive result is a function of the
      domain, glued at the [Π] by the induction at the rest of the shape. *)
  Lemma rec_pi_case : forall k Δ' Us' pre B t A N v,
      (forall IT OT, A = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® DP k pre B) ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
      (forall IT OT, A = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Δ' -> dr k pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
         rec_prop k Δ (List.map (fun U => U[φ]ʷ) Us') (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
      rec_prop k Δ' Us' pre (pt_pi B t) A N v.
  Proof.
    intros * Hq1 Hq2 IH3; unfold rec_prop.
    intros Mk ms c0 gs1 t0 gs2 ws d ys σ' oq' σs r a j R P El HMk Hc0 Hpre Hms Hws Hsk Hys Hoq Hσ' HUs' HA HN Hsh Er Ea HR Hr
           Huj HiAj Hg HIT.
    subst A pre Us'.
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hsk'].
    destruct (rec_shape_facts k Mk c0 gs1 t0 gs2 (S d) HMk Hc0) as ((Mj & HMj & HPl) & Hmd & Hmp).
    rewrite Hsk' in HMj, HPl, Hmd, Hmp.
    cbn [ptyp_ty_at ptyp_ih ptyp_ihty] in HN, HIT, Hq1, Hq2, IH3 |- *.
    set (IT := B[σs]) in *.
    set (OTy := ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (q σs) t) in *.
    specialize (Hq1 _ _ eq_refl); specialize (Hq2 _ _ eq_refl); specialize (IH3 _ _ eq_refl).
    pose proof (eval_ih_pi_inv _ _ _ _ _ _ _ _ Er) as ->.
    destruct (eval_ihty_pi_inv _ _ _ _ _ _ _ Ea) as (b1 & Eb1 & ->).
    pose proof HR as HRsave.
    basic_invert_per_univ_elem HR.
    match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
    match goal with H : _ <~> (fun _ _ => forall _ _ _, rel_mod_app _ _ _ _ _) |- _ => rename H into HRE end.
    destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' Hg) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & HEleq).
    pose proof (ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hms Hc0 eq_refl Hws HB Hys Eb1) as HgD.
    destruct (wf_pi_inversion' HIT) as [HITt HOTt].
    assert (HIT' : forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® IP).
    { intros Δ φ Hφ.
      eapply (glu_typ_transfer u (ul j) (ul j)); [ exact Huj | apply uidx_le_refl | eexists; exact equiv_a_a' | exact HgD
                                                 | exact Hgb1 | exact (Hq1 _ _ Hφ) ]. }
    assert (HDEl : forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                     Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k (ms ++ ws ++ ys) B).
    { intros * Hφ Hb.
      eapply glu_elem_retype; [ exact Hgb1 | exact HgD | exact (glu_univ_elem_trm_typ _ _ _ _ Hgb1 _ _ _ _ Hb) | exact Hb
                              | exact (Hq1 _ _ Hφ) ]. }
    set (body := ptyp_ih p D oq' (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (blocks_wk (blocks_sub Bks σ') ↑)
                   (q σs) (a_app N[↑]ʷ (a_var 0)) t).
    set (OTi := ptyp_ihty (blocks_motives (blocks_sub Bks σ')) (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t).
    assert (Happ : forall Δ φ b c (equiv_c : in_rel c c), Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                     exists rc a2, $| d_ihfn ρ Bks p ups t v & c | gc_deps ⍮ gc_stack ↘ rc /\
                       ⟦ fam_cod ⟧ (nil ↦ d_ihfam ρ (blocks_motives Bks) (env_args nil (ups ++ ms ++ ws ++ ys)) t v) ↦ c ↘ a2 /\
                       Δ ⊢ body[(ι φ),,b] : OTi[(ι φ),,b] ® rc ∈ OEl c equiv_c).
    { intros * Hφ Hb.
      pose proof (rel_dr ups k _ _ _ _ _ c Eb1 equiv_a_a' equiv_c) as Hdc.
      pose proof (HDEl _ _ _ _ Hφ Hb) as HbD.
      destruct (Hq2 _ _ _ _ Hφ Hdc HbD) as [fc Efc].
      pose proof (IH3 _ _ _ _ _ Hφ Hdc HbD Efc) as IH'.
      destruct (Hcod _ _ equiv_c) as [a2 a2' Ea2 Ea2' Ha22].
      assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
      destruct (proj1 (HRE _ _) Hr _ _ equiv_c) as [rc rc' Erc Erc' Hrc].
      assert (rc' = rc) as -> by (eapply functional_eval_app; eassumption).
      destruct (eval_fam_cod_ihfam_inv _ _ _ _ _ _ _ Ea2) as (fx & Efx & Ea2i).
      assert (fx = fc) as -> by (eapply functional_eval_app; eassumption).
      destruct (eval_app_ihfn_inv _ _ _ _ _ _ _ _ Erc) as (y & Ey & Erc0).
      assert (y = fc) as -> by (eapply functional_eval_app; eassumption).
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hdc) as (r0 & r0' & Er0 & Er0' & Hsh').
      assert (r0 = fc) as -> by (eapply functional_eval_app; eassumption).
      assert (r0' = fc) as -> by (eapply functional_eval_app; eassumption).
      exists rc, a2; split; [ exact Erc | split; [ exact Ea2 |] ].
      pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hb) as Hbt.
      unfold body, OTi; rewrite ih_body_inst, (ih_cod_inst _ _ _ _ _ _ Mj HMj HPl); cbn [sentry_exp].
      replace (List.map (fun U => U[sb_wk σ' φ]) Us) with (List.map (fun U => U[φ]ʷ) (List.map (fun U => U[σ']) Us))
        by (rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub).
      eapply (IH' Mk ms c0 gs1 t0 gs2 ws (S d) (ys ++ c :: nil) (sb_wk σ' φ) oq' (q σs ⨟ ((ι φ),,b)) rc a2 j _ _ _);
        [ exact HMk | exact Hc0 | rewrite <- !List.app_assoc; reflexivity | exact Hms | exact Hws | exact Hsk'
        | | exact Hoq | exact (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) | | | | exact Hsh' | exact Erc0 | | exact Ha22
        | exact Hrc | exact Huj | exact HiAj | exact (Hcodg _ equiv_c _ Ea2) |].
      - apply tele_prefix_rel_snoc; [ exact Hys |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hdc.
      - rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_sub.
      - unfold OTy; apply (shape_ty_step VP HVP p D HPD); rewrite List.length_map; exact HUl.
      - exact (app_wk_typed _ _ _ _ _ _ _ HN Hφ Hbt).
      - replace (ups ++ (ms ++ ws ++ ys) ++ c :: nil) with ((ups ++ ms ++ ws ++ ys) ++ c :: nil)
          by (rewrite <- !List.app_assoc; reflexivity).
        rewrite env_args_snoc; exact Ea2i.
      - pose proof (ih_cod_inst σ' σs N t φ (se_exp b) Mj HMj HPl) as E; cbn [sentry_exp] in E; rewrite <- E.
        exact (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ Hbt). }
    (** The body's type, at the generic variable. *)
    assert (HITid : Δ' ⊢ IT ® IP) by (pose proof (HIT' Δ' wk_id (kripke_id _ HΔ')) as Hx0; rewrite exp_wk_id in Hx0; exact Hx0).
    assert (HΔIT : ⊢ Δ' ▹ IT) by mauto 3.
    pose proof (var0_glu_elem Hgb1 HITid) as Hvar.
    pose proof (var_per_elem (length Δ') equiv_a_a') as Heqv.
    destruct (Happ _ _ _ _ Heqv (kripke_shift _ _ HΔIT) Hvar) as (rc0 & a0 & _ & Ea0 & Hg0).
    pose proof (glu_univ_elem_trm_escape _ _ _ _ (Hcodg _ Heqv _ Ea0) _ _ _ _ Hg0) as Hbodyt.
    assert (Ebv : body[(ι ↑),,#0] = body).
    { transitivity (body[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold body; rewrite !ih_body_inst; cbn [sentry_exp].
      apply ptyp_ih_exp_agree; [ exact Hmd | apply sb_exp_agree_var0 ]. }
    assert (Eov : OTi[(ι ↑),,#0] = OTi).
    { transitivity (OTi[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold OTi; rewrite !(ih_cod_inst σ' σs N t ↑ _ Mj HMj HPl); cbn [sentry_exp].
      apply ptyp_ihty_agree_exp; [ exact Hmd | exact Hmp | reflexivity | apply sb_exp_agree_var0 ]. }
    rewrite Ebv, Eov in Hbodyt.
    apply HEleq; eapply mk_pi_glu_exp_pred with (IT := IT) (OT := OTi);
      [ apply wf_fn with (i := j); [ exact HITt | exact Hbodyt ]
      | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRsave Hper); exact Hr
      | apply wf_exp_eq_refl; exact HIT | exact HITt | exact HOTt | exact HIT' |].
    intros Δ φ N0 n0 Hφ HN0 equiv_n.
    destruct (Happ _ _ _ _ equiv_n Hφ HN0) as (rc & a2 & Erc & Ea2 & Hgl).
    exists rc; split; [ exact Erc |].
    pose proof (Hcodg _ equiv_n _ Ea2) as Hga2.
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hga2 | exact Hgl |].
    apply wf_exp_eq_sym; eapply fn_wk_beta; [ exact HITt | exact HOTt | exact Hbodyt | exact Hφ
                                          | exact (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ HN0) ].
  Qed.

End ElimGlu.

End Fixed_GCtx.
