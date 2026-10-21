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

(** A valid type at a valid substitution: the value of the instance
    against the type's at the substitution's value. *)
Lemma typ_inst_val : forall Δ0 Γ0 A (i : nat) τ RΓ0 E Eτ a b,
    Δ0 ⊨ A : Typeω@i -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨ˢ τ ≈ τ : Δ0 ->
    RΓ0 E E -> ⟦ τ ⟧s E ↘ Eτ -> ⟦ A[τ] ⟧ E ↘ a -> ⟦ A ⟧ Eτ ↘ b -> Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HA HΓ0 Hτ HE Hev Ea Eb.
  destruct (rel_exp_of_typ_inversion HA) as (R & HR & Hgen).
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev) as [a1 b1 c1 d1 Ea1 Eb1 Ec1 Ed1 Hch].
  assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (c1 = b) as -> by (eapply functional_eval_exp; eassumption).
  pairwise.
Qed.

(** The eliminator at typed blocks, at equal scrutinees
    ([wf_exp_eq_elim_cong] with the same parameters and blocks). *)
Lemma wf_elim_scrut_eq : forall Γ p D oq m Mm bm Bks Ps M M' (i : nat),
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
    Γ ⊢ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Γ ⊢ a_elim oq (List.firstn (ind_nu D) Ps) m Bks M ≈ a_elim oq (List.firstn (ind_nu D) Ps) m Bks M'
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hg HMm Hbm HPl HPs HBt HMM.
  eapply wf_exp_eq_elim_cong with (Bks' := Bks) (Ps' := Ps);
    first [ exact Hl | exact Hg | exact HMm | exact Hbm | exact (bt_len _ _ _ _ _ _ _ _ HBt) | exact HPl | exact HPs | exact HMM
          | reflexivity | exact (bt_nm _ _ _ _ _ _ _ _ HBt) | exact (bt_ann _ _ _ _ _ _ _ _ HBt) | exact (bt_motive _ _ _ _ _ _ _ _ HBt)
          | exact (bt_mctx _ _ _ _ _ _ _ _ HBt) | exact (bt_names _ _ _ _ _ _ _ _ HBt) | exact (bt_bctx _ _ _ _ _ _ _ _ HBt)
          | exact (bt_counts _ _ _ _ _ _ _ _ HBt) | idtac ].
  - intros k P P' T HP HP' HT; rewrite HP in HP'; injection HP' as <-; apply wf_exp_eq_refl; exact (HPs _ _ _ HP HT).
  - intros k Mk b b' HMk Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; apply wf_exp_eq_refl; exact (bt_motive _ _ _ _ _ _ _ _ HBt _ _ _ HMk Hb).
  - intros k b b' Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; reflexivity.
  - intros k Mk b b' i0 c gs n B B' HMk Hb Hb' HB HB' Hcon; rewrite Hb in Hb'; injection Hb' as <-.
    rewrite HB in HB'; injection HB' as <-; apply wf_exp_eq_refl.
    exact (bt_brs _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ HMk Hb Hcon (List.nth_error_In _ _ HB)).
Qed.

(** [ι] at typed blocks ([wf_exp_eq_elim_iota] with the blocks' typing
    premises read off [blocks_typed]). *)
Lemma wf_elim_iota_bt : forall Γ p D oq m Mm bm Bks c gs Ps As (i : nat) n B,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm -> ind_con Mm c = Some gs -> List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
       Γ ⊢ N : T) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
    brs_lookup (eb_brs bm) c = Some (n, B) ->
    Γ ⊢ a_elim oq (List.firstn (ind_nu D) Ps) m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                    (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As))
       ≈ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++
                          elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As)]
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                          apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                            (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)].
Proof.
  intros * HΓ Hl Hg HMm Hbm Hcon HPl HPs HAl HAs HBt HlB.
  eapply wf_exp_eq_elim_iota;
    first [ exact HΓ | exact Hl | exact Hg | exact HMm | exact Hbm | exact Hcon | exact (bt_len _ _ _ _ _ _ _ _ HBt) | exact HPl
          | exact HPs | exact HAl | exact HAs | reflexivity | exact (bt_nm _ _ _ _ _ _ _ _ HBt) | exact (bt_ann _ _ _ _ _ _ _ _ HBt)
          | exact (bt_motive _ _ _ _ _ _ _ _ HBt) | exact (bt_mctx _ _ _ _ _ _ _ _ HBt) | exact (bt_names _ _ _ _ _ _ _ _ HBt)
          | exact (bt_bctx _ _ _ _ _ _ _ _ HBt) | exact (bt_counts _ _ _ _ _ _ _ _ HBt) | exact (bt_brs _ _ _ _ _ _ _ _ HBt)
          | exact HlB ].
Qed.

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

  (** The recursive results' telescope of a branch, at a substitution
      [σ'] past the non-uniform parameters and the arguments: the
      telescope of the eliminator at [σ']. *)
  Lemma ihs_insts_move : forall k Mk c gs σ' Ns' As L, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
      List.length Ns' = im_nn Mk -> List.length As = List.length gs ->
      tele_insts (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs) (sb_of_list σ' (Ns' ++ As)) L
      = tele_insts (ihs_ctx_aux (im_nn Mk) (blocks_motives (blocks_sub Bks σ')) (List.map (fun U => U[σ']) Us)
                      (List.length gs) nil 0 gs) (sb_of_list Id (Ns' ++ As)) L.
  Proof.
    intros * HMk Hcon HNl HAl.
    rewrite (tele_insts_sb_eq _ _ (sb_qn (0 + List.length gs + im_nn Mk) σ' ⨟ sb_of_list Id (Ns' ++ As))).
    2:{ replace (0 + List.length gs + im_nn Mk) with (List.length (Ns' ++ As)) by (rewrite List.length_app; lia).
        symmetry; etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ]. }
    rewrite <- tele_insts_tele_sub.
    rewrite (ihs_ctx_aux_sub (im_nn Mk) (blocks_motives Bks) (blocks_motives (blocks_sub Bks σ')) Us (List.length gs) σ' gs nil 0
               eq_refl); [ reflexivity |].
    intros gs1 t gs2 Heq.
    pose proof (dc_members _ Hc _ _ HMk) as HMc.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    split.
    - rewrite HUl; exact (mc_recs _ _ HMc _ _ _ _ _ Hin Heq).
    - destruct (mc_rec_len _ _ HMc _ _ Hin _ _ _ Heq) as (Mj & HMj & HlMj).
      rewrite HlMj; apply (blocks_motives_sub D Bks σ' _ Mj Hnm HMj).
  Qed.

  (** ** On a Constructor

      The constructor [c] of the member [k], glued in the group, at a
      substitution [σ'] glued to [ρ]: the eliminator is the branch of [c]
      in [k]'s block at the non-uniform parameters, the arguments and the
      recursive results ([ι]); the branch is glued at the substitution of
      them, the arguments glued at their own types ([AtType]), the
      recursive results by the induction. *)
  Section ConCase.
    Variables (k : nat) (Mk : imember) (hd : qname) (k' : nat) (c : String.string) (gs : list carg)
      (Us' Ns' : list exp) (bs vs : list domain) (As : list exp) (Δ' : ctx) (M' : exp).
    Hypotheses (HMk : ind_member D k = Some Mk) (Href : im_ref p k Mk = (hd, k')) (Hcon : ind_con Mk c = Some gs)
      (HUl' : List.length Us' = ind_nu D) (HNl' : List.length Ns' = im_nn Mk)
      (Hbl : List.length bs = (im_unu D Mk + im_nn Mk)%nat) (Hvl : List.length vs = List.length gs)
      (HAl : List.length As = List.length gs)
      (HMeq : Δ' ⊢ M' ≈ apps (a_con p k c) (Us' ++ Ns' ++ As) : im_ty_at p k Mk Us' Ns')
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
          rec_prop k Δ' Us' (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N v).
    Variables (σ' : sub) (oq' : option qname) (ns : list domain).
    Hypotheses (Hgrp : elim_grp D oq' p k) (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HUs' : Us' = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : im_ty_at p k Mk Us' Ns') (Hgn : glu_nparams k Mk NEl Δ' Us' Ns' ns)
      (Hns : tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns)
      (HGm : G k ups ups ns ns (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs ++ vs))).
    #[local] Abbreviation X := (List.skipn (im_unu D Mk) bs).

    (** The scrutinee's parameters against the stored ones, and the
        arguments related. *)
    Lemma cc_rel : tele_rel (nr k) (List.rev (im_nparams Mk)) ns X /\
        con_args_rel p D (okr_at D ups nr) nr ar dr k ups ups X X gs vs vs.
    Proof.
      unfold grp_rel in HGm; inversion HGm; subst.
      match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HMk in H1; injection H1 as <- end.
      match goal with H1 : ind_con Mk c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
      repeat match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => apply app_split_eq in E; [| lia ]; destruct E as [-> ->] end.
      split; assumption.
    Qed.

    Lemma cc_LX : List.length X = im_nn Mk.
    Proof. rewrite List.length_skipn; lia. Qed.

    (** The non-uniform parameters and the arguments, glued at the instance
        of their closed telescope at [τU]: at their own types ([AtType]). *)
    Lemma cc_args : glu_args Δ' (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) σ' ρ (Ns' ++ As) (X ++ vs).
    Proof.
      destruct cc_rel as [_ Hia].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf
                  nb Hnbu Hnbq) as [_ Hrt].
      pose proof (ac_args_prefix VP HVP HGall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf nb Hnbu Hnbq
                    k Mk c gs Us' Ns' bs vs As Δ' HMk Hcon HNl' Hbl Hvl HAl Hb Hv Hnp HAs Harg Hrec
                    (fun gs1 t gs2 N A v H1 H2 H3 H4 => Hrt _ _ _ _ _ _ _ _ (Hrec gs1 t gs2 N A v H1 H2 H3 H4)) HUg' Hia
                    (List.length gs) (le_n _)) as HgA.
      rewrite (List.firstn_all2 (n := List.length gs) gs), (List.firstn_all2 (n := List.length gs) As),
        (List.firstn_all2 (n := List.length gs) vs) in HgA by lia.
      pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf k Mk Δ' Us' Ns' X HMk Hnp Hb) as HgN.
      assert (Hg : glu_args Δ' (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list Id Us') (env_args nil ups) (Ns' ++ As) (X ++ vs)).
      { apply glu_args_app; [ exact (decl_closed_nparams_ass D Hc _ _ HMk) | rewrite length_im_nparams; exact HNl'
                            | rewrite length_im_nparams; exact cc_LX |].
        split; [ exact HgN | rewrite sb_of_list_app, env_args_app in HgA; exact HgA ]. }
      rewrite HUs' in Hg.
      apply tele_inst_args; [ | | | | exact Hg |].
      - rewrite <- List.app_assoc; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMk) ].
      - rewrite <- List.app_assoc; exact (vg_cargs_sem p D Hvg Hcv k Mk c gs HMk Hcon).
      - pose proof (Completeness.Inductives.Elim.ihs_pre_sem p D Γ Us Bks Mk gs (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon)
                      nil gs eq_refl) as H.
        cbn [ihs_ctx_aux List.app] in H; unfold cinst in H.
        rewrite tele_sub_app, length_im_nparams, <- List.app_assoc; exact H.
      - pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk (cons_lookup_in _ _ _ Hcon) (eq_sym (List.app_nil_r gs))) as H.
        unfold im_params in H; rewrite List.app_assoc in H.
        apply ctx_scoped_app in H as [H _]; rewrite Nat.add_0_r in H; exact H.
      - pose proof (EB Completeness.Inductives.Elim.closed_args_gargs k Mk c gs HMk Hcon X X vs vs Hb Hv Hia (List.length gs) (le_n _))
          as H.
        rewrite (List.firstn_all2 (n := List.length gs) gs), (List.firstn_all2 (n := List.length gs) vs) in H by lia; exact H.
    Qed.

    Lemma cc_oq : oq' = Some p \/ oq' = None.
    Proof. destruct Hgrp as [-> | [-> _]]; auto. Qed.

    Lemma cc_Ps_typed : forall j P T, List.nth_error (Us' ++ Ns') j = Some P ->
        List.nth_error (tele_insts (im_params D Mk) Id (Us' ++ Ns')) j = Some T -> Δ' ⊢ P : T.
    Proof.
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf k Mk Δ' Us' Ns' X HMk Hnp Hb) as HgN.
      assert (Hga : glu_args Δ' (im_params D Mk) Id nil (Us' ++ Ns') (ups ++ X)).
      { unfold im_params; apply glu_args_app; [ exact Ua | exact HUl' | exact ups_len |].
        split; [ exact HUg' | exact HgN ]. }
      exact (glu_args_typed _ _ _ _ _ _ (member_params_ass D Hc _ _ HMk) Hga).
    Qed.

    (** The substitution [ι] instantiates the branch's context with, typed. *)
    Lemma cc_iota_sub : Δ' ⊢ˢ sb_of_list Id (Ns' ++ As ++ elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As)
        : elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us' ++ Δ'.
    Proof.
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      assert (HΔ' : ⊢ Δ') by (gen_presups; assumption).
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      pose proof (wf_iota_sub _ _ _ p D oq' k Mk c gs (Us' ++ Ns') As (blocks_sub Bks σ') iA Hl cc_oq HMk Hcon HΔ'
                    ltac:(rewrite List.length_app, HUl', HNl'; unfold im_np; lia) cc_Ps_typed HAl HAs
                    ltac:(rewrite firstn_app_exact by exact HUl'; exact HBt')) as H.
      rewrite firstn_app_exact, skipn_app_exact in H by exact HUl'; exact H.
    Qed.

    (** The recursive results of the branch, glued: each is the
        eliminator at the matching recursive argument, glued by the
        induction hypothesis [IH] at its motive. *)
    Lemma cc_ihs_args : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        forall RB, EF elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                     ∈ per_ctx_env ↘ RB ->
        RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs)) ->
        glu_args Δ' (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs) (sb_of_list σ' (Ns' ++ As))
          (env_args ρ (X ++ vs)) (elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As) ihs.
    Proof.
      intros ihs Ei RB HRB HZ.
      pose proof (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      destruct cc_rel as [HnX Hia].
      pose proof cc_LX as LX.
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      assert (Esplit : elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                       = ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs ++ cinst Γ p D Mk Us gs)
        by (unfold elim_bctx, cinst; rewrite <- !List.app_assoc; reflexivity).
      assert (Hpgi : per_gargs (List.rev (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs))
                       (env_args ρ (X ++ vs)) (env_args ρ (X ++ vs)) ihs ihs).
      { pose proof (Completeness.Inductives.Elim.ihs_pre_sem p D Γ Us Bks Mk gs HBs nil gs eq_refl) as HC0.
        cbn [ihs_ctx_aux List.app] in HC0.
        destruct (rel_ctx_wf_per_ctx_env HC0) as [RC HRC].
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite Esplit in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs)) in HRB', HBs'.
        assert (Lr : List.length ihs = List.length (List.rev (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs)))
          by (rewrite List.length_rev, length_ihs_ctx_aux; exact Lih).
        assert (HZ' : RB (env_args (env_args ρ (X ++ vs)) ihs) (env_args (env_args ρ (X ++ vs)) ihs))
          by (rewrite <- env_args_app, <- List.app_assoc; exact HZ).
        destruct (Decl.rel_gargs _ _ _ _ HRC HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ')
          as [_ H].
        exact H. }
      constructor; [ rewrite length_elim_ihs, length_ihs_ctx_aux by exact HAl; reflexivity | rewrite length_ihs_ctx_aux; exact Lih |].
      intros j0 M T r B0 HMj0 HT Hr HB0.
      destruct (ihs_rev_nth (im_nn Mk) (blocks_motives Bks) Us (List.length gs) gs j0 _ HB0) as (gs1 & t & gs2 & Heq & Hk & EB).
      injection EB as ->; subst j0.
      set (j := cargs_nrec gs1) in *.
      assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [N HN].
      rewrite (elim_ihs_nth _ _ _ _ _ gs1 _ gs t gs2 As N Heq HAl HN) in HMj0; injection HMj0 as <-.
      destruct (Completeness.Inductives.Elim.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (v & v' & Hv1 & Hv1' & Hsh).
      rewrite Hv1' in Hv1; injection Hv1 as <-.
      destruct (eval_ihs_nth _ _ _ _ gs1 _ _ _ Ei t gs2 v' Heq Hv1') as (r' & Hr' & Er').
      fold j in Hr'; rewrite Hr in Hr'; injection Hr' as <-.
      set (σg := cargs_sub (sb_of_list Id (Us' ++ Ns')) gs1 As).
      rewrite (ihs_insts_move k Mk c gs σ' Ns' As _ HMk Hcon HNl' HAl) in HT.
      rewrite <- HUs' in HT.
      (** The syntactic type of the entry. *)
      assert (ET : T = ptyp_ihty (blocks_motives (blocks_sub Bks σ')) Id σg N t).
      { destruct (tele_insts_nth _ _ _ _ _ HT) as (B'' & HB'' & ET).
        rewrite (ihs_ctx_nth _ _ _ _ gs gs1 t gs2 Heq) in HB''; fold j in HB''; injection HB'' as <-.
        subst T; rewrite <- sb_of_list_app, <- List.app_assoc.
        set (L' := List.firstn j (elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As)).
        assert (LL' : List.length L' = j)
          by (unfold L'; rewrite List.length_firstn, length_elim_ihs by exact HAl; unfold j; rewrite Heq, Views.cargs_nrec_app; lia).
        set (δ := sb_of_list Id (Ns' ++ As ++ L')).
        assert (Hθδ : sb_eq (ihs_sub (im_nn Mk) Us' (List.length gs) (cargs_pat gs1) j ⨟ δ) σg).
        { unfold δ, σg; rewrite <- LL'.
          pose proof (ihs_sub_iota D Mk (Us' ++ Ns') As L' gs1 gs ltac:(rewrite List.length_app, HUl', HNl'; unfold im_np; lia) HAl
                        ltac:(rewrite Heq, List.length_app; lia)) as H.
          rewrite firstn_app_exact, skipn_app_exact in H by exact HUl'; exact H. }
        assert (Hβδ : sb_eq (sb_of_wk (wk_shiftn (j + List.length gs + im_nn Mk)) ⨟ δ) Id).
        { intros z; unfold δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
          replace (z + (j + List.length gs + im_nn Mk)) with (List.length (Ns' ++ As ++ L') + z)
            by (rewrite !List.length_app, HNl', HAl, LL'; lia).
          rewrite sb_of_list_ge; reflexivity. }
        assert (Hidx : (a_var (j + List.length gs - 1 - List.length (cargs_pat gs1)))[δ] = N).
        { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ.
          rewrite (sb_of_list_nth _ _ _ N) by (rewrite !List.length_app, HNl', HAl, LL', Heq, List.length_app, length_cargs_pat; cbn; lia).
          rewrite !List.length_app, HNl', HAl, LL', length_cargs_pat.
          replace (im_nn Mk + (List.length gs + j) - 1 - (j + List.length gs - 1 - List.length gs1))
            with (im_nn Mk + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
          cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl'; replace (im_nn Mk + List.length gs1 - im_nn Mk) with (List.length gs1) by lia.
          rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact HN. }
        rewrite ptyp_ihty_sub, Hidx.
        rewrite (ptyp_ihty_sb_eq t _ _ Id _ σg N Hβδ Hθδ); reflexivity. }
      (** The entry is typed, by the typing of [ι]. *)
      assert (HMt' : Δ' ⊢ ptyp_ih p D oq' Us' (blocks_sub Bks σ') σg N t : T).
      { set (Ihs := elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As) in *.
        assert (Lei : List.length Ihs = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
        set (Rst := tele_sub (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) (sb_of_list Id Us')) ++ tele_sub (im_nparams Mk) (sb_of_list Id Us')).
        assert (HRa : tele_ass Rst)
          by (unfold Rst; apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | apply (decl_closed_nparams_ass D Hc _ _ HMk) ]).
        assert (LRst : List.length Rst = List.length (Ns' ++ As))
          by (unfold Rst; rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams, HNl', HAl; lia).
        assert (Hlen : List.length (Ns' ++ As ++ Ihs) = List.length (elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us'))
          by (rewrite length_elim_bctx, !List.length_app, HNl', HAl, Lei; lia).
        apply (wf_sub_of_list_inv _ _ _ (elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ')) Us') Δ' Id (Ns' ++ As ++ Ihs)
                  (elim_bctx_ass p D k Mk gs _ Us' Hc HMk) Hlen cc_iota_sub (im_nn Mk + List.length gs + j)).
        - rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
          rewrite List.length_app, HNl', HAl.
          replace (im_nn Mk + List.length gs + j - (im_nn Mk + List.length gs)) with j by lia.
          exact (elim_ihs_nth _ _ _ _ _ gs1 _ gs t gs2 As N Heq HAl HN).
        - unfold elim_bctx; fold Rst.
          assert (LRi : List.length (tele_insts Rst Id (Ns' ++ As)) = im_nn Mk + List.length gs)
            by (rewrite length_tele_insts by exact HRa; rewrite LRst, Nat.min_id, List.length_app, HNl', HAl; reflexivity).
          rewrite List.app_assoc, tele_insts_app by (first [ exact HRa | exact (eq_sym LRst) ]).
          rewrite List.nth_error_app2 by lia; rewrite LRi.
          replace (im_nn Mk + List.length gs + j - (im_nn Mk + List.length gs)) with j by lia.
          exact HT. }
      destruct (presup_exp HMt') as [_ [jT HjT]].
      rewrite ET in HjT.
      (** The type of the recursive argument. *)
      destruct (nth_error_lt_some (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us' ++ Ns')) As) (List.length gs1)) as [TN HTN].
      { rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. }
      assert (HTNeq : TN = ptyp_ty_at p D Us' σg t).
      { rewrite (cargs_rec_type_at p D Mk gs gs1 t gs2 (Us' ++ Ns') As TN Heq Hc
                   ltac:(rewrite List.length_app, HUl', HNl'; unfold im_np; lia) HTN).
        rewrite firstn_app_exact by exact HUl'.
        apply ptyp_ty_at_sb_eq; rewrite sb_of_list_app; unfold σg; rewrite <- (cargs_sub_firstn gs1 (sb_of_list Id (Us' ++ Ns')) As).
        apply cargs_sub_pat; rewrite List.length_firstn; lia. }
      pose proof (IH gs1 t gs2 N TN v' Heq HN HTN Hv1') as IHr.
      (** The semantic type of the entry. *)
      destruct (per_gargs_nth_el _ _ _ _ _ j _ Hpgi HB0 ltac:(rewrite Lih; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia))
        as (i0 & Rae & ae & ae' & x & x' & Eae & Eae' & HRae & Hx & Hx' & Hrr).
      assert (ae' = ae) as -> by (eapply functional_eval_exp; eassumption).
      rewrite Hr in Hx; injection Hx as <-; rewrite Hr in Hx'; injection Hx' as <-.
      set (fa := List.firstn (List.length gs1) vs) in *.
      set (aft := List.skipn (S (List.length gs1)) vs).
      assert (Evs : vs = fa ++ v' :: aft) by (unfold fa, aft; rewrite <- (skipn_nth_cons' _ _ _ Hv1'), List.firstn_skipn; reflexivity).
      set (ihp := List.firstn j ihs) in *.
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn, Hvl, Heq, List.length_app; cbn; lia).
      assert (Laft : List.length aft = List.length gs2) by (unfold aft; rewrite List.length_skipn, Hvl, Heq, List.length_app; cbn; lia).
      assert (Lihp : List.length ihp = j) by (unfold ihp; rewrite List.length_firstn, Lih; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
      pose proof (EB Completeness.Inductives.Elim.e_HCtxT ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs gs1 t gs2 Heq) as HCtxT.
      pose proof (rel_ctx_wf_tail HCtxT) as HCtx.
      destruct (rel_ctx_wf_per_ctx_env HCtx) as [RS HRS].
      assert (HEE : RS (env_args ρ (X ++ vs ++ ihp)) (env_args ρ (X ++ vs ++ ihp))).
      { assert (Esp : ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                     = ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)
                       ++ ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs1)
          by (rewrite Heq at 2; rewrite Views.ihs_ctx_aux_app, List.app_nil_r; reflexivity).
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite Esplit, Esp, <- List.app_assoc in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)))
          in HRB', HBs'.
        assert (Lr : List.length (List.skipn j ihs)
                     = List.length (List.rev (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))))
          by (rewrite List.length_rev, length_ihs_ctx_aux, List.length_skipn, Lih; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
        assert (HZ' : RB (env_args (env_args ρ (X ++ vs ++ ihp)) (List.skipn j ihs)) (env_args (env_args ρ (X ++ vs ++ ihp)) (List.skipn j ihs)))
          by (rewrite <- env_args_app, <- !List.app_assoc; unfold ihp; rewrite List.firstn_skipn; exact HZ).
        destruct (Decl.rel_gargs _ _ _ _ HRS HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ') as [H _].
        exact H. }
      rewrite Evs, <- !List.app_assoc in HEE; cbn [List.app] in HEE.
      pose proof Eae as Eae0; rewrite <- env_args_app in Eae0; fold ihp in Eae0.
      rewrite Evs, <- !List.app_assoc in Eae0; cbn [List.app] in Eae0.
      destruct (EB Completeness.Inductives.Elim.side_w ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs gs1 t gs2 Heq RS HRS
                  ρ X fa v' aft ihp Hρ LX Lfa Laft Lihp HEE) as (w & Hw & HwU & Lw).
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk; fold fa in Hpk.
      destruct (rec_shape_facts k Mk c gs1 t gs2 0 HMk ltac:(rewrite <- Heq; exact Hcon)) as ((Mj & HMj & _) & _ & _).
      cbn [ptyp_skip] in HMj.
      destruct (HBks _ _ HMj) as [bj Hbj].
      assert (Hsh0 : rec_arg_rel p D (okr_at D ups nr) nr ar dr k ups ups (X ++ nonrec_arg_vals gs1 fa ++ nil)
                       (X ++ nonrec_arg_vals gs1 fa ++ nil) (ptyp_skip 0 t) v' v')
        by (rewrite List.app_nil_r; exact Hsh).
      (** The motive at the recursive argument, as the induction
          hypothesis sees it. *)
      destruct (EB Completeness.Inductives.Elim.ihty_link ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon HBs gs1 t gs2 Heq RS HRS
                  Mj bj HMj Hbj (List.length (ptyp_doms t)) 0 ρ X fa v' aft ihp w nil v' ae i0 Rae eq_refl LX Lfa Laft Lihp eq_refl
                  Hρ HEE Hw HwU Lw Hb Hpk (tele_prefix_rel_nil _) (eval_apps_nil _ _ _) Hsh0 Eae0 HRae) as (b & Eb & Hab).
      rewrite List.app_nil_r in Eb.
      set (J := max (max (ulvl u) iA) (max i0 jT)).
      destruct Hab as [Rab HRab].
      destruct (per_univ_elem_sym _ _ _ _ HRab) as [HRba _].
      pose proof (per_univ_trans _ _ _ _ _ _ HRba HRab) as HRbb.
      pose proof (per_univ_elem_cumu_ge i0 J _ _ _ ltac:(unfold J; lia) HRbb) as HRbbJ.
      assert (HRr : Rab r r) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRae HRab); exact Hrr).
      destruct (per_univ_glu_univ_elem J b (ex_intro _ Rab HRbbJ)) as (Pb & Elb & Hgb).
      pose proof (lift_exp_ge _ _ _ _ jT J ltac:(unfold J; lia) HjT) as HjJ.
      assert (HuJ : uidx_le u (ul J)) by (apply uidx_le_ul_max; unfold J; lia).
      assert (HiAJ : iA <= J) by (unfold J; lia).
      assert (Hc1 : ind_con Mk c = Some (gs1 ++ ca_rec t :: gs2)) by (rewrite <- Heq; exact Hcon).
      assert (Hpre1 : X ++ nonrec_arg_vals gs1 fa = X ++ nonrec_arg_vals gs1 fa ++ nil) by (rewrite List.app_nil_r; reflexivity).
      pose proof (IHr Mk X c gs1 t gs2 (nonrec_arg_vals gs1 fa) 0 nil σ' oq' σg r b J Rab Pb Elb HMk
                    Hc1 Hpre1 Hb Hpk eq_refl (tele_prefix_rel_nil _)
                    cc_oq Hσ' HUs' HTNeq (HAs _ _ _ HN HTN) Hsh Er' Eb HRbbJ HRr HuJ HiAJ Hgb HjJ) as HMg.
      destruct (glu_transfer_per_elem _ i0 _ _ _ _ _ _ _ _ Hgb (ex_intro _ Rab HRba) (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HMg) HMg)
        as (kk & P' & El' & Hg' & HTP' & HMg').
      rewrite ET; exact (mk_glu_arg _ _ _ _ _ _ kk ae P' El' Eae Hg' HTP' HMg').
    Qed.

    (** The constructor in the group at its stored parameters. *)
    Lemma cc_GX : G k ups ups X X (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs ++ vs)).
    Proof.
      destruct cc_rel as [HnX _].
      exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ k Mk _ _ _ _ _ _ _ _ HMk HGm HnX HnX).
    Qed.

    (** The recursive results, related at the motives. *)
    Lemma cc_ihs : exists ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs /\
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs.
    Proof.
      destruct cc_rel as [_ Hia].
      destruct per_elim_at_ups as (_ & H2 & _).
      destruct (H2 _ _ _ _ _ _ _ _ Hia) as (ihs & ihs' & Ei & Ei' & Hir).
      pose proof (functional_eval_ihs _ _ _ _ _ _ _ _ Ei Ei') as <-.
      exists ihs; split; assumption.
    Qed.

    (** The environment of the branch's context the branch is evaluated
        in. *)
    Lemma cc_env : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs ->
        forall RB, EF elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                     ∈ per_ctx_env ↘ RB ->
        RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs)).
    Proof.
      intros ihs Ei Hir RB HRB.
      exact (EB Completeness.Inductives.Elim.cv_bctx_elem ρ Hρ Bks iA HBks HMall HAv k Mk c gs HMk Hcon
               (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) ρ ρ Hρ Hρ ups ups hd k' bs bs vs vs ihs ihs cc_GX Hir RB HRB).
    Qed.

    (** The substitution [ι] at [σ'], glued to that environment. *)
    Lemma cc_sub : forall ihs, ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs ->
        forall Sb, EG elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ ∈ glu_ctx_env ↘ Sb ->
        Δ' ⊢ˢ sb_of_list σ' (Ns' ++ As ++ elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As)
          ® env_args ρ (X ++ vs ++ ihs) ∈ Sb.
    Proof.
      intros ihs Ei Hir Sb HSb.
      pose proof (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
      pose proof (cc_ihs_args ihs Ei RB HRB (cc_env ihs Ei Hir RB HRB)) as Hgi.
      pose proof cc_args as Hga.
      destruct (glu_args_length _ _ _ _ _ _ Hga) as [L1 L2].
      assert (HCa : tele_ass (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU))
        by (apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_nparams_ass D Hc _ _ HMk) ]).
      assert (Esp : elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ
                    = (ihs_ctx_aux (im_nn Mk) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                       ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) ++ Γ)
        by (rewrite tele_sub_app, length_im_nparams; unfold elim_bctx; rewrite <- !List.app_assoc; reflexivity).
      rewrite Esp in HSb.
      eapply glu_sub_of_list; [ | exact HSb | exact HSbΓ | exact Hσ' |].
      - apply List.Forall_app; split; [ apply ihs_ctx_aux_ass | exact HCa ].
      - rewrite (List.app_assoc Ns'), (List.app_assoc X).
        apply glu_args_app; [ exact HCa | exact L1 | exact L2 |].
        split; [ exact Hga | exact Hgi ].
    Qed.

    (** The value of the branch's type in that environment, against the
        motive's at the scrutinee: the branch's type is the motive at the
        constructor as the group reads it ([τb]), related to the scrutinee
        in the group. *)
    Lemma cc_bty_rel : forall b ihs abt a0, List.nth_error Bks k = Some b ->
        ⟦ihs vs of gs under p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        rec_results_rel dr Rel k ups ups X X gs vs vs ihs ihs ->
        ⟦ elim_bty p k Mk c gs (eb_motive b) Us ⟧ env_args ρ (X ++ vs ++ ihs) ↘ abt ->
        ⟦ eb_motive b ⟧ env_args ρ (ns ++ d_con hd k' c (bs ++ vs) :: nil) ↘ a0 ->
        Dom abt ≈ a0 ∈ per_univ iA.
    Proof.
      intros b ihs abt a0 Hbk Ei Hir Eabt Ea0.
      pose proof (vbs_bctx _ _ _ _ _ _ HBv k Mk c gs HMk Hcon) as HBs.
      destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
      pose proof (cc_env ihs Ei Hir RB HRB) as HZ.
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      pose proof cc_LX as LX.
      destruct (rel_exp_under_ctx_simple_at HRB
                  (Completeness.Inductives.Elim.bty_con_valid VP p D HVP HPD Γ Us HUl HUs Bks k Mk c gs HMk Hcon HBs) _ _ HZ)
        as (l1 & l2 & El1 & El2 & _).
      pose proof (Completeness.Inductives.Elim.eval_bty p D Us HUl k Mk c gs ρ X vs ihs l1 LX Hvl Lih El1) as Hev.
      pose proof (Completeness.Inductives.Elim.gsub_bty VP p D HVP HPD Γ HΓ Us HUl HUs Bks HMall k Mk c gs HMk Hcon HBs) as Hgs.
      assert (HUb : List.length (List.map (fun U => U[wk_shiftn (im_nn Mk + List.length gs + cargs_nrec gs)]ʷ) Us) = ind_nu D)
        by (rewrite List.length_map; exact HUl).
      assert (LNA : List.length (vars_from (cargs_nrec gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec gs) (List.length gs))
                    = (im_nn Mk + List.length gs)%nat)
        by (rewrite List.length_app, !length_vars_from; lia).
      destruct (Completeness.Inductives.Elim.con_ref_apps_value VP p D HVP HPD k Mk c gs _ _ _ (X ++ vs) l1 HMk Hcon HUb
                  (Completeness.Inductives.Elim.eval_bty_args Mk gs ρ X vs ihs LX Hvl Lih) LNA El1) as (cs1 & Lcs1 & El1v).
      rewrite Href in El1v; cbn [fst snd] in El1v; subst l1.
      assert (HG1 : G k ups ups X ns (d_con hd k' c (cs1 ++ X ++ vs)) (d_con hd k' c (bs ++ vs))).
      { pose proof cc_GX as H.
        assert (Ebs : bs ++ vs = List.firstn (im_unu D Mk) bs ++ X ++ vs) by (rewrite List.app_assoc, List.firstn_skipn; reflexivity).
        rewrite Ebs in H at 1.
        assert (L1 : List.length (List.firstn (im_unu D Mk) bs) = im_unu D Mk) by (rewrite List.length_firstn; lia).
        assert (L2 : List.length cs1 = List.length (List.firstn (im_unu D Mk) bs)) by (rewrite L1; exact Lcs1).
        pose proof (Completeness.Inductives.Elim.ind_rel_con_prefix_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      (List.firstn (im_unu D Mk) bs) cs1 (X ++ vs) Mk HMk L1 L2 H) as H'.
        destruct cc_rel as [HnX _].
        pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
        exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ k Mk _ _ _ _ _ _ _ _ HMk H' Hb (tsym _ _ HMk _ _ HnX)). }
      destruct (mot_rel k Mk b b ups ups X ns _ _ HMk Hbk Hbk HG1) as (a1 & a2 & Ea1 & Ea2 & Hr12).
      assert (a2 = a0) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (typ_inst_val _ _ _ _ _ _ _ _ _ _ (HAv _ _ _ HMk Hbk) HRB (Instance.gsub_valid Hgs) HZ Hev Eabt Ea1) as H1.
      eapply per_univ_trans'; [ exact H1 | exists (Rel k X (d_con hd k' c (cs1 ++ X ++ vs)) ns (d_con hd k' c (bs ++ vs))); exact Hr12 ].
    Qed.

    (** The constructor applied, as the member it is at reads it
        ([im_ref], [im_pre]): itself at a declared member, the container's
        at a view. *)
    Lemma cc_con_ref : Δ' ⊢ apps (a_con p k c) (Us' ++ Ns' ++ As) ≈ apps (a_con hd k' c) (im_pre Mk Us' ++ Ns' ++ As)
        : im_ty_at p k Mk Us' Ns'.
    Proof.
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      pose proof Href as Href'.
      unfold im_ref in Href'; destruct (im_head Mk) as [pm | qc kc Is vm] eqn:Hh; injection Href' as <- <-.
      - unfold im_pre; rewrite Hh; apply wf_exp_eq_refl; gen_presups; eassumption.
      - destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mq & Hq & HMq & _ & _ & _ & _ & Hfst & _).
        destruct (cons_lookup_names (im_cons Mq) c) as [gh Hgh].
        { rewrite <- Hfst; apply (List.in_map fst _ (c, gs)), cons_lookup_in; exact Hcon. }
        unfold im_pre; rewrite Hh.
        exact (view_head_con_eq p D k Mk qc kc Is vm Dq Mq Hdt Hl Hc HMk Hh Hq HMq Δ' Us' Ns' As c gs gh HΔ' HUl' HNl'
                 cc_Ps_typed Hgh Hcon HAl HAs).
    Qed.

    (** The constructor case: the eliminator evaluates to the branch at
        [ι]'s values, glued there; the elimination of [M'] is the branch at
        [ι] by [ι] and the congruence of the scrutinee, and the type of the
        branch is the motive's at the constructor, equal to its at [M']. *)
    Lemma cc_main : elim_out k Mk Δ' σ' oq' Ns' M' (d_con hd k' c (bs ++ vs)) ns.
    Proof.
      destruct cc_ihs as (ihs & Ei & Hir).
      destruct (HBks _ _ HMk) as [b Hbk].
      destruct (brs_names_lookup _ _ _ _ (Hna _ _ _ HMk Hbk) Hcon) as (n & B & HlB & HinB).
      pose proof (Har _ _ _ _ _ _ _ HMk Hbk Hcon HinB) as Hn.
      destruct (gbk_branch _ _ _ _ _ _ HBg _ _ _ _ _ _ _ HMk Hbk Hcon HinB) as [Sbb HSbb lvl Hbody].
      pose proof (cc_sub ihs Ei Hir Sbb HSbb) as Hτ.
      destruct (Hbody _ _ _ Hτ) as [abt rB Pb Elb Eabt ErB Hgb HBgl].
      destruct (ER im_ref_target k Mk hd k' HMk Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      (** The eliminator's value. *)
      assert (Ee : ⟦elim d_con hd k' c (bs ++ vs) at k of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rB).
      { eapply eval_elim_con; [ exact Hl | exact HMk | exact Href | exact Hq | exact HMq | exact Hcon
                              | rewrite List.length_app; unfold im_np; lia | exact Hbk | exact HlB | rewrite Hnnq; exact Hn | |].
        - rewrite skipn_app_exact by (unfold im_np; lia); exact Ei.
        - rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact ErB. }
      (** The motive at the scrutinee, glued in the group ([AtType]). *)
      destruct (Completeness.Inductives.ViewReadback.mref_exists VP HVP p D HPD ups ups_gargs ups_len k Mk HMk) as [[[hd0 k0] pre] Er].
      destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D k Mk ups hd0 k0 pre Hl HMk ups_len Er) as [Href0 Lpre].
      rewrite Href in Href0; injection Href0 as E1 E2; subst hd0 k0.
      assert (HIG : ind_glu_elem p D ups NEl AEl DP DEl k Δ' Us' Ns' M' (d_con hd k' c (bs ++ vs)))
        by (eapply ind_glu_elem_con; eassumption).
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf
                  nb Hnbu Hnbq) as [Hel _].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (Hgl : forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
                Δ' ⊢ im_ty_at p k Mk (List.map (fun U => U[σ']) Us) Ns' ® P ->
                Δ' ⊢ M' : im_ty_at p k Mk (List.map (fun U => U[σ']) Us) Ns' ® d_con hd k' c (bs ++ vs) ∈ El).
      { intros i P El _ Hglu HT; rewrite <- HUs' in HT |- *.
        exact (Hel _ _ _ _ _ _ HIG Mk ns hd k' pre i P El HMk Er HUg' HMt Hgn Hns HGm Hglu HT). }
      pose proof Hgn as Hgn'; rewrite HUs' in Hgn'.
      destruct (motive_glu k Mk Δ' σ' Ns' ns M' _ hd k' pre HMk Hσ' Hgn' Hns Er Hgl) as (a0 & Ea0 & Hpa0 & HPa0).
      exists rB a0; [ exact Ee | exact Ea0 | exact Hpa0 |].
      intros P El Hg.
      pose proof (HPa0 P El Hg) as HTP.
      rewrite (blocks_motives_nth _ _ _ Hbk) in Ea0, HTP |- *.
      pose proof (cc_bty_rel b ihs abt a0 Hbk Ei Hir Eabt Ea0) as Hrel.
      (** [ι], at the blocks at [σ']. *)
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      assert (HBt2 : blocks_typed gc_deps gc_stack Δ' p D (List.firstn (ind_nu D) (Us' ++ Ns')) (blocks_sub Bks σ') iA)
        by (rewrite firstn_app_exact by exact HUl'; exact HBt').
      assert (HPl : List.length (Us' ++ Ns') = im_np D Mk) by (rewrite List.length_app, HUl', HNl'; unfold im_np; lia).
      assert (Hbk' : List.nth_error (blocks_sub Bks σ') k = Some (eblock_sub b σ')) by (rewrite nth_error_blocks_sub, Hbk; reflexivity).
      assert (HlB' : brs_lookup (eb_brs (eblock_sub b σ')) c = Some (n, B[sb_qn n σ']))
        by (rewrite Completeness.Inductives.Elim.eb_brs_sub, brs_lookup_sub, HlB; reflexivity).
      set (Ihs := elim_ihs p D oq' Us' (blocks_sub Bks σ') (sb_of_list Id (Us' ++ Ns')) gs As) in *.
      assert (LIhs : List.length Ihs = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
      pose proof (wf_elim_iota_bt Δ' p D oq' k Mk (eblock_sub b σ') (blocks_sub Bks σ') c gs (Us' ++ Ns') As iA n (B[sb_qn n σ'])
                    HΔ' Hl Hgrp HMk Hbk' Hcon HPl cc_Ps_typed HAl HAs HBt2 HlB') as E1.
      rewrite firstn_app_exact, skipn_app_exact in E1 by exact HUl'.
      fold Ihs in E1; rewrite Href in E1; cbn [fst snd] in E1.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in E1.
      set (conA := apps (a_con hd k' c) (im_pre Mk Us' ++ Ns' ++ As)) in *.
      set (A' := (eb_motive b)[sb_qn (S (im_nn Mk)) σ']) in *.
      (** The scrutinee is the constructor, as its member reads it. *)
      assert (Emt : ind_mty p D k Us' Ns' = im_ty_at p k Mk Us' Ns') by (unfold ind_mty; rewrite HMk; reflexivity).
      assert (HMM : Δ' ⊢ M' ≈ conA : ind_mty p D k (List.firstn (ind_nu D) (Us' ++ Ns')) (List.skipn (ind_nu D) (Us' ++ Ns')))
        by (rewrite firstn_app_exact, skipn_app_exact, Emt by exact HUl'; exact (wf_exp_eq_trans _ _ _ _ _ _ _ HMeq cc_con_ref)).
      pose proof (wf_elim_scrut_eq Δ' p D oq' k Mk (eblock_sub b σ') (blocks_sub Bks σ') (Us' ++ Ns') M' conA iA Hl Hgrp HMk Hbk' HPl
                    cc_Ps_typed HBt2 HMM) as E2.
      rewrite firstn_app_exact, skipn_app_exact in E2 by exact HUl'.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in E2; fold A' in E2.
      pose proof (bt_motive _ _ _ _ _ _ _ _ HBt' _ _ _ HMk Hbk') as HAt.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMk Hbk) in HAt; fold A' in HAt.
      assert (HΨ : ⊢ elim_mctx p D k Mk (List.firstn (ind_nu D) (Us' ++ Ns')) ++ Δ')
        by (rewrite firstn_app_exact by exact HUl'; gen_presups; assumption).
      destruct (presup_exp_eq HMM) as (_ & HM1 & HM2 & _).
      pose proof (wf_elim_inst_sub_eq _ _ Δ' p D k Mk (Us' ++ Ns') M' conA Hl HMk HΔ' HPl cc_Ps_typed HM1 HM2 HMM HΨ) as Esub.
      rewrite firstn_app_exact, skipn_app_exact in Esub by exact HUl'.
      pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HAt Esub) as E3.
      (** The branch's type at [ι] at [σ'] is the motive at the constructor. *)
      assert (LL : List.length (Ns' ++ As ++ Ihs) = n) by (rewrite !List.length_app, HNl', HAl, LIhs, Hn; lia).
      assert (T1 : (elim_bty p k Mk c gs (eb_motive b) Us)[sb_of_list σ' (Ns' ++ As ++ Ihs)] = A'[sb_of_list Id (Ns' ++ conA :: nil)]).
      { rewrite <- exp_sub_qn_of_list, LL, Hn, (elim_bty_sub p D k Mk c gs (eb_motive b) Us σ' Hc HMk HUl).
        fold A'; rewrite <- HUs', (elim_bty_iota p D k Mk c gs A' Us' Ns' As Ihs Hc HMk HUl' HNl' HAl LIhs).
        rewrite Href; reflexivity. }
      assert (T2 : B[sb_of_list σ' (Ns' ++ As ++ Ihs)] = B[sb_qn n σ'][sb_of_list Id (Ns' ++ As ++ Ihs)])
        by (rewrite <- LL, exp_sub_qn_of_list; reflexivity).
      rewrite T1, T2 in HBgl.
      destruct (presup_exp_eq E3) as (_ & HTm & _).
      assert (Eall : Δ' ⊢ a_elim oq' Us' k (blocks_sub Bks σ') M' ≈ B[sb_qn n σ'][sb_of_list Id (Ns' ++ As ++ Ihs)]
                       : A'[sb_of_list Id (Ns' ++ M' :: nil)]).
      { eapply wf_exp_eq_trans; [ exact E2 |].
        eapply wf_exp_eq_conv; [ exact E1 | exact HTm | apply wf_exp_eq_sym; exact E3 ]. }
      (** The branch's gluing moved to the motive's. *)
      assert (HTbr : Δ' ⊢ A'[sb_of_list Id (Ns' ++ conA :: nil)] ® P)
        by (eapply glu_univ_elem_typ_resp_exp_eq; [ exact Hg | exact HTP | exact E3 ]).
      pose proof (glu_univ_elem_exp_conv Hrel Hgb Hg HBgl HTbr) as HM3.
      pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hg _ _ _ _ _ HM3 (wf_exp_eq_sym _ _ _ _ _ _ E3)) as HM4.
      rewrite <- HUs'.
      exact (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hg _ _ _ _ _ HM4 (wf_exp_eq_sym _ _ _ _ _ _ Eall)).
    Qed.
  End ConCase.

  (** ** Fresh Variables, Glued

      The fresh variables a stuck eliminator's readback reads a block's
      motive under, at [ups], against the entries of the motive's context
      in [ρ]: each of a type related to its entry's. *)
  Lemma mctx_entry_link : forall v Mv, ind_member D v = Some Mv -> forall s ns hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
      tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns ->
      ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      forall kk X a, List.nth_error (List.rev (elim_mctx p D v Mv Us)) kk = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn kk (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv) :: nil)) ↘ a ->
        exists b (n : nat), List.nth_error (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (s + im_nn Mv) :: nil) kk = Some (⇑! b (s + kk)) /\
          Dom a ≈ b ∈ per_univ n.
  Proof.
    intros v Mv HMv s ns hd k pre Fn Hns Er kk X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (HMall _ _ HMv) as HMm.
    pose proof (rel_ctx_wf_tail HMm) as HNt.
    pose proof (member_params_ass D Hc _ _ HMv) as HPa.
    pose proof (vid_params _ HD _ _ HMv) as HPs.
    pose proof (EB Completeness.Inductives.Elim.nparams_closed_of_canon v Mv HMv ns ns Hns) as Hpg.
    unfold elim_mctx in HX; cbn [List.rev] in HX.
    destruct (Nat.lt_ge_cases kk (im_nn Mv)) as [Hk | Hk].
    - (** A non-uniform parameter. *)
      rewrite List.nth_error_app1 in HX by (rewrite List.length_rev, length_tele_sub, length_im_nparams; lia).
      rewrite firstn_app_le in Ea by lia.
      destruct (inst_entry_link (im_nparams Mv) HPa HPs HNt ns Hpg ltac:(rewrite length_im_nparams; exact Ln) kk X a HX Ea)
        as (A0 & b & n & HA & Eb & Hab).
      destruct (fresh_tele_nth _ _ _ _ Fn kk A0 HA) as (b' & Eb' & Hb').
      rewrite <- env_args_app in Eb'.
      assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
      exists b, n; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
    - (** The scrutinee: at the member's type. *)
      assert (kk = im_nn Mv) as ->.
      { match type of HX with List.nth_error ?l _ = _ =>
          assert (Hlt : kk < List.length l) by (apply List.nth_error_Some; rewrite HX; discriminate) end.
        rewrite List.length_app, List.length_rev, length_tele_sub, length_im_nparams in Hlt; cbn in Hlt; lia. }
      rewrite List.nth_error_app2 in HX by (rewrite List.length_rev, length_tele_sub, length_im_nparams; lia).
      rewrite List.length_rev, length_tele_sub, length_im_nparams, Nat.sub_diag in HX; cbn in HX; injection HX as <-.
      rewrite firstn_app_le, List.firstn_all2 in Ea by lia.
      destruct (Completeness.Inductives.Elim.mty_vars_valid p D Hvg Hcv v Mv HMv) as [jx HXv].
      destruct (inst_link (im_nparams Mv) _ jx ns HPa HPs HNt HXv Hpg ltac:(rewrite length_im_nparams; exact Ln))
        as (a1 & b & Ea1 & Eb & Hab).
      unfold τU in Ea1; rewrite length_im_nparams, (Completeness.Inductives.Elim.mty_vars_inst p D v Mv Us Hc HUl) in Ea1.
      assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (rel_ctx_wf_per_ctx_env HPs) as [RK HRK].
      assert (HKE : RK (env_args nil (ups ++ ns ++ nil)) (env_args nil (ups ++ ns ++ nil))).
      { rewrite List.app_nil_r.
        apply (gargs_env_rel _ _ _ _ _ _ HRK HPs); [ rewrite !List.length_app, length_im_params, ups_len; unfold im_np, ind_nu in *; lia |].
        exact (Completeness.Inductives.Model.params_gargs D HD Hc Hsu v Mv HMv ups ups bu ns ns ups_gargs ups_len Hbu Hns). }
      replace (ups ++ ns) with (ups ++ ns ++ nil) in Eb by (rewrite List.app_nil_r; reflexivity).
      destruct (mty_val_rel VP HVP p D HPD ups ups_len ups_gargs v Mv hd k pre (im_nparams Mv) RK ns nil 0 b ns HMv Er HPs HRK
                  ltac:(rewrite List.app_nil_r, length_im_nparams; exact Ln) Ln eq_refl HKE Eb Hns) as (i0 & R0 & H0).
      destruct (Decl.per_univ_elem_to_nat _ _ _ _ H0) as [n0 Hn0].
      exists (d_ind hd k (pre ++ ns)), n0; split.
      + rewrite List.nth_error_app2, Ln, Nat.sub_diag by lia; reflexivity.
      + apply per_univ_sym'; eapply per_univ_trans'; [ exists R0; exact Hn0 | apply per_univ_sym'; exact Hab ].
  Qed.

  (** The readback of the motive of the block of the member [v] under the
      fresh variables, against the motive at [σ''] past its context. *)
  Lemma rb_motive : forall v Mv b, ind_member D v = Some Mv -> List.nth_error Bks v = Some b ->
      forall Δ σ'' hd k pre ns a A', Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> ⟦mref v of p ups ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ length Δ ↘ ns ->
      ⟦ eb_motive b ⟧ env_args ρ (ns ++ ⇑! (d_ind hd k (pre ++ ns)) (length Δ + im_nn Mv) :: nil) ↘ a ->
      Rtyp a in gc_deps ⍮ gc_stack ⍮ S (length Δ + im_nn Mv) ↘ A' ->
      elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ (eb_motive b)[sb_qn (S (im_nn Mv)) σ''] ≈ A' : Typeω@iA.
  Proof.
    intros v Mv b HMv Hb Δ σ'' hd k pre ns a A' Hσ'' Er Fn Ea HRA.
    destruct (Completeness.Inductives.ViewReadback.fresh_nparams_exist p D Hvg ups ups_gargs ups_len v Mv (List.length Δ) HMv)
      as (ns' & Fn' & Hns).
    pose proof (functional_fresh_tele' _ _ _ _ _ Fn' Fn) as <-.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    pose proof (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMv Hb) as HAg.
    destruct HAg as [SbM HSbM iM HAg'].
    assert (HMl : List.length (elim_mctx p D v Mv Us) = S (im_nn Mv)) by (rewrite length_elim_mctx; reflexivity).
    assert (Lx : List.length (ns' ++ ⇑! (d_ind hd k (pre ++ ns')) (List.length Δ + im_nn Mv) :: nil) = List.length (elim_mctx p D v Mv Us))
      by (rewrite HMl, List.length_app, Ln; cbn; lia).
    pose proof (glu_sub_fresh _ Γ SbΓ (elim_mctx_ass p D v Mv Us Hc HMv) HSbΓ SbM HSbM Δ σ'' ρ _ Hσ'' Lx
                  (mctx_entry_link v Mv HMv (List.length Δ) ns' hd k pre Fn Hns Er)) as Hτ.
    rewrite (elim_mctx_sub p D v Mv Us σ'' Hc HMv HUl), HMl in Hτ.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM (gbk_motive _ _ _ _ _ _ HBg _ _ _ HMv Hb) Hτ) as (HAτ & a0 & Ea0 & Hpa & HPa).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (P & El & Hg).
    pose proof (HPa P El Hg) as HP.
    destruct (realize_glu_typ_top _ _ _ _ Hg _ _ HP) as [_ _ Hrbt].
    assert (HΔm : ⊢ elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ) by (gen_presups; assumption).
    assert (Hlen : List.length (elim_mctx p D v Mv (List.map (fun U => U[σ'']) Us) ++ Δ) = S (List.length Δ + im_nn Mv))
      by (rewrite List.length_app, length_elim_mctx; lia).
    rewrite <- Hlen in HRA.
    pose proof (Hrbt _ wk_id _ (kripke_id _ HΔm) HRA) as H.
    rewrite exp_wk_id in H; exact H.
  Qed.

  (** The fresh variables a stuck eliminator's readback reads a branch of
      the member [v] under, at [ups] (the non-uniform parameters, the
      arguments and the recursive results), against the entries of the
      branch's context in [ρ]: each of a type related to its entry's. *)
  Lemma bctx_entry_link : forall v Mv c gs, ind_member D v = Some Mv -> ind_con Mv c = Some gs ->
      forall s ns vs ihs hd k pre,
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
      Fcargs gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns) ⍮ (s + im_nn Mv) ↘ vs ->
      Fihs vs at gs gs under ρ (blocks_motives Bks) in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns)
        ⍮ (s + im_nn Mv + List.length gs) ↘ ihs ->
      List.length pre = im_unu D Mv ->
      G v ups ups ns ns (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)) ->
      rec_results_rel dr Rel v ups ups ns ns gs vs vs ihs ihs ->
      forall kk X a, List.nth_error (List.rev (elim_bctx p D Mv gs (blocks_motives Bks) Us)) kk = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn kk (ns ++ vs ++ ihs)) ↘ a ->
        exists b (n : nat), List.nth_error (ns ++ vs ++ ihs) kk = Some (⇑! b (s + kk)) /\ Dom a ≈ b ∈ per_univ n.
  Proof.
    intros v Mv c gs HMv Hcon s ns vs ihs hd k pre Fn Fc Fi Lpre Hm Hir kk X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_im_nparams in Ln.
    assert (Hns : tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns /\ con_args_rel p D (okr_at D ups nr) nr ar dr v ups ups ns ns gs vs vs /\
                  tele_rel (ar v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs)).
    { unfold grp_rel in Hm; inversion Hm; subst.
      match goal with H1 : ind_member D v = Some ?M1 |- _ => rewrite HMv in H1; injection H1 as <- end.
      match goal with H1 : ind_con Mv c = Some ?g1 |- _ => rewrite Hcon in H1; injection H1 as <- end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app; lia ]; destruct E as [-> ->] end.
      match goal with E : (?b1 ++ ?w1 = (pre ++ ns) ++ vs)%list |- _ =>
        apply app_split_eq in E; [| rewrite List.length_app in *; lia ]; destruct E as [-> ->] end.
      rewrite skipn_app_exact in * by exact Lpre.
      split; [ assumption | split; assumption ]. }
    destruct Hns as (Hns & Hia & Hav).
    destruct (ER con_args_rel_length _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
    destruct (Completeness.Inductives.Elim.rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
    assert (Hbe : elim_bctx p D Mv gs (blocks_motives Bks) Us
                  = ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                    ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)
      by (unfold elim_bctx; rewrite tele_sub_app, length_im_nparams; reflexivity).
    rewrite Hbe, List.rev_app_distr in HX.
    assert (LC : List.length (List.rev (tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)) = (im_nn Mv + List.length gs)%nat)
      by (rewrite List.length_rev, length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams; lia).
    destruct (Nat.lt_ge_cases kk (im_nn Mv + List.length gs)) as [Hk | Hk].
    - (** The non-uniform parameters and the arguments: entries of the
          instance at [τU] of a closed telescope. *)
      rewrite List.nth_error_app1 in HX by lia.
      assert (Hfk : List.firstn kk (ns ++ vs ++ ihs) = List.firstn kk (ns ++ vs))
        by (rewrite List.app_assoc, firstn_app_le by (rewrite List.length_app; lia); reflexivity).
      rewrite Hfk in Ea.
      pose proof (EB Completeness.Inductives.Elim.closed_args_gargs v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                    (List.length gs) (le_n _)) as Hpg.
      rewrite List.firstn_all2, List.firstn_all2 in Hpg by lia.
      assert (HCa : tele_ass ((cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D))
        by (rewrite <- List.app_assoc; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMv) ]).
      assert (HCs : ⊨ (cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; exact (vg_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon)).
      assert (HCS : ⊨ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU ++ Γ).
      { pose proof (Completeness.Inductives.Elim.ihs_pre_sem p D Γ Us Bks Mv gs (vbs_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon)
                      nil gs eq_refl) as H.
        cbn [ihs_ctx_aux List.app] in H; unfold cinst in H.
        rewrite tele_sub_app, length_im_nparams, <- List.app_assoc; exact H. }
      destruct (inst_entry_link _ HCa HCs HCS (ns ++ vs) Hpg
                  ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia) kk X a HX Ea) as (A0 & b & n & HA0 & Eb & Hab).
      rewrite List.rev_app_distr in HA0.
      destruct (Nat.lt_ge_cases kk (im_nn Mv)) as [Hk1 | Hk1].
      + rewrite List.nth_error_app1 in HA0 by (rewrite List.length_rev, length_im_nparams; lia).
        destruct (fresh_tele_nth _ _ _ _ Fn kk A0 HA0) as (b' & Eb' & Hb').
        rewrite <- env_args_app in Eb'.
        rewrite firstn_app_le in Eb by lia.
        assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
        exists b, n; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
      + rewrite List.nth_error_app2 in HA0 by (rewrite List.length_rev, length_im_nparams; lia).
        rewrite List.length_rev, length_im_nparams in HA0.
        destruct (nth_error_lt_some gs (kk - im_nn Mv) ltac:(lia)) as [g Hg].
        destruct (List.nth_error_split _ _ Hg) as (gs1 & gs2 & Heq & Hl1).
        rewrite <- Hl1 in HA0.
        rewrite firstn_app_ge in Eb by lia; rewrite Ln in Eb; rewrite <- Hl1 in Eb.
        assert (Hnthw : forall x, List.nth_error vs (List.length gs1) = Some x -> List.nth_error (ns ++ vs ++ ihs) kk = Some x).
        { intros x Hx; rewrite List.nth_error_app2 by lia; rewrite Ln, <- Hl1; rewrite List.nth_error_app1 by lia; exact Hx. }
        destruct (fresh_cargs_nth _ _ _ _ _ _ Fc gs1 g gs2 Heq) as [Fa Fr].
        pose proof (EB Completeness.Inductives.Elim.closed_args_gargs v Mv c gs HMv Hcon ns ns vs vs Hns Hav Hia
                      (List.length gs1) ltac:(lia)) as Hpg1.
        replace (List.firstn (List.length gs1) gs) with gs1 in Hpg1 by (rewrite Heq; symmetry; apply firstn_app_len; reflexivity).
        assert (Hpg2 : per_gargs (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) nil nil
                         (ups ++ ns ++ List.firstn (List.length gs1) vs) (ups ++ ns ++ List.firstn (List.length gs1) vs)).
        { unfold im_params; rewrite List.app_assoc, List.rev_app_distr.
          apply Decl.per_gargs_app_intro; [ rewrite List.length_rev; exact ups_len | exact ups_gargs | exact Hpg1 ]. }
        assert (Lfa : List.length (List.firstn (List.length gs1) vs) = List.length gs1) by (rewrite List.length_firstn; lia).
        destruct g as [B0 | t].
        * (** A non-recursive argument: its type at the non-recursive
              values. *)
          pose proof (cargs_rev_nth_arg p D Mv gs gs1 B0 gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as ->.
          destruct (Fa B0 eq_refl) as (a' & Ea' & Hv).
          rewrite <- env_args_app, <- List.app_assoc in Ea'.
          destruct (vg_arg_types p D Hvg Hcv v Mv c gs gs1 B0 gs2 ups ns (List.firstn (List.length gs1) vs) HMv Hcon Heq ups_len Ln Lfa Hpg2)
            as (i & R & a1 & a1' & Ea1 & Ea1' & HR).
          assert (a1 = b) as -> by (eapply functional_eval_exp; eassumption).
          assert (a1' = a') as -> by (eapply functional_eval_exp; eassumption).
          exists a', n; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia |].
          eapply per_univ_trans'; [ exact Hab | exists R; exact HR ].
        * (** A recursive argument: the type of its shape ([shty_link]). *)
          pose proof (cargs_rev_nth_rec p D Mv gs gs1 t gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as ->.
          destruct (Fr t eq_refl) as (a' & Ea' & Hv).
          rewrite <- env_args_app, <- List.app_assoc in Ea'.
          set (fa := List.firstn (List.length gs1) vs) in *.
          pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hav Lv Heq) as Hpk; fold fa in Hpk.
          destruct (vg_cargs_sem_all p D Hvg Hcv v Mv c gs HMv Hcon gs1 (ca_rec t :: gs2) Heq) as [HW0 _].
          destruct (rel_ctx_wf_per_ctx_env HW0) as [R0 HR0].
          assert (HE0 : R0 (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))).
          { apply (gargs_env_rel _ _ _ _ _ _ HR0 HW0);
              [ rewrite !List.length_app, length_cargs_ctx, length_im_params, Ln, Lfa, ups_len; unfold im_np, ind_nu in *; lia |].
            exact Hpg2. }
          assert (Hpre_env : forall R, EF cargs_ctx p D Mv gs1 ++ im_params D Mv ≈ cargs_ctx p D Mv gs1 ++ im_params D Mv
                                          ∈ per_ctx_env ↘ R ->
                               R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))).
          { intros R HR; apply (per_ctx_env_right_irrel _ _ _ _ _ HR0 HR); exact HE0. }
          pose proof (fun Mj qc kc Is vm Dq cups cs bs0 bs0' =>
                        ViewReadback.view_end_type VP HVP p D HPD ups ups_gargs ups_len (ptyp_mem t) Mj qc kc Is vm Dq cups cs bs0 bs0') as Hend.
          assert (Hbb : Dom b ≈ b ∈ per_univ n) by (eapply per_univ_trans'; [ apply per_univ_sym'; exact Hab | exact Hab ]).
          destruct Hbb as [Rb HRb].
          destruct (shty_link p D Hvg Hcv v Mv c gs HMv Hcon (vg_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon) gs1 t gs2 Heq
                      ups ns fa ups_len Ln Lfa ups_gargs Hns Hpk Hpre_env Hend
                      (List.length (ptyp_doms t)) 0 nil b n Rb ltac:(lia) (tele_prefix_rel_nil _) ltac:(cbn; apply per_gargs_nil)
                      ltac:(cbn [List.repeat List.app ptyp_skip]; rewrite List.app_nil_r; exact Eb) HRb)
            as (bsh & Ebsh & Hbs).
          cbn [ptyp_skip] in Ebsh; rewrite List.app_nil_r in Ebsh.
          pose proof (functional_eval_shty _ _ _ _ _ _ Ebsh Ea') as <-.
          exists bsh, n; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia |].
          eapply per_univ_trans'; [ exact Hab | exact Hbs ].
    - (** A recursive result: the type of the recursive result
          ([ihty_link]). *)
      rewrite List.nth_error_app2 in HX by lia; rewrite LC in HX.
      destruct (ihs_rev_nth (im_nn Mv) (blocks_motives Bks) Us (List.length gs) gs (kk - (im_nn Mv + List.length gs)) _ HX)
        as (gs1 & t & gs2 & Heq & Hi' & HXe).
      rewrite <- Hi' in HXe; injection HXe as ->.
      set (j := cargs_nrec gs1) in *.
      assert (Hfk : List.firstn kk (ns ++ vs ++ ihs) = (ns ++ vs) ++ List.firstn j ihs)
        by (rewrite List.app_assoc, firstn_app_ge by (rewrite List.length_app; lia); rewrite List.length_app, Ln, Lv, Hi'; reflexivity).
      rewrite Hfk in Ea.
      destruct (Completeness.Inductives.Elim.con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & v' & Hx & Hv1' & Hsh).
      rewrite Hv1' in Hx; injection Hx as <-.
      destruct (fresh_ihs_nth _ _ _ _ _ _ _ Fi gs1 t gs2 Heq) as (v0 & a' & Hv0 & Ea' & Hih).
      rewrite Hv1' in Hv0; injection Hv0 as <-.
      set (fa := List.firstn (List.length gs1) vs) in *.
      set (aft := List.skipn (S (List.length gs1)) vs).
      assert (Evs : vs = fa ++ v' :: aft) by (unfold fa, aft; rewrite <- (skipn_nth_cons' _ _ _ Hv1'), List.firstn_skipn; reflexivity).
      assert (Lj : j <= List.length ihs) by (rewrite Li; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
      set (ihp := List.firstn j ihs) in *.
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn, Lv, Heq, List.length_app; cbn; lia).
      assert (Laft : List.length aft = List.length gs2) by (unfold aft; rewrite List.length_skipn, Lv, Heq, List.length_app; cbn; lia).
      assert (Lihp : List.length ihp = j) by (unfold ihp; rewrite List.length_firstn; lia).
      pose proof (vbs_bctx _ _ _ _ _ _ HBv v Mv c gs HMv Hcon) as HBs.
      pose proof (EB Completeness.Inductives.Elim.e_HCtxT ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs gs1 t gs2 Heq) as HCtxT.
      destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HCtxT) as [jT HT].
      pose proof (rel_ctx_wf_tail HCtxT) as HCtx.
      destruct (rel_ctx_wf_per_ctx_env HCtx) as [RS HRS].
      destruct (rel_ctx_wf_per_ctx_env HBs) as [RB HRB].
      assert (Hm' : G v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                      (d_con hd k c ((pre ++ ns) ++ vs)) (d_con hd k c ((pre ++ ns) ++ vs)))
        by (rewrite skipn_app_exact by exact Lpre; exact Hm).
      assert (Hir' : rec_results_rel dr Rel v ups ups (List.skipn (im_unu D Mv) (pre ++ ns)) (List.skipn (im_unu D Mv) (pre ++ ns))
                       gs vs vs ihs ihs)
        by (rewrite skipn_app_exact by exact Lpre; exact Hir).
      pose proof (EB Completeness.Inductives.Elim.cv_bctx_elem ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs ρ ρ Hρ Hρ
                    ups ups hd k (pre ++ ns) (pre ++ ns) vs vs ihs ihs Hm' Hir' RB HRB) as HZ.
      rewrite skipn_app_exact in HZ by exact Lpre.
      assert (HEE : RS (env_args ρ (ns ++ vs ++ ihp)) (env_args ρ (ns ++ vs ++ ihp))).
      { assert (Esp : ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs
                     = ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)
                       ++ ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs1)
          by (rewrite Heq at 2; rewrite Views.ihs_ctx_aux_app, List.app_nil_r; reflexivity).
        assert (Esplit : elim_bctx p D Mv gs (blocks_motives Bks) Us ++ Γ
                         = ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) nil 0 gs ++ cinst Γ p D Mv Us gs)
          by (unfold elim_bctx, cinst; rewrite <- !List.app_assoc; reflexivity).
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite Esplit, Esp, <- List.app_assoc in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2)))
          in HRB', HBs'.
        assert (Lr : List.length (List.skipn j ihs)
                     = List.length (List.rev (ihs_ctx_aux (im_nn Mv) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))))
          by (rewrite List.length_rev, length_ihs_ctx_aux, List.length_skipn, Li; unfold j; rewrite Heq, Views.cargs_nrec_app; cbn; lia).
        assert (HZ' : RB (env_args (env_args ρ (ns ++ vs ++ ihp)) (List.skipn j ihs)) (env_args (env_args ρ (ns ++ vs ++ ihp)) (List.skipn j ihs)))
          by (rewrite <- env_args_app, <- !List.app_assoc; unfold ihp; rewrite List.firstn_skipn; exact HZ).
        destruct (Decl.rel_gargs _ _ _ _ HRS HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ') as [H _].
        exact H. }
      rewrite Evs, <- !List.app_assoc in HEE; cbn [List.app] in HEE.
      rewrite <- List.app_assoc, Evs, <- !List.app_assoc in Ea; cbn [List.app] in Ea.
      destruct (rel_exp_of_typ_inversion_simple_at HRS HT _ _ HEE) as (ty & ty' & Et & Et' & [R HR]).
      assert (ty = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (ty' = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (EB Completeness.Inductives.Elim.side_w ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs gs1 t gs2 Heq RS HRS
                  ρ ns fa v' aft ihp Hρ Ln Lfa Laft Lihp HEE) as (w & Hw & HwU & Lw).
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hav Lv Heq) as Hpk; fold fa in Hpk.
      destruct (rec_shape_facts v Mv c gs1 t gs2 0 HMv ltac:(rewrite <- Heq; exact Hcon)) as ((Mj & HMj & _) & _ & _).
      cbn [ptyp_skip] in HMj.
      destruct (HBks _ _ HMj) as [bj Hbj].
      assert (Hsh0 : rec_arg_rel p D (okr_at D ups nr) nr ar dr v ups ups (ns ++ nonrec_arg_vals gs1 fa ++ nil)
                       (ns ++ nonrec_arg_vals gs1 fa ++ nil) (ptyp_skip 0 t) v' v')
        by (rewrite List.app_nil_r; exact Hsh).
      destruct (EB Completeness.Inductives.Elim.ihty_link ρ Hρ Bks iA HBks HMall HAv v Mv c gs HMv Hcon HBs gs1 t gs2 Heq RS HRS
                  Mj bj HMj Hbj (List.length (ptyp_doms t)) 0 ρ ns fa v' aft ihp w nil v' a jT R eq_refl Ln Lfa Laft Lihp eq_refl
                  Hρ HEE Hw HwU Lw Hns Hpk (tele_prefix_rel_nil _) (eval_apps_nil _ _ _) Hsh0 Ea HR) as (b & Eb & Hab).
      rewrite List.app_nil_r in Eb; cbn [ptyp_skip] in Eb.
      rewrite <- env_args_app, <- List.app_assoc in Ea'.
      pose proof (functional_eval_ihty _ _ _ _ _ _ _ Eb Ea') as <-.
      exists b, jT; split; [| exact Hab ].
      rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
      rewrite List.length_app, Ln, Lv.
      replace (kk - (im_nn Mv + List.length gs)) with j by (unfold j; lia).
      unfold j; rewrite Hih; do 3 f_equal; unfold j in *; lia.
  Qed.

  (** ** On a Neutral

      A neutral of the member [j], glued in the group, at a substitution
      [σ'] glued to [ρ]: the eliminator is stuck, at the motive's value at
      the scrutinee; it is glued there when its readback is the
      elimination's ([nc_out]), which the readback of its blocks under
      fresh variables gives. *)
  Section NeutCase.
    Variables (j : nat) (Mj : imember) (hd : qname) (k' : nat) (as' : list domain) (e : domain_ne)
      (Δ' : ctx) (Us' Ns' : list exp) (M' : exp).
    Hypotheses (HMj : ind_member D j = Some Mj) (Href : im_ref p j Mj = (hd, k')) (He : Dom e ≈ e ∈ per_bot)
      (Hrb : forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (im_ty_at p j Mj Us' Ns')[φ]ʷ).
    Variables (σ' : sub) (oq' : option qname) (ns : list domain).
    Hypotheses (Hgrp : elim_grp D oq' p j) (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HUs' : Us' = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : im_ty_at p j Mj Us' Ns') (Hgn : glu_nparams j Mj NEl Δ' Us' Ns' ns)
      (Hns : tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns)
      (HGm : G j ups ups ns ns (⇑ (d_ind hd k' as') e) (⇑ (d_ind hd k' as') e)).

    Lemma nc_inv : List.length as' = (im_unu D Mj + im_nn Mj)%nat /\
        tele_rel (nr j) (List.rev (im_nparams Mj)) ns (List.skipn (im_unu D Mj) as').
    Proof.
      unfold grp_rel in HGm; inversion HGm; subst.
      match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end.
      split; assumption.
    Qed.

    Lemma nc_Ps_typed : forall i P T, List.nth_error (Us' ++ Ns') i = Some P ->
        List.nth_error (tele_insts (im_params D Mj) Id (Us' ++ Ns')) i = Some T -> Δ' ⊢ P : T.
    Proof.
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (HUl' : List.length Us' = ind_nu D) by (rewrite HUs', List.length_map; exact HUl).
      pose proof (glu_args_of_nparams D ups u NP NEl AP AEl DP DEl Hf j Mj Δ' Us' Ns' ns HMj Hgn Hns) as HgN.
      assert (Hga : glu_args Δ' (im_params D Mj) Id nil (Us' ++ Ns') (ups ++ ns)).
      { unfold im_params; apply glu_args_app; [ exact Ua | exact HUl' | exact ups_len |].
        split; [ exact HUg' | exact HgN ]. }
      exact (glu_args_typed _ _ _ _ _ _ (member_params_ass D Hc _ _ HMj) Hga).
    Qed.

    (** The neutral case, given the readback of the stuck eliminator: its
        value is the stuck eliminator at the motive's value at the stored
        parameters, related to the motive's at [ns]. *)
    Lemma nc_out :
        (forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne d_elim ρ Bks p ups j as' e in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
           Δ ⊢ (a_elim oq' (List.map (fun U => U[σ']) Us) j (blocks_sub Bks σ') M')[φ]ʷ ≈ M0
             : ((List.nth j (blocks_motives Bks) a_True)[sb_qn (S (im_nn Mj)) σ'][sb_of_list Id (Ns' ++ M' :: nil)])[φ]ʷ) ->
        elim_out j Mj Δ' σ' oq' Ns' M' (⇑ (d_ind hd k' as') e) ns.
    Proof.
      intros Hrbe.
      destruct nc_inv as [La Hsn].
      destruct (ER im_ref_target j Mj hd k' HMj Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
      destruct (HBks _ _ HMj) as [b Hb].
      pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ j Mj _ _ _ _ _ _ _ _ HMj HGm Hsn Hns) as HG2.
      destruct (mot_rel j Mj b b ups ups _ ns _ _ HMj Hb Hb HG2) as (a1 & a2 & Ea1 & Ea2 & Hr12).
      assert (Ee : ⟦elim ⇑ (d_ind hd k' as') e at j of p ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ⇑ a1 (d_elim ρ Bks p ups j as' e)).
      { eapply eval_elim_neut; [ exact Hl | exact HMj | exact Href | exact Hq | exact HMq | unfold im_np; lia | exact Hb
                               | rewrite (Hnm _ _ _ HMj Hb), Hnnq; reflexivity | rewrite Hnuq; exact Ea1 ]. }
      (** The motive at the scrutinee, glued in the group ([AtType]). *)
      destruct (Completeness.Inductives.ViewReadback.mref_exists VP HVP p D HPD ups ups_gargs ups_len j Mj HMj) as [[[hd0 k0] pre] Er].
      destruct (Completeness.Inductives.ViewReadback.mref_ref_len p D j Mj ups hd0 k0 pre Hl HMj ups_len Er) as [Href0 Lpre].
      rewrite Href in Href0; injection Href0 as E1 E2; subst hd0 k0.
      assert (HIG : ind_glu_elem p D ups NEl AEl DP DEl j Δ' Us' Ns' M' (⇑ (d_ind hd k' as') e))
        by (eapply ind_glu_elem_neut; eassumption).
      destruct (glu_at_type_all VP HVP HGall Hviewsall p D HPD ups bu u NP NEl AP AEl DP DEl ups_len ups_gargs Hbu Hule Hf
                  nb Hnbu Hnbq) as [Hel _].
      pose proof (us_glu_args Δ' σ' Hσ') as HUg'; rewrite <- HUs' in HUg'.
      assert (Hgl : forall (i : nat) P El, nb <= i -> DG d_ind hd k' (pre ++ ns) ∈ glu_univ_elem i ↘ P ↘ El ->
                Δ' ⊢ im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® P ->
                Δ' ⊢ M' : im_ty_at p j Mj (List.map (fun U => U[σ']) Us) Ns' ® ⇑ (d_ind hd k' as') e ∈ El).
      { intros i P El _ Hglu HT; rewrite <- HUs' in HT |- *.
        exact (Hel _ _ _ _ _ _ HIG Mj ns hd k' pre i P El HMj Er HUg' HMt Hgn Hns HGm Hglu HT). }
      pose proof Hgn as Hgn'; rewrite HUs' in Hgn'.
      destruct (motive_glu j Mj Δ' σ' Ns' ns M' _ hd k' pre HMj Hσ' Hgn' Hns Er Hgl) as (a0 & Ea0 & Hpa0 & HPa0).
      pose proof Ea0 as Ea0'; rewrite (blocks_motives_nth _ _ _ Hb) in Ea0'.
      assert (a0 = a2) as -> by (eapply functional_eval_exp; eassumption).
      exists (⇑ a1 (d_elim ρ Bks p ups j as' e)) a2; [ exact Ee | exact Ea0 | exact Hpa0 |].
      intros P El Hg.
      pose proof (HPa0 P El Hg) as HTP.
      assert (Haa : Dom a2 ≈ a1 ∈ per_univ iA) by (apply per_univ_sym'; eexists; exact Hr12).
      pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ Haa Hg) as Hg1.
      (** The elimination, typed. *)
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      pose proof (blocks_typed_sub _ _ _ _ _ _ _ _ _ _ Hl HUl HBt Hσt) as HBt'; rewrite <- HUs' in HBt'.
      pose proof (gnp_len _ _ _ _ _ _ _ Hgn) as HNl'.
      assert (HUl' : List.length Us' = ind_nu D) by (rewrite HUs', List.length_map; exact HUl).
      assert (HBt2 : blocks_typed gc_deps gc_stack Δ' p D (List.firstn (ind_nu D) (Us' ++ Ns')) (blocks_sub Bks σ') iA)
        by (rewrite firstn_app_exact by exact HUl'; exact HBt').
      assert (HPl : List.length (Us' ++ Ns') = im_np D Mj) by (rewrite List.length_app, HUl', HNl'; unfold im_np; lia).
      assert (Hbk' : List.nth_error (blocks_sub Bks σ') j = Some (eblock_sub b σ')) by (rewrite nth_error_blocks_sub, Hb; reflexivity).
      assert (Emt : ind_mty p D j Us' Ns' = im_ty_at p j Mj Us' Ns') by (unfold ind_mty; rewrite HMj; reflexivity).
      assert (HMM : Δ' ⊢ M' ≈ M' : ind_mty p D j (List.firstn (ind_nu D) (Us' ++ Ns')) (List.skipn (ind_nu D) (Us' ++ Ns')))
        by (rewrite firstn_app_exact, skipn_app_exact, Emt by exact HUl'; apply wf_exp_eq_refl; exact HMt).
      pose proof (wf_elim_scrut_eq Δ' p D oq' j Mj (eblock_sub b σ') (blocks_sub Bks σ') (Us' ++ Ns') M' M' iA Hl Hgrp HMj Hbk' HPl
                    nc_Ps_typed HBt2 HMM) as E2.
      rewrite firstn_app_exact, skipn_app_exact in E2 by exact HUl'.
      rewrite Completeness.Inductives.Elim.eb_motive_sub, (Hnm _ _ _ HMj Hb) in E2.
      destruct (presup_exp_eq E2) as (_ & Hty & _).
      rewrite (blocks_motives_nth _ _ _ Hb) in HTP, Hrbe |- *.
      rewrite <- HUs' in Hrbe |- *.
      eapply realize_glu_elem_bot; [ exact Hg1 |].
      econstructor; [ exact Hty | exact Hg1 | exact HTP | |].
      - exact (ER per_bot_elim j Mj hd k' as' as' e e ups ups ns ns HMj HGm).
      - exact Hrbe.
    Qed.
  End NeutCase.

End ElimGlu.

End Fixed_GCtx.
