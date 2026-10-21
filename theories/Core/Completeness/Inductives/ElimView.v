(** * The Eliminator at a View, as the Container's (E1′)

    The eliminator of a group [D] at its view [m] of the container's
    declared member [k'] at the instance [Is] is the container's
    eliminator at [k'], at the view's blocks wrapped ([vwrap]).  At related
    environments the two eliminate related elements to related values
    (the cross relation): by induction on the group's elements, a
    constructor's branch against its wrapped branch, which is the group's
    branch at an instance of its context ([ViewBranch.v]); a stuck
    eliminator against the container's stuck eliminator, read back alike
    by the views' rank, the blocks the two read being the group's own by
    the agreement of the views' maps ([view_maps_coherent]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con Elim Iota ViewBranch.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Recursive Results a Container Has

    Recursive results of two constructors' arguments [vs] and [vs'] of the
    group's kinds [gs], at the positions the container's kinds [gs'] have
    recursive: related as the group's recursive results there, by the
    shape [gs] gives; none at the others. *)
Inductive wrap_results_rel (dr : nat -> list domain -> exp -> relation domain)
    (Rel : nat -> list domain -> domain -> list domain -> domain -> relation domain) (k : nat) (u u' : list domain) :
    list domain -> list domain -> list carg -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
| wrap_results_nil : forall pre pre', wrap_results_rel dr Rel k u u' pre pre' nil nil nil nil nil nil
| wrap_results_arg : forall pre pre' A' A gs' gs v v' vs vs' ihs ihs',
    wrap_results_rel dr Rel k u u' (pre ++ v :: nil) (pre' ++ v' :: nil) gs' gs vs vs' ihs ihs' ->
    wrap_results_rel dr Rel k u u' pre pre' (ca_arg A' :: gs') (ca_arg A :: gs) (v :: vs) (v' :: vs') ihs ihs'
| wrap_results_nest : forall pre pre' A' t gs' gs v v' vs vs' ihs ihs',
    wrap_results_rel dr Rel k u u' pre pre' gs' gs vs vs' ihs ihs' ->
    wrap_results_rel dr Rel k u u' pre pre' (ca_arg A' :: gs') (ca_rec t :: gs) (v :: vs) (v' :: vs') ihs ihs'
| wrap_results_rec : forall pre pre' t' t gs' gs v v' vs vs' ih ih' ihs ihs',
    rec_result_rel dr Rel k u u' pre pre' t v v' ih ih' ->
    wrap_results_rel dr Rel k u u' pre pre' gs' gs vs vs' ihs ihs' ->
    wrap_results_rel dr Rel k u u' pre pre' (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) (v' :: vs') (ih :: ihs) (ih' :: ihs').

Lemma wrap_results_rel_at : forall dr Rel k u u' pre pre' gs' gs vs vs' ihs ihs',
    wrap_results_rel dr Rel k u u' pre pre' gs' gs vs vs' ihs ihs' ->
    forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
    exists v v' ih ih', List.nth_error vs (List.length gs1) = Some v /\ List.nth_error vs' (List.length gs1) = Some v' /\
      List.nth_error ihs (cargs_nrec gs1') = Some ih /\ List.nth_error ihs' (cargs_nrec gs1') = Some ih' /\
      rec_result_rel dr Rel k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) t v v' ih ih'.
Proof.
  induction 1 as [pre pre' | pre pre' A0' A gs' gs v v' vs vs' ihs ihs' H IH | pre pre' A' t0 gs' gs v v' vs vs' ihs ihs' H IH
                 | pre pre' t0' t0 gs' gs v v' vs vs' ih ih' ihs ihs' Hr H IH];
    intros [| g1' gs1'] Qt' gs2' [| g1 gs1] Qt gs2 Heq' Heq Hl; cbn [List.app List.length] in Heq', Heq, Hl;
    inversion Heq'; inversion Heq; subst; try discriminate.
  - destruct (IH _ _ _ _ _ _ eq_refl eq_refl ltac:(lia)) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hr).
    exists x, x', y, y'; cbn; rewrite <- !List.app_assoc in Hr; repeat split; assumption.
  - destruct (IH _ _ _ _ _ _ eq_refl eq_refl ltac:(lia)) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hr).
    exists x, x', y, y'; cbn; repeat split; assumption.
  - exists v, v', ih, ih'; cbn; rewrite !List.app_nil_r; repeat split; assumption.
  - destruct (IH _ _ _ _ _ _ eq_refl eq_refl ltac:(lia)) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hr0).
    exists x, x', y, y'; cbn; repeat split; assumption.
Qed.

(** A list substitution evaluated: the values of its terms after its
    base's. *)
Lemma eval_sb_of_list_inv : forall Ms σ ρ E E0, ⟦ sb_of_list σ Ms ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ E ->
    ⟦ σ ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ E0 ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ env_eq E (env_args E0 ms).
Proof.
  induction Ms as [| M Ms IH]; intros σ ρ E E0 H H0; cbn [sb_of_list] in H.
  - exists nil; split; [ constructor |]; cbn; intros x; specialize (H x); specialize (H0 x).
    destruct (σ x); cbn in H, H0.
    + rewrite H, H0; reflexivity.
    + destruct H as (m & -> & Hm); destruct H0 as (m' & -> & Hm'); f_equal; eapply functional_eval_exp; eassumption.
    + destruct H as (h & -> & Hh); destruct H0 as (h' & -> & Hh'); f_equal; eapply functional_eval_modexp; eassumption.
  - pose proof (H (List.length Ms + 0)) as Hx; rewrite sb_of_list_ge in Hx; cbn in Hx.
    destruct Hx as (m & Hme & Hm).
    destruct (IH _ _ _ (E0 ↦ m) H (eval_sub_extend _ _ _ _ _ H0 Hm)) as (ms & Hms & HE).
    exists (m :: ms); split; [ econstructor; eassumption | exact HE ].
Qed.

(** ** The Group's Side

    A group [D] of a valid family, the eliminator's context [Γ], its
    uniform parameters [Us] and valid blocks [Bks]; the canonical uniform
    parameters [u0] at an environment [C1], and an environment [C2]
    related to it ([Elim.v], Sections [Base] and [Motives]). *)
Section CrossBase.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hl := vgr_lookup _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.
  Let Hass := vgr_ass _ _ Hvg.
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Variable (C1 : env) (u0 : list domain).
  Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
  Variable (C2 : env).
  Hypothesis (HC12 : RΓ C1 C2).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := vbs_has _ _ _ _ _ _ HBk.
  Let HMall := vbs_mctx _ _ _ _ _ _ HBk.
  Let HAv := vbs_motive _ _ _ _ _ _ HBk.
  Let As := blocks_motives Bks.
  Let τU := sb_of_list Id Us.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C2 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation EM f := (EB f C2 HC12 Bks iA HBks HMall HAv).
  #[local] Abbreviation WB f := (f VP p D HP HPD Γ Us Bks iA HΓ HUl HUs HBk).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).
  #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (icp_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (icp_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (icp_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (icp_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (icp_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (icp_dom_iff _ _ Hcp).
  #[local] Abbreviation trefl_l := (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).

  (** *** The Wrapped Branch's Context at Related Arguments

      Arguments of two constructors of the view's member [v], related
      canonically, with recursive results related where the container has
      them: related at the recursive results of the wrapped branch's
      context.  Each result's type is the group's at the instance of its
      stage ([wrap_ihty_eq]), whose relation is the recursive result's
      ([rest_char]). *)
  Section WrapCv.
    Variable (v : nat) (Mv : imember) (c : String.string) (gs' gs : list carg).
    Hypotheses (HMv : ind_member D v = Some Mv) (Hcon : ind_con Mv c = Some gs) (Hk : cargs_kinds gs' gs).
    Let nn := im_nn Mv.
    Let na := List.length gs.
    Let T := List.rev (im_nparams Mv).
    Let Cs := tele_sub (cargs_ctx p D Mv gs) (sb_qn nn τU).
    Let Ns := tele_sub (im_nparams Mv) τU.
    Let Ψc := Cs ++ Ns ++ Γ.
    Let HB := vbs_bctx _ _ _ _ _ _ HBk _ _ _ _ HMv Hcon.

    Lemma cv_wrap_ihs : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall X X' vs vs' w w',
        tele_rel (nr v) T X X' ->
        tele_rel (ar v X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 X X' gs vs vs' ->
        wrap_results_rel dr Rel v u0 u0 X X' gs' gs vs vs' w w' ->
        per_gargs (List.rev (Cs ++ Ns)) B1 B2 (X ++ vs) (X' ++ vs') ->
        forall kk, kk <= na ->
        per_gargs (List.rev (wrap_ihs_ctx nn As Us na nil 0 (List.firstn kk gs') (List.firstn kk gs)))
          (env_args B1 (X ++ vs)) (env_args B2 (X' ++ vs'))
          (List.firstn (cargs_nrec (List.firstn kk gs')) w) (List.firstn (cargs_nrec (List.firstn kk gs')) w').
    Proof.
      intros B1 B2 HB1 HB2 * HX Har Hia Hwr Hci.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      pose proof HX as HX0; rewrite tele_rel_iff in HX0; destruct HX0 as (LX & LX' & _).
      unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
      pose proof (trefl_l _ _ HMv _ _ HX) as HXX.
      pose proof (cargs_kinds_length _ _ Hk) as Lgs.
      induction kk as [| kk IH]; intros Hkk; [ cbn; constructor |].
      destruct (nth_error_lt_some' gs kk ltac:(unfold na in Hkk; lia)) as [g Hg].
      destruct (nth_error_lt_some' gs' kk ltac:(unfold na in Hkk; lia)) as [g' Hg'].
      assert (Heq0 : gs = List.firstn kk gs ++ g :: List.skipn (S kk) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg), List.firstn_skipn; reflexivity).
      assert (Heq0' : gs' = List.firstn kk gs' ++ g' :: List.skipn (S kk) gs')
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg'), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn kk gs) = kk) by (rewrite List.length_firstn; unfold na in Hkk; lia).
      assert (Lk' : List.length (List.firstn kk gs') = kk) by (rewrite List.length_firstn; unfold na in Hkk; lia).
      pose proof (IH ltac:(lia)) as IHk.
      rewrite (firstn_S_snoc _ _ _ Hg), (firstn_S_snoc _ _ _ Hg').
      set (G1 := List.firstn kk gs) in *; set (G1' := List.firstn kk gs') in *.
      set (G2 := List.skipn (S kk) gs) in *; set (G2' := List.skipn (S kk) gs') in *.
      assert (Hkk' : cargs_kinds (G1' ++ g' :: G2') (G1 ++ g :: G2)) by (rewrite <- Heq0, <- Heq0'; exact Hk).
      destruct (cargs_kinds_app_inv G1' G1 (g' :: G2') (g :: G2) ltac:(lia) Hkk') as [Hk1 Hkg].
      rewrite wrap_ihs_ctx_app by exact Hk1.
      rewrite cargs_nrec_app'.
      destruct g' as [A' | t'], g as [A | t]; cbn in Hkg; try contradiction; cbn [wrap_ihs_ctx List.app cargs_nrec];
        rewrite ?Nat.add_0_r; try exact IHk.
      (** An argument recursive in both: its result. *)
      cbn [Nat.add].
      set (r := cargs_nrec G1') in *.
      assert (LG : List.length G1' = List.length G1) by lia.
      destruct (wrap_results_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ Hwr G1' t' G2' G1 t G2 Heq0' Heq0 LG)
        as (x & x' & ih & ih' & Hx & Hx' & Hih & Hih' & Hrr).
      destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia G1 t G2 Heq0) as (y & y' & Hy & Hy' & Hra).
      rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
      rewrite Nat.add_1_r; unfold r; rewrite (firstn_S_snoc _ _ _ Hih), (firstn_S_snoc _ _ _ Hih'); fold r.
      cbn [List.rev].
      set (W1 := wrap_ihs_ctx nn As Us na nil 0 G1' G1) in *.
      pose proof (WB w_valid v Mv c gs' gs HMv Hcon Hk G1' (ca_rec t' :: G2') G1 (ca_rec t :: G2) Heq0' Heq0 LG) as HEW.
      pose proof (WB w_valid v Mv c gs' gs HMv Hcon Hk (G1' ++ ca_rec t' :: nil) G2' (G1 ++ ca_rec t :: nil) G2
                    ltac:(rewrite <- List.app_assoc; exact Heq0') ltac:(rewrite <- List.app_assoc; exact Heq0)
                    ltac:(rewrite !List.length_app; cbn; lia)) as HWT.
      rewrite wrap_ihs_ctx_app in HWT by exact Hk1; cbn [wrap_ihs_ctx List.app Nat.add] in HWT.
      fold r W1 in HWT.
      fold nn na As W1 τU Cs Ns in HEW, HWT.
      destruct (rel_ctx_wf_ass_inv HWT) as [jT HT].
      destruct (rel_ctx_wf_per_ctx_env HEW) as [RW HRW].
      assert (LW1 : List.length W1 = r) by (unfold W1, r; apply length_wrap_ihs_ctx; exact Hk1).
      assert (Lw : r <= List.length w)
        by (pose proof (proj1 (List.nth_error_Some w r) ltac:(unfold r; rewrite Hih; discriminate)); lia).
      assert (Lw' : r <= List.length w')
        by (pose proof (proj1 (List.nth_error_Some w' r) ltac:(unfold r; rewrite Hih'; discriminate)); lia).
      assert (LCN : List.length (Cs ++ Ns) = List.length (X ++ vs))
        by (unfold Cs, Ns; rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams; unfold nn, im_nn in *; lia).
      assert (HEp : RW (env_args B1 ((X ++ vs) ++ List.firstn r w)) (env_args B2 ((X' ++ vs') ++ List.firstn r w'))).
      { pose proof HRW as HRW'; replace (W1 ++ Cs ++ Ns ++ Γ) with ((W1 ++ Cs ++ Ns) ++ Γ) in HRW' by (rewrite <- !List.app_assoc; reflexivity).
        pose proof HEW as HEW'; replace (W1 ++ Cs ++ Ns ++ Γ) with ((W1 ++ Cs ++ Ns) ++ Γ) in HEW' by (rewrite <- !List.app_assoc; reflexivity).
        eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRW' HEW' HB12).
        - pose proof LCN as L0; rewrite !List.length_app in L0; rewrite !List.length_app, List.length_firstn; lia.
        - rewrite (List.rev_app_distr W1 (Cs ++ Ns)); apply per_gargs_app_intro;
            [ rewrite List.length_rev; exact (eq_sym LCN) | exact Hci | exact IHk ]. }
      destruct (rel_exp_of_typ_inversion_simple_at HRW HT _ _ HEp) as (ty & ty' & Et & Et' & [R HR]).
      destruct (per_univ_elem_to_nat _ _ _ _ HR) as [n Hn].
      pose proof Et as EtF; pose proof Et' as EtF'.
      rewrite env_args_app in Et, Et'.
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R);
        [ rewrite List.length_rev, List.length_firstn, LW1; lia | exact IHk | exact (mk_rel_mod_eval _ _ Et Et' Hn) |].
      clear Et Et'.
      (** The stage's instance takes the two sides to the group's branch
          context, where the result's type is the group's. *)
      pose proof (WB st_sub v Mv c gs' gs HMv Hcon Hk G1' (ca_rec t' :: G2') G1 (ca_rec t :: G2) Heq0' Heq0 LG HEW) as SW.
      fold nn na As in SW; fold W1 in SW; rewrite LW1 in SW.
      set (Lt := wrap_ihs G1' G1 _ 0 r) in SW.
      assert (LLt : List.length Lt = cargs_nrec G1)
        by (unfold Lt; exact (WB length_wrap_ihs_kinds v Mv c gs' gs HMv Hcon Hk G1' G1 _ 0 r Hk1)).
      assert (HQ : ihs_ctx_aux nn As Us na nil 0 G1 ++ cinst Γ p D Mv Us gs = ihs_ctx_aux nn As Us na nil 0 G1 ++ Cs ++ Ns ++ Γ)
        by (rewrite cinst_eq, tele_sub_app, length_im_nparams, <- List.app_assoc; reflexivity).
      pose proof (EB e_HCtx C2 HC12 Bks iA HBks HMall HAv v Mv c gs HMv Hcon HB G1 t G2 Heq0) as HCtx.
      pose proof (EB e_HCtxT C2 HC12 Bks iA HBks HMall HAv v Mv c gs HMv Hcon HB G1 t G2 Heq0) as HCtx2.
      destruct (rel_ctx_wf_ass_inv HCtx2) as [jG HTG].
      destruct (rel_ctx_wf_per_ctx_env HCtx) as [RS HRS].
      destruct (rel_sub_under_ctx_simple (gsub_valid SW)) as (RW0 & HRW0 & RS0 & HRS0 & Hsb).
      assert (EW : RW0 <~> RW) by (eapply per_ctx_env_right_irrel; [ exact HRW0 | exact HRW ]).
      pose proof HRS as HRS'; fold nn na As in HRS'; rewrite HQ in HRS'.
      assert (ES : RS0 <~> RS) by (eapply per_ctx_env_right_irrel; [ exact HRS0 | exact HRS' ]).
      assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
      destruct (Hsb _ _ (proj2 (EW _ _) HEp)) as (F1 & F2 & EF1 & EF2 & HF12).
      apply ES in HF12.
      assert (Hwk : forall (B : env) (l : list domain), List.length l = r + na + nn -> ⟦ ι wk_shiftn (r + na + nn) ⟧s env_args B l ↘ B).
      { intros B l Ll.
        pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length l)) (env_args B l) (wk_mono_shiftn _)) as H.
        rewrite eval_wk_shiftn_args, Ll in H; exact H. }
      assert (Hdec : forall B Y ys wr F, List.length Y = nn -> List.length ys = na -> List.length wr = r ->
                ⟦ wrap_inst nn na r Lt ⟧s env_args B ((Y ++ ys) ++ wr) ↘ F ->
                exists ihp, ⟦ Lt ⟧* gc_deps ⍮ gc_stack ⍮ env_args B ((Y ++ ys) ++ wr) ↘ ihp /\ List.length ihp = cargs_nrec G1 /\
                  ⟦ wrap_inst nn na r Lt ⟧s env_args B ((Y ++ ys) ++ wr) ↘ env_args B (Y ++ ys ++ ihp) /\
                  env_eq F (env_args B (Y ++ ys ++ ihp))).
      { intros B Y ys wr F LY Lys Lwr HF.
        assert (Lall : List.length ((Y ++ ys) ++ wr) = r + na + nn) by (rewrite !List.length_app; lia).
        destruct (eval_sb_of_list_inv _ _ _ _ _ HF (Hwk B _ Lall)) as (ms & Hms & Hee).
        destruct (eval_exps_app_inv _ _ _ _ _ _ Hms) as (m1 & m23 & -> & Hm1 & Hm23).
        destruct (eval_exps_app_inv _ _ _ _ _ _ Hm23) as (m2 & ihp & -> & Hm2 & Hih0).
        pose proof (eval_vars_from_args Y B (ys ++ wr)) as HY; rewrite <- List.app_assoc in Hm1; rewrite List.length_app, Lys, Lwr, LY in HY.
        replace (na + r) with (r + na) in HY by lia.
        pose proof (functional_eval_exps' _ _ _ _ Hm1 HY) as ->.
        pose proof (eval_vars_from_args ys (env_args B Y) wr) as Hys; rewrite <- List.app_assoc, env_args_app in Hm2; rewrite Lys, Lwr in Hys.
        pose proof (functional_eval_exps' _ _ _ _ Hm2 Hys) as ->.
        exists ihp; split; [ exact Hih0 | split; [ rewrite (eval_exps_length _ _ _ Hih0); exact LLt | split; [| exact Hee ] ] ].
        apply eval_sb_of_list; [ exact (Hwk B _ Lall) |].
        apply eval_exps_app; [ rewrite <- List.app_assoc; exact HY |].
        apply eval_exps_app; [ rewrite <- List.app_assoc, env_args_app; exact Hys | exact Hih0 ]. }
      assert (Lr : List.length (List.firstn r w) = r) by (rewrite List.length_firstn; lia).
      assert (Lr' : List.length (List.firstn r w') = r) by (rewrite List.length_firstn; lia).
      destruct (Hdec _ _ _ _ _ LX Lv Lr EF1) as (ihp & Eihp & Lihp & Eτ1 & Ee1).
      destruct (Hdec _ _ _ _ _ LX' Lv' Lr' EF2) as (ihp' & Eihp' & Lihp' & Eτ2 & Ee2).
      assert (HEg : RS (env_args B1 (X ++ vs ++ ihp)) (env_args B2 (X' ++ vs' ++ ihp')))
        by (apply (per_ctx_env_Proper HRS _ _ Ee1 _ _ Ee2); exact HF12).
      clear Hdec Hsb HF12 EF1 EF2 Ee1 Ee2 HRS0 RS0 ES HRW0 EW HQ HCtx2.
      assert (Hty : forall E a,
                 ⟦ ptyp_ihty As (ι wk_shiftn (r + na + nn)) (cargs_sub (wrap_base Us nn na r) G1 (vars_from r na))
                     #(r + (na - 1 - length G1)) t ⟧ E ↘ a ->
                 ⟦ (ptyp_ihty As (ι wk_shiftn (cargs_nrec G1 + na + nn)) (ihs_sub nn Us na (cargs_pat G1) (cargs_nrec G1))
                      #(cargs_nrec G1 + na - 1 - length (cargs_pat G1)) t)[wrap_inst nn na r Lt] ⟧ E ↘ a).
      { intros E a Ea; rewrite <- LLt, (wrap_ihty_eq As nn Us na r G1 t Lt) by lia; exact Ea. }
      rewrite cinst_eq, tele_sub_app, length_im_nparams, <- List.app_assoc in HTG.
      assert (HPW : PER RW) by (eapply per_env_PER; exact HRW).
      assert (HW11 : RW (env_args B1 ((X ++ vs) ++ List.firstn r w)) (env_args B1 ((X ++ vs) ++ List.firstn r w)))
        by (etransitivity; [ exact HEp | symmetry; exact HEp ]).
      assert (HW22 : RW (env_args B2 ((X' ++ vs') ++ List.firstn r w')) (env_args B2 ((X' ++ vs') ++ List.firstn r w')))
        by (etransitivity; [ symmetry; exact HEp | exact HEp ]).
      destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HTG HRW (gsub_valid SW) HW11 Eτ1) as (a1 & b1 & Ea1 & Eb1 & Hab1).
      destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HTG HRW (gsub_valid SW) HW22 Eτ2) as (a2 & b2 & Ea2 & Eb2 & Hab2).
      assert (a1 = ty) as -> by (eapply functional_eval_exp; [ exact Ea1 | exact (Hty _ _ EtF) ]).
      assert (a2 = ty') as -> by (eapply functional_eval_exp; [ exact Ea2 | exact (Hty _ _ EtF') ]).
      clear Ea1 Ea2 Hty SW HW11 HW22 Eτ1 Eτ2 Eihp Eihp' Hwk F1 F2 HRS' RW0.
      (** The group's result there ([Elim.v], [cv_ihs]). *)
      assert (Hsplit : forall (Y ws : list domain) w0 (ihq : list domain), List.nth_error ws kk = Some w0 -> List.length ws = List.length gs ->
                 Y ++ ws ++ ihq = Y ++ List.firstn kk ws ++ w0 :: List.skipn (S kk) ws ++ ihq).
      { intros * Hw0 Lw0.
        pose proof (List.firstn_skipn kk ws) as Hfs; rewrite (skipn_nth_cons' _ _ _ Hw0) in Hfs.
        rewrite <- Hfs at 1; rewrite <- !List.app_assoc; reflexivity. }
      rewrite Lk in Hx, Hx', Hrr, Hra.
      assert (Lf : forall ws : list domain, List.length ws = List.length gs -> List.length (List.firstn kk ws) = List.length G1)
        by (intros; rewrite List.length_firstn; lia).
      assert (Ls : forall ws : list domain, List.length ws = List.length gs -> List.length (List.skipn (S kk) ws) = List.length G2)
        by (intros; unfold G2; rewrite !List.length_skipn; lia).
      set (K := List.length (cargs_nonrec G1)).
      assert (Hnv : forall ws, List.length ws = List.length gs -> List.firstn K (nonrec_arg_vals gs ws) = nonrec_arg_vals G1 (List.firstn kk ws)).
      { intros ws Lw0; rewrite <- (List.firstn_skipn kk ws) at 1.
        rewrite Heq0 at 1; fold G1 G2.
        rewrite nonrec_arg_vals_app by (rewrite List.length_firstn; lia).
        rewrite firstn_app_exact by (apply length_nonrec_arg_vals; rewrite List.length_firstn; lia); reflexivity. }
      assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq0, cargs_nonrec_app, List.length_app; lia).
      assert (Hpk : tele_prefix_rel (ar v X c) K (nonrec_arg_vals G1 (List.firstn kk vs)) (nonrec_arg_vals G1 (List.firstn kk vs'))).
      { rewrite <- (Hnv vs Lv), <- (Hnv vs' Lv'); apply tele_prefix_rel_of_full with (T := cargs_nonrec gs); [ exact Har | exact HKl ]. }
      rewrite (Hsplit X vs x ihp Hx Lv) in Eb1, HEg.
      rewrite (Hsplit X' vs' x' ihp' Hx' Lv') in Eb2, HEg.
      assert (HE1 : RS (env_args B1 (X ++ List.firstn kk vs ++ x :: List.skipn (S kk) vs ++ ihp))
                       (env_args B1 (X ++ List.firstn kk vs ++ x :: List.skipn (S kk) vs ++ ihp)))
        by (etransitivity; [ exact HEg | symmetry; exact HEg ]).
      assert (HE2 : RS (env_args B2 (X' ++ List.firstn kk vs' ++ x' :: List.skipn (S kk) vs' ++ ihp'))
                       (env_args B2 (X' ++ List.firstn kk vs' ++ x' :: List.skipn (S kk) vs' ++ ihp')))
        by (etransitivity; [ symmetry; exact HEg | exact HEg ]).
      destruct (EB side_w C2 HC12 Bks iA HBks HMall HAv v Mv c gs HMv Hcon HB G1 t G2 Heq0 RS HRS
                  B1 X (List.firstn kk vs) x (List.skipn (S kk) vs) ihp HB1 LX (Lf _ Lv) (Ls _ Lv) Lihp HE1)
        as (w1 & Hw1 & HwU1 & Lw1).
      destruct (EB side_w C2 HC12 Bks iA HBks HMall HAv v Mv c gs HMv Hcon HB G1 t G2 Heq0 RS HRS
                  B2 X' (List.firstn kk vs') x' (List.skipn (S kk) vs') ihp' HB2 LX' (Lf _ Lv') (Ls _ Lv') Lihp' HE2)
        as (w2 & Hw2 & HwU2 & Lw2).
      destruct (length_rec_ps D HD v Mv HMv c gs G1 t G2 Hcon Heq0) as (Mj & HMj & _).
      destruct (HBks _ _ HMj) as [bj Hbj].
      assert (Hn' : per_univ n ty ty') by (eexists; exact Hn).
      destruct (per_univ_trans' _ _ _ _ _ (per_univ_trans' _ _ _ _ _ (per_univ_sym' _ _ _ Hab1) Hn') Hab2) as [R' HR'].
      destruct (per_univ_trans' _ _ _ _ _ Hn' Hab2) as [Rx HRx].
      assert (ER : R <~> R').
      { etransitivity; [ eapply per_univ_elem_right_irrel; [ exact Hn | exact HRx ] | eapply per_univ_elem_left_irrel; [ exact HRx | exact HR' ] ]. }
      apply ER.
      apply (EB rest_char C2 HC12 Bks iA HBks HMall HAv v Mv c gs HMv Hcon HB G1 t G2 Heq0 RS HRS Mj bj HMj Hbj X B1 B2 X X'
               (List.firstn kk vs) (List.firstn kk vs') (List.skipn (S kk) vs) (List.skipn (S kk) vs')
               ihp ihp' w1 w2 x x' LX LX' (Lf _ Lv) (Lf _ Lv') (Ls _ Lv) (Ls _ Lv') Lihp Lihp' HE1 HE2 Hw1 Hw2 HwU1 HwU2 Lw1 Lw2
               HXX HX Hpk HB1 HB2 (List.length (ptyp_doms t)) 0 nil nil x x' ih ih' b1 b2 jG R');
        [ lia | reflexivity | reflexivity | apply tele_prefix_rel_nil | apply eval_apps_nil | apply eval_apps_nil
        | repeat rewrite List.app_nil_r; exact Hra | repeat rewrite List.app_nil_r; exact Hrr | exact Eb1 | exact Eb2 | exact HR' ].
    Qed.
  End WrapCv.
End CrossBase.

End Fixed_GCtx.
