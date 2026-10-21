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

Lemma wrap_results_rel_len : forall dr Rel k u u' pre pre' gs' gs vs vs' ihs ihs',
    wrap_results_rel dr Rel k u u' pre pre' gs' gs vs vs' ihs ihs' ->
    List.length ihs = cargs_nrec gs' /\ List.length ihs' = cargs_nrec gs'.
Proof. induction 1; cbn; lia. Qed.

(** ** The Shapes and Recursive Results of a View against its Container's

    A shape [t'] of the container's against the view's [t]: as many
    domains, ending in a member the view's map takes to [t]'s ([cargs_corr]
    at a recursive argument). *)
Fixpoint shape_corr (vm : list nat) (t' t : ptyp) : Prop :=
  match t', t with
  | pt_self j' _, pt_self j _ => List.nth_error vm j' = Some j
  | pt_pi _ t1', pt_pi _ t1 => shape_corr vm t1' t1
  | _, _ => False
  end.

Lemma shape_corr_of : forall vm t' t, List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) -> ptyp_depth t' = ptyp_depth t ->
    shape_corr vm t' t.
Proof.
  intros vm t'; induction t' as [j' Ps' | B' t' IH]; intros [j Ps | B t] Hm Hd; unfold ptyp_depth in Hd; cbn in *;
    try discriminate; [ exact Hm | apply IH; [ exact Hm | unfold ptyp_depth; lia ] ].
Qed.

(** The recursive results of two constructors' arguments: [vs] of the
    container's kinds [gs'] with the container's recursive results [w], and
    [vs'] of the view's kinds [gs] with the view's [ihs].  At an argument
    recursive in both, related as recursive results; at one the view nests
    through, the view's result is the group's eliminator's at the argument
    (at [ρa], [pq], [ua], [Bksa]). *)
Inductive cross_results_rel (dr : nat -> list domain -> exp -> relation domain)
    (Rel : nat -> list domain -> domain -> list domain -> domain -> relation domain) (k : nat) (u u' : list domain)
    (ρa : env) (pq : qname) (ua : list domain) (Bksa : list eblock) :
    list domain -> list domain -> list carg -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
| cross_results_nil : forall pre pre', cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' nil nil nil nil nil nil
| cross_results_arg : forall pre pre' A' A gs' gs v v' vs vs' w ihs,
    cross_results_rel dr Rel k u u' ρa pq ua Bksa (pre ++ v :: nil) (pre' ++ v' :: nil) gs' gs vs vs' w ihs ->
    cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' (ca_arg A' :: gs') (ca_arg A :: gs) (v :: vs) (v' :: vs') w ihs
| cross_results_nest : forall pre pre' A' t gs' gs v v' vs vs' w ih ihs,
    ⟦ih v' of t under pq ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ih ->
    cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' gs' gs vs vs' w ihs ->
    cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' (ca_arg A' :: gs') (ca_rec t :: gs) (v :: vs) (v' :: vs') w (ih :: ihs)
| cross_results_rec : forall pre pre' t' t gs' gs v v' vs vs' ihb iha w ihs,
    rec_result_rel dr Rel k u u' pre pre' t v v' ihb iha ->
    cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' gs' gs vs vs' w ihs ->
    cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) (v' :: vs')
      (ihb :: w) (iha :: ihs).

(** The view's recursive results at the arguments recursive in both. *)
Fixpoint wsel (gs' gs : list carg) (ihs : list domain) : list domain :=
  match gs', gs, ihs with
  | ca_rec _ :: gs1', ca_rec _ :: gs1, ih :: ihs1 => ih :: wsel gs1' gs1 ihs1
  | ca_arg _ :: gs1', ca_rec _ :: gs1, _ :: ihs1 => wsel gs1' gs1 ihs1
  | _ :: gs1', ca_arg _ :: gs1, _ => wsel gs1' gs1 ihs
  | _, _, _ => nil
  end.

Lemma cross_to_wrap : forall dr Rel k u u' ρa pq ua Bksa pre pre' gs' gs vs vs' w ihs,
    cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' gs' gs vs vs' w ihs ->
    wrap_results_rel dr Rel k u u' pre pre' gs' gs vs vs' w (wsel gs' gs ihs).
Proof. induction 1; cbn [wsel]; econstructor; eassumption. Qed.

Lemma cross_results_rel_len : forall dr Rel k u u' ρa pq ua Bksa pre pre' gs' gs vs vs' w ihs,
    cross_results_rel dr Rel k u u' ρa pq ua Bksa pre pre' gs' gs vs vs' w ihs ->
    List.length vs = List.length gs /\ List.length vs' = List.length gs /\ List.length w = cargs_nrec gs' /\
    List.length ihs = cargs_nrec gs.
Proof. induction 1; cbn; lia. Qed.

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

    (** The environments of the wrapped branch's context at such arguments
        and results. *)
    Lemma cv_wrap : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall X X' vs vs' w w',
        tele_rel (nr v) T X X' ->
        tele_rel (ar v X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 X X' gs vs vs' ->
        wrap_results_rel dr Rel v u0 u0 X X' gs' gs vs vs' w w' ->
        forall RB, EF wrap_bctx p D Mv gs' gs As Us ++ Γ ≈ wrap_bctx p D Mv gs' gs As Us ++ Γ ∈ per_ctx_env ↘ RB ->
        RB (env_args B1 (X ++ vs ++ w)) (env_args B2 (X' ++ vs' ++ w')).
    Proof.
      intros B1 B2 HB1 HB2 * HX Har Hia Hwr RB HRB.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (wrap_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ Hwr) as [Lw Lw'].
      pose proof HX as HX0; rewrite tele_rel_iff in HX0; destruct HX0 as (LX & LX' & _).
      unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
      destruct (us_class VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HUC B1 HB1) as (u1 & Hu1 & H10).
      destruct (us_class VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HUC B2 HB2) as (u2 & Hu2 & H20).
      pose proof (EB closed_args_gargs v Mv c gs HMv Hcon X X' vs vs' HX Har Hia (List.length gs) (le_n _)) as Hcg.
      rewrite List.firstn_all, !List.firstn_all2 in Hcg by lia.
      assert (HKa : tele_ass ((cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D))
        by (rewrite <- List.app_assoc; fold (im_params D Mv); apply List.Forall_app; split;
            [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc v Mv HMv) ]).
      assert (HK : ⊨ (cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; fold (im_params D Mv); exact (vg_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon)).
      pose proof (ihs_pre_sem p D Γ Us Bks Mv gs HB nil gs eq_refl) as HC0; cbn [ihs_ctx_aux List.app] in HC0; rewrite cinst_eq in HC0.
      pose proof (EB cv_gen _ HKa HK HC0 B1 B2 u1 u2 HB12 Hu1 Hu2 H10 H20 _ _ Hcg
                    ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia)) as Hci.
      rewrite tele_sub_app, length_im_nparams in Hci; fold τU nn Cs Ns in Hci.
      pose proof (cv_wrap_ihs B1 B2 HB1 HB2 _ _ _ _ _ _ HX Har Hia Hwr Hci na (le_n _)) as Hih.
      unfold na in Hih; rewrite (List.firstn_all gs), List.firstn_all2, !List.firstn_all2 in Hih by (try rewrite (cargs_kinds_length _ _ Hk); lia).
      pose proof (WB valid_wrap_bctx v Mv c gs' gs HMv Hcon Hk) as HW.
      unfold As in HRB; rewrite (WB w_ctx_eq v Mv c gs' gs HMv Hcon Hk) in HW, HRB.
      fold nn na As τU Cs Ns in HW, HRB.
      set (Wc := wrap_ihs_ctx nn As Us na nil 0 gs' gs) in HW, HRB, Hih.
      replace (Wc ++ Cs ++ Ns ++ Γ) with ((Wc ++ Cs ++ Ns) ++ Γ) in HW, HRB by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (List.app_assoc X), (List.app_assoc X').
      eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRB HW HB12).
      - unfold Wc; rewrite !List.length_app, length_wrap_ihs_ctx by exact Hk.
        unfold Cs, Ns; rewrite !length_tele_sub, length_cargs_ctx, length_im_nparams; unfold nn, na, im_nn in *; lia.
      - rewrite List.rev_app_distr; apply per_gargs_app_intro;
          [ unfold Cs, Ns; rewrite List.length_rev, !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams;
            unfold nn, im_nn in *; lia | exact Hci | exact Hih ].
    Qed.
  End WrapCv.
End CrossBase.

(** ** The Container's Eliminator against the Group's

    The eliminator of the container's group [D'] at [qc], at the blocks
    [VBb] at [ρb] and the uniform parameters [ub], against the group's at
    [Bks] at [C1]: at related elements of the group's member [j] the view's
    map [vm] takes the container's [i'] to, related values, when the blocks
    are related member by member ([Hmot_x], [Hbr_x]) and so are the stuck
    eliminators ([Hbot_x]).  The container's side is on the left. *)
Section CrossElim.
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
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := vbs_has _ _ _ _ _ _ HBk.
  Let HMall := vbs_mctx _ _ _ _ _ _ HBk.
  Let HAv := vbs_motive _ _ _ _ _ _ HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C1 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation EM f := (EB f C1 HC11 Bks iA HBks HMall HAv).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).
  #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (icp_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (icp_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (icp_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (icp_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (icp_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (icp_dom_iff _ _ Hcp).

  (** The view [m] of the container's member [k'], its map [vm]. *)
  Variable (qc : qname) (D' : ind_decl) (m : nat) (Mm : imember) (k' : nat) (Is : list exp) (vm : list nat).
  Hypotheses (Hq : ind_lookup gc_deps gc_stack qc = Some D') (HMm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm).

  (** The container's eliminator. *)
  Variable (ρb : env) (VBb : list eblock) (ub : list domain).
  Hypotheses (HbB : forall i' Mi', ind_member D' i' = Some Mi' -> exists b, List.nth_error VBb i' = Some b)
    (HnmB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> eb_nm b = S (im_nn Mi'))
    (HnaB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> brs_names (im_cons Mi') (eb_brs b))
    (HarB : forall i' Mi' b c gs' n B, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b ->
              ind_con Mi' c = Some gs' -> In (c, n, B) (eb_brs b) -> n = (im_nn Mi' + List.length gs' + cargs_nrec gs')%nat).
  Hypothesis (Hmot_x : forall i' Mi' v bb ba u u' ns ns' x x', ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v ->
                List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba -> G v u u' ns ns' x x' ->
                exists a a', ⟦ eb_motive bb ⟧ env_args ρb (ns ++ x :: nil) ↘ a /\
                  ⟦ eb_motive ba ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
                  DF a ≈ a' ∈ per_univ_elem iA ↘ Rel v ns x ns' x').
  Hypothesis (Hbr_x : forall i' Mi' v Mv bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k,
                ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
                List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba ->
                ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                brs_lookup (eb_brs bb) c = Some (nb, Bb) -> brs_lookup (eb_brs ba) c = Some (na, Ba) ->
                G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs')
                  (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
                cross_results_rel dr Rel v u u' C1 p u0 Bks
                  (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') gs' gs vs vs' w ihs ->
                exists r r', ⟦ Bb ⟧ env_args ρb (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ r /\
                  ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mv) bs' ++ vs' ++ ihs) ↘ r' /\
                  Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs))
                    (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs' ++ vs')) r r').
  Hypothesis (Hbot_x : forall i' j Mj hd k as1 as2 e e' w w' ns ns', List.nth_error vm i' = Some j ->
                ind_member D j = Some Mj ->
                G j w w' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e') ->
                Dom d_elim ρb VBb qc ub i' as1 e ≈ d_elim C1 Bks p u0 j as2 e' ∈ per_bot).

  (** The members of the container's group and those of the group the
      view's map takes them to. *)
  Lemma x_member : forall i' j, List.nth_error vm i' = Some j ->
      exists Mi' Mj, ind_member D' i' = Some Mi' /\ view_member p D qc D' vm i' Mi' j Mj.
  Proof.
    intros i' j Hv.
    destruct (gta_vwrap _ Hass _ _ _ _ _ _ HMm Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    assert (Hi : i' < List.length (ind_members D')) by (rewrite <- (vwo_length _ _ _ Hvw); apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' _ _ Hi) as [Mi' HMi'].
    destruct (view_agree_members p D m Mm qc k' Is vm D' Hass HMm Hh Hq i' Mi' HMi') as (v & Mv & Hvm).
    pose proof (vmb_v _ _ _ _ _ _ _ _ _ Hvm) as Hv'; rewrite Hv in Hv'; injection Hv' as <-.
    exists Mi', Mv; split; [ exact HMi' | exact Hvm ].
  Qed.

  (** *** The Group's Eliminator against Itself at [C1] *)
  Lemma x_ok : elim_ups_ok p D u0 nr ar dr u0 u0.
  Proof. exact (EB ups_ok u0 u0 (EB u0_env) (EB u0_env) u0_len' u0_len'). Qed.

  Lemma x_mot0 : forall j Mj ba bb u u' ns ns' x x', ind_member D j = Some Mj ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> G j u u' ns ns' x x' ->
      exists a a', ⟦ eb_motive ba ⟧ env_args C1 (ns ++ x :: nil) ↘ a /\ ⟦ eb_motive bb ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns x ns' x'.
  Proof.
    intros * HMj Hba Hbb Hm; rewrite Hba in Hbb; injection Hbb as <-.
    exact (EB mot_mid C1 HC11 Bks iA HMall j Mj ba (eb_motive ba) HMj Hba (HAv _ _ _ HMj Hba) u u' ns ns' x x' Hm).
  Qed.

  Lemma x_br0 : forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k', ind_member D j = Some Mj ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> ind_con Mj c = Some gs ->
      brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
      G j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
      rec_results_rel dr Rel j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') gs vs vs' ihs ihs' ->
      exists r r', ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ↘ r /\
        ⟦ Bb ⟧ env_args C1 (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ↘ r' /\
        Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs)) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r'.
  Proof.
    assert (HBB : forall j Mj b b' c gs n B B', ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
               List.nth_error Bks j = Some b' -> ind_con Mj c = Some gs ->
               brs_lookup (eb_brs b) c = Some (n, B) -> brs_lookup (eb_brs b') c = Some (n, B') ->
               elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B ≈ B' : elim_bty p j Mj c gs (eb_motive b) Us).
    { intros * HMj Hb Hb' Hcon Hlb Hlb'; rewrite Hb in Hb'; injection Hb' as <-.
      rewrite Hlb in Hlb'; injection Hlb' as <-.
      exact (vbs_branch _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HMj Hb Hcon (brs_lookup_in _ _ _ _ Hlb)). }
    exact (EM br_mid (vbs_bctx _ _ _ _ _ _ HBk) Bks HBB).
  Qed.

  #[local] Abbreviation XS f := (f p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs')
     iA C1 C1 Bks Bks u0 u0 x_ok Rel HBks HBks (vbs_nm _ _ _ _ _ _ HBk) (vbs_nm _ _ _ _ _ _ HBk)
     (vbs_names _ _ _ _ _ _ HBk) (vbs_names _ _ _ _ _ _ HBk) (vbs_arity _ _ _ _ _ _ HBk) (vbs_arity _ _ _ _ _ _ HBk)
     (dt_nodup _ _ _ Hdt) x_mot0 x_br0).

  Lemma x_self : (forall j u u' ns ns' x x', G j u u' ns ns' x x' ->
        exists r r', ⟦elim x at j of p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r /\
          ⟦elim x' at j of p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r' /\ Rel j ns x ns' x' r r') /\
      (forall k u u' pre pre' gs vs vs',
        con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
        exists ihs ihs', ⟦ihs vs of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ihs /\
          ⟦ihs vs' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ihs' /\
          rec_results_rel dr Rel k u u' pre pre' gs vs vs' ihs ihs') /\
      (forall k u u' pre pre' t x x',
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t x x' ->
        exists ih ih', ⟦ih x of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ih /\
          ⟦ih x' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ih' /\
          rec_result_rel dr Rel k u u' pre pre' t x x' ih ih') /\
      (forall k u u' pre pre' t f c f' c',
        rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t f c f' c' ->
        exists fc fc' r r', $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
          ⟦ih fc of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r /\
          ⟦ih fc' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r' /\
          rec_result_rel dr Rel k u u' pre pre' t fc fc' r r').
  Proof. exact (XS per_ind_elim_all). Qed.

  Lemma x_move : forall j Mj u u' ns ns' x x' ns1 ns1', ind_member D j = Some Mj -> G j u u' ns ns' x x' ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns1 -> tele_rel (nr j) (List.rev (im_nparams Mj)) ns' ns1' ->
      (Rel j ns x ns' x' <~> Rel j ns1 x ns1' x').
  Proof. exact (XS motive_rel_move). Qed.

  Lemma x_ref_target : forall j Mj hd k, ind_member D j = Some Mj -> im_ref p j Mj = (hd, k) ->
      exists Dq Mk, ind_lookup gc_deps gc_stack hd = Some Dq /\ ind_member Dq k = Some Mk /\
        im_nn Mk = im_nn Mj /\ ind_nu Dq = im_unu D Mj.
  Proof. exact (XS im_ref_target). Qed.

  (** *** Related Elements Eliminate to Related Values *)
  Theorem cross_elim_all :
    (forall j u u' ns ns' x x', G j u u' ns ns' x x' ->
       forall i', List.nth_error vm i' = Some j ->
       exists r r', ⟦elim x at i' of qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r /\
         ⟦elim x' at j of p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r' /\ Rel j ns x ns' x' r r') /\
    (forall k u u' pre pre' gs vs vs',
       con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
       forall gs', cargs_corr vm gs' gs ->
       exists w ihs, ⟦ihs vs of gs' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ w /\
         ⟦ihs vs' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ihs /\
         cross_results_rel dr Rel k u u' C1 p u0 Bks pre pre' gs' gs vs vs' w ihs) /\
    (forall k u u' pre pre' t x x',
       rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t x x' ->
       forall t', shape_corr vm t' t ->
       exists ih ih', ⟦ih x of t' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ih /\
         ⟦ih x' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ih' /\
         rec_result_rel dr Rel k u u' pre pre' t x x' ih ih') /\
    (forall k u u' pre pre' t f c f' c',
       rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t f c f' c' ->
       forall t', shape_corr vm t' t ->
       exists fc fc' r r', $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
         ⟦ih fc of t' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r /\
         ⟦ih fc' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r' /\
         rec_result_rel dr Rel k u u' pre pre' t fc fc' r r').
  Proof.
    pose proof (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
    apply ind_rel_mut_ind_all.
    - (** A constructor: the container's wrapped branch against the
          group's, moved to the indices. *)
      intros * HM Href Hn Hcn Lb Lb' Hs Hs' Ha Hia IH i' Hvi.
      destruct (x_member i' k Hvi) as (Mi' & Mk0 & HMi' & Hvmb).
      pose proof (vmb_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMk0; rewrite HM in HMk0; injection HMk0 as <-.
      destruct (vmb_cons' _ _ _ _ _ _ _ _ _ Hvmb c gs Hcn) as (gs' & Hc' & Hcorr).
      destruct (IH gs' Hcorr) as (w & ihs & Ew & Ei & Hcr).
      destruct (HbB _ _ HMi') as [bb Hbb]; destruct (HBks _ _ HM) as [ba Hba].
      destruct (brs_names_lookup _ _ _ _ (HnaB _ _ _ HMi' Hbb) Hc') as (nb & Bb & HBb & HinB).
      destruct (brs_names_lookup _ _ _ _ (vbs_names _ _ _ _ _ _ HBk _ _ _ HM Hba) Hcn) as (na & Ba & HBa & HinA).
      pose proof (HarB _ _ _ _ _ _ _ HMi' Hbb Hc' HinB) as Hnb.
      pose proof (vbs_arity _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HM Hba Hcn HinA) as Hna.
      destruct (x_ref_target _ _ _ _ HM Href) as (Dq & Mq & Hq' & HMq & Hnnq & Hnuq).
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      pose proof (cargs_corr_len _ _ _ Hcorr) as Lgs.
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn'.
      match goal with |- exists r r', ⟦elim d_con _ _ _ (?bs ++ ?vs) at _ of _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ r /\
                                       ⟦elim d_con _ _ _ (?bs' ++ ?vs') at _ of _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ r' /\ _ =>
        assert (Hcur : G _ _ _ _ _ (d_con _ _ _ (bs ++ vs)) (d_con _ _ _ (bs' ++ vs')))
          by (eapply ind_rel_con; [ exact HM | exact Href | exact Hn | exact Hcn | exact Lb | exact Lb' | exact Hs | exact Hs'
                                 | exact Ha | exact Hia ]) end.
      pose proof (ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hcur Hs Hs') as Hm.
      destruct (Hbr_x i' Mi' k Mk bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k'0 HMi' Hvi HM Hbb Hba Hc' Hcn HBb HBa
                  Hm Hcr) as (r & r' & Er & Er' & Hrr).
      exists r, r'; split; [| split ].
      + eapply eval_elim_con; [ exact Hq | exact HMi' | rewrite <- (vmb_ref _ _ _ _ _ _ _ _ _ Hvmb); exact Href | exact Hq'
                              | exact HMq | exact Hc' | rewrite List.length_app; unfold im_np; lia | exact Hbb | exact HBb
                              | rewrite Hnnq, Hnn'; exact Hnb | |].
        * rewrite skipn_app_exact by (unfold im_np; lia); exact Ew.
        * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er.
      + eapply eval_elim_con; [ exact Hl | exact HM | exact Href | exact Hq' | exact HMq | exact Hcn
                              | rewrite List.length_app; unfold im_np; lia | exact Hba | exact HBa | rewrite Hnnq; exact Hna | |].
        * rewrite skipn_app_exact by (unfold im_np; lia); exact Ei.
        * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er'.
      + apply (x_move _ _ _ _ _ _ _ _ _ _ HM Hm (tsym _ _ HM _ _ Hs) (tsym _ _ HM _ _ Hs')); exact Hrr.
    - (** A neutral: both stuck, their readbacks agree. *)
      intros * uu uu' HM Href Hn L1 L2 Hs1 Hs2 He i' Hvi.
      destruct (x_member i' k Hvi) as (Mi' & Mk0 & HMi' & Hvmb).
      pose proof (vmb_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMk0; rewrite HM in HMk0; injection HMk0 as <-.
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn'.
      assert (Hcur : G k uu uu' ns ns' (⇑ (d_ind hd k'0 as1) m0) (⇑ (d_ind hd k'0 as2) m'))
        by (eapply ind_rel_neut; [ exact HM | exact Href | exact Hn | exact L1 | exact L2 | exact Hs1 | exact Hs2 | exact He ]).
      pose proof (ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hcur Hs1 Hs2) as Hm.
      destruct (x_ref_target _ _ _ _ HM Href) as (Dq & Mq & Hq' & HMq & Hnnq & Hnuq).
      destruct (HbB _ _ HMi') as [bb Hbb]; destruct (HBks _ _ HM) as [ba Hba].
      destruct (Hmot_x i' Mi' k bb ba uu uu' _ _ _ _ HMi' Hvi Hbb Hba Hm) as (a & a' & Ea & Ea' & HR).
      pose proof (Hbot_x i' k Mk hd k'0 as1 as2 m0 m' uu uu' ns ns' Hvi HM Hcur) as Hb.
      exists (⇑ a (d_elim ρb VBb qc ub i' as1 m0)), (⇑ a' (d_elim C1 Bks p u0 k as2 m')); split; [| split ].
      + eapply eval_elim_neut; [ exact Hq | exact HMi' | rewrite <- (vmb_ref _ _ _ _ _ _ _ _ _ Hvmb); exact Href | exact Hq'
                               | exact HMq | unfold im_np; lia | exact Hbb | rewrite (HnmB _ _ _ HMi' Hbb), Hnnq, Hnn'; reflexivity
                               | rewrite Hnuq; exact Ea ].
      + eapply eval_elim_neut; [ exact Hl | exact HM | exact Href | exact Hq' | exact HMq | unfold im_np; lia | exact Hba
                               | rewrite (vbs_nm _ _ _ _ _ _ HBk _ _ _ HM Hba), Hnnq; reflexivity | rewrite Hnuq; exact Ea' ].
      + apply (x_move _ _ _ _ _ _ _ _ _ _ HM Hm (tsym _ _ HM _ _ Hs1) (tsym _ _ HM _ _ Hs2)).
        exact (per_bot_then_per_elem HR Hb).
    - intros k0 u u' pre pre' [| [A' | t'] gs'] Hco; cbn in Hco; try contradiction.
      exists nil, nil; split; [ constructor | split; [ constructor | constructor ] ].
    - intros * Hia IH [| [A' | t'] gs'] Hco; cbn in Hco; try contradiction.
      destruct (IH gs' Hco) as (w & ihs & Ew & Ei & Hcr).
      exists w, ihs; split; [ constructor; exact Ew | split; [ constructor; exact Ei | constructor; exact Hcr ] ].
    - intros * Hsh IHsh Hia IHia [| [A' | t'] gs'] Hco; cbn in Hco; try contradiction.
      + (** Nested through: the group's own result. *)
        destruct (IHia gs' Hco) as (w & ihs & Ew & Ei & Hcr).
        destruct (proj1 (proj2 (proj2 x_self)) _ _ _ _ _ _ _ _ Hsh) as (ih0 & ih & _ & Eh & _).
        exists w, (ih :: ihs); split; [ constructor; exact Ew |].
        split; [ econstructor; [ exact Eh | exact Ei ] | econstructor; [ exact Eh | exact Hcr ] ].
      + destruct Hco as (Hm & Hd & Hco).
        destruct (IHia gs' Hco) as (w & ihs & Ew & Ei & Hcr).
        destruct (IHsh t' (shape_corr_of _ _ _ Hm Hd)) as (ih & ih' & Eh & Eh' & Hhh).
        exists (ih :: w), (ih' :: ihs); split; [ econstructor; [ exact Eh | exact Ew ] |].
        split; [ econstructor; [ exact Eh' | exact Ei ] | econstructor; [ exact Hhh | exact Hcr ] ].
    - intros * Hb Hb' Ok Ok' Hr IHr [j' Ps' | B' t'] Hsc; cbn in Hsc; try contradiction.
      destruct (IHr j' Hsc) as (r & r' & Er & Er' & Hrr).
      exists r, r'; split; [ constructor; exact Er | split; [ constructor; exact Er' | econstructor; [ exact Hb | exact Hb' | exact Hrr ] ] ].
    - intros * Hf IH [j' Ps' | B' t'] Hsc; cbn in Hsc; try contradiction.
      match goal with |- exists ih ih', ⟦ih ?f of _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ih /\
                                         ⟦ih ?f' of pt_pi _ ?t under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ih' /\ _ =>
        exists (d_ihfn ρb VBb qc ub t' f), (d_ihfn C1 Bks p u0 t f') end.
      split; [ constructor | split; [ constructor |] ].
      constructor; intros c c' Hcc.
      destruct (IH c c' Hcc t' Hsc) as (fc & fc' & r & r' & Ef & Ef' & Er & Er' & Hrr).
      econstructor; [ exact Ef | exact Ef' | econstructor; eassumption | econstructor; eassumption | exact Hrr ].
    - intros * Ef Ef' Hsh IHsh t' Hsc.
      destruct (IHsh t' Hsc) as (ih & ih' & Eh & Eh' & Hhh).
      do 4 eexists; split; [ exact Ef | split; [ exact Ef' | split; [ exact Eh | split; [ exact Eh' | exact Hhh ] ] ] ].
  Qed.
End CrossElim.

(** ** The Group's Recursive Results in a Wrapped Branch

    The recursive result of an argument the view nests through, in the
    wrapped branch's context [Ψw] ([wrap_bctx]): the group's eliminator at
    the argument's variable, at its blocks moved there ([ptyp_ih]).  At an
    environment [Eb] of [Ψw] over [C1], against the group's eliminator at
    [C1] at a related argument: related recursive results (the outer link
    of [Iota.s_clo], the eliminator's blocks moved by the weakening to
    [C1]). *)
Section WrapClo.
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
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := vbs_has _ _ _ _ _ _ HBk.
  Let HMall := vbs_mctx _ _ _ _ _ _ HBk.
  Let HAv := vbs_motive _ _ _ _ _ _ HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C1 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation EM f := (EB f C1 HC11 Bks iA HBks HMall HAv).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).
  #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (icp_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (icp_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (icp_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (icp_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (icp_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (icp_dom_iff _ _ Hcp).
  #[local] Abbreviation WB f := (f VP p D HP HPD Γ Us Bks iA HΓ HUl HUs HBk).

  (** The view's member [v], its constructor [c] of kinds [gs], the
      container's kinds [gs']. *)
  Variable (v : nat) (Mv : imember) (c : String.string) (gs' gs : list carg) (bv : eblock).
  Hypotheses (HMv : ind_member D v = Some Mv) (Hcon : ind_con Mv c = Some gs) (Hk : cargs_kinds gs' gs)
    (Hbv : List.nth_error Bks v = Some bv).
  Let As := blocks_motives Bks.
  Let nn := im_nn Mv.
  Let na := List.length gs.
  Let τU := sb_of_list Id Us.
  Let Cs := tele_sub (cargs_ctx p D Mv gs) (sb_qn nn τU).
  Let Ns := tele_sub (im_nparams Mv) τU.
  Let Ψc := Cs ++ Ns ++ Γ.
  Let Ew := wrap_ihs_ctx nn As Us na nil 0 gs' gs.
  Let Ψw := Ew ++ Ψc.
  Let n := List.length Ew + na + nn.
  Let Uw := List.map (fun U => U[wk_shiftn n]ʷ) Us.
  Let Nw := vars_from (List.length Ew + na) nn.
  Let Aw := vars_from (List.length Ew) na.
  Let Ps := Uw ++ Nw.
  Let Bw := blocks_wk Bks (wk_shiftn n).

  Lemma wc_HE : ⊨ Ψw.
  Proof. pose proof (WB valid_wrap_bctx v Mv c gs' gs HMv Hcon Hk) as H; rewrite (WB w_ctx_eq v Mv c gs' gs HMv Hcon Hk) in H; exact H. Qed.

  Lemma wc_LUw : List.length Uw = ind_nu D.
  Proof. unfold Uw; rewrite List.length_map; exact HUl. Qed.

  Lemma wc_HPl : List.length Ps = im_np D Mv.
  Proof. unfold Ps; rewrite List.length_app, wc_LUw; unfold Nw; rewrite length_vars_from; unfold im_np, nn; lia. Qed.

  Lemma wc_HfP : List.firstn (ind_nu D) Ps = Uw.
  Proof. unfold Ps; rewrite <- wc_LUw; apply firstn_app_len; reflexivity. Qed.

  Lemma wc_HBk : valid_blocks p D Ψw (List.firstn (ind_nu D) Ps) Bw iA.
  Proof.
    pose proof (valid_blocks_gsub p D Γ Us Bks iA Ψw (sb_of_wk (wk_shiftn n)) Hc HUl
                  (gsub_wk _ _ _ (WB w_wk v Mv c gs' gs HMv Hcon Hk Ew wc_HE) wc_HE HΓ) HBk) as H.
    rewrite map_sub_of_wk, blocks_sub_of_wk in H; rewrite wc_HfP; exact H.
  Qed.

  Lemma wc_Hb : List.nth_error Bw v = Some (eblock_sub bv (sb_of_wk (wk_shiftn n))).
  Proof. unfold Bw; rewrite <- blocks_sub_of_wk, nth_error_blocks_sub, Hbv; reflexivity. Qed.

  Lemma wc_HPs : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mv) Id Ps) k = Some T ->
      Ψw ⊨ P : T.
  Proof.
    intros k P T HP0 HT; unfold Ps in HP0, HT.
    refine (params_valid_join D v Mv Ψw Uw Nw Hc HMv wc_LUw (WB w_us v Mv c gs' gs HMv Hcon Hk Ew wc_HE) _ k P T HP0 HT).
    intros j N T0 HN HT0; refine (WB w_nvars v Mv c gs' gs HMv Hcon Hk Ew wc_HE (sb_of_list Id Uw) _ j N T0 HN HT0).
    intros y Hy; unfold Uw; rewrite sb_of_list_map by lia; reflexivity.
  Qed.

  Lemma wc_HAl : List.length Aw = List.length gs.
  Proof. unfold Aw; rewrite length_vars_from; reflexivity. Qed.

  Lemma wc_HAs : forall k N T, List.nth_error Aw k = Some N ->
      List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id Ps) Aw) k = Some T -> Ψw ⊨ N : T.
  Proof. exact (WB w_avars v Mv c gs' gs HMv Hcon Hk Ew wc_HE). Qed.

  #[local] Abbreviation IR f := (f VP p D HP HPD Ψw (Some p) v Mv _ Bw c gs Ps Aw iA wc_HE (or_introl eq_refl) HMv wc_Hb Hcon
     wc_HPl wc_HPs wc_HAl wc_HAs (vbs_has _ _ _ _ _ _ wc_HBk) (vbs_nm _ _ _ _ _ _ wc_HBk) (vbs_mctx _ _ _ _ _ _ wc_HBk)
     (vbs_motive _ _ _ _ _ _ wc_HBk) (vbs_names _ _ _ _ _ _ wc_HBk) (vbs_bctx _ _ _ _ _ _ wc_HBk)
     (vbs_arity _ _ _ _ _ _ wc_HBk) (vbs_branch _ _ _ _ _ _ wc_HBk)).

  (** *** At an Environment of the Wrapped Branch's Context *)
  Variable (RW : relation env).
  Hypothesis (HRW : EF Ψw ≈ Ψw ∈ per_ctx_env ↘ RW).
  Variable (X vs w X' vs' u u' : list domain).
  Let Eb := env_args C1 (X ++ vs ++ w).
  Hypotheses (HEb : RW Eb Eb) (LX : List.length X = nn) (Lv : List.length vs = na) (Lw : List.length w = List.length Ew).
  Hypotheses (HX : tele_rel (nr v) (List.rev (im_nparams Mv)) X X')
    (Har : tele_rel (ar v X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs'))
    (Hia : con_args_rel p D (okr_at D u0 nr) nr ar dr v u u' X X' gs vs vs').

  (** The recursive argument after [gs1], of shape [t] ending in [Mj]. *)
  Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
  Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
  Variable (Mj : imember).
  Hypothesis (HMj : ind_member D (ptyp_mem t) = Some Mj).
  Let K := List.length (cargs_nonrec gs1).
  Let L := List.length (ptyp_doms t).
  Let σt := cargs_sub (sb_of_list Id Ps) gs1 Aw.
  Let Mt := List.nth (List.length gs1) Aw (a_var 0).
  Let nvb := nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs).
  Let nva := nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs').
  Let ΨL := tele_sub (doms_ctx (List.firstn L (ptyp_doms t))) σt ++ Ψw.

  Lemma wc_leaf : forall a, List.nth_error vs (List.length gs1) = Some a ->
      forall a' ys ys' f f',
      tele_prefix_rel (shape_doms_rel (dr v) X nvb (ptyp_doms t)) L ys ys' ->
      $*| a & ys | gc_deps ⍮ gc_stack ↘ f -> $*| a' & ys' | gc_deps ⍮ gc_stack ↘ f' ->
      rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u u' (X ++ nvb ++ ys) (X' ++ nva ++ ys')
        (pt_self (ptyp_mem t) (ptyp_ps t)) f f' ->
      exists rb ra, ⟦ elim_at p D (Some p) (List.map (fun U => U[sb_shift_iter L Id]) Uw) (blocks_sub Bw (sb_shift_iter L Id))
                        (ptyp_mem t) (apps_vars_iter L Mt) ⟧ env_args Eb ys ↘ rb /\
        ⟦elim f' at (ptyp_mem t) of p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ra /\
        rec_result_rel dr Rel v u u' (X ++ nvb ++ ys) (X' ++ nva ++ ys') (pt_self (ptyp_mem t) (ptyp_ps t)) f f' rb ra.
  Proof.
    intros a Ha a' ys ys' f f' Hys Ef Ef' Hsh.
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    pose proof Hys as Hys0; rewrite tele_prefix_rel_iff in Hys0; destruct Hys0 as (Lys & Lys' & _).
    pose proof (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HMv _ _ HX) as HXX.
    destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv0 Lv0'].
    assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (Lf1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
      by (rewrite List.length_firstn, Lv0, Heq, List.length_app; cbn; lia).
    assert (Lf1' : List.length (List.firstn (List.length gs1) vs') = List.length gs1)
      by (rewrite List.length_firstn, Lv0', Heq, List.length_app; cbn; lia).
    assert (Hnv : List.firstn K (nonrec_arg_vals gs vs) = nvb).
    { rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
      rewrite Heq at 1; rewrite nonrec_arg_vals_app by exact Lf1.
      rewrite firstn_app_exact by (apply length_nonrec_arg_vals; exact Lf1); reflexivity. }
    assert (Hnv' : List.firstn K (nonrec_arg_vals gs vs') = nva).
    { rewrite <- (List.firstn_skipn (List.length gs1) vs') at 1.
      rewrite Heq at 1; rewrite nonrec_arg_vals_app by exact Lf1'.
      rewrite firstn_app_exact by (apply length_nonrec_arg_vals; exact Lf1'); reflexivity. }
    assert (Hpk : tele_prefix_rel (ar v X c) K nvb nva).
    { rewrite <- Hnv, <- Hnv'; apply tele_prefix_rel_of_full with (T := cargs_nonrec gs); [ exact Har | exact HKl ]. }
    pose proof (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HMv X c gs HXX Hcon K _ _ HKl Hpk) as Hpk1.
    pose proof (doms_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HMv X c gs gs1 t gs2 nvb HXX Hcon Heq Hpk1
                  L ys ys' (le_n _) Hys) as Hys1.
    (** The environment of the domains, of the context extended by them. *)
    assert (LΨ : List.length (Ew ++ Cs ++ Ns) = n)
      by (unfold Cs, Ns, n; rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams; unfold na, nn, im_nn; lia).
    assert (LXvw : List.length (X ++ vs ++ w) = List.length (Ew ++ Cs ++ Ns)) by (rewrite LΨ, !List.length_app, LX, Lv, Lw; unfold n; lia).
    assert (HRW' : EF (Ew ++ Cs ++ Ns) ++ Γ ≈ (Ew ++ Cs ++ Ns) ++ Γ ∈ per_ctx_env ↘ RW) by (rewrite <- !List.app_assoc; exact HRW).
    assert (HE' : ⊨ (Ew ++ Cs ++ Ns) ++ Γ) by (rewrite <- !List.app_assoc; exact wc_HE).
    destruct (us_wk_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs (Ew ++ Cs ++ Ns) RW C1 (X ++ vs ++ w) HRW' HE' HEb LXvw)
      as (wU & u1 & EwU & Eu1 & HwU).
    pose proof (functional_eval_exps' _ _ _ _ Eu1 HUC) as ->.
    rewrite LΨ in EwU; fold Uw in EwU.
    assert (LwU : List.length wU = ind_nu D) by (rewrite (eval_exps_length _ _ _ EwU); exact wc_LUw).
    assert (ENw : ⟦ Nw ⟧* gc_deps ⍮ gc_stack ⍮ Eb ↘ X).
    { pose proof (eval_vars_from_args X C1 (vs ++ w)) as H; unfold Nw; rewrite List.length_app, Lv, Lw, LX in H.
      replace (List.length Ew + na) with (na + List.length Ew) by lia; exact H. }
    assert (EAw : ⟦ Aw ⟧* gc_deps ⍮ gc_stack ⍮ Eb ↘ vs).
    { pose proof (eval_vars_from_args vs (env_args C1 X) w) as H; unfold Aw, Eb; rewrite env_args_app; rewrite Lv, Lw in H; exact H. }
    pose proof (eval_sigt D Mv gs Ps Aw wc_HPl wc_HAl gs1 (ca_rec t :: gs2) Eb (wU ++ X) vs Heq
                  (eval_exps_app _ _ _ _ _ _ _ EwU ENw) EAw) as Hσt.
    fold σt nvb in Hσt.
    pose proof (vbs_bctx _ _ _ _ _ _ HBk _ _ _ _ HMv Hcon) as HB.
    destruct (rel_ctx_wf_per_ctx_env (EB e_HCtx C1 HC11 Bks iA HBks HMall HAv v Mv c gs HMv Hcon HB gs1 t gs2 Heq)) as [RS HRS].
    assert (Lnvb : List.length nvb = K) by (apply length_nonrec_arg_vals; exact Lf1).
    pose proof (EM side_dom_gargs v Mv c gs HMv Hcon HB gs1 t gs2 Heq RS HRS L Eb wU X nvb ys (le_n _) HwU LwU LX Lnvb HXX Hpk1 Hys1)
      as Hg.
    pose proof (IR r_HΨ gs1 t gs2 Heq Mj HMj L (le_n _)) as HΨL; cbv beta in HΨL; fold σt ΨL in HΨL.
    destruct (rel_ctx_wf_per_ctx_env HΨL) as [RΨ HRΨ].
    assert (HEL : RΨ (env_args Eb ys) (env_args Eb ys)).
    { rewrite List.app_assoc in Hg.
      exact (tele_stage_rel (doms_ctx (List.firstn L (ptyp_doms t))) (cargs_strat gs1 ++ im_params D Mv ++ Ψw) Ψw σt RW Eb _
               ltac:(unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass)
               (IR r_dctxΓ gs1 t gs2 Heq Mj HMj L (le_n _)) HRW
               (gsub_valid (gsub_sigt VP p D HP HPD Ψw v Mv c gs Ps Aw wc_HE HMv Hcon wc_HPl wc_HPs wc_HAl wc_HAs
                              gs1 (ca_rec t :: gs2) Heq))
               HEb Hσt ys Hg ltac:(rewrite doms_ctx_length, List.length_firstn; unfold L in *; lia) RΨ HRΨ). }
    set (EL := env_args Eb ys) in *.
    set (σL := sb_shift_iter L Id).
    (** The blocks moved past the domains: the group's moved by the
        weakening to [C1]. *)
    pose proof (IR r_base gs1 t gs2 Heq Mj HMj L (le_n _)) as HbL; cbv beta in HbL; fold σt ΨL σL in HbL.
    pose proof (gsub_wk _ _ _ (WB w_wk v Mv c gs' gs HMv Hcon Hk Ew wc_HE) wc_HE HΓ) as Hgw; fold n in Hgw.
    pose proof (gsub_comp ΨL Ψw (sb_of_wk (wk_shiftn n)) σL Γ Hgw HΨL (gsub_valid HbL) (proj2 (gsub_props HbL))) as Hg0.
    set (σ0 := sb_of_wk (wk_shiftn n) ⨟ σL) in Hg0.
    assert (Hσw : sb_eq (ι (wk_shiftn L)) σL) by (unfold σL; rewrite sb_shift_iter_eq, sb_compose_id_left; reflexivity).
    assert (HevL : ⟦ σL ⟧s EL ↘ Eb).
    { apply (eval_sub_sb_eq (ι (wk_shiftn L))); [ exact Hσw |].
      pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn L) EL (wk_mono_shiftn _)) as H.
      unfold EL in H; rewrite <- Lys, eval_wk_shiftn_args in H; rewrite <- Lys; exact H. }
    assert (Hev : ⟦ σ0 ⟧s EL ↘ C1).
    { pose proof (eval_sub_wk_pre (wk_shiftn n) σL EL Eb HevL) as H.
      unfold Eb in H; pose proof (eval_wk_shiftn_args C1 (X ++ vs ++ w)) as E0; rewrite LXvw, LΨ in E0.
      rewrite E0 in H; exact H. }
    assert (HUt : forall j U, List.nth_error Us j = Some U -> exists T, Γ ⊨ U : T).
    { intros j U HU.
      destruct (nth_error_lt_some' (tele_insts (ind_uparams D) Id Us) j) as [T HT].
      { rewrite length_tele_insts by exact (uparams_ass D Hc).
        assert (j < List.length Us) by (apply List.nth_error_Some; congruence); unfold ind_nu in HUl; lia. }
      exists T; exact (HUs _ _ _ HU HT). }
    destruct (vals_sub_link VP p D HP HPD Γ HΓ RU HRU Us HUl HUt (proj2 (gsub_props (gsub_U VP p D HP HPD Γ HΓ Us HUl HUs)))
                ΨL RΨ σ0 EL C1 u0 HRΨ (gsub_valid Hg0) HEL Hev HUC) as (wL & EwL & HwL0).
    assert (LwL : List.length wL = ind_nu D) by (rewrite (eval_exps_length _ _ _ EwL), List.length_map; exact HUl).
    pose proof (EB ups_ok wL u0 HwL0 (EB u0_env) LwL u0_len') as Hok.
    assert (HUeq : List.map (fun U => U[σL]) Uw = List.map (fun U => U[σ0]) Us).
    { unfold Uw; rewrite List.map_map; apply List.map_ext; intros U; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity. }
    assert (HBeq : blocks_sub Bw σL = blocks_sub Bks σ0) by (unfold Bw; rewrite <- blocks_sub_of_wk, blocks_sub_sub; reflexivity).
    rewrite HUeq, HBeq.
    clear HUeq HBeq HRW' HE' Hg HRS RS Hgw HbL HUt Hσt ENw EwU.
    (** The eliminations, at the outer link. *)
    destruct (blocks_sub_facts D Bks σ0 HBks (vbs_nm _ _ _ _ _ _ HBk) (vbs_names _ _ _ _ _ _ HBk) (vbs_arity _ _ _ _ _ _ HBk))
      as (HbA1 & HnmA1 & HnaA1 & HarA1).
    assert (HAA0 : forall j Mj b b0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> List.nth_error Bks j = Some b0 ->
               elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ eb_motive b0 : Typeω@iA).
    { intros * HMj0 Hb Hb0; rewrite Hb in Hb0; injection Hb0 as <-; exact (HAv _ _ _ HMj0 Hb). }
    assert (HB0s : forall j Mj b b0 c gs n B0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
               List.nth_error Bks j = Some b0 -> ind_con Mj c = Some gs -> brs_lookup (eb_brs b0) c = Some (n, B0) ->
               n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat /\
               elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B0 : elim_bty p j Mj c gs (eb_motive b) Us).
    { intros * HMj0 Hb Hb0 Hcon1 Hlb; rewrite Hb in Hb0; injection Hb0 as <-.
      split; [ exact (vbs_arity _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HMj0 Hb Hcon1 (brs_lookup_in _ _ _ _ Hlb))
             | exact (vbs_branch _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HMj0 Hb Hcon1 (brs_lookup_in _ _ _ _ Hlb)) ]. }
    pose proof (per_ind_elim_all p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs')
                  iA EL C1 (blocks_sub Bks σ0) Bks wL u0 Hok
                  Rel HbA1 HBks HnmA1 (vbs_nm _ _ _ _ _ _ HBk) HnaA1 (vbs_names _ _ _ _ _ _ HBk) HarA1 (vbs_arity _ _ _ _ _ _ HBk)
                  (dt_nodup _ _ _ Hdt)
                  (EM mot_link Bks (vbs_nm _ _ _ _ _ _ HBk) HAA0 ΨL RΨ σ0 EL C1 HRΨ (gsub_valid Hg0) HEL Hev HC11)
                  (EM br_out (vbs_bctx _ _ _ _ _ _ HBk) Bks HB0s ΨL RΨ σ0 EL C1 HRΨ (gsub_valid Hg0) HEL Hev HC11)) as [PE _].
    destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & bs' & Ebs & Ebs' & _ & _ & Hff).
    destruct (PE _ _ _ _ _ _ _ Hff) as (r1 & r2 & Er1 & Er2 & Hr12).
    exists r1, r2; split; [| split; [ exact Er2 | econstructor; [ exact Ebs | exact Ebs' | exact Hr12 ] ] ].
    (** The eliminator in the wrapped context, at its value. *)
    assert (Hlt : List.length gs1 < na) by (unfold na; rewrite Heq, List.length_app; cbn; lia).
    assert (EMt : Mt = a_var (List.length Ew + (na - 1 - List.length gs1))).
    { unfold Mt, Aw; replace (List.length gs1) with (na - 1 - (na - 1 - List.length gs1)) at 1 by lia; apply vars_from_nth; lia. }
    destruct (eval_exps_nth _ _ _ (List.length gs1) Mt EAw) as (a0 & Ha0 & Ea0).
    { unfold Mt; apply List.nth_error_nth'; unfold Aw; rewrite length_vars_from; exact Hlt. }
    rewrite Ha in Ha0; injection Ha0 as <-.
    unfold elim_at; destruct (ind_has_views D); (eapply eval_exp_elim; [ exact EwL | | reflexivity | exact Er1 ]);
      rewrite apps_vars_iter_eq; apply eval_apps_exp; exists a, ys; (split; [| split; [| exact Ef ] ]).
    all: try (pose proof (eval_vars_from_args ys Eb nil) as H; rewrite List.app_nil_r in H; cbn [List.length] in H;
              rewrite Lys in H; exact H).
    all: rewrite <- exp_sub_of_wk, (exp_sub_sb_eq _ _ _ Hσw); rewrite EMt in Ea0 |- *; inversion Ea0; subst;
      eapply eval_sub_var; exact HevL.
  Qed.
End WrapClo.

End Fixed_GCtx.
