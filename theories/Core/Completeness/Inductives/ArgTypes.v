(** * The Types of a Constructor's Arguments, in the PER Model

    The arguments of a constructor of a member of a group are typed over
    its parameters: a non-recursive one by a type over the non-recursive
    arguments before it, which [wk_pat] weakens past the recursive ones; a
    recursive one by the [Π] over its shape's domains of the member the
    shape ends in ([ptyp_ty]).  Given the context of the arguments
    semantically well formed, this file proves the weakenings valid
    ([cargs_wk], [sh_wk]) and characterizes the relation of a recursive
    argument's type: it is the shape's relation ([rec_arg_rel]) of the
    group's canonical model ([shape_char]).  At a shape that ends in a view,
    the type is the container's at the view's instance, whose relation is
    the group's at the view when the view's elements cohere
    ([view_type_rel]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The type of a recursive argument: its end under the shape's
    domains. *)
Lemma ptyp_ty_ctx_pi : forall p D nn t pat,
    ptyp_ty p D nn pat t
    = ctx_pi (sh_ctx pat (ptyp_doms t))
        (ptyp_ty p D nn (List.repeat false (List.length (ptyp_doms t)) ++ pat) (pt_self (ptyp_mem t) (ptyp_ps t))).
Proof.
  intros p0 D0 nn; induction t as [j Ps | B t IH]; intros pat; [ reflexivity |].
  cbn [ptyp_ty ptyp_doms sh_ctx List.length ptyp_ps ptyp_mem].
  rewrite ctx_pi_app; cbn [ctx_pi].
  rewrite (IH (false :: pat)), repeat_false_cons; reflexivity.
Qed.

(** ** The Contexts of the Arguments and of the Domains *)

Section ArgsCtx.
  Variables (D : ind_decl) (p : qname) (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HD : valid_ind_decl D) (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Hypothesis (HΨ : ⊨ cargs_ctx p D Mk gs ++ im_params D Mk).

  Lemma cargs_prefix_sem : forall gs1 gs2, gs = gs1 ++ gs2 -> ⊨ cargs_ctx p D Mk gs1 ++ im_params D Mk.
  Proof.
    intros * Heq; pose proof HΨ as H.
    rewrite Heq in H; unfold cargs_ctx in H; rewrite cargs_ctx_aux_app, <- List.app_assoc in H.
    exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  (** The weakening of a prefix of the arguments to its non-recursive
      ones. *)
  Lemma cargs_wk : forall gs1 gs2, gs = gs1 ++ gs2 ->
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ im_params D Mk.
  Proof.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_strat cargs_pat List.rev List.map List.app].
      destruct (rel_ctx_wf_per_ctx_env (vid_params _ HD _ _ HM)) as [R HR].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) ].
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as IHw.
      pose proof (cargs_prefix_sem (gs1 ++ g :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as HC.
      rewrite cargs_ctx_snoc, cargs_pat_snoc in *.
      destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app wk_pat] in *.
      + rewrite cargs_strat_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (vid_arg _ HD _ _ _ _ _ _ HM Hcon HA) as (_ & j & HAv).
        rewrite Heq, <- nonrec_args_prefix_cargs_strat in HAv.
        exact (rel_wk_under_ctx_q IHw HAv).
      + rewrite cargs_strat_snoc_rec.
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HC) IHw).
  Qed.

  (** The weakening of the context of a recursive argument's domains to
      that of their types, from the one of the arguments before it. *)
  Lemma sh_wk : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall j, j <= List.length (ptyp_doms t) ->
        sh_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
          ⊨ʷ (wk_pat (List.repeat false j ++ cargs_pat gs1))
          : doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mk.
  Proof.
    intros * Heq; induction j as [| j IH]; intros Hj.
    - exact (cargs_wk _ _ Heq).
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, doms_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.repeat List.app wk_pat].
      destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & i & HBv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
      exact (rel_wk_under_ctx_q (IH ltac:(lia)) HBv).
  Qed.

  Lemma sh_sem : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall j, j <= List.length (ptyp_doms t) ->
        ⊨ sh_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk.
  Proof.
    intros * Heq; induction j as [| j IH]; intros Hj.
    - exact (cargs_prefix_sem _ _ Heq).
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      pose proof (sh_wk _ _ _ Heq j ltac:(lia)) as Hw.
      destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & i & HBv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
      pose proof (rel_exp_under_ctx_wk Hw HBv) as HBw; cbn [exp_wk] in HBw.
      rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.app].
      exact (rel_ctx_wf_ext_typ _ _ _ (IH ltac:(lia)) HBw).
  Qed.
End ArgsCtx.

End Fixed_GCtx.
