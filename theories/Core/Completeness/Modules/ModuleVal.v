(** * Operations on Related Module Values

    Applying related module values to related arguments gives related
    values.  Values lacking a parameter are related extensionally, so
    selection from them commutes with application ([selm_appm_comm]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Syntactic.System.Global Require Import Paths Presup LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import KindsTyping.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

(** ** Evaluation Is Deterministic *)

Lemma functional_eval_selm : forall h y r1 r2,
    h ·ₘ y gc_deps ⍮ gc_stack ↘ r1 -> h ·ₘ y gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros * H1 H2; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_selmc : forall h ch r1 r2,
    h ·ₘ* ch gc_deps ⍮ gc_stack ↘ r1 -> h ·ₘ* ch gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros * H1 H2; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_appms : forall h ns r1 r2,
    $ᵐ*| h & ns | gc_deps ⍮ gc_stack ↘ r1 -> $ᵐ*| h & ns | gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros * H1 H2; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

(** ** Application *)

Lemma per_dmod_appm : forall h h' a, per_dmod h h' -> nextparam h a ->
    exists i R a', nextparam h' a' /\ per_univ_elem i R a a' /\
      forall c c', R c c' -> exists hc hc', $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc /\
                                      $ᵐ| h' & c' | gc_deps ⍮ gc_stack ↘ hc' /\ per_dmod hc hc'.
Proof.
  intros * Hr Hn; inversion Hr; subst.
  - exfalso; eapply nextparam_global_sat; eassumption.
  - exfalso; eapply nextparam_body_nil; eassumption.
  - match goal with Hn0 : nextparam h ?a0 |- _ => pose proof (nextparam_functional _ _ Hn _ Hn0) as <- end.
    do 3 eexists; split; [ eassumption |]; split; [ eassumption |].
    intros c c' Hc.
    match goal with E1 : forall c c', _ -> exists hc, eval_appm _ _ h c hc,
                    E2 : forall c c', _ -> exists hc', eval_appm _ _ h' c' hc' |- _ =>
      destruct (E1 _ _ Hc) as (hc & Hh); destruct (E2 _ _ Hc) as (hc' & Hh') end.
    exists hc, hc'; repeat split; [ exact Hh | exact Hh' | eauto ].
Qed.

(** ** Closures and Global Telescopes *)

Lemma close_unsat : forall Δ D ρ, 0 < List.length Δ -> ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_local Δ D ρ.
Proof. intros * Hl; destruct D; [ apply eval_close_body | apply eval_close_alias; exact Hl ]. Qed.

(** A closure given fewer arguments than it lacks parameters. *)
Lemma appms_local : forall args Δ D ρ, tele_ass Δ -> List.length args < List.length Δ ->
    $ᵐ*| dm_local Δ D ρ & args | gc_deps ⍮ gc_stack ↘
      dm_local (List.firstn (List.length Δ - List.length args) Δ) D (env_args ρ args).
Proof.
  induction args as [| c args IH]; intros * Ha Hl; cbn [List.length] in *.
  - rewrite Nat.sub_0_r, List.firstn_all; constructor.
  - destruct (tele_ass_last _ Ha ltac:(destruct Δ; cbn in Hl; [ lia | discriminate ])) as (Δ0 & A & ->).
    rewrite List.length_app in Hl |- *; cbn [List.length] in Hl |- *.
    apply List.Forall_app in Ha as [Ha0 _].
    econstructor; [ apply eval_appm_local, close_unsat; lia |].
    replace (List.length Δ0 + 1 - S (List.length args)) with (List.length Δ0 - List.length args) by lia.
    rewrite List.firstn_app, (proj2 (Nat.sub_0_le (List.length Δ0 - List.length args) (List.length Δ0)) ltac:(lia)).
    cbn [List.firstn]; rewrite List.app_nil_r.
    exact (IH _ _ _ Ha0 ltac:(lia)).
Qed.

Lemma appms_snoc : forall args h c r,
    $ᵐ*| h & args ++ c :: nil | gc_deps ⍮ gc_stack ↘ r <->
    exists h1, $ᵐ*| h & args | gc_deps ⍮ gc_stack ↘ h1 /\ $ᵐ| h1 & c | gc_deps ⍮ gc_stack ↘ r.
Proof.
  induction args as [| a args IH]; intros; cbn [app]; split.
  - intros Ha; inversion Ha; subst; match goal with Hn : eval_appms _ _ _ nil _ |- _ => inversion Hn; subst end.
    exists h; split; [ constructor | assumption ].
  - intros (h1 & Hn & Ha); inversion Hn; subst; econstructor; [ exact Ha | constructor ].
  - intros Ha; inversion Ha; subst; match goal with Hr : eval_appms _ _ _ (args ++ _) _ |- _ => apply IH in Hr as (h2 & ? & ?) end.
    exists h2; split; [ econstructor |]; eassumption.
  - intros (h1 & Hn & Ha); inversion Hn; subst; econstructor; [ eassumption | apply IH; eauto ].
Qed.

Lemma firstn_rev_nth : forall (L : list centry) k e, List.nth_error (List.rev L) k = Some e ->
    exists L0, List.firstn (List.length L - k) L = L0 ++ e :: nil.
Proof.
  intros * Hn.
  destruct (List.nth_error_split _ _ Hn) as (M1 & M2 & HM & Hk).
  assert (HL : L = List.rev M2 ++ e :: List.rev M1).
  { rewrite <- (List.rev_involutive L), HM, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity. }
  exists (List.rev M2); rewrite HL, List.length_app; cbn [List.length]; rewrite !List.length_rev, Hk.
  rewrite List.firstn_app, List.length_rev, List.firstn_all2 by (rewrite List.length_rev; lia).
  replace (List.length M2 + S k - k - List.length M2) with 1 by lia; reflexivity.
Qed.

(** A body stored just below a stored body: over its own parameters and the
    parent's. *)
Lemma gc_child_body : forall p T Φ y TΦ, gc_loc gc_deps gc_stack p = Some (T, Φ) ->
    gc_loc gc_deps gc_stack (qname_app p (y :: nil)) = Some TΦ ->
    exists Δy Φy, gc_loc gc_deps gc_stack (qname_app p (y :: nil)) = Some (Δy ++ T, Φy).
Proof.
  intros * Hm Hl; destruct TΦ as [T' Φ'].
  rewrite <- qname_in_app in Hl |- *.
  destruct (loc_child_tele _ _ Hgw _ _ _ _ _ _ Hm Hl) as (Δy & -> & _); eauto.
Qed.

Lemma nth_rev_app_lt : forall (Δ T : list centry) k, k < List.length T ->
    List.nth_error (List.rev (Δ ++ T)) k = List.nth_error (List.rev T) k.
Proof. intros * Hk; rewrite List.rev_app_distr, List.nth_error_app1 by (rewrite List.length_rev; lia); reflexivity. Qed.

Lemma nextparam_global_lt : forall p args a, nextparam (dm_global p args) a ->
    exists T Φ, gc_loc gc_deps gc_stack p = Some (T, Φ) /\ List.length args < List.length T.
Proof.
  intros * Hn; inversion Hn; subst; do 2 eexists; split; [ eassumption |].
  match goal with Hx : nth_error _ _ = Some _ |- _ => assert (Hx' : nth_error (rev T) (length args) <> None) by congruence end.
  apply nth_error_Some in Hx'; rewrite length_rev in Hx'; exact Hx'.
Qed.

(** ** Selection from a Value Lacking a Parameter *)

(** A submodule of a value lacking a parameter lacks the same one. *)
Lemma nextparam_selm : forall h a, nextparam h a -> forall y r, h ·ₘ y gc_deps ⍮ gc_stack ↘ r -> nextparam r a.
Proof.
  intros * Hn * Hs; inversion Hs; subst.
  - (* a body submodule of a global module *)
    inversion Hn; subst.
    match goal with Hm : gc_loc _ _ p = Some _, Hl : gc_loc _ _ (qname_app p _) = Some _ |- _ =>
      destruct (gc_child_body _ _ _ _ _ Hm Hl) as (Δy & Φy & Hm') end.
    econstructor; [ exact Hm' | | eassumption ].
    rewrite nth_rev_app_lt; [ eassumption |].
    match goal with Hx : nth_error (rev T) _ = Some _ |- _ =>
      assert (Hx' : nth_error (rev T) (length args) <> None) by congruence end.
    apply nth_error_Some in Hx'; rewrite length_rev in Hx'; exact Hx'.
  - (* an alias submodule of a global module: its closure at the arguments *)
    destruct (nextparam_global_lt _ _ _ Hn) as (T & Φ & Hm & Hlt).
    match goal with Ha : gc_module _ _ (qname_app p _) = Some (mr_alias _) |- _ =>
      rewrite <- qname_in_app in Ha;
      destruct (loc_alias_params _ _ Hgw _ _ _ _ _ Hm Ha) as (Δy & HΔ & HaΔ); rewrite qname_in_app in Ha end;
      cbn [gu_params] in HΔ; subst.
    pose proof (gc_loc_tele_ass _ _ Hgw _ _ _ Hm) as HaT.
    assert (Ha : tele_ass (Δy ++ T)) by (apply List.Forall_app; split; assumption).
    match goal with Hc : eval_close _ _ _ ?D nil ?h0 |- _ =>
      pose proof (functional_eval_close _ _ _ _ _ Hc (close_unsat (Δy ++ T) D nil ltac:(rewrite List.length_app; lia))) as -> end.
    match goal with Ha' : eval_appms _ _ (dm_local _ ?D _) args r |- _ =>
      pose proof (functional_eval_appms _ _ _ _ Ha' (appms_local args (Δy ++ T) D nil Ha ltac:(rewrite List.length_app; lia))) as -> end.
    inversion Hn; subst.
    match goal with Hm0 : gc_loc _ _ p = Some _ |- _ => rewrite Hm in Hm0; injection Hm0 as <- <- end.
    match goal with Hx : nth_error (rev T) _ = Some ?e |- _ =>
      rewrite <- (nth_rev_app_lt Δy) in Hx by exact Hlt;
      destruct (firstn_rev_nth _ _ _ Hx) as (L0 & HL0) end.
    rewrite HL0; constructor; assumption.
  - (* a closure lacking a parameter *)
    constructor; exact Hn.
  - (* a saturated body lacks none *)
    exfalso; eapply nextparam_body_nil; exact Hn.
  - (* a submodule closure *)
    inversion Hn; subst; constructor; assumption.
Qed.

(** Selection from a value lacking a parameter commutes with application. *)
Lemma selm_appm_comm : forall h a, nextparam h a -> forall y r c hc,
    h ·ₘ y gc_deps ⍮ gc_stack ↘ r -> $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc ->
    forall rc, $ᵐ| r & c | gc_deps ⍮ gc_stack ↘ rc <-> hc ·ₘ y gc_deps ⍮ gc_stack ↘ rc.
Proof.
  intros * Hn * Hs Hh rc; inversion Hs; subst.
  - (* a body submodule of a global module *)
    inversion Hh; subst; split; intros Hr.
    + inversion Hr; subst; eapply eval_selm_global; eassumption.
    + inversion Hr; subst; [ constructor |].
      exfalso; eapply gc_loc_not_alias; eassumption.
  - (* an alias submodule of a global module *)
    inversion Hh; subst; split; intros Hr.
    + eapply eval_selm_global_alias; [ eassumption | eassumption | apply appms_snoc; eauto ].
    + inversion Hr; subst; [ exfalso; eapply gc_loc_not_alias; eassumption |].
      match goal with H1 : gc_module _ _ ?qq = Some _, H2 : gc_module _ _ ?qq = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as -> -> end.
      match goal with H1 : eval_close _ _ ?Δ ?D nil ?a, H2 : eval_close _ _ ?Δ ?D nil ?b |- _ =>
        pose proof (functional_eval_close _ _ _ _ _ H1 H2) as <- end.
      match goal with Ha : eval_appms _ _ _ (_ ++ _) _ |- _ => apply appms_snoc in Ha as (h1 & Ha1 & Ha2) end.
      match goal with H1 : eval_appms _ _ ?h0 args ?a, H2 : eval_appms _ _ ?h0 args ?b |- _ =>
        assert_fails (constr_eq a b); pose proof (functional_eval_appms _ _ _ _ H1 H2) as <- end.
      exact Ha2.
  - (* a closure lacking a parameter *)
    split; intros Hr.
    + inversion Hr; subst.
      match goal with H1 : eval_appm _ _ ?h c ?a, H2 : eval_appm _ _ ?h c ?b |- _ =>
        assert_fails (constr_eq a b); pose proof (functional_eval_appm _ _ _ _ H1 H2) as <- end.
      match goal with Hc : eval_selmc _ _ _ (y :: nil) _ |- _ => inversion Hc; subst end.
      match goal with Hc : eval_selmc _ _ _ nil _ |- _ => inversion Hc; subst end; assumption.
    + econstructor; [ exact Hh | econstructor; [ exact Hr | constructor ] ].
  - exfalso; eapply nextparam_body_nil; exact Hn.
  - (* a submodule closure *)
    inversion Hh; subst; split; intros Hr.
    + inversion Hr; subst.
      match goal with H1 : eval_appm _ _ ?h c ?a, H2 : eval_appm _ _ ?h c ?b |- _ =>
        assert_fails (constr_eq a b); pose proof (functional_eval_appm _ _ _ _ H1 H2) as <- end.
      match goal with Hc : eval_selmc _ _ _ (_ ++ _) _ |- _ => apply eval_selmc_snoc_inv in Hc as (h1 & Hc0 & Hy) end.
      match goal with H1 : eval_selmc _ _ ?h ch ?a, H2 : eval_selmc _ _ ?h ch ?b |- _ =>
        assert_fails (constr_eq a b); pose proof (functional_eval_selmc _ _ _ _ H1 H2) as <- end.
      exact Hy.
    + econstructor; [ eassumption | eapply eval_selmc_snoc; eassumption ].
Qed.

(** A value lacking a parameter has a submodule wherever it has one at an
    argument. *)
Lemma selm_of_appm : forall h a, nextparam h a -> forall c hc y rc,
    $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc -> hc ·ₘ y gc_deps ⍮ gc_stack ↘ rc ->
    exists r, h ·ₘ y gc_deps ⍮ gc_stack ↘ r.
Proof.
  intros * Hn * Hh Hs; inversion Hn; subst.
  - eexists; apply eval_selm_unsat; rewrite List.length_app; cbn; lia.
  - inversion Hh; subst; inversion Hs; subst.
    + eexists; eapply eval_selm_global; eassumption.
    + match goal with Ha : eval_appms _ _ _ (_ ++ _) _ |- _ => apply appms_snoc in Ha as (h1 & Ha1 & _) end.
      eexists; eapply eval_selm_global_alias; eassumption.
  - eexists; apply eval_selm_member.
Qed.

End Fixed_GCtx.
