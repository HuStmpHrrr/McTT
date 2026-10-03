(** * Valid Global Modules

    The members of a closed global module are read in its body, so a path to
    it is valid in its members ([gpath_at]) once its body is valid: its
    telescope is a semantically well-formed context, its definitions are valid
    at their types, and its aliases' units are valid. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases TrueFalseCases UnitCases InstanceCases
  MemberCases MemberTyping MemberReps MemberSem ModexpCases PathCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Arguments Related at a Telescope *)

Lemma gargs_rel : forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' ->
    forall Tb Rb, EF Tb ≈ Tb ∈ per_ctx_env ↘ Rb -> Rb ρ ρ' -> ⊨ rev ts ++ Tb ->
    exists R, EF rev (firstn (List.length args) ts) ++ Tb ≈ rev (firstn (List.length args) ts) ++ Tb ∈ per_ctx_env ↘ R /\
      R (env_args ρ args) (env_args ρ' args').
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' R1 HA Ha Hg IH]; intros Tb Rb HTb Hρ HC; cbn [firstn List.length rev app].
  - exists Rb; split; assumption.
  - cbn [rev] in HC; rewrite <- app_assoc in HC; cbn [app] in HC.
    destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
    assert (Hρ' : per_env_extend A A Rb (ρ ↦ a) (ρ' ↦ a')).
    { split; [ exact Hρ |].
      destruct HA as [x x' Hx Hx' Hxx]; eapply per_head_of; [ exact Hx | exact Hx' | exact Hxx | exact Ha ]. }
    destruct (IH _ _ HTb' Hρ' HC) as (R & HR & HRρ).
    exists R; rewrite <- app_assoc; cbn [app]; split; [ exact HR | exact HRρ ].
Qed.

Lemma per_ctx_env_nil_true : EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ (fun _ _ => True).
Proof. apply per_ctx_env_nil; reflexivity. Qed.

(** The parameters of a global module whose telescope is valid. *)
Lemma gparam_of_tele : forall qp T, ⊨ T -> gc_module gc_deps gc_stack qp = Some (mr_body T) -> gparam_at qp.
Proof.
  intros * HT Hq T' args args' A Hm Hg Hn.
  rewrite Hq in Hm; injection Hm as <-.
  destruct (nth_error_split _ _ Hn) as (l1 & l2 & Hl & Hlen).
  assert (HT' : ⊨ rev (rev T) ++ ⋅) by (rewrite rev_involutive, app_nil_r; exact HT).
  destruct (gargs_rel _ _ _ _ _ Hg _ _ per_ctx_env_nil_true I HT') as (R & HR & Hρ).
  assert (Hf : firstn (List.length args) (rev T) = l1)
    by (rewrite Hl, <- Hlen, firstn_app, Nat.sub_diag, firstn_all; cbn; rewrite app_nil_r; reflexivity).
  rewrite Hf, app_nil_r in HR.
  assert (HTs : T = rev l2 ++ ce_ass A :: rev l1)
    by (rewrite <- (rev_involutive T), Hl, rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
  rewrite HTs in HT.
  destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HT)) as [i HA].
  destruct (rel_exp_of_typ_inversion_simple_at HR HA _ _ Hρ) as (a & a' & Ha & Ha' & [RA HRA]).
  exists i, RA; econstructor; eassumption.
Qed.

(** Supplying arguments related at a telescope to a closure still missing
    them. *)
Lemma ltele_supply_gargs : forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' ->
    forall rest D D', per_ltele (ts ++ rest) ρ D (ts ++ rest) ρ' D' nil nil ->
    per_ltele (ts ++ rest) ρ D (ts ++ rest) ρ' D' args args'.
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' R1 HA Ha Hg IH]; intros rest D D' Hl; [ exact Hl |].
  cbn [app] in Hl |- *.
  inversion Hl; subst.
  match goal with HA2 : PER.Definitions.rel_typ _ A ρ A ρ' ?R2, Hmiss : forall c c', ?R2 c c' -> _ |- _ =>
    econstructor; [ exact HA | exact Ha |]; apply IH, Hmiss;
    destruct HA as [x x' Hx Hx' Hxx]; destruct HA2 as [y y' Hy Hy' Hyy];
    functional_eval_rewrite_clear;
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hxx Hyy) as E; apply E, Ha end.
Qed.

Lemma galias_of : forall qp y U T Δ,
    gc_module gc_deps gc_stack qp = Some (mr_body T) ->
    gc_module gc_deps gc_stack (path_app qp (y :: nil)) = Some (mr_alias U nil) ->
    gu_params U = Δ ++ T -> ⋅ ⊨ᵐ me_lit U ≈ me_lit U -> galias_at qp y.
Proof.
  intros * Hq Hy HU HUv T' U' ch args args' Hm Hm' Hg.
  rewrite Hq in Hm; injection Hm as <-.
  rewrite Hy in Hm'; injection Hm' as <- <-.
  pose proof (unit_chain_at HUv per_ctx_env_nil_true nil nil I) as Hd.
  inversion Hd; subst.
  constructor.
  match goal with Hl : per_ltele _ _ _ _ _ _ nil nil |- _ => rename Hl into Hlt end.
  rewrite HU, rev_app_distr in Hlt |- *.
  exact (ltele_supply_gargs _ _ _ _ _ Hg _ _ _ Hlt).
Qed.

(** ** The Arity of a Global Module *)

Lemma gwalk : forall qp T, gparam_at qp -> gc_module gc_deps gc_stack qp = Some (mr_body T) -> tele_ass T -> ⊨ T ->
    forall Tin Tout args ρ R, T = Tin ++ Tout -> List.length args = List.length Tout ->
      EF Tout ≈ Tout ∈ per_ctx_env ↘ R -> R (env_args ρ args) (env_args nil args) ->
      exists a, ⟦ ctx_pi Tin a_True ⟧ env_args ρ args ↘ a /\ mtyped (dm_global qp args) nil mk_mod a.
Proof.
  intros * Hgp Hm HU HT Tin.
  induction Tin as [| e Tin IH] using rev_ind; intros Tout args ρ R ET Hl HR Hρ; cbn [app ctx_pi] in *.
  - subst; exists ⊤ᵈ; split; [ constructor |].
    eapply mty_top; [ econstructor; [ exact Hm | exact Hl ] | exact (per_univ_elem_True 0) ].
  - pose proof ET as ET'.
    rewrite ET in HU; destruct (tele_ass_app_inv _ _ HU) as [HU1 HU2].
    destruct (tele_ass_app_inv _ _ HU1) as [_ He]; inversion He as [| ? ? [A1 ->] _]; subst.
    pose proof HT as HT'.
    rewrite <- app_assoc in HT'; cbn [app] in HT'.
    destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HT')) as [i HA1].
    destruct (rel_exp_of_typ_inversion_simple_at HR HA1 _ _ Hρ) as (a1 & a0 & Ha1 & Ha0 & [Ra HRa]).
    rewrite ctx_pi_app; cbn [ctx_pi].
    eexists; split; [ econstructor; exact Ha1 |].
    assert (Hn : nth_error (rev ((Tin ++ ce_ass A1 :: nil) ++ Tout)) (List.length args) = Some (ce_ass A1)).
    { rewrite <- app_assoc, rev_app_distr; cbn [app rev].
      rewrite nth_error_app1 by (rewrite length_app, length_rev; cbn; lia).
      rewrite nth_error_app2 by (rewrite length_rev; lia).
      rewrite length_rev, Hl, Nat.sub_diag; reflexivity. }
    eapply mty_pi; [ right; do 2 eexists; split; [ reflexivity | split; reflexivity ]
                   | econstructor; [ exact Hgp | exact Hm | exact Hn | exact Ha0 ] | exact HRa |].
    intros c w1 b Hc Hw1 Hb.
    inversion Hw1; subst.
    pose proof (per_ctx_env_of_typ HR HA1) as HR'.
    destruct (IH (ce_ass A1 :: Tout) (args ++ c :: nil) ρ _ ltac:(rewrite <- app_assoc; reflexivity)
                ltac:(rewrite length_app; cbn; lia) HR') as (b' & Hb' & Hm').
    { rewrite !env_args_snoc; split; [ exact Hρ |].
      eapply per_head_of; [ exact Ha1 | exact Ha0 | exact HRa | exact Hc ]. }
    rewrite env_args_snoc in Hb'.
    pose proof (functional_eval_exp _ _ _ _ Hb Hb') as <-; exact Hm'.
Qed.

(** ** Chains of Global Submodules *)

Definition chain_bodies (p : path) (pre : list String.string) : Prop :=
  forall pre1 y pre2, pre = pre1 ++ y :: pre2 ->
    exists T, gc_module gc_deps gc_stack (path_app p (pre1 ++ y :: nil)) = Some (mr_body T) /\
      gparam_at (path_app p (pre1 ++ y :: nil)).

Lemma chain_bodies_cons : forall p y pre, chain_bodies p (y :: pre) -> chain_bodies (path_app p (y :: nil)) pre.
Proof.
  intros * H pre1 z pre2 ->.
  destruct (H (y :: pre1) z pre2 eq_refl) as (T & HT & Hg).
  rewrite path_app_app; exists T; split; assumption.
Qed.

Lemma gsub_chain : forall pre p args ch k a, chain_bodies p pre ->
    mtyped (dm_global (path_app p pre) args) ch k a -> mtyped (dm_global p args) (pre ++ ch) k a.
Proof.
  induction pre as [| y pre IH]; intros * Hc Hm; cbn [app].
  - rewrite path_app_nil in Hm; exact Hm.
  - destruct (Hc nil y pre eq_refl) as (T & HT & Hg); cbn [app] in HT, Hg.
    eapply mty_gsub; [ exact Hg | exact HT |].
    apply IH; [ exact (chain_bodies_cons _ _ _ Hc) | rewrite path_app_app; exact Hm ].
Qed.

Lemma selc_global_chain : forall pre p args z d, chain_bodies p pre ->
    eval_selc gc_deps gc_stack (dm_global p args) (pre ++ z :: nil) d ->
    eval_selc gc_deps gc_stack (dm_global (path_app p pre) args) (z :: nil) d.
Proof.
  induction pre as [| y pre IH]; intros * Hc Hs; cbn [app] in Hs.
  - rewrite path_app_nil; exact Hs.
  - destruct (Hc nil y pre eq_refl) as (T & HT & _); cbn [app] in HT.
    inversion Hs; subst; [ destruct pre; discriminate |].
    match goal with Hs1 : eval_selm _ _ _ y _ |- _ => inversion Hs1; subst end;
      [| match goal with Ha : gc_module _ _ _ = Some (mr_alias _ _) |- _ => rewrite HT in Ha; discriminate end ].
    replace (path_app p (y :: pre)) with (path_app (path_app p (y :: nil)) pre) by (rewrite path_app_app; reflexivity).
    eapply IH; [ exact (chain_bodies_cons _ _ _ Hc) | eassumption ].
Qed.

Lemma eval_glob_any : forall r ρ ρ' v, ⟦ a_glob r ⟧ ρ ↘ v -> ⟦ a_glob r ⟧ ρ' ↘ v.
Proof. intros * H; inversion H; subst; [ eapply eval_exp_glob_delta | eapply eval_exp_glob_neut ]; eassumption. Qed.

Lemma rep_closed_tele : forall T X i b, ⊨ T -> tele_ass T -> T ⊨ X : Type@i -> (b = true -> X = a_True) ->
    rep ⋅ (ctx_pi T X) (List.length T) b.
Proof.
  intros * HT HU HX Hb.
  assert (HT' : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
  rewrite <- (app_nil_r T) in HX.
  pose proof (rep_nest _ _ _ nil T X 0 b (gsub_id _ sem_ctx_nil) HU (Forall_nil _) HT'
                (rep_leaf _ _ _ _ HT' HX Hb)) as H.
  rewrite exp_sub_id, Nat.add_0_r in H; exact H.
Qed.

End Fixed_GCtx.
