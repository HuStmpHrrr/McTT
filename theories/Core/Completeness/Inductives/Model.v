(** * Valid Groups: the Canonical Model and the Type Formers

    A group is semantically valid ([valid_ind_decl]) when its telescopes and
    types are: these are the judgments of its typing, read in the PER model.
    From them, each declared member at related parameters is a type of the
    universe its sort denotes ([ind_relate]), with the canonical relations
    of [Core.Semantic.Inductives.IndPER]: the group's canonical model.  The
    type formers are then elements of their [Π]-types
    ([valid_exp_under_ctx_ind]), and the values of the declared members at
    the group's uniform parameters make an environment of the context of
    the group's members as variables ([selfs_env_rel]), at which the view
    equations are read ([Inductives/ViewEquations.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas DescTyping.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases VariableCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance Telescope.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Lists *)

Lemma length_nparams_prefix : forall M k, k <= im_nn M -> List.length (nparams_prefix M k) = k.
Proof. intros; unfold nparams_prefix; rewrite List.length_rev, List.length_firstn, List.length_rev, length_im_nparams; lia. Qed.

Lemma length_nonrec_args_prefix : forall gs k, k <= List.length (cargs_nonrec gs) -> List.length (nonrec_args_prefix gs k) = k.
Proof. intros; unfold nonrec_args_prefix; rewrite List.length_rev, List.length_firstn, List.length_map; lia. Qed.

Lemma nparams_prefix_suffix : forall D M k, exists Δ, im_params D M = Δ ++ nparams_prefix M k ++ ind_uparams D.
Proof.
  intros; exists (List.rev (List.skipn k (List.rev (im_nparams M)))).
  unfold im_params; rewrite List.app_assoc; f_equal.
  unfold nparams_prefix; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
Qed.

Lemma rev_nparams_prefix : forall (D : ind_decl) M k,
    List.rev (nparams_prefix M k ++ ind_uparams D) = List.rev (ind_uparams D) ++ List.firstn k (List.rev (im_nparams M)).
Proof. intros; unfold nparams_prefix; rewrite List.rev_app_distr, List.rev_involutive; reflexivity. Qed.

Lemma rev_im_params : forall D M, List.rev (im_params D M) = List.rev (ind_uparams D) ++ List.rev (im_nparams M).
Proof. intros; unfold im_params; apply List.rev_app_distr. Qed.

Lemma length_im_params : forall D M, List.length (im_params D M) = im_np D M.
Proof. intros; unfold im_params, im_np, ind_nu; rewrite List.length_app, length_im_nparams; lia. Qed.

Lemma doms_ctx_snoc : forall Bs B, doms_ctx (Bs ++ B :: nil) = ce_ass B :: doms_ctx Bs.
Proof. intros; unfold doms_ctx; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

(** A weakening that keeps the last [k] entries keeps them, with their
    types. *)
Lemma eval_wk_pat_falses : forall yts k pat E, List.length yts = k ->
    ⟪wk_pat (List.repeat false k ++ pat)⟫ (env_extend_typed E yts) = env_extend_typed (⟪wk_pat pat⟫ E) yts.
Proof.
  intros yts; induction yts as [| [y t] yts IH] using List.rev_ind; intros k pat E Hl.
  - cbn in Hl; subst k; reflexivity.
  - rewrite List.length_app in Hl; cbn in Hl.
    replace k with (S (List.length yts)) by lia.
    cbn [List.repeat List.app wk_pat].
    rewrite !env_extend_typed_app; cbn [env_extend_typed List.fold_left fst snd].
    rewrite eval_wk_q_cons by typeclasses eauto.
    rewrite IH by reflexivity; reflexivity.
Qed.

Lemma tele_ass_map_ass : forall As, tele_ass (List.map ce_ass As).
Proof. induction As; constructor; eauto. Qed.

Lemma eval_exps_length : forall Ms ρ ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> List.length ms = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

Lemma eval_exps_each : forall Ms ρ, (forall m M, List.nth_error Ms m = Some M -> exists v, ⟦ M ⟧ ρ ↘ v) ->
    exists vs, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs.
Proof.
  induction Ms as [| M Ms IH]; intros ρ H; [ exists nil; constructor |].
  destruct (H 0 M eq_refl) as [v Hv].
  destruct (IH ρ ltac:(intros m N HN; exact (H (S m) N HN))) as [vs Hvs].
  exists (v :: vs); econstructor; eassumption.
Qed.

Lemma eval_exps_nth : forall Ms ρ vs m M, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> List.nth_error Ms m = Some M ->
    exists v, List.nth_error vs m = Some v /\ ⟦ M ⟧ ρ ↘ v.
Proof.
  induction Ms as [| M0 Ms IH]; intros * H Hm; inversion H; subst; [ destruct m; discriminate |].
  destruct m as [| m]; cbn in Hm |- *; [ injection Hm as <-; eauto | eapply IH; eassumption ].
Qed.

(** ** The Declaration's Judgments, Positionwise

    The typing of a declaration states its judgments at decompositions of
    its lists; the semantic validity states them at positions. *)

Lemma cargs_strat_nonrec : forall gs, cargs_strat gs = List.rev (List.map ce_ass (cargs_nonrec gs)).
Proof. induction gs as [| [r A | Ps] gs IH]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma nonrec_args_prefix_cargs_strat : forall gs1 gs2, cargs_strat gs1 = nonrec_args_prefix (gs1 ++ gs2) (List.length (cargs_nonrec gs1)).
Proof.
  intros; unfold nonrec_args_prefix; rewrite cargs_strat_nonrec, cargs_nonrec_app, List.map_app, List.firstn_app.
  rewrite List.firstn_all2 by (rewrite List.length_map; lia).
  rewrite List.length_map, Nat.sub_diag; cbn; rewrite List.app_nil_r; reflexivity.
Qed.

Lemma nonrec_nth_split : forall gs k A, List.nth_error (cargs_nonrec gs) k = Some A ->
    exists gs1 gs2 r, gs = gs1 ++ ca_arg r A :: gs2 /\ List.length (cargs_nonrec gs1) = k.
Proof.
  induction gs as [| [r0 B | Ps] gs IH]; intros k A H; cbn in H; [ destruct k; discriminate | |].
  - destruct k as [| k]; cbn in H.
    + injection H as ->; exists nil, gs, r0; split; reflexivity.
    + destruct (IH _ _ H) as (gs1 & gs2 & r & -> & Hl); exists (ca_arg r0 B :: gs1), gs2, r; split; [ reflexivity | cbn; lia ].
  - destruct (IH _ _ H) as (gs1 & gs2 & r & -> & Hl); exists (ca_rec Ps :: gs1), gs2, r; split; [ reflexivity | cbn; lia ].
Qed.

(** Each non-recursive argument has its sort. *)
Lemma nonrec_relevance_nth : forall gs j A, List.nth_error (cargs_nonrec gs) j = Some A ->
    exists r, List.nth_error (cargs_nonrec_relevance gs) j = Some r.
Proof.
  induction gs as [| [r0 B | Ps] gs IH]; intros j A H; cbn in *; [ destruct j; discriminate | | exact (IH _ _ H) ].
  destruct j as [| j]; cbn in *; [ exists r0; reflexivity | exact (IH _ _ H) ].
Qed.

Lemma nparams_nth_split : forall M k A, List.nth_error (List.rev (im_nparams M)) k = Some (ce_ass A) ->
    exists Δ1, im_nparams M = Δ1 ++ ce_ass A :: nparams_prefix M k.
Proof.
  intros * H; destruct (List.nth_error_split _ _ H) as (l1 & l2 & Hl & Hlen).
  exists (List.rev l2).
  assert (Hf : List.firstn k (List.rev (im_nparams M)) = l1)
    by (rewrite Hl, <- Hlen, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
  unfold nparams_prefix; rewrite Hf, <- (List.rev_involutive (im_nparams M)), Hl, List.rev_app_distr; cbn.
  rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma nparams_prefix_S : forall M k A, List.nth_error (List.rev (im_nparams M)) k = Some (ce_ass A) ->
    nparams_prefix M (S k) = ce_ass A :: nparams_prefix M k.
Proof. intros * H; unfold nparams_prefix; rewrite (firstn_S_snoc _ _ _ H), List.rev_app_distr; reflexivity. Qed.

Lemma nparams_prefix_full : forall M, nparams_prefix M (im_nn M) = im_nparams M.
Proof. intros; unfold nparams_prefix; rewrite List.firstn_all2 by (rewrite List.length_rev, length_im_nparams; lia); apply List.rev_involutive. Qed.

(** Related arguments at a closed telescope make related environments of
    it. *)
Lemma gargs_env_rel : forall Ctx R zs zs' ρ ρ', EF Ctx ≈ Ctx ∈ per_ctx_env ↘ R -> ⊨ Ctx ->
    List.length zs = List.length Ctx ->
    per_gargs (List.rev Ctx) ρ ρ' zs zs' -> R (env_tele ρ (List.rev Ctx) zs) (env_tele ρ' (List.rev Ctx) zs').
Proof.
  intros * HR HC Hl Hg.
  assert (HC' : ⊨ List.rev (List.rev Ctx) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  destruct (gargs_rel _ _ _ _ _ Hg _ _ per_ctx_env_nil_true I HC') as (R' & HR' & Hρ).
  rewrite List.firstn_all2 in HR' by (rewrite List.length_rev; lia).
  rewrite List.rev_involutive, List.app_nil_r in HR'.
  assert (E : R' <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E; exact Hρ.
Qed.

(** The values of an entry of a closed telescope of types of universes,
    at related arguments before it, are relevant. *)
Lemma closed_relevant_dom : forall C, ⊨ C ->
    (forall Δ1 T Δ2, C = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, Δ2 ⊨ T : Typeω@i) ->
    forall ρ ρ' ts1 A ts2 ys ys' b, List.rev C = ts1 ++ ce_ass A :: ts2 -> per_gargs ts1 ρ ρ' ys ys' ->
      List.length ys = List.length ts1 -> ⟦ A ⟧ env_tele ρ ts1 ys ↘ b -> domain_relevance b = relevant.
Proof.
  intros * HC Hrel * Heq Hg Hl Eb.
  assert (HCe : C = List.rev ts2 ++ ce_ass A :: List.rev ts1)
    by (rewrite <- (List.rev_involutive C), Heq, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  destruct (Hrel _ _ _ HCe) as [i HA].
  assert (HC1 : ⊨ List.rev ts1) by (rewrite HCe in HC; exact (rel_ctx_wf_tail (rel_ctx_wf_app_r _ _ HC))).
  destruct (rel_ctx_wf_per_ctx_env HC1) as [R HR].
  assert (Hρ : R (env_tele ρ ts1 ys) (env_tele ρ' ts1 ys')).
  { rewrite <- (List.rev_involutive ts1) at 1 2.
    apply (gargs_env_rel _ _ _ _ _ _ HR HC1); [ rewrite List.length_rev; exact Hl | rewrite List.rev_involutive; exact Hg ]. }
  destruct (rel_exp_of_typ_relevant_at HR HA _ _ Hρ) as (b0 & Eb0 & Hr).
  assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
  exact Hr.
Qed.

(** The same for a closed telescope of entries of given sorts: the values
    of an entry are of its sort. *)
Lemma closed_sorted_dom : forall C (rf : nat -> relevance), ⊨ C ->
    (forall Δ1 T Δ2, C = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, Δ2 ⊨ T : relevance_sort (rf (List.length Δ2)) Typeω@i) ->
    forall ρ ρ' ts1 A ts2 ys ys' b, List.rev C = ts1 ++ ce_ass A :: ts2 -> per_gargs ts1 ρ ρ' ys ys' ->
      List.length ys = List.length ts1 -> ⟦ A ⟧ env_tele ρ ts1 ys ↘ b -> domain_relevance b = rf (List.length ts1).
Proof.
  intros * HC Hrel * Heq Hg Hl Eb.
  assert (HCe : C = List.rev ts2 ++ ce_ass A :: List.rev ts1)
    by (rewrite <- (List.rev_involutive C), Heq, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  destruct (Hrel _ _ _ HCe) as [i HA]; rewrite List.length_rev in HA.
  assert (HC1 : ⊨ List.rev ts1) by (rewrite HCe in HC; exact (rel_ctx_wf_tail (rel_ctx_wf_app_r _ _ HC))).
  destruct (rel_ctx_wf_per_ctx_env HC1) as [R HR].
  assert (Hρ : R (env_tele ρ ts1 ys) (env_tele ρ' ts1 ys')).
  { rewrite <- (List.rev_involutive ts1) at 1 2.
    apply (gargs_env_rel _ _ _ _ _ _ HR HC1); [ rewrite List.length_rev; exact Hl | rewrite List.rev_involutive; exact Hg ]. }
  destruct (rel_exp_of_relevance_sort_at HR HA _ _ Hρ) as (b0 & Eb0 & Hr).
  assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
  exact Hr.
Qed.

(** A telescope of types of universes is one of parameter types. *)
Lemma rel_param_typed_of_universes : forall Γ C,
    (forall Δ1 T Δ2, C = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, Δ2 ++ Γ ⊨ T : Typeω@i) ->
    forall Δ1 T Δ2, C = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i.
Proof. intros * H * E; destruct (H _ _ _ E) as [i Hi]; exists i; left; exact Hi. Qed.

(** An entry of a telescope over [Γ] that is a type of a universe or a
    type of levels ([rel_param_typed]) is no proposition at an environment
    the context PER relates. *)
Lemma relevant_entry_not_propositional : forall Δ Γ R x, tele_ass Δ -> x < List.length Δ ->
    (forall Δ1 T Δ2, Δ = Δ1 ++ ce_ass T :: Δ2 -> List.length Δ1 = x -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i) ->
    EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> ~ entry_propositional gc_deps gc_stack (Δ ++ Γ) ρ x.
Proof.
  intros * Ha Hx Hrel HR ρ ρ' Hρ [T HT E HE a Ea Hp].
  destruct (nth_error_lt_some' Δ x Hx) as [e He].
  assert (Hea : exists A, e = ce_ass A)
    by (unfold tele_ass in Ha; rewrite List.Forall_forall in Ha; apply Ha; eapply List.nth_error_In; exact He).
  destruct Hea as [A ->].
  unfold ctx_entry_type in HT; rewrite List.nth_error_app1, He in HT by exact Hx; injection HT as ->.
  destruct (List.nth_error_split _ _ He) as (l1 & l2 & HΔ & Hl1).
  destruct (Hrel _ _ _ HΔ Hl1) as [i HA].
  pose proof (rel_param_typed_relevant HA) as HAr.
  pose proof (rel_type_inversion (rel_param_typed_type _ _ _ HA)) as [RT [HRT _]].
  assert (HRe : EF (l1 ++ ce_ass T :: nil) ++ (l2 ++ Γ) ≈ (l1 ++ ce_ass T :: nil) ++ (l2 ++ Γ) ∈ per_ctx_env ↘ R)
    by (rewrite HΔ in HR; rewrite <- !List.app_assoc in *; cbn [List.app] in *; exact HR).
  destruct (rel_wk_shiftn _ _ _ _ HRe HRT) as [_ Hwk].
  pose proof (Hwk _ _ Hρ) as Ht; rewrite !eval_wk_shiftn in Ht.
  assert (Hlx : List.length (l1 ++ ce_ass T :: nil) = S x) by (rewrite List.length_app; cbn; lia).
  rewrite Hlx in Ht.
  assert (Hsk : List.skipn (S x) (Δ ++ Γ) = l2 ++ Γ).
  { rewrite HΔ, <- List.app_assoc; cbn [List.app].
    change (l1 ++ ce_ass T :: l2 ++ Γ) with (l1 ++ (ce_ass T :: nil) ++ l2 ++ Γ).
    rewrite List.app_assoc, <- Hlx, List.skipn_app, List.skipn_all2 by lia.
    rewrite Nat.sub_diag; reflexivity. }
  rewrite Hsk in HE.
  pose proof (per_ctx_env_resp_agree HRT _ _ _ _ (symmetry HE) (reflexivity _) Ht) as HE'.
  destruct (HAr _ HRT _ _ HE') as (b & Eb & Hr).
  assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
  congruence.
Qed.

(** An entry of a telescope over [Γ] that is a proposition is one at an
    environment the context PER relates. *)
Lemma prop_entry_propositional : forall Δ Γ R x, tele_ass Δ -> x < List.length Δ ->
    (forall Δ1 T Δ2, Δ = Δ1 ++ ce_ass T :: Δ2 -> List.length Δ1 = x -> Δ2 ++ Γ ⊨ T : Propₘ) ->
    EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> entry_propositional gc_deps gc_stack (Δ ++ Γ) ρ x.
Proof.
  intros * Ha Hx Hrel HR ρ ρ' Hρ.
  destruct (nth_error_lt_some' Δ x Hx) as [e He].
  assert (Hea : exists A, e = ce_ass A)
    by (unfold tele_ass in Ha; rewrite List.Forall_forall in Ha; apply Ha; eapply List.nth_error_In; exact He).
  destruct Hea as [A ->].
  destruct (List.nth_error_split _ _ He) as (l1 & l2 & HΔ & Hl1).
  pose proof (Hrel _ _ _ HΔ Hl1) as HA.
  pose proof HA as [RT HRT _ _].
  assert (HRe : EF (l1 ++ ce_ass A :: nil) ++ (l2 ++ Γ) ≈ (l1 ++ ce_ass A :: nil) ++ (l2 ++ Γ) ∈ per_ctx_env ↘ R)
    by (rewrite HΔ in HR; rewrite <- !List.app_assoc in *; cbn [List.app] in *; exact HR).
  destruct (rel_wk_shiftn _ _ _ _ HRe HRT) as [_ Hwk].
  pose proof (Hwk _ _ Hρ) as Ht; rewrite !eval_wk_shiftn in Ht.
  assert (Hlx : List.length (l1 ++ ce_ass A :: nil) = S x) by (rewrite List.length_app; cbn; lia).
  rewrite Hlx in Ht.
  destruct (rel_exp_of_prop_inversion_simple_at HRT HA _ _ Ht) as (a & a' & Ea & Ea' & Hpp).
  apply (mk_entry_propositional _ _ _ _ _ A ltac:(unfold ctx_entry_type; rewrite List.nth_error_app1, He by exact Hx; reflexivity)
           (List.skipn (S x) ρ) ltac:(reflexivity) a Ea (per_prop_left _ _ Hpp)).
Qed.

(** A telescope of types of universes or of levels over [Γ] has no
    propositional entry at an environment its context PER relates. *)
Corollary relevant_entries_not_propositional : forall Δ Γ R, tele_ass Δ ->
    (forall Δ1 T Δ2, Δ = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i) ->
    EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> forall x, x < List.length Δ -> ~ entry_propositional gc_deps gc_stack (Δ ++ Γ) ρ x.
Proof.
  intros * Ha Hrel HR ρ ρ' Hρ x Hx.
  exact (relevant_entry_not_propositional Δ Γ R x Ha Hx (fun Δ1 T Δ2 E _ => Hrel Δ1 T Δ2 E) HR ρ ρ' Hρ).
Qed.

(** The relevant parameters of a closed telescope stay relevant over any
    valid context. *)
Lemma closed_relevant_over : forall C Γ, tele_ass C -> ⊨ C -> ⊨ Γ ->
    (exists l, rel_params_relevant ⋅ C l) ->
    forall Δ1 T Δ2, C = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i.
Proof.
  intros * Ha HC HΓ [l Hl] * E.
  exists l.
  assert (Ha2 : tele_ass Δ2)
    by (rewrite E in Ha; unfold tele_ass in Ha; apply List.Forall_app in Ha as [_ Ha]; inversion Ha; assumption).
  assert (HC2 : ⊨ Δ2) by (rewrite E in HC; exact (rel_ctx_wf_tail (rel_ctx_wf_app_r _ _ HC))).
  destruct (Hl _ _ _ E) as [H | H]; rewrite List.app_nil_r in H; [ left | right ];
    exact (closed_app_valid _ _ _ _ _ Ha2 HC2 HΓ H).
Qed.

(** The values of an instance [Ms] of a telescope [C] of relevant entries
    over [Γ], at two environments of [Γ]: related at [C ++ Γ] after the
    environments, and the instance's values.  The values extend the
    environments, retagged at [Γ] as the identity has them, at the tags of
    [C]'s entries ([env_extend_tagged]). *)
#[warnings="-cannot-define-projection"]
Record instance_values (C Γ : ctx) (Ms : list exp) (RCΓ : relation env) (B1 B2 : env) : Prop := mk_instance_values
  { (** The terms' values at the left environment *)
    iv_left : list domain
    (** and at the right one *)
  ; iv_right : list domain
    (** The left ones are the terms' values *)
  ; iv_eval_left : ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ iv_left
    (** So are the right ones *)
  ; iv_eval_right : ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ iv_right
    (** They are related at the telescope after the environments *)
  ; iv_rel : RCΓ (env_extend_tagged Γ (List.rev C) (ctx_retag Γ B1) iv_left)
                 (env_extend_tagged Γ (List.rev C) (ctx_retag Γ B2) iv_right)
    (** The left extension is the instance's value *)
  ; iv_sub_left : ⟦ sb_of_list Id Ms : C ++ Γ ⟧s B1 ↘ env_extend_tagged Γ (List.rev C) (ctx_retag Γ B1) iv_left
    (** So is the right one *)
  ; iv_sub_right : ⟦ sb_of_list Id Ms : C ++ Γ ⟧s B2 ↘ env_extend_tagged Γ (List.rev C) (ctx_retag Γ B2) iv_right }.

(** A semantic substitution of the instance gives its values: no entry of
    [C] is a proposition at the substitution's values, so these are the
    terms' values. *)
Lemma instance_values_of_sub : forall C Γ Ms RΓ RCΓ, tele_ass C ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF C ++ Γ ≈ C ++ Γ ∈ per_ctx_env ↘ RCΓ ->
    (forall Δ1 T Δ2, C = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i) ->
    Γ ⊨ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms : C ++ Γ -> List.length Ms = List.length C ->
    forall B1 B2, RΓ B1 B2 -> instance_values C Γ Ms RCΓ B1 B2.
Proof.
  intros * Ha HRΓ HRCΓ0 Hrel' Hσ Hl B1 B2 HB.
  destruct (rel_sub_under_ctx_simple Hσ) as (RΓ' & HRΓ' & RCΓ' & HRCΓ & Hs).
  assert (E : RΓ <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  assert (EC : RCΓ' <~> RCΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) HB)) as (ρσ & ρ'σ' & Ev1 & Ev2 & Hρσ).
  assert (HPC : PER RCΓ') by (eapply per_env_PER; exact HRCΓ).
  pose proof (relevant_entries_not_propositional C Γ RCΓ' Ha Hrel' HRCΓ _ _ Hρσ) as Hnp1.
  pose proof (relevant_entries_not_propositional C Γ RCΓ' Ha Hrel' HRCΓ ρ'σ' ρσ ltac:(symmetry; exact Hρσ)) as Hnp2.
  assert (HlC : List.length (List.rev C) = List.length Ms) by (rewrite List.length_rev; lia).
  assert (Hnp1' : forall x, x < List.length (List.rev C) ->
                    ~ entry_propositional gc_deps gc_stack (List.rev (List.rev C) ++ Γ) ρσ x)
    by (intros x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx; exact (Hnp1 x Hx)).
  assert (Hnp2' : forall x, x < List.length (List.rev C) ->
                    ~ entry_propositional gc_deps gc_stack (List.rev (List.rev C) ++ Γ) ρ'σ' x)
    by (intros x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx; exact (Hnp2 x Hx)).
  rewrite <- (List.rev_involutive C) in Ev1, Ev2.
  destruct (eval_sb_of_list_inv Ms (List.rev C) Id Γ B1 ρσ _ HlC Ev1 Hnp1' (eval_sub_id _ _)) as (u1 & Eu1 & Hag1).
  destruct (eval_sb_of_list_inv Ms (List.rev C) Id Γ B2 ρ'σ' _ HlC Ev2 Hnp2' (eval_sub_id _ _)) as (u2 & Eu2 & Hag2).
  rewrite List.length_rev in Hag1, Hag2.
  rewrite List.rev_involutive in Ev1, Ev2.
  assert (H12 : RCΓ' (env_extend_tagged Γ (List.rev C) (ctx_retag Γ B1) u1) (env_extend_tagged Γ (List.rev C) (ctx_retag Γ B2) u2))
    by (eapply (per_ctx_env_resp_agree HRCΓ); [ rewrite List.length_app; exact Hag1 | rewrite List.length_app; exact Hag2 | exact Hρσ ]).
  (** The instance's values at the terms' values: no entry of [C] is a
      proposition there, as at the values the substitution has. *)
  assert (Hsub : forall B u ρ0, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u ->
             env_agree_upto (List.length C + List.length Γ) ρ0 (env_extend_tagged Γ (List.rev C) (ctx_retag Γ B) u) ->
             (forall x, x < List.length C -> ~ entry_propositional gc_deps gc_stack (C ++ Γ) ρ0 x) ->
             ⟦ sb_of_list Id Ms : C ++ Γ ⟧s B ↘ env_extend_tagged Γ (List.rev C) (ctx_retag Γ B) u).
  { intros B u ρ0 Eu Hag Hnp.
    rewrite <- (List.rev_involutive C) at 1.
    apply eval_sb_of_list; [ exact (eval_sub_id _ _) | exact Eu | exact HlC |].
    intros x Hx Hpx; exfalso; rewrite List.length_rev in Hx; rewrite List.rev_involutive in Hpx.
    apply (Hnp x Hx).
    apply (entry_propositional_resp_agree _ (env_extend_tagged Γ (List.rev C) (ctx_retag Γ B) u)); [| exact Hpx ].
    rewrite List.length_app; intros y Hy; symmetry; exact (Hag y Hy). }
  exists u1 u2; [ exact Eu1 | exact Eu2 | exact (proj1 (EC _ _) H12)
                | exact (Hsub _ _ _ Eu1 Hag1 Hnp1) | exact (Hsub _ _ _ Eu2 Hag2 Hnp2) ].
Qed.

(** A substitution extended by terms [Ms] whose entries are sorted by
    [rf]: those of a relevant sort no proposition at the value [E], the
    values [ms] the terms' values there, and those of the propositional
    one propositions there, the values [ms] the terms kept as proofs over
    [ρ].  [E] then holds the values [ms] at their entries' tags over its
    tail.  The term [M] at index [j] of [Ms] is the entry
    [|Ms| - 1 - j]. *)
Lemma eval_sb_of_list_sorted_vals : forall Ms ts σ Δ ρ E ms (rf : nat -> relevance),
    List.length ts = List.length Ms -> List.length ms = List.length Ms ->
    ⟦ sb_of_list σ Ms : List.rev ts ++ Δ ⟧s ρ ↘ E ->
    (forall j M m, List.nth_error Ms j = Some M -> List.nth_error ms j = Some m -> rf (List.length Ms - 1 - j) = relevant ->
       ~ entry_propositional gc_deps gc_stack (List.rev ts ++ Δ) E (List.length Ms - 1 - j) /\ ⟦ M ⟧ ρ ↘ m) ->
    (forall j M m, List.nth_error Ms j = Some M -> List.nth_error ms j = Some m -> rf (List.length Ms - 1 - j) = propositional ->
       entry_propositional gc_deps gc_stack (List.rev ts ++ Δ) E (List.length Ms - 1 - j) /\ m = ⋆ᵈ⟨M, ρ⟩) ->
    forall x, env_entry E x = env_entry (env_extend_tagged Δ ts (List.skipn (List.length ts) E) ms) x.
Proof.
  #[local] Transparent eval_sub.
  induction Ms as [| M Ms IH]; intros [| e ts] * Hl Hlm H Hr Hp; cbn [List.length] in Hl, Hlm; try discriminate.
  - destruct ms; cbn [List.length] in Hlm; [| discriminate Hlm ]; intros x; reflexivity.
  - destruct ms as [| m ms]; cbn [List.length] in Hlm; [ discriminate Hlm |].
    assert (Hl' : List.length ts = List.length Ms) by lia.
    assert (Hlm' : List.length ms = List.length Ms) by lia.
    cbn [List.length] in Hr, Hp.
    cbn [sb_of_list List.rev] in H, Hr, Hp; rewrite <- List.app_assoc in H, Hr, Hp; cbn [List.app] in H, Hr, Hp.
    assert (Hag : forall x, env_entry E x = env_entry (env_extend_tagged (e :: Δ) ts (List.skipn (List.length ts) E) ms) x).
    { apply (IH ts _ (e :: Δ) _ _ ms rf Hl' Hlm' H).
      - intros j M0 m0 HM0 Hm0 Hrf; replace (List.length Ms - 1 - j) with (S (List.length Ms) - 1 - S j) by lia.
        apply (Hr (S j)); [ exact HM0 | exact Hm0 | replace (S (List.length Ms) - 1 - S j) with (List.length Ms - 1 - j) by lia; exact Hrf ].
      - intros j M0 m0 HM0 Hm0 Hrf; replace (List.length Ms - 1 - j) with (S (List.length Ms) - 1 - S j) by lia.
        apply (Hp (S j)); [ exact HM0 | exact Hm0 | replace (S (List.length Ms) - 1 - S j) with (List.length Ms - 1 - j) by lia; exact Hrf ]. }
    (** The head term, at the entry past the later ones. *)
    assert (Hx : List.length ts < List.length (List.rev ts ++ e :: Δ))
      by (rewrite List.length_app, List.length_rev; cbn [List.length]; lia).
    destruct (H _ Hx) as [HP HN].
    assert (Hσx : sb_of_list (σ ,, M) Ms (List.length ts) = se_exp M)
      by (rewrite Hl', <- (Nat.add_0_r (List.length Ms)), sb_of_list_ge; reflexivity).
    rewrite Hσx in HP, HN.
    assert (Hi : S (List.length Ms) - 1 - 0 = List.length ts) by lia.
    assert (Hme : env_entry E (List.length ts) = de_term m (ctx_entry_tag (List.rev ts ++ e :: Δ) (List.length ts) E)).
    { destruct (rf (List.length ts)) eqn:Erf.
      - destruct (Hr 0 M m eq_refl eq_refl ltac:(rewrite Hi; exact Erf)) as [Hn Em]; rewrite Hi in Hn.
        destruct (HN Hn) as (m' & Hme & Hm'); rewrite Hme; f_equal.
        eapply functional_eval_exp; eassumption.
      - destruct (Hp 0 M m eq_refl eq_refl ltac:(rewrite Hi; exact Erf)) as [Hpx ->]; rewrite Hi in Hpx.
        exact (HP Hpx). }
    rewrite <- (List.length_rev ts), ctx_entry_tag_app_at, List.length_rev in Hme.
    (** The tail past the later entries has the head term's value, at its
        tag, before the rest. *)
    intros x; rewrite Hag; cbn [List.length env_extend_tagged].
    apply env_extend_tagged_eq; intros [| k]; rewrite env_entry_skipn.
    + rewrite Nat.add_0_r, Hme; reflexivity.
    + transitivity (env_entry (List.skipn (S (List.length ts)) E) k); [| reflexivity ].
      rewrite env_entry_skipn; f_equal; lia.
Qed.

(** Any value of a substitution extended by terms [Ms] whose entries are
    sorted by [rf] holds, at the entries, values [ms]: the terms' values
    at the relevant ones, the terms kept as proofs at the propositional
    ones, stored at the entries' tags over its tail. *)
Lemma eval_sb_of_list_sorted_split : forall Ms ts σ Δ ρ E (rf : nat -> relevance),
    List.length ts = List.length Ms -> ⟦ sb_of_list σ Ms : List.rev ts ++ Δ ⟧s ρ ↘ E ->
    (forall x, x < List.length ts -> rf x = relevant -> ~ entry_propositional gc_deps gc_stack (List.rev ts ++ Δ) E x) ->
    (forall x, x < List.length ts -> rf x = propositional -> entry_propositional gc_deps gc_stack (List.rev ts ++ Δ) E x) ->
    exists ms, List.length ms = List.length Ms /\
      (forall j M m, List.nth_error Ms j = Some M -> List.nth_error ms j = Some m ->
         (rf (List.length Ms - 1 - j) = relevant -> ⟦ M ⟧ ρ ↘ m) /\
         (rf (List.length Ms - 1 - j) = propositional -> m = ⋆ᵈ⟨M, ρ⟩)) /\
      forall x, env_entry E x = env_entry (env_extend_tagged Δ ts (List.skipn (List.length ts) E) ms) x.
Proof.
  #[local] Transparent eval_sub.
  induction Ms as [| M Ms IH]; intros [| e ts] * Hl H Hr Hp; cbn [List.length] in Hl; try discriminate.
  { exists nil; split; [ reflexivity | split; [ intros [] ? ? Hj; discriminate Hj | intros x; reflexivity ] ]. }
  assert (Hl' : List.length ts = List.length Ms) by lia.
  cbn [sb_of_list List.rev] in H, Hr, Hp; rewrite <- List.app_assoc in H, Hr, Hp; cbn [List.app] in H, Hr, Hp.
  destruct (IH ts _ (e :: Δ) _ _ rf Hl' H ltac:(intros x Hx; apply Hr; cbn [List.length]; lia)
              ltac:(intros x Hx; apply Hp; cbn [List.length]; lia)) as (ms & Hlm & Hms & Hag).
  assert (Hx : List.length ts < List.length (List.rev ts ++ e :: Δ))
    by (rewrite List.length_app, List.length_rev; cbn [List.length]; lia).
  destruct (H _ Hx) as [HP HN].
  assert (Hσx : sb_of_list (σ ,, M) Ms (List.length ts) = se_exp M)
    by (rewrite Hl', <- (Nat.add_0_r (List.length Ms)), sb_of_list_ge; reflexivity).
  rewrite Hσx in HP, HN.
  (** The head term's value: its value or the term kept as a proof, by its
      entry's sort. *)
  assert (Hhead : exists m, env_entry E (List.length ts) = de_term m (ctx_entry_tag (List.rev ts ++ e :: Δ) (List.length ts) E) /\
                    (rf (List.length ts) = relevant -> ⟦ M ⟧ ρ ↘ m) /\ (rf (List.length ts) = propositional -> m = ⋆ᵈ⟨M, ρ⟩)).
  { destruct (rf (List.length ts)) eqn:Erf.
    - destruct (HN (Hr (List.length ts) ltac:(cbn [List.length]; lia) Erf)) as (m & Hme & Hm).
      exists m; split; [ exact Hme | split; [ intros _; exact Hm | discriminate ] ].
    - exists ⋆ᵈ⟨M, ρ⟩; split; [ exact (HP (Hp (List.length ts) ltac:(cbn [List.length]; lia) Erf)) | split; [ discriminate | reflexivity ] ]. }
  destruct Hhead as (m & Hme & Hm1 & Hm2).
  rewrite <- (List.length_rev ts), ctx_entry_tag_app_at, List.length_rev in Hme.
  exists (m :: ms); split; [ cbn; lia | split ].
  - intros [| j] N n HN0 Hn0; cbn [List.nth_error] in HN0, Hn0.
    + injection HN0 as <-; injection Hn0 as <-.
      replace (List.length (M :: Ms) - 1 - 0) with (List.length ts) by (cbn [List.length]; lia).
      split; assumption.
    + replace (List.length (M :: Ms) - 1 - S j) with (List.length Ms - 1 - j) by (cbn [List.length]; lia).
      exact (Hms _ _ _ HN0 Hn0).
  - intros x; rewrite Hag; cbn [List.length env_extend_tagged].
    apply env_extend_tagged_eq; intros [| k]; rewrite env_entry_skipn.
    + rewrite Nat.add_0_r, Hme; reflexivity.
    + transitivity (env_entry (List.skipn (S (List.length ts)) E) k); [| reflexivity ].
      rewrite env_entry_skipn; f_equal; lia.
Qed.

(** The same over any base substitution [σ], at one environment of the
    substitution's context [Ψ]: the instance's value is [σ]'s, extended by
    the terms' values. *)
Lemma sb_of_list_values_of_sub : forall C Γ Ψ σ Ms RΨ RCΓ ρ σρ, tele_ass C ->
    EF Ψ ≈ Ψ ∈ per_ctx_env ↘ RΨ -> EF C ++ Γ ≈ C ++ Γ ∈ per_ctx_env ↘ RCΓ ->
    (forall Δ1 T Δ2, C = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i) ->
    Ψ ⊨ˢ sb_of_list σ Ms ≈ sb_of_list σ Ms : C ++ Γ -> List.length Ms = List.length C ->
    RΨ ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ σρ ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\
      ⟦ sb_of_list σ Ms : C ++ Γ ⟧s ρ ↘ env_extend_tagged Γ (List.rev C) σρ ms /\
      RCΓ (env_extend_tagged Γ (List.rev C) σρ ms) (env_extend_tagged Γ (List.rev C) σρ ms).
Proof.
  intros * Ha HRΨ HRCΓ0 Hrel' Hσ Hl Hρ Hev.
  destruct (rel_sub_under_ctx_simple Hσ) as (RΨ' & HRΨ' & RCΓ' & HRCΓ & Hs).
  assert (E : RΨ <~> RΨ') by (eapply per_ctx_env_right_irrel; eassumption).
  assert (EC : RCΓ' <~> RCΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (ρτ & ρτ' & Ev1 & _ & Hρτ).
  assert (HPC : PER RCΓ') by (eapply per_env_PER; exact HRCΓ).
  assert (Hρτρτ : RCΓ' ρτ ρτ) by (etransitivity; [ exact Hρτ | symmetry; exact Hρτ ]).
  pose proof (relevant_entries_not_propositional C Γ RCΓ' Ha Hrel' HRCΓ _ _ Hρτρτ) as Hnp.
  assert (HlC : List.length (List.rev C) = List.length Ms) by (rewrite List.length_rev; lia).
  assert (Hnp' : forall x, x < List.length (List.rev C) ->
                   ~ entry_propositional gc_deps gc_stack (List.rev (List.rev C) ++ Γ) ρτ x)
    by (intros x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx; exact (Hnp x Hx)).
  rewrite <- (List.rev_involutive C) in Ev1.
  destruct (eval_sb_of_list_inv Ms (List.rev C) σ Γ ρ ρτ σρ HlC Ev1 Hnp' Hev) as (ms & Ems & Hag).
  rewrite List.length_rev in Hag.
  assert (Hrel : RCΓ' (env_extend_tagged Γ (List.rev C) σρ ms) (env_extend_tagged Γ (List.rev C) σρ ms))
    by (eapply (per_ctx_env_resp_agree HRCΓ); [ rewrite List.length_app; exact Hag | rewrite List.length_app; exact Hag | exact Hρτρτ ]).
  exists ms; split; [ exact Ems | split; [| exact (proj1 (EC _ _) Hrel) ] ].
  rewrite <- (List.rev_involutive C) at 1.
  apply eval_sb_of_list; [ exact Hev | exact Ems | exact HlC |].
  intros x Hx Hpx; exfalso; rewrite List.length_rev in Hx; rewrite List.rev_involutive in Hpx.
  apply (Hnp x Hx).
  apply (entry_propositional_resp_agree _ (env_extend_tagged Γ (List.rev C) σρ ms)); [| exact Hpx ].
  rewrite List.length_app; intros y Hy; symmetry; exact (Hag y Hy).
Qed.

(** The values of an instance [Ms] of a closed telescope [C] of relevant
    entries, over [Γ], at two environments of [Γ]: related at [C], and the
    instance's values.  At [C] the values are its own environment, at
    the closures of its types ([env_tele]); the instance's values extend
    the environments as in [instance_values]. *)
#[warnings="-cannot-define-projection"]
Record closed_instance_values (C Γ : ctx) (Ms : list exp) (RC : relation env) (B1 B2 : env) : Prop := mk_closed_instance_values
  { (** The terms' values at the left environment *)
    civ_left : list domain
    (** and at the right one *)
  ; civ_right : list domain
    (** The left ones are the terms' values *)
  ; civ_eval_left : ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ civ_left
    (** So are the right ones *)
  ; civ_eval_right : ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ civ_right
    (** They are related at the telescope *)
  ; civ_rel : RC (env_tele nil (List.rev C) civ_left) (env_tele nil (List.rev C) civ_right)
    (** The left extension is the instance's value *)
  ; civ_sub_left : ⟦ sb_of_list Id Ms : C ++ Γ ⟧s B1 ↘ env_extend_tagged Γ (List.rev C) (ctx_retag Γ B1) civ_left
    (** So is the right one *)
  ; civ_sub_right : ⟦ sb_of_list Id Ms : C ++ Γ ⟧s B2 ↘ env_extend_tagged Γ (List.rev C) (ctx_retag Γ B2) civ_right }.

(** A semantic substitution of the instance gives its values: no entry of
    [C] is a proposition at the substitution's values, so these are the
    terms' values, related at [C]. *)
Lemma closed_instance_values_of_sub : forall C Γ Ms RΓ RC, tele_ass C -> ⊨ C -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF C ≈ C ∈ per_ctx_env ↘ RC ->
    (exists l, rel_params_relevant ⋅ C l) ->
    Γ ⊨ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms : C ++ Γ -> List.length Ms = List.length C ->
    forall B1 B2, RΓ B1 B2 -> closed_instance_values C Γ Ms RC B1 B2.
Proof.
  intros * Ha HC HΓ HRΓ HRC Hrel Hσ Hl B1 B2 HB.
  destruct (closed_app_sem _ _ Ha HC HΓ) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  destruct (instance_values_of_sub C Γ Ms RΓ RCΓ Ha HRΓ HRCΓ (closed_relevant_over C Γ Ha HC HΓ Hrel) Hσ Hl B1 B2 HB)
    as [u1 u2 Eu1 Eu2 H12 Es1 Es2].
  pose proof (Hres _ _ HRC HRCΓ _ _ H12) as H12'.
  pose proof (eval_exps_length _ _ _ Eu1) as L1; pose proof (eval_exps_length _ _ _ Eu2) as L2.
  exists u1 u2; [ exact Eu1 | exact Eu2 | | exact Es1 | exact Es2 ].
  assert (Hl1 : List.length (List.rev C) = List.length u1) by (rewrite List.length_rev; lia).
  assert (Hl2 : List.length (List.rev C) = List.length u2) by (rewrite List.length_rev; lia).
  rewrite !env_extend_tagged_typed in H12'.
  rewrite <- (tagged_entries_fst _ Γ (ctx_retag Γ B1) _ Hl1), <- (tagged_entries_fst _ Γ (ctx_retag Γ B2) _ Hl2).
  eapply closed_env_tele; [ exact Ha | exact HC | exact HRC | | | exact H12' ];
    rewrite tagged_entries_length; lia.
Qed.

(** Related arguments of a closed telescope [C] over related environments
    of [Γ] are related environments of [C ++ Γ]. *)
Lemma closed_args_rel_over : forall C Γ RΓ RCΓ E E' zs zs', tele_ass C -> ⊨ C -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF C ++ Γ ≈ C ++ Γ ∈ per_ctx_env ↘ RCΓ -> RΓ E E' ->
    List.length zs = List.length C -> per_gargs (List.rev C) nil nil zs zs' ->
    RCΓ (env_tele E (List.rev C) zs) (env_tele E' (List.rev C) zs').
Proof.
  intros * Ha HC HΓ HRΓ HRCΓ HE Hl Hg.
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true HC' (List.Forall_rev Ha) nil nil E E' zs zs' I I I Hg) as Hg'.
  destruct (closed_app_sem _ _ Ha HC HΓ) as [HCΓ _].
  exact (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRCΓ HCΓ HE Hl Hg').
Qed.

(** Arguments related at a telescope are related by the canonical
    relations. *)
Lemma gargs_tele_canon : forall ts (tr : nat -> list domain -> relation domain) E,
    (forall j A pre, List.nth_error ts j = Some (ce_ass A) ->
       (tr j pre <~> per_head A A (env_tele E ts pre) (env_tele E ts pre))) ->
    forall E' vs vs', per_gargs ts E E' vs vs' -> List.length vs = List.length ts -> tele_rel tr ts vs vs'.
Proof.
  intros * Htr * Hg Hl.
  assert (Hgen : forall ts' ρ ρ' xs xs', per_gargs ts' ρ ρ' xs xs' ->
             forall k pre, ρ = env_tele E ts pre -> List.length pre = k -> ts' = List.skipn k ts ->
             tele_rel_from tr k pre xs xs').
  { induction 1 as [ts' ρ ρ' | i A ρ ρ' x x' ts' ys ys' R HA Hx Hg' IH]; intros k pre Hρ Hk Hts'; [ exact I |].
    split.
    - assert (Hnth : List.nth_error ts k = Some (ce_ass A)).
      { assert (H0 : List.nth_error (List.skipn k ts) 0 = Some (ce_ass A)) by (rewrite <- Hts'; reflexivity).
        rewrite List.nth_error_skipn, Nat.add_0_r in H0; exact H0. }
      apply (Htr _ _ _ Hnth).
      destruct HA as [b b' Eb Eb' HR].
      subst ρ.
      eapply per_head_of; [ exact Eb | exact Eb | | exact Hx ].
      eapply per_univ_trans; [ exact HR | apply per_univ_sym; exact HR ].
    - assert (Hnth : List.nth_error ts k = Some (ce_ass A)).
      { assert (H0 : List.nth_error (List.skipn k ts) 0 = Some (ce_ass A)) by (rewrite <- Hts'; reflexivity).
        rewrite List.nth_error_skipn, Nat.add_0_r in H0; exact H0. }
      apply (IH (S k) (pre ++ x :: nil)); [ rewrite (env_tele_snoc_at E ts pre A x) by congruence; rewrite Hρ; reflexivity | rewrite List.length_app; cbn; lia |].
      assert (Hsk : List.skipn (S k) ts = List.tl (List.skipn k ts))
        by (change (S k) with (1 + k); rewrite <- List.skipn_skipn; destruct (List.skipn k ts); reflexivity).
      rewrite Hsk, <- Hts'; reflexivity. }
  split; [ exact Hl |].
  exact (Hgen _ _ _ _ _ Hg 0 nil eq_refl eq_refl eq_refl).
Qed.

(** ** Equal Extensions, Entry by Entry

    Two extensions equal in the PER model are equal entry by entry: the
    outer parts are, and the two last entries are types related over the
    first's outer part.  A substitution built from valid parts moves such
    an equation along it ([rel_ext_under_ctx_gsub]). *)

(** The parts of an equation of two extensions by assumptions. *)
#[warnings="-cannot-define-projection"]
Record rel_ext_ass_parts Γ Ψ Ψ' A A' : Prop := mk_rel_ext_ass_parts
  { (** The outer parts are equal *)
    rel_ext_ass_tail : Γ ⊨ˣ Ψ ≈ Ψ'
    (** The left type is valid, at its sort *)
  ; rel_ext_ass_left : exists S, type_sort S /\ Ψ ++ Γ ⊨ A : S
    (** The right type is valid, at its sort *)
  ; rel_ext_ass_right : exists S, type_sort S /\ Ψ' ++ Γ ⊨ A' : S
    (** The level the two types are equal at *)
  ; rel_ext_ass_level : nat
    (** The two types are equal over the left outer part *)
  ; rel_ext_ass_eq : Ψ ++ Γ ⊨ᵗ A ≈ A' at rel_ext_ass_level }.

Lemma rel_ext_under_ctx_ass_inv : forall Γ Ψ Ψ' A A', Γ ⊨ˣ Ψ ▹ A ≈ Ψ' ▹ A' -> rel_ext_ass_parts Γ Ψ Ψ' A A'.
Proof.
  intros * [HL HR [R HRR]]; cbn [List.app] in HL, HR, HRR.
  inversion HRR as [| ? ? i0 ? ? tail_rel head_rel ? HT _ Hhead _ | | |]; subst.
  pose proof (rel_ctx_wf_tail HL) as HL0; pose proof (rel_ctx_wf_tail HR) as HR0.
  destruct (rel_ctx_wf_ass_typ HL) as [i1 HA]; destruct (rel_ctx_wf_ass_typ HR) as [i2 HA'].
  apply (mk_rel_ext_ass_parts _ _ _ _ _ (mk_rel_ext_under_ctx _ _ _ HL0 HR0 (ex_intro _ tail_rel HT))
           (rel_ctx_wf_ass_inv HL) (rel_ctx_wf_ass_inv HR) (max (max i1 i2) i0)).
  destruct (rel_ctx_wf_per_ctx_env HL0) as [RL HRL]; destruct (rel_ctx_wf_per_ctx_env HR0) as [RR HRR0].
  assert (EL : tail_rel <~> RL) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (ER : tail_rel <~> RR) by (eapply per_ctx_env_left_irrel; eassumption).
  assert (HPt : PER tail_rel) by (eapply per_env_PER; exact HT).
  set (i := max (max i1 i2) i0).
  assert (HAi : Ψ ++ Γ ⊨ᵗ A ≈ A at i) by (eapply rel_type_cumu_ge; [| exact HA ]; lia).
  assert (HA'i : Ψ' ++ Γ ⊨ᵗ A' ≈ A' at i) by (eapply rel_type_cumu_ge; [| exact HA' ]; lia).
  (** [A'] in the left context: the two contexts have related
      environments and the same propositional entries. *)
  assert (HA'L : Ψ ++ Γ ⊨ᵗ A' ≈ A' at i).
  { eapply (rel_type_under_ctx_restrict HRL HRR0); [ | | | exact HA'i ].
    - intros ρ ρ' Hρ; apply ER, EL; exact Hρ.
    - rewrite (per_ctx_env_length HT); lia.
    - intros ρ ρ' Hρ; apply EL in Hρ; exact (ctx_props_agree_of_per _ _ _ HT ρ ρ' Hρ). }
  apply (rel_type_under_ctx_of_simple HRL HAi HA'L).
  intros ρ ρ' Hρ.
  destruct (Hhead _ _ (proj2 (EL _ _) Hρ)) as [a a' Ea Ea' Haa].
  exists a, a'; split; [ exact Ea | split; [ exact Ea' |] ].
  eexists; eapply per_univ_elem_cumu_ge; [| exact Haa ]; lia.
Qed.

Lemma rel_ext_under_ctx_gsub : forall Γ τ Δ Ψ Ψ', gsub Γ τ Δ -> tele_ass Ψ -> tele_ass Ψ' ->
    Δ ⊨ˣ Ψ ≈ Ψ' -> Γ ⊨ˣ tele_sub Ψ τ ≈ tele_sub Ψ' τ.
Proof.
  intros Γ τ Δ Ψ; induction Ψ as [| e Ψ IH]; intros Ψ' Hg Ha Ha' HΨ.
  - pose proof (per_ctx_respects_length (rel_ext_under_ctx_eq _ _ _ HΨ)) as Hl; rewrite !List.length_app in Hl.
    destruct Ψ' as [| e' Ψ']; cbn in Hl; [| lia ].
    destruct (gsub_sem Hg) as [HΓ _].
    constructor; [ exact HΓ | exact HΓ | exact (rel_ctx_wf_per_ctx HΓ) ].
  - pose proof (per_ctx_respects_length (rel_ext_under_ctx_eq _ _ _ HΨ)) as Hl; rewrite !List.length_app in Hl.
    destruct Ψ' as [| e' Ψ']; cbn in Hl; [ lia |].
    assert (He : exists A, e = ce_ass A) by (inversion Ha as [| ? ? He _]; exact He).
    assert (He' : exists A', e' = ce_ass A') by (inversion Ha' as [| ? ? He' _]; exact He').
    destruct He as [A ->]; destruct He' as [A' ->].
    assert (Hsa : tele_ass Ψ) by (inversion Ha; assumption).
    assert (Hsa' : tele_ass Ψ') by (inversion Ha'; assumption).
    destruct (rel_ext_under_ctx_ass_inv _ _ _ _ _ HΨ) as [HΨ0 (S & HS & HA) (S' & HS' & HA') i HAA].
    pose proof (IH _ Hg Hsa Hsa' HΨ0) as IH0.
    assert (Hl0 : List.length Ψ = List.length Ψ') by lia.
    pose proof (gsub_qn _ _ _ _ Hg Hsa (rel_ext_under_ctx_left _ _ _ HΨ0)) as Hq.
    pose proof (gsub_qn _ _ _ _ Hg Hsa' (rel_ext_under_ctx_right _ _ _ HΨ0)) as Hq'.
    pose proof (rel_exp_under_ctx_gsub Hq HA) as HAτ.
    pose proof (rel_type_under_ctx_gsub Hq HAA) as HAAτ.
    pose proof (rel_exp_under_ctx_gsub Hq' HA') as HA'τ.
    rewrite (type_sort_sub _ _ HS) in HAτ; rewrite (type_sort_sub _ _ HS') in HA'τ.
    rewrite <- Hl0 in HA'τ.
    cbn [tele_sub centry_sub]; rewrite <- Hl0.
    destruct IH0 as [H1 H2 H3].
    constructor; cbn [List.app].
    + exact (rel_ctx_wf_extend_sort H1 HS HAτ).
    + exact (rel_ctx_wf_extend_sort H2 HS' HA'τ).
    + exact (per_ctx_extend_type H3 HAAτ).
Qed.

(** The variables of a closed telescope, each of the type its telescope
    gives it at the variables before. *)
Lemma valid_vars_tele : forall Φ Δ,
    tele_ass Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> ⊨ Φ ++ Δ ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      Φ ++ Δ ⊨ N : T.
Proof.
  intros * Hass Hs Hmv HΔ k N T HN HT.
  apply vars_from_nth_error in HN as [Hk ->].
  apply tele_insts_nth in HT as (A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HsA : exp_scoped k A).
  { rewrite HΔeq in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HsA _].
    rewrite List.length_rev, Nat.add_0_r in HsA; congruence. }
  assert (HmA : exp_mvc 0 A).
  { unfold ctx_mvc in Hmv; rewrite HΔeq in Hmv; apply List.Forall_app in Hmv as [_ Hmv].
    apply List.Forall_cons_iff in Hmv as [HmA _]; exact HmA. }
  replace (A[sb_of_list Id (List.firstn k (vars_from (List.length Φ) (List.length Δ)))])
    with (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ).
  - apply valid_exp_under_ctx_vlookup; [| exact HΔ ].
    replace (List.length Φ + (List.length Δ - 1 - k)) with (0 + List.length (Φ ++ List.rev l2))
      by (rewrite List.length_app, List.length_rev; lia).
    replace (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ)
      with (A[wk_shift]ʷ[wk_shiftn (List.length (Φ ++ List.rev l2))]ʷ)
      by (rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app, List.length_rev; lia).
    rewrite HΔeq, List.app_assoc.
    apply ctx_lookup_app_r; constructor.
  - rewrite <- exp_sub_of_wk; eapply exp_scoped_mvc_agree; [ exact HsA | exact HmA |].
    intros x Hx; rewrite sb_of_list_firstn_vars by lia; cbn; f_equal; lia.
Qed.

(** ** The Group's Conditions, from its Typing

    The conditions the universe clause asks of a group ([grp_tele_ass]) are
    syntactic, and its typing gives them, with the typing of its views'
    containers. *)
Lemma grp_tele_ass_of_typed : forall D, decl_typed gc_deps gc_stack D ->
    (forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup gc_deps gc_stack qc = Some Dq -> decl_typed gc_deps gc_stack Dq) ->
    grp_tele_ass D.
Proof.
  intros D HD Hcont; constructor.
  - exact (decl_typed_ass _ _ _ HD).
  - exact (decl_typed_nparams_ass _ _ _ HD).
  - intros v Mv qc kc Is vm HMv Hh.
    destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ HMv Hh) as (Dq & Mc & HDq & HMc & _ & HlIs & _ & Hvm & _).
    destruct (decl_typed_view_wrap _ _ _ HD _ _ _ _ _ _ HMv Hh) as (D' & HD' & Hvw).
    rewrite HDq in HD'; injection HD' as <-.
    destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ HMc Hvm) as (Mv' & HMv' & Hnn & _).
    rewrite HMv in HMv'; injection HMv' as <-.
    exists Dq, Mc; repeat split; [ exact HDq | exact HMc | exact (eq_sym Hnn) | exact HlIs ].
  - exact (decl_typed_rank _ _ _ HD).
  - exact (decl_typed_view_wrap _ _ _ HD).
  - exact (decl_typed_view_maps_coherent _ _ _ HD).
  - intros v Mv qc kc Is vm Dq i' Mi' HMv Hh HDq HMi'.
    destruct (decl_typed_view_wrap _ _ _ HD _ _ _ _ _ _ HMv Hh) as (D' & HD' & Hvw).
    rewrite HDq in HD'; injection HD' as <-.
    assert (Hi' : i' < List.length vm)
      by (rewrite (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; unfold ind_member in HMi'; congruence).
    destruct (nth_error_lt_some' _ _ Hi') as [w Hw].
    destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ HMi' Hw) as (Mw & HMw & Hnn & _).
    refine (mk_view_member_image _ _ _ _ _ _ w Mw Hw HMw Hnn _).
    destruct (im_head Mi') as [pm' | q'' k'' Is'' vm'' | q'' Is'' fl''] eqn:Hh'.
    + destruct (decl_typed_view_decl _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ HMv Hh HDq HMi' Hh' Hw) as (Mw' & vm' & HMw' & Hhw).
      rewrite HMw in HMw'; injection HMw' as <-; exists vm'; exact Hhw.
    + destruct (decl_typed_view_view _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMv Hh HDq HMi' Hh' Hw) as (Mw' & X & vm' & HMw' & Hhw & HlX).
      rewrite HMw in HMw'; injection HMw' as <-; exists X, vm'; split; [ exact Hhw | exact HlX ].
    + destruct (decl_typed_view_rview _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ _ _ HMv Hh HDq HMi' Hh' Hw) as (Mw' & X & HMw' & Hhw & HlX).
      rewrite HMw in HMw'; injection HMw' as <-; exists X; split; [ exact Hhw | exact HlX ].
  - exact (decl_typed_params_length _ _ _ HD).
  - intros v Mv qc kc Is vm Dq i' Mi' c gs' HMv Hh HDq HMi' Hin.
    exact (decl_typed_params_length _ _ _ (Hcont _ _ _ _ _ _ _ HMv Hh HDq) _ _ _ _ HMi' Hin).
  - exact (decl_typed_record_struct _ _ _ HD).
  - intros v Mv qc kc Is vm Dq HMv Hh HDq.
    exact (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ (Hcont _ _ _ _ _ _ _ HMv Hh HDq))).
  - intros v Mv qc kc Is vm Dq HMv Hh HDq.
    exact (decl_typed_record_struct _ _ _ (Hcont _ _ _ _ _ _ _ HMv Hh HDq)).
Qed.

(** The values of the declared members of the group at [p] at the uniform
    parameters [ups], in order: the values of the members as variables
    ([grp_selfs]) the substitution [grp_sb p D] gives at [ups]. *)
Definition selfs_vals (p : qname) (D : ind_decl) (ups : list domain) : list domain :=
  List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D)).

(** ** A Telescope at the Sort

    A type of a declaration in the context [Pre] over the uniform
    parameters, of the sort shifted past [Pre], evaluates at related
    arguments to types of the universe the sort denotes at the uniform
    parameters. *)
Section Sort.
  Variable (D : ind_decl).
  Hypothesis (HD : valid_ind_decl D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)).

  Lemma sort_univ : forall ρ b, ⟦ ind_sort D ⟧ ρ ↘ b -> is_univ b.
  Proof.
    intros * Hb; destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in Hb; inversion Hb; subst; unfold is_univ; eauto.
  Qed.

  Lemma sort_wk_univ : forall φ ρ b, ⟦ (ind_sort D)[φ]ʷ ⟧ ρ ↘ b -> is_univ b.
  Proof.
    intros * Hb; destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in Hb; cbn in Hb; inversion Hb; subst;
      unfold is_univ; eauto.
  Qed.

  Lemma uparams_ass : tele_ass (ind_uparams D).
  Proof. exact (decl_closed_ass _ Hc). Qed.

  Lemma rev_uparams_ass : tele_ass (List.rev (ind_uparams D)).
  Proof. apply List.Forall_rev, uparams_ass. Qed.

  Lemma sort_typ_rel_relevant : forall Pre T, ⊨ Pre ++ ind_uparams D ->
      Pre ++ ind_uparams D ⊨ T : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      forall ups ups' zs zs', List.length zs = List.length Pre -> List.length zs' = List.length Pre ->
        List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
        per_gargs (List.rev (Pre ++ ind_uparams D)) nil nil (ups ++ zs) (ups' ++ zs') ->
        forall a, ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        exists t t', ⟦ T ⟧ components_env D ups (List.rev Pre) zs ↘ t /\ ⟦ T ⟧ components_env D ups' (List.rev Pre) zs' ↘ t' /\
          Dom t ≈ t' ∈ per_relevant_nonlevel (per_univ (univ_idx a)).
  Proof.
    intros * HC HT * Hz Hz' Hu Hu' Hg a Ha.
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (components_env D ups (List.rev Pre) zs) (components_env D ups' (List.rev Pre) zs')).
    { rewrite <- !env_tele_uparams by assumption.
      apply (gargs_env_rel _ _ _ _ _ _ HR HC); [ unfold ind_nu in *; rewrite !List.length_app; lia | exact Hg ]. }
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    assert (HRee : R (components_env D ups (List.rev Pre) zs) (components_env D ups (List.rev Pre) zs))
      by (etransitivity; [ exact HRe | symmetry; exact HRe ]).
    destruct (rel_exp_under_ctx_simple_full_at HR HT) as [i0 Hsimp].
    destruct (Hsimp _ _ HRe) as (b & b' & R0 & Eb & Eb' & HR0 & Htt).
    (** The type is of a universe, so the terms are related. *)
    destruct Htt as [Hp | (t & t' & Et & Et' & Htt)];
      [ destruct (sort_wk_univ _ _ _ Eb) as [[? ->] | [? ->]]; discriminate |].
    destruct (per_univ_elem_univ _ _ _ _ HR0 (sort_wk_univ _ _ _ Eb)) as [_ ER0].
    (** The sort shifted past [Pre] is the sort at the uniform parameters. *)
    destruct (valid_ind_decl_sort _ HD) as [i HS].
    destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HC) HS) as (RΓ & HΓ & j & Hwk).
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hwk _ _ (proj1 (E _ _) HRee)) as (x & x' & Rx & Ex & Ex' & HRx & Hmm).
    destruct Hmm as [Hp | (m & m' & Em & Em' & Hmm)]; [ cbn in Ex; inversion Ex; subst; discriminate |].
    rewrite <- Hz, eval_wk_shiftn_components_env in Em'.
    assert (m' = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (m = b) as -> by (eapply functional_eval_exp; eassumption).
    cbn in Ex; inversion Ex; subst.
    basic_invert_per_univ_elem HRx.
    match goal with Hm : ?r b a, H : ?r <~> _ |- _ => apply H in Hm; destruct Hm as [[Rm HRm] _ _] end.
    destruct (per_univ_elem_univ _ _ _ _ HRm (sort_wk_univ _ _ _ Eb)) as [Hidx _].
    exists t, t'; split; [ exact Et | split; [ exact Et' |] ].
    rewrite Hidx; apply ER0; exact Htt.
  Qed.

  (** So the values are related types of the universe. *)
  Corollary sort_typ_rel : forall Pre T, ⊨ Pre ++ ind_uparams D ->
      Pre ++ ind_uparams D ⊨ T : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      forall ups ups' zs zs', List.length zs = List.length Pre -> List.length zs' = List.length Pre ->
        List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
        per_gargs (List.rev (Pre ++ ind_uparams D)) nil nil (ups ++ zs) (ups' ++ zs') ->
        forall a, ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        exists t t', ⟦ T ⟧ components_env D ups (List.rev Pre) zs ↘ t /\ ⟦ T ⟧ components_env D ups' (List.rev Pre) zs' ↘ t' /\
          Dom t ≈ t' ∈ per_univ (univ_idx a).
  Proof.
    intros * HC HT * Hz Hz' Hu Hu' Hg a Ha.
    destruct (sort_typ_rel_relevant _ _ HC HT _ _ _ _ Hz Hz' Hu Hu' Hg a Ha) as (t & t' & Et & Et' & Htt).
    exists t, t'; split; [ exact Et | split; [ exact Et' | exact (per_relevant_nonlevel_rel _ _ _ Htt) ] ].
  Qed.

  (** The same at either sort: a proposition evaluates to related
      propositions, related at every universe. *)
  Lemma sort_rel_typ_rel : forall r Pre T, ⊨ Pre ++ ind_uparams D ->
      Pre ++ ind_uparams D ⊨ T : relevance_sort r (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      forall ups ups' zs zs', List.length zs = List.length Pre -> List.length zs' = List.length Pre ->
        List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
        per_gargs (List.rev (Pre ++ ind_uparams D)) nil nil (ups ++ zs) (ups' ++ zs') ->
        forall a, ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        exists t t', ⟦ T ⟧ components_env D ups (List.rev Pre) zs ↘ t /\ ⟦ T ⟧ components_env D ups' (List.rev Pre) zs' ↘ t' /\
          Dom t ≈ t' ∈ per_univ (univ_idx a).
  Proof.
    intros [] * HC HT * Hz Hz' Hu Hu' Hg a Ha; [ exact (sort_typ_rel _ _ HC HT _ _ _ _ Hz Hz' Hu Hu' Hg a Ha) |].
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (components_env D ups (List.rev Pre) zs) (components_env D ups' (List.rev Pre) zs')).
    { rewrite <- !env_tele_uparams by assumption.
      apply (gargs_env_rel _ _ _ _ _ _ HR HC); [ unfold ind_nu in *; rewrite !List.length_app; lia | exact Hg ]. }
    destruct (rel_exp_of_prop_inversion_simple_at HR HT _ _ HRe) as (t & t' & Et & Et' & Hp).
    exists t, t'; split; [ exact Et | split; [ exact Et' |] ].
    exists per_proof; apply per_univ_elem_of_prop; exact Hp.
  Qed.

  (** Arguments related at a telescope of types at the sort or
      propositions, by the canonical relations, are arguments related at
      it. *)
  Lemma tele_canon_gargs : forall (ts : list centry) (Pre0 : ctx) (tr : nat -> list domain -> relation domain)
      ups ups' zs zs' a,
      tele_ass ts ->
      List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      List.length zs = List.length Pre0 -> List.length zs' = List.length Pre0 ->
      per_gargs (List.rev (Pre0 ++ ind_uparams D)) nil nil (ups ++ zs) (ups' ++ zs') ->
      ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
      (forall j A, List.nth_error ts j = Some (ce_ass A) ->
         ⊨ List.rev (List.firstn j ts) ++ Pre0 ++ ind_uparams D /\
         exists r, List.rev (List.firstn j ts) ++ Pre0 ++ ind_uparams D
           ⊨ A : relevance_sort r (ind_sort D)[wk_shiftn (j + List.length Pre0)]ʷ) ->
      (forall j A pre, List.nth_error ts j = Some (ce_ass A) -> List.length pre = j ->
         (tr j pre <~> per_head A A (components_env D ups (List.rev Pre0 ++ ts) (zs ++ pre))
                                   (components_env D ups (List.rev Pre0 ++ ts) (zs ++ pre)))) ->
      forall k vs vs', k <= List.length ts -> tele_prefix_rel tr k vs vs' ->
        per_gargs (List.firstn k ts) (components_env D ups (List.rev Pre0) zs) (components_env D ups' (List.rev Pre0) zs') vs vs'.
  Proof.
    intros * Hts Hu Hu' Hz Hz' Hg Ha Hv Htr k.
    induction k as [| k IH]; intros vs vs' Hk Hp.
    - rewrite tele_prefix_rel_iff in Hp; destruct Hp as (Hl & Hl' & _).
      destruct vs, vs'; cbn in *; try discriminate; constructor.
    - pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hl & Hl' & Hr).
      destruct (nth_error_lt_some' ts k ltac:(lia)) as [e He].
      assert (HA : exists A, e = ce_ass A)
        by (unfold tele_ass in Hts; rewrite List.Forall_forall in Hts; apply Hts; eapply List.nth_error_In; exact He).
      destruct HA as [A ->].
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [v Hv0].
      destruct (nth_error_lt_some' vs' k ltac:(lia)) as [v' Hv0'].
      rewrite (firstn_S_snoc _ _ _ He).
      assert (Hvs : vs = List.firstn k vs ++ v :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0), List.firstn_all2 by lia; reflexivity).
      assert (Hvs' : vs' = List.firstn k vs' ++ v' :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0'), List.firstn_all2 by lia; reflexivity).
      pose proof (IH _ _ ltac:(lia) (tele_prefix_rel_of_pre _ _ _ _ k Hp ltac:(lia))) as IHk.
      rewrite Hvs, Hvs'.
      destruct (Hv _ _ He) as [HC [r HT]].
      assert (Hlf : List.length (List.firstn k ts) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv : List.length (List.firstn k vs) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv' : List.length (List.firstn k vs') = k) by (rewrite List.length_firstn; lia).
      assert (Hg' : per_gargs (List.rev (List.rev (List.firstn k ts) ++ Pre0 ++ ind_uparams D)) nil nil
                      (ups ++ zs ++ List.firstn k vs) (ups' ++ zs' ++ List.firstn k vs')).
      { rewrite List.rev_app_distr, List.rev_involutive, !List.app_assoc.
        apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, List.length_app; unfold ind_nu in *; lia | exact Hg |].
        rewrite !env_tele_uparams by assumption; exact IHk. }
      set (Pre := List.rev (List.firstn k ts) ++ Pre0).
      assert (HC' : ⊨ Pre ++ ind_uparams D) by (unfold Pre; rewrite <- List.app_assoc; exact HC).
      assert (HT' : Pre ++ ind_uparams D ⊨ A : relevance_sort r (ind_sort D)[wk_shiftn (List.length Pre)]ʷ)
        by (unfold Pre; rewrite <- List.app_assoc, List.length_app, List.length_rev, Hlf; exact HT).
      assert (Hg'' : per_gargs (List.rev (Pre ++ ind_uparams D)) nil nil
                       (ups ++ (zs ++ List.firstn k vs)) (ups' ++ (zs' ++ List.firstn k vs')))
        by (unfold Pre; rewrite <- List.app_assoc; exact Hg').
      destruct (sort_rel_typ_rel r Pre A HC' HT' ups ups' (zs ++ List.firstn k vs) (zs' ++ List.firstn k vs')
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  Hu Hu' Hg'' a Ha)
        as (t & t' & Et & Et' & [R0 HR0]).
      destruct (per_univ_elem_to_nat _ _ _ _ HR0) as [n Hn].
      unfold Pre in Et, Et'; rewrite List.rev_app_distr, List.rev_involutive in Et, Et'.
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R0); [ lia | exact IHk | |].
      + unfold components_env in Et, Et' |- *.
        rewrite env_tele_app in Et, Et' by (rewrite List.length_rev; lia).
        exact (mk_rel_mod_eval t t' Et Et' Hn).
      + pose proof (Hr _ _ _ Hv0 Hv0') as Hrv.
        apply (Htr _ _ _ He Hlv) in Hrv.
        assert (HRtt : DF t ≈ t ∈ per_univ_elem n ↘ R0)
          by (eapply per_univ_trans; [ exact Hn | apply per_univ_sym; exact Hn ]).
        rewrite <- (List.firstn_skipn k ts), List.app_assoc, components_env_prefix in Hrv
          by (rewrite !List.length_app, List.length_rev, List.length_firstn; lia).
        exact (Hrv _ _ _ _ Et Et HRtt).
  Qed.

  Lemma uparams_sem : ⊨ ind_uparams D.
  Proof. exact (valid_ind_decl_uparams _ HD). Qed.

  Lemma rev_uparams_sem : ⊨ List.rev (List.rev (ind_uparams D)) ++ ⋅.
  Proof. rewrite List.rev_involutive, List.app_nil_r; exact uparams_sem. Qed.

  Lemma uparams_refl_l : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof.
    intros * Hg; eapply (per_gargs_refl_l _ _ _ per_ctx_env_nil_true rev_uparams_sem); [ exact rev_uparams_ass | exact I | exact Hg ].
  Qed.

  Lemma length_ups_gargs : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D -> List.length ups' = ind_nu D.
  Proof. intros * Hg Hu; destruct (per_gargs_length _ _ _ _ _ Hg) as [Hl _]; lia. Qed.

  (** A member's parameters are parameter types ([rel_param_typed]): the
      uniform ones, types of universes or of levels, by the group's
      validity, the others types of universes at its sort. *)
  Lemma im_params_relevant : forall k Mk, ind_member D k = Some Mk ->
      forall Δ1 T Δ2, im_params D Mk = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, rel_param_typed Δ2 T i.
  Proof.
    intros k Mk HM * E; unfold im_params in E.
    destruct (valid_ind_decl_uparams_relevant _ HD) as [l Hl].
    destruct (List.app_eq_app _ _ _ _ E) as (Δc & [[E1 E2] | [E1 E2]]).
    - destruct Δc as [| e Δc]; cbn [List.app] in E2.
      + exists l; pose proof (Hl nil T Δ2 (eq_sym E2)) as H; rewrite List.app_nil_r in H; exact H.
      + injection E2 as He E2'; subst e Δ2.
        assert (Hn : List.nth_error (List.rev (im_nparams Mk)) (List.length Δc) = Some (ce_ass T)).
        { rewrite E1, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc.
          rewrite List.nth_error_app2 by (rewrite List.length_rev; lia).
          rewrite List.length_rev, Nat.sub_diag; reflexivity. }
        destruct (valid_ind_decl_nparams _ HD _ _ _ _ HM Hn) as (_ & i & Hi).
        assert (Hp : nparams_prefix Mk (List.length Δc) = Δc).
        { unfold nparams_prefix; rewrite E1, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc.
          rewrite List.firstn_app, List.length_rev, Nat.sub_diag, List.firstn_all2 by (rewrite List.length_rev; lia).
          cbn [List.firstn]; rewrite List.app_nil_r, List.rev_involutive; reflexivity. }
        rewrite Hp in Hi; exists i; left; exact Hi.
    - exists l; pose proof (Hl Δc T Δ2 E2) as H; rewrite List.app_nil_r in H; exact H.
  Qed.

  (** Its non-uniform parameters are types of universes, at its sort,
      over the uniform ones. *)
  Lemma im_nparams_typed : forall k Mk, ind_member D k = Some Mk ->
      forall X1 A X2, im_nparams Mk = X1 ++ ce_ass A :: X2 -> exists i : nat, X2 ++ ind_uparams D ⊨ A : Typeω@i.
  Proof.
    intros k Mk HM * E1.
    assert (Hn : List.nth_error (List.rev (im_nparams Mk)) (List.length X2) = Some (ce_ass A)).
    { rewrite E1, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc.
      rewrite List.nth_error_app2 by (rewrite List.length_rev; lia).
      rewrite List.length_rev, Nat.sub_diag; reflexivity. }
    destruct (valid_ind_decl_nparams _ HD _ _ _ _ HM Hn) as (_ & i & Hi).
    assert (Hp : nparams_prefix Mk (List.length X2) = X2).
    { unfold nparams_prefix; rewrite E1, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc.
      rewrite List.firstn_app, List.length_rev, Nat.sub_diag, List.firstn_all2 by (rewrite List.length_rev; lia).
      cbn [List.firstn]; rewrite List.app_nil_r, List.rev_involutive; reflexivity. }
    rewrite Hp in Hi; exists i; exact Hi.
  Qed.

  (** So are those of a prefix of its non-uniform parameters, over the
      uniform ones. *)
  Corollary nparams_prefix_relevant : forall k Mk m, ind_member D k = Some Mk ->
      forall Δ1 T Δ2, nparams_prefix Mk m = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ ind_uparams D) T i.
  Proof.
    intros * HM * E.
    destruct (nparams_prefix_suffix D Mk m) as [Δ HΔ].
    apply (im_params_relevant _ _ HM (Δ ++ Δ1)); rewrite HΔ, E, <- !List.app_assoc; reflexivity.
  Qed.

  (** ** The Telescopes of a Member *)
  Section Member.
    Variables (k : nat) (Mk : imember).
    Hypothesis (HM : ind_member D k = Some Mk).

    Lemma member_nparams_ass : tele_ass (im_nparams Mk).
    Proof. exact (member_closed_ass _ _ (decl_closed_members _ Hc _ _ HM)). Qed.

    Lemma member_params_ass : tele_ass (im_params D Mk).
    Proof. exact (decl_closed_params_ass _ _ _ Hc HM). Qed.

    Lemma rev_params_ass : tele_ass (List.rev (im_params D Mk)).
    Proof. apply List.Forall_rev, member_params_ass. Qed.

    Lemma rev_params_sem : ⊨ List.rev (List.rev (im_params D Mk)) ++ ⋅.
    Proof. rewrite List.rev_involutive, List.app_nil_r; exact (valid_ind_decl_params _ HD _ _ HM). Qed.

    Lemma nparams_prefix_sem : forall j, ⊨ nparams_prefix Mk j ++ ind_uparams D.
    Proof.
      intros; destruct (nparams_prefix_suffix D Mk j) as [Δ HΔ]; pose proof (valid_ind_decl_params _ HD _ _ HM) as H; rewrite HΔ in H.
      exact (rel_ctx_wf_app_r _ _ H).
    Qed.

    Lemma length_rec_ps : forall c gs gs1 t gs2, ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj.
    Proof. intros * Hcon Heq; exact (valid_ind_decl_params_length _ HD _ _ _ _ HM Hcon _ _ _ Heq). Qed.

    (** The non-recursive arguments before a recursive one, after the
        member's non-uniform parameters, reversed: their telescope after
        that of the parameters. *)
    Lemma nonrec_prefix_rev : forall gs gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mk)
        = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1.
    Proof.
      intros * ->; unfold nonrec_args_prefix, cargs_nonrec_tele.
      rewrite List.rev_app_distr, List.rev_involutive; f_equal.
      rewrite cargs_nonrec_app, List.map_app, List.firstn_app, List.length_map, Nat.sub_diag.
      rewrite <- (List.length_map ce_ass (cargs_nonrec gs1)) at 1; rewrite List.firstn_all; cbn.
      apply List.app_nil_r.
    Qed.

    (** The context of a recursive argument's shape, its domains after the
        non-recursive arguments before it and the member's non-uniform
        parameters, reversed: the telescope of its components. *)
    Lemma rec_ctx_rev : forall gs gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        List.rev (ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mk)
        = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t.
    Proof.
      intros * ->; unfold ptyp_tele, doms_ctx, nonrec_args_prefix, cargs_nonrec_tele, shape_doms_tele.
      rewrite !List.rev_app_distr, !List.rev_involutive, <- List.app_assoc; f_equal; f_equal.
      rewrite cargs_nonrec_app, List.map_app, List.firstn_app, List.length_map, Nat.sub_diag.
      rewrite <- (List.length_map ce_ass (cargs_nonrec gs1)) at 1; rewrite List.firstn_all; cbn.
      apply List.app_nil_r.
    Qed.

    (** The parameters of a recursive argument, at related arguments before
        it, are related at the non-uniform parameters of the member its
        shape ends in. *)
    Lemma rec_closure : forall c gs gs1 t gs2 Mj, ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        ind_member D (ptyp_mem t) = Some Mj ->
        forall ups ups' ms ms' ws ws' ys ys',
          List.length ups = ind_nu D -> List.length ms = im_nn Mk -> List.length ws = List.length (cargs_nonrec gs1) ->
          List.length ys = ptyp_depth t ->
          List.length ups' = ind_nu D -> List.length ms' = im_nn Mk -> List.length ws' = List.length (cargs_nonrec gs1) ->
          List.length ys' = ptyp_depth t ->
          per_gargs (List.rev (ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)) nil nil
            (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys') ->
          let Ts := List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t in
          exists bs bs', ⟦ (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts (ms ++ ws ++ ys) ↘ bs /\
            ⟦ (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups' Ts (ms' ++ ws' ++ ys') ↘ bs' /\
            per_gargs (List.rev (im_nparams Mj)) (decl_env D ups) (decl_env D ups') bs bs' /\
            (forall m P T, List.nth_error (ptyp_ps t) m = Some P ->
               List.nth_error (tele_insts (im_nparams Mj)
                                 (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk))) (ptyp_ps t)) m
                 = Some T ->
               (per_head T T (components_env D ups Ts (ms ++ ws ++ ys)) (components_env D ups' Ts (ms' ++ ws' ++ ys'))
                  <~> canon_nparams_rel D ups (ptyp_mem t) m (List.firstn m bs)) /\
               (** a non-uniform parameter is relevant *)
               rel_typ_sort T (components_env D ups Ts (ms ++ ws ++ ys)) relevant).
    Proof.
      intros * Hcon Heq HMj * Hu Hm Hw Hy Hu' Hm' Hw' Hy' Hg Ts.
      rename t into Ps.
      set (K := List.length (cargs_nonrec gs1)) in *.
      set (L := ptyp_depth Ps + K + im_nn Mk).
      set (Ξ0 := ptyp_tele Ps ++ nonrec_args_prefix gs K ++ im_params D Mk).
      set (E := components_env D ups Ts (ms ++ ws ++ ys)); set (E' := components_env D ups' Ts (ms' ++ ws' ++ ys')).
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (HΞ0 : ⊨ Ξ0).
      { pose proof (valid_ind_decl_dctx _ HD _ _ _ _ _ _ _ (List.length (ptyp_doms Ps)) HM Hcon Heq (le_n _)) as H.
        rewrite List.firstn_all in H; exact H. }
      destruct (rel_ctx_wf_per_ctx_env HΞ0) as [R0 HR0].
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      assert (HEE : R0 E E').
      { assert (HΞe : Ξ0 = (ptyp_tele Ps ++ nonrec_args_prefix gs K ++ im_nparams Mk) ++ ind_uparams D)
          by (unfold Ξ0, im_params; rewrite <- !List.app_assoc; reflexivity).
        unfold E, E', Ts; rewrite <- (rec_ctx_rev _ _ _ _ Heq), <- !env_tele_uparams by assumption.
        fold K; rewrite <- HΞe.
        apply (gargs_env_rel Ξ0 R0 (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys') nil nil); [ exact HR0 | exact HΞ0 | | exact Hg ].
        unfold Ξ0, ptyp_tele; rewrite !List.length_app, length_nonrec_args_prefix, doms_ctx_length by exact HK.
        rewrite length_im_params; unfold ptyp_depth, im_np in *; lia. }
      destruct (length_rec_ps _ _ _ _ _ Hcon Heq) as (Mj' & HMj' & HPl).
      rewrite HMj in HMj'; injection HMj' as <-.
      assert (HwkE : ⟪wk_shiftn L⟫ E = decl_env D ups).
      { unfold E, L; replace (ptyp_depth Ps + K + im_nn Mk) with (List.length (ms ++ ws ++ ys))
          by (rewrite !List.length_app; lia); apply eval_wk_shiftn_components_env. }
      assert (HwkE' : ⟪wk_shiftn L⟫ E' = decl_env D ups').
      { unfold E', L; replace (ptyp_depth Ps + K + im_nn Mk) with (List.length (ms' ++ ws' ++ ys'))
          by (rewrite !List.length_app; lia); apply eval_wk_shiftn_components_env. }
      (** The substitution of the uniform parameters: a shift past the
          arguments and the non-uniform parameters. *)
      assert (Hwk : Ξ0 ⊨ˢ sb_of_wk (wk_shiftn L) ≈ sb_of_wk (wk_shiftn L) : ind_uparams D).
      { apply rel_sub_of_wk.
        assert (HL : L = List.length (ptyp_tele Ps ++ nonrec_args_prefix gs K ++ im_nparams Mk))
          by (unfold L, ptyp_tele, ptyp_depth; rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams, doms_ctx_length
                by exact HK; lia).
        assert (HΞe : Ξ0 = (ptyp_tele Ps ++ nonrec_args_prefix gs K ++ im_nparams Mk) ++ ind_uparams D)
          by (unfold Ξ0, im_params; rewrite <- !List.app_assoc; reflexivity).
        rewrite HΞe, HL; apply rel_wk_under_ctx_shiftn; rewrite <- HΞe; exact HΞ0. }
      (** The uniform parameters are related at their telescope, and every
          context of the outer non-uniform parameters of [Mj] is valid. *)
      assert (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups').
      { pose proof Hg as Hg0; unfold im_params in Hg0.
        rewrite !List.rev_app_distr, <- !List.app_assoc in Hg0.
        assert (Hl1 : List.length ups = List.length (List.rev (ind_uparams D))) by (rewrite List.length_rev; exact Hu).
        assert (Hl1' : List.length ups' = List.length (List.rev (ind_uparams D))) by (rewrite List.length_rev; exact Hu').
        exact (proj1 (per_gargs_app (List.rev (ind_uparams D)) _ _ _ ups ups' _ _ Hl1 Hg0 Hl1')). }
      assert (HWm : forall m, ⊨ nparams_prefix Mj m ++ ind_uparams D).
      { intros m0; pose proof (valid_ind_decl_params _ HD _ _ HMj) as HP; unfold im_params in HP.
        rewrite <- (List.rev_involutive (im_nparams Mj)), <- (List.firstn_skipn m0 (List.rev (im_nparams Mj))),
          List.rev_app_distr, <- List.app_assoc in HP.
        exact (rel_ctx_wf_app_r _ _ HP). }
      (** The induction over the parameters of the recursive argument. *)
      assert (Hall : forall m, m <= im_nn Mj ->
                 Ξ0 ⊨ˢ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps Ps))
                   ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps Ps)) : nparams_prefix Mj m ++ ind_uparams D /\
                 exists bs bs', ⟦ List.firstn m (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ bs /\
                   ⟦ List.firstn m (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ E' ↘ bs' /\
                   per_gargs (List.firstn m (List.rev (im_nparams Mj))) (decl_env D ups) (decl_env D ups') bs bs' /\
                   (forall m' P T, m' < m -> List.nth_error (ptyp_ps Ps) m' = Some P ->
                      List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) (ptyp_ps Ps)) m' = Some T ->
                      (per_head T T E E' <~> canon_nparams_rel D ups (ptyp_mem Ps) m' (List.firstn m' bs)) /\
                      rel_typ_sort T E relevant)).
      { induction m as [| m IH]; intros Hmn.
        - cbn [List.firstn sb_of_list]; unfold nparams_prefix; cbn [List.firstn List.rev List.app].
          split; [ exact Hwk |]; exists nil, nil; split; [ constructor | split; [ constructor | split; [ constructor | intros; lia ] ] ].
        - destruct (IH ltac:(lia)) as (Hτ & bs & bs' & Ebs & Ebs' & Hgb & Hil).
          destruct (nth_error_lt_some' (ptyp_ps Ps) m ltac:(lia)) as [P HP].
          assert (HT : exists T, List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) (ptyp_ps Ps)) m = Some T).
          { apply nth_error_lt_some'.
            rewrite length_tele_insts by exact (member_closed_ass _ _ (decl_closed_members _ Hc _ _ HMj)).
            rewrite length_im_nparams; lia. }
          destruct HT as [T HT].
          destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
          pose proof (valid_ind_decl_rec_field _ HD _ _ _ _ _ _ _ _ _ _ _ HM Hcon Heq HMj HP HT) as HPv.
          destruct (valid_ind_decl_nparams _ HD _ _ _ _ HMj HA) as (_ & j & HAv).
          set (τ := sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps Ps))) in *.
          (** The new entry, and the substitution extended by it. *)
          assert (Hτ' : Ξ0 ⊨ˢ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) (ptyp_ps Ps))
                          ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) (ptyp_ps Ps)) : nparams_prefix Mj (S m) ++ ind_uparams D).
          { rewrite (firstn_S_snoc _ _ _ HP), sb_of_list_app, (nparams_prefix_S _ _ _ HA); cbn [sb_of_list List.app].
            (** The parameter is scoped by the context of the shape. *)
            assert (HPs : exp_scoped (List.length Ξ0) P).
            { pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ HM) _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as Ht.
              pose proof (ptyp_scoped_ps _ _ Ht) as HF; rewrite List.Forall_forall in HF.
              specialize (HF P (List.nth_error_In _ _ HP)).
              rewrite cargs_strat_nonrec, List.length_rev, List.length_map in HF.
              unfold Ξ0, ptyp_tele; rewrite !List.length_app, doms_ctx_length, length_nonrec_args_prefix, length_im_params by exact HK.
              unfold ptyp_depth in HF; fold K in HF; exact HF. }
            eapply rel_sub_under_ctx_extend; [ exact Hτ | exact (rel_type_of_typ HAv) | exact HPv | exact HPs | exact HPs ]. }
          split; [ exact Hτ' |].
          (** The values of the new parameter, and its type's: the type is
              of a universe, so they are related. *)
          destruct (rel_exp_under_ctx_simple_at HR0 HPv _ _ HEE) as [Hp | (b & b' & Eb & Eb' & Hbb)];
            [ exfalso; exact (not_rel_typ_propositional_of_typ_sub HR0 Hτ HAv _ _ HEE Hp) |].
          (** The values of [τ]: the arguments before, related at their
              telescope, hold the proof at its propositions. *)
          assert (Hlbs0 : List.length bs = m) by (rewrite (eval_exps_length _ _ _ Ebs), List.length_firstn; lia).
          assert (Hlbs0' : List.length bs' = m) by (rewrite (eval_exps_length _ _ _ Ebs'), List.length_firstn; lia).
          assert (Hgm : forall vs vs', List.length vs = ind_nu D ->
                     per_gargs (List.rev (ind_uparams D)) nil nil vs vs' ->
                     per_gargs (List.firstn m (List.rev (im_nparams Mj))) (decl_env D vs) (decl_env D vs') bs bs' ->
                     per_gargs (List.rev (nparams_prefix Mj m ++ ind_uparams D)) nil nil (vs ++ bs) (vs' ++ bs')).
          { intros vs vs' Hv Hgv Hgbs; unfold nparams_prefix; rewrite List.rev_app_distr, List.rev_involutive.
            apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hv | exact Hgv | exact Hgbs ]. }
          assert (Hlm : List.length (ups ++ bs) = List.length (nparams_prefix Mj m ++ ind_uparams D))
            by (unfold nparams_prefix; rewrite !List.length_app, List.length_rev, List.length_firstn, List.length_rev,
                  length_im_nparams; unfold ind_nu in Hu; lia).
          (** The values of [τ]: the parameters' environment extended by the
              arguments, none of the entries a proposition there. *)
          assert (Hlτ : List.length (List.firstn m (List.rev (im_nparams Mj))) = List.length (List.firstn m (ptyp_ps Ps)))
            by (rewrite !List.length_firstn, List.length_rev, length_im_nparams; lia).
          assert (Hpa : tele_ass (nparams_prefix Mj m))
            by (unfold nparams_prefix; apply List.Forall_rev, Forall_firstn', List.Forall_rev; exact (member_closed_ass _ _ (decl_closed_members _ Hc _ _ HMj))).
          destruct (rel_ctx_wf_per_ctx_env (HWm m)) as [Rm HRm].
          assert (HPm : PER Rm) by (eapply per_env_PER; exact HRm).
          assert (Hτev_at : forall vs E0 cs, List.length vs = ind_nu D -> ⟪wk_shiftn L⟫ E0 = decl_env D vs ->
                     ⟦ List.firstn m (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ E0 ↘ cs ->
                     Rm (components_env D vs (List.firstn m (List.rev (im_nparams Mj))) cs)
                        (components_env D vs (List.firstn m (List.rev (im_nparams Mj))) cs) ->
                     ⟦ τ : nparams_prefix Mj m ++ ind_uparams D ⟧s E0 ↘ components_env D vs (List.firstn m (List.rev (im_nparams Mj))) cs).
          { intros vs E0 cs Hv Hwk0 Ecs Hcs.
            assert (Hlcs : List.length cs = List.length (List.firstn m (List.rev (im_nparams Mj))))
              by (rewrite (eval_exps_length _ _ _ Ecs); symmetry; exact Hlτ).
            assert (HX : env_extend_tagged (ind_uparams D) (List.firstn m (List.rev (im_nparams Mj)))
                           (ctx_retag (ind_uparams D) (⟪wk_shiftn L⟫ E0)) cs
                         = components_env D vs (List.firstn m (List.rev (im_nparams Mj))) cs).
            { rewrite Hwk0, ctx_retag_decl_env by exact Hv.
              apply env_extend_tagged_exact; [ rewrite length_decl_env; exact Hv | exact Hlcs ]. }
            rewrite <- HX; unfold τ, nparams_prefix.
            apply eval_sb_of_list; [ apply eval_sub_of_wk; typeclasses eauto | exact Ecs | exact Hlτ |].
            rewrite HX; intros x Hx Hpx.
            apply (relevant_entries_not_propositional (nparams_prefix Mj m) (ind_uparams D) Rm Hpa
                     (nparams_prefix_relevant _ _ m HMj) HRm _ _ Hcs x); [ | exact Hpx ].
            unfold nparams_prefix; rewrite List.length_rev; exact Hx. }
          assert (Hgm' := Hgm _ _ Hu Hgu Hgb).
          pose proof (gargs_env_rel _ _ _ _ _ _ HRm (HWm m) Hlm Hgm') as Hbb'.
          rewrite !env_tele_uparams in Hbb' by assumption.
          unfold nparams_prefix in Hbb'; rewrite List.rev_involutive in Hbb'.
          assert (Hτev : ⟦ τ : nparams_prefix Mj m ++ ind_uparams D ⟧s E ↘ components_env D ups (List.firstn m (List.rev (im_nparams Mj))) bs)
            by (apply Hτev_at; [ exact Hu | exact HwkE | exact Ebs | etransitivity; [ exact Hbb' | symmetry; exact Hbb' ] ]).
          assert (Hτev' : ⟦ τ : nparams_prefix Mj m ++ ind_uparams D ⟧s E' ↘ components_env D ups' (List.firstn m (List.rev (im_nparams Mj))) bs')
            by (apply Hτev_at; [ exact Hu' | exact HwkE' | exact Ebs' | etransitivity; [ symmetry; exact Hbb' | exact Hbb' ] ]).
          destruct (rel_type_inversion (rel_type_of_typ HAv)) as (RA & HRA & HAgen).
          destruct (HAgen _ _ HR0 _ _ Hτ _ _ _ _ HEE Hτev Hτev') as [t1 t2 t3 t4 Et1 Et2 Et3 Et4 Hch].
          destruct Hch as ([R12 HR12] & [R23 HR23] & [R34 HR34]).
          destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR12 HR23) as (R13 & HR13 & E13).
          destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR13 HR34) as (R14 & HR14 & E14).
          pose proof (Hbb _ _ _ _ Et1 Et4 HR14) as Hb14.
          assert (E23 : R23 <~> R14)
            by (etransitivity; [ symmetry; eapply per_univ_elem_left_irrel; [ exact HR13 | exact HR23 ]
                               | eapply per_univ_elem_right_irrel; [ exact HR13 | exact HR14 ] ]).
          assert (Hlbs : List.length bs = m) by (rewrite (eval_exps_length _ _ _ Ebs), List.length_firstn; lia).
          exists (bs ++ b :: nil), (bs' ++ b' :: nil); split; [| split; [| split ] ].
          + rewrite (firstn_S_snoc _ _ _ HP); apply eval_exps_app; [ exact Ebs | econstructor; [ exact Eb | constructor ] ].
          + rewrite (firstn_S_snoc _ _ _ HP); apply eval_exps_app; [ exact Ebs' | econstructor; [ exact Eb' | constructor ] ].
          + rewrite (firstn_S_snoc _ _ _ HA).
            destruct (per_univ_elem_to_nat _ _ _ _ HR23) as [n Hn].
            apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R23);
              [ rewrite List.length_firstn, List.length_rev, length_im_nparams, (eval_exps_length _ _ _ Ebs), List.length_firstn; lia
              | exact Hgb | exact (mk_rel_mod_eval t2 t3 Et2 Et3 Hn) | apply E23, Hb14 ].
          + intros m' P' T' Hmm' HP' HT'.
            destruct (Nat.lt_ge_cases m' m) as [Hlt | Hge].
            * rewrite List.firstn_app, Hlbs, (proj2 (Nat.sub_0_le m' m)) by lia; cbn; rewrite List.app_nil_r.
              exact (Hil _ _ _ Hlt HP' HT').
            * assert (m' = m) as -> by lia.
              rewrite HT in HT'; injection HT' as <-.
              split; [| exact (rel_exp_of_typ_sub_relevant HR0 Hτ HAv _ _ HEE) ].
              rewrite List.firstn_app, Hlbs, Nat.sub_diag, List.firstn_all2 by lia; cbn; rewrite List.app_nil_r.
              unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HMj HA).
              assert (HR22 : DF t2 ≈ t2 ∈ per_univ_elem j ↘ R23)
                by (eapply per_univ_trans; [ exact HR23 | apply per_univ_sym; exact HR23 ]).
              pose proof (per_head_iff Et1 Et4 HR14) as Q1.
              pose proof (per_head_iff Et2 Et2 HR22) as Q2.
              rewrite (member_nparams_eq _ _ _ HMj), (components_env_firstn D ups (List.rev (im_nparams Mj)) bs), Hlbs
                by (rewrite Hlbs, List.length_rev, length_im_nparams; lia).
              intros x y; rewrite <- (Q1 x y), <- (Q2 x y), <- (E23 x y); reflexivity. }
      destruct (Hall (im_nn Mj) (le_n _)) as (_ & bs & bs' & Ebs & Ebs' & Hgb & Hil).
      rewrite List.firstn_all2 in Ebs, Ebs' by lia.
      rewrite List.firstn_all2 in Hgb by (rewrite List.length_rev, length_im_nparams; lia).
      exists bs, bs'; split; [ exact Ebs | split; [ exact Ebs' | split; [ exact Hgb |] ] ].
      intros m P T HP HT.
      assert (Hm0 : m < im_nn Mj) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
      exact (Hil _ _ _ Hm0 HP HT).
    Qed.

    (** The canonical relations of the non-uniform parameters are those of
        the telescope. *)
    Lemma nr_gargs : forall ups ups' a, per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        forall j vs vs', j <= im_nn Mk -> tele_prefix_rel (canon_nparams_rel D ups k) j vs vs' ->
          per_gargs (List.firstn j (List.rev (im_nparams Mk))) (decl_env D ups) (decl_env D ups') vs vs'.
    Proof.
      intros * Hg Hu Ha * Hj Hp.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof (tele_canon_gargs (List.rev (im_nparams Mk)) nil (canon_nparams_rel D ups k) ups ups' nil nil a
                    ltac:(apply List.Forall_rev, member_nparams_ass) Hu Hu' eq_refl eq_refl
                    ltac:(rewrite !List.app_nil_r; exact Hg) Ha) as Hcan.
      cbn [List.rev List.app List.length] in Hcan.
      assert (Hce : forall u, components_env D u nil nil = decl_env D u) by reflexivity.
      rewrite !Hce in Hcan; apply Hcan; [ | | rewrite List.length_rev, length_im_nparams; exact Hj | exact Hp ].
      - intros j0 A HA; rewrite Nat.add_0_r.
        split; [ exact (nparams_prefix_sem j0) | exists relevant; exact (proj1 (valid_ind_decl_nparams _ HD _ _ _ _ HM HA)) ].
      - intros j0 A pre HA _; unfold canon_nparams_rel.
        rewrite (nth_ctyp_eq _ _ _ _ _ HM HA), (member_nparams_eq _ _ _ HM); reflexivity.
    Qed.

    Lemma params_gargs : forall ups ups' a ms ms', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        per_gargs (List.rev (im_params D Mk)) nil nil (ups ++ ms) (ups' ++ ms').
    Proof.
      intros * Hg Hu Ha Hm.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      rewrite rev_im_params; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg |].
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
      rewrite <- (List.firstn_all2 (n := im_nn Mk) (List.rev (im_nparams Mk))) by (rewrite List.length_rev, length_im_nparams; lia).
      eapply nr_gargs; [ exact Hg | exact Hu | exact Ha | lia |].
      rewrite <- (List.firstn_all2 (n := im_nn Mk) ms), <- (List.firstn_all2 (n := im_nn Mk) ms')
        by (rewrite List.length_rev, length_im_nparams in *; lia).
      apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk)); [ exact Hm | rewrite List.length_rev, length_im_nparams; lia ].
    Qed.

    (** The canonical relations of a constructor's non-recursive arguments
        are those of its telescope. *)
    Lemma ar_gargs : forall c gs ups ups' a ms ms', ind_con Mk c = Some gs ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        forall j vs vs', j <= List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups k ms c) j vs vs' ->
          per_gargs (List.firstn j (List.map ce_ass (cargs_nonrec gs)))
            (components_env D ups (List.rev (im_nparams Mk)) ms) (components_env D ups' (List.rev (im_nparams Mk)) ms') vs vs'.
    Proof.
      intros * Hcon Hg Hu Ha Hm * Hj Hp.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
      rewrite List.length_rev in Hl, Hl'.
      pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
      eapply (tele_canon_gargs (List.map ce_ass (cargs_nonrec gs)) (im_nparams Mk) (canon_args_rel D ups k ms c) ups ups' ms ms' a);
        [ apply tele_ass_map_ass | exact Hu | exact Hu' | exact Hl | exact Hl'
        | exact Hpg | exact Ha | | | rewrite List.length_map; exact Hj | exact Hp ].
      - intros j0 A HA.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (cargs_nonrec gs) j0) as [A0 |] eqn:HA0; cbn in HA; [ injection HA as -> | discriminate ].
        assert (Hj0 : j0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (nonrec_relevance_nth _ _ _ HA0) as [r Hr].
        destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HM Hcon HA0 Hr) as [HAv _].
        split; [ exact (valid_ind_decl_strat _ HD _ _ _ _ j0 HM Hcon ltac:(lia)) | exists r; exact HAv ].
      - intros j0 A pre HA _.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (cargs_nonrec gs) j0) as [A0 |] eqn:HA0; cbn in HA; [ injection HA as -> | discriminate ].
        unfold canon_args_rel.
        rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hcon HA0), (member_nparams_eq _ _ _ HM), (member_con_tele_eq _ _ _ _ _ HM Hcon).
        reflexivity.
    Qed.

    (** The canonical relations of the domains of a recursive argument's
        shape are those of their telescope. *)
    Lemma dom_gargs : forall c gs gs1 t gs2 ups ups' a ms ms' ws ws', ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        tele_prefix_rel (canon_args_rel D ups k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        forall j ys ys', j <= List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t) j ys ys' ->
          per_gargs (List.firstn j (List.map ce_ass (ptyp_doms t)))
            (components_env D ups (List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mk)) (ms ++ ws))
            (components_env D ups' (List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mk)) (ms' ++ ws'))
            ys ys'.
    Proof.
      intros * Hcon Heq Hg Hu Ha Hm Hw * Hj Hp.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      set (K := List.length (cargs_nonrec gs1)) in *.
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
      rewrite List.length_rev, length_im_nparams in Hl, Hl'.
      pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
      pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg Hu Ha Hm _ ws ws' HK Hw) as Hgw.
      eapply (tele_canon_gargs (List.map ce_ass (ptyp_doms t)) (nonrec_args_prefix gs K ++ im_nparams Mk)
                (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t)
                ups ups' (ms ++ ws) (ms' ++ ws') a);
        [ apply tele_ass_map_ass | exact Hu | exact Hu'
        | rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by exact HK; lia
        | rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by exact HK; lia
        | | exact Ha | | | rewrite List.length_map; exact Hj | exact Hp ].
      - rewrite <- List.app_assoc; fold (im_params D Mk); rewrite List.rev_app_distr, (List.app_assoc ups), (List.app_assoc ups').
        apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, length_im_params; unfold im_np in *; lia | exact Hpg |].
        unfold nonrec_args_prefix; rewrite List.rev_involutive; unfold im_params; rewrite !env_tele_uparams by assumption.
        exact Hgw.
      - intros j0 A HA.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (ptyp_doms t) j0) as [B |] eqn:HB; cbn in HA; [ injection HA as -> | discriminate ].
        assert (Hj0 : j0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as [HBv _].
        rewrite List.firstn_map; fold (doms_ctx (List.firstn j0 (ptyp_doms t))).
        rewrite <- !List.app_assoc; fold (im_params D Mk); rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by exact HK.
        split; [ exact (valid_ind_decl_dctx _ HD _ _ _ _ _ _ _ j0 HM Hcon Heq ltac:(lia)) |].
        replace (j0 + (K + im_nn Mk)) with (j0 + K + im_nn Mk) by lia; exists relevant; exact HBv.
      - intros j0 A pre HA Hlp.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (ptyp_doms t) j0) as [B |] eqn:HB; cbn in HA; [ injection HA as -> | discriminate ].
        assert (Hj0 : j0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        unfold shape_doms_rel, canon_doms_rel; rewrite (List.nth_error_nth _ _ _ HB).
        (** The components' telescope, cut at the components given. *)
        unfold K; rewrite (nonrec_prefix_rev _ _ _ _ Heq), <- !List.app_assoc.
        rewrite (List.app_assoc ms ws pre), (List.app_assoc (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) (List.map ce_ass (ptyp_doms t))).
        rewrite (components_env_app_firstn D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (List.map ce_ass (ptyp_doms t)) (ms ++ ws) pre)
          by (rewrite ?List.length_app, ?List.length_rev, ?length_im_nparams, ?List.length_map; unfold cargs_nonrec_tele, K in *;
              rewrite ?List.length_map; lia).
        rewrite <- !List.app_assoc, Hlp; reflexivity.
    Qed.

    (** The arguments of a constructor before a recursive one, with the
        domains of its shape, as arguments of their telescope. *)
    Lemma rec_prefix_gargs : forall c gs gs1 t gs2 ups ups' a ms ms' ws ws' ys ys', ind_con Mk c = Some gs ->
        gs = gs1 ++ ca_rec t :: gs2 ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        tele_prefix_rel (canon_args_rel D ups k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        forall j, j <= List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t) j ys ys' ->
          per_gargs (List.rev (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk))
            nil nil (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys').
    Proof.
      intros * Hcon Heq Hg Hu Ha Hm Hw j Hj Hy.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg Hu Ha Hm _ ws ws' HK Hw) as Hgv.
      pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
      pose proof (dom_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg Hu Ha Hm Hw j ys ys' Hj Hy) as Hgy.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      assert (Hrv : List.rev (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)
                    = (List.rev (im_params D Mk) ++ List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1))))
                        ++ List.rev (doms_ctx (List.firstn j (ptyp_doms t))))
        by (rewrite !List.rev_app_distr; reflexivity).
      rewrite Hrv.
      replace (ups ++ ms ++ ws ++ ys) with (((ups ++ ms) ++ ws) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      replace (ups' ++ ms' ++ ws' ++ ys') with (((ups' ++ ms') ++ ws') ++ ys') by (rewrite <- !List.app_assoc; reflexivity).
      apply per_gargs_app_intro;
        [ rewrite !List.length_app, !List.length_rev, length_nonrec_args_prefix, length_im_params by exact HK; unfold im_np in *; lia | |].
      - apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, length_im_params; unfold im_np in *; lia | exact Hpg |].
        unfold nonrec_args_prefix; rewrite List.rev_involutive; unfold im_params; rewrite !env_tele_uparams by assumption.
        exact Hgv.
      - unfold doms_ctx; rewrite List.rev_involutive, <- List.firstn_map.
        assert (Hre : forall u v, List.length u = ind_nu D ->
                   env_tele nil (List.rev (im_params D Mk) ++ List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)))) ((u ++ ms) ++ v)
                   = components_env D u (List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mk)) (ms ++ v)).
        { intros u v Hlu; rewrite <- List.app_assoc, <- env_tele_uparams by exact Hlu.
          unfold im_params; rewrite !List.rev_app_distr, <- !List.app_assoc; reflexivity. }
        assert (Hre' : forall u v, List.length u = ind_nu D ->
                   env_tele nil (List.rev (im_params D Mk) ++ List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)))) ((u ++ ms') ++ v)
                   = components_env D u (List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_nparams Mk)) (ms' ++ v)).
        { intros u v Hlu; rewrite <- List.app_assoc, <- env_tele_uparams by exact Hlu.
          unfold im_params; rewrite !List.rev_app_distr, <- !List.app_assoc; reflexivity. }
        rewrite Hre, Hre' by assumption; exact Hgy.
    Qed.
  End Member.

  (** ** The Group at Related Uniform Parameters *)

  Section Canon.
    Variable (ups : list domain) (a : domain).
    Hypothesis (Hgd : per_gargs (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
      (Ha : ⟦ ind_sort D ⟧ decl_env D ups ↘ a).

    Lemma canon_hn : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        nparams_related (univ_idx a) D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm k0 A vs vs' HM Hk Hp.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (Hk0 : k0 < im_nn Mm)
        by (rewrite <- length_im_nparams, <- List.length_rev; apply List.nth_error_Some; congruence).
      pose proof (nr_gargs _ _ HM _ _ _ Hg2 Hu Ha k0 vs vs' ltac:(lia) Hp) as Hgv.
      pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
      pose proof (proj1 (valid_ind_decl_nparams _ HD _ _ _ _ HM Hk)) as HAv; rewrite <- (length_nparams_prefix Mm k0) in HAv at 2 by lia.
      (** The type reads only the components before it. *)
      rewrite (components_env_firstn D ups _ vs), (components_env_firstn D ups2 _ vs')
        by (rewrite List.length_rev, length_im_nparams; lia).
      rewrite Hlv, Hlv'.
      replace (List.firstn k0 (List.rev (im_nparams Mm))) with (List.rev (nparams_prefix Mm k0))
        by (unfold nparams_prefix; apply List.rev_involutive).
      eapply (sort_typ_rel (nparams_prefix Mm k0) A (nparams_prefix_sem _ _ HM k0) HAv ups ups2 vs vs');
        [ rewrite length_nparams_prefix; lia | rewrite length_nparams_prefix; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite rev_nparams_prefix; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg2 | exact Hgv ].
    Qed.

    Lemma canon_ha : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        args_related (univ_idx a) D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm ms ms' c gs k0 A vs vs' HM Hm Hcon HA Hp.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (Hk : k0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
      pose proof (ar_gargs _ _ HM _ _ _ _ _ _ _ Hcon Hg2 Hu Ha Hm k0 vs vs' ltac:(lia) Hp) as Hgv.
      pose proof (params_gargs _ _ HM _ _ _ _ _ Hg2 Hu Ha Hm) as Hpg.
      pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      destruct (nonrec_relevance_nth _ _ _ HA) as [r Hr].
      destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HM Hcon HA Hr) as [HAv _].
      assert (HC : ⊨ (nonrec_args_prefix gs k0 ++ im_nparams Mm) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; exact (valid_ind_decl_strat _ HD _ _ _ _ k0 HM Hcon ltac:(lia))).
      assert (HT : (nonrec_args_prefix gs k0 ++ im_nparams Mm) ++ ind_uparams D
                     ⊨ A : relevance_sort r (ind_sort D)[wk_shiftn (List.length (nonrec_args_prefix gs k0 ++ im_nparams Mm))]ʷ)
        by (rewrite <- List.app_assoc, List.length_app, length_nonrec_args_prefix, length_im_nparams by lia; exact HAv).
      (** The type reads only the arguments before it. *)
      rewrite (components_env_app_firstn D ups _ _ ms vs), (components_env_app_firstn D ups2 _ _ ms' vs')
        by (rewrite ?List.length_rev, ?length_im_nparams; unfold cargs_nonrec_tele; rewrite ?List.length_map; lia).
      rewrite Hlv, Hlv'.
      replace (List.rev (im_nparams Mm) ++ List.firstn k0 (cargs_nonrec_tele gs)) with (List.rev (nonrec_args_prefix gs k0 ++ im_nparams Mm))
        by (unfold nonrec_args_prefix, cargs_nonrec_tele; rewrite List.rev_app_distr, List.rev_involutive; reflexivity).
      eapply (sort_rel_typ_rel r (nonrec_args_prefix gs k0 ++ im_nparams Mm) A HC HT ups ups2 (ms ++ vs) (ms' ++ vs'));
        [ rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by lia; lia
        | rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by lia; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite <- List.app_assoc; fold (im_params D Mm); rewrite List.rev_app_distr, !List.app_assoc.
      apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, length_im_params; unfold im_np; lia | exact Hpg |].
      unfold nonrec_args_prefix; rewrite List.rev_involutive; unfold im_params; rewrite !env_tele_uparams by assumption.
      exact Hgv.
    Qed.

    Lemma canon_hd : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        doms_related (univ_idx a) D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' HM Hm Hcon Heq Hw HB Hy.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      set (K := List.length (cargs_nonrec gs1)) in *.
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hkl : k0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      pose proof (rec_prefix_gargs _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg2 Hu Ha Hm Hw k0 ltac:(lia) Hy) as Hgall.
      pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
      pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & Hly' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as [HBv _].
      set (Pre := doms_ctx (List.firstn k0 (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ im_nparams Mm).
      fold K in HBv.
      assert (HLP : List.length Pre = k0 + K + im_nn Mm)
        by (unfold Pre; rewrite !List.length_app, doms_ctx_length, List.length_firstn, length_nonrec_args_prefix, length_im_nparams by exact HK; lia).
      assert (HC : ⊨ Pre ++ ind_uparams D)
        by (unfold Pre; rewrite <- !List.app_assoc; exact (valid_ind_decl_dctx _ HD _ _ _ _ _ _ _ k0 HM Hcon Heq ltac:(lia))).
      assert (HT : Pre ++ ind_uparams D ⊨ B : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ)
        by (rewrite HLP; unfold Pre; rewrite <- !List.app_assoc; exact HBv).
      (** The domain reads only the components before it. *)
      rewrite (List.app_assoc ms ws ys), (List.app_assoc ms' ws' ys'), (List.app_assoc (List.rev (im_nparams Mm))).
      rewrite (components_env_app_firstn D ups _ _ (ms ++ ws) ys), (components_env_app_firstn D ups2 _ _ (ms' ++ ws') ys')
        by (rewrite ?List.length_app, ?List.length_rev, ?length_im_nparams; unfold cargs_nonrec_tele, shape_doms_tele, K in *;
            rewrite ?List.length_map; lia).
      rewrite Hly, Hly'.
      replace ((List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1) ++ List.firstn k0 (shape_doms_tele t)) with (List.rev Pre)
        by (unfold Pre, doms_ctx, shape_doms_tele; rewrite List.rev_app_distr, List.rev_involutive, List.firstn_map;
            unfold K; rewrite (nonrec_prefix_rev Mm _ _ _ _ Heq); reflexivity).
      rewrite <- !List.app_assoc.
      eapply (sort_typ_rel_relevant Pre B HC HT ups ups2 (ms ++ ws ++ ys) (ms' ++ ws' ++ ys'));
        [ rewrite HLP, !List.length_app; lia | rewrite HLP, !List.length_app; lia | exact Hu | exact Hu2 | | exact Ha ].
      unfold Pre; rewrite <- !List.app_assoc; exact Hgall.
    Qed.

    Lemma canon_hc : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        recs_related D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm ms ms' c gs gs1 t gs2 ws ws' ys ys' HM Hm Hcon Heq Hp Hy.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      pose proof (rec_prefix_gargs _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg2 Hu Ha Hm Hp _ (le_n _)
                    (tele_rel_pre _ _ _ _ Hy)) as Hgall.
      rewrite List.firstn_all in Hgall; fold (ptyp_tele t) in Hgall.
      pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlw & Hlw' & _).
      pose proof Hy as Hy0; rewrite tele_rel_iff in Hy0; destruct Hy0 as (Hly & Hly' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      destruct (length_rec_ps _ _ HM _ _ _ _ _ Hcon Heq) as (Mj & HMj & HPl).
      destruct (rec_closure _ _ HM _ _ _ _ _ _ Hcon Heq HMj ups ups2 ms ms' ws ws' ys ys' Hu Hlm Hlw Hly Hu2 Hlm' Hlw' Hly' Hgall)
        as (bs & bs' & Ebs & Ebs' & Hgb & _).
      apply (mk_rel_evals _ _ _ _ bs bs' Ebs Ebs').
      unfold nparams_tele_rel; rewrite HMj.
      eapply (gargs_tele_canon _ (canon_nparams_rel D ups (ptyp_mem t)) (decl_env D ups)); [ | exact Hgb |].
      - intros j A pre HA; unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HMj HA), (member_nparams_eq _ _ _ HMj).
        reflexivity.
      - rewrite (eval_exps_length _ _ _ Ebs), List.length_rev, length_im_nparams; exact HPl.
    Qed.

    (** The conditions of the clause at the canonical relations at [ups],
        and the bases admissible beside [ups]. *)
    Lemma canon_props_at : grp_tele_ass D -> ind_canon_props D ups.
    Proof.
      intros Hass0; constructor;
        [ exact (canon_nparams_per _ D ups ups (canon_hn ups Hgd))
        | exact (canon_nparams_invariant _ D ups ups Hass0 Hu Hu (canon_hn ups Hgd))
        | exact (canon_args_per _ D ups ups (canon_ha ups Hgd))
        | exact (canon_args_invariant _ D ups ups Hass0 Hu Hu (canon_hn ups Hgd) (canon_ha ups Hgd))
        | exact (canon_doms_per _ D ups ups Hu Hu (canon_hd ups Hgd))
        | exact (canon_doms_invariant _ D ups ups Hass0 Hu Hu (canon_hn ups Hgd) (canon_ha ups Hgd) (canon_hd ups Hgd)) ].
    Qed.

    Lemma canon_adm_at : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        adm_uparams D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) ups2.
    Proof.
      intros ups2 Hg2.
      exact (canon_adm (univ_idx a) D ups ups Hu Hu ups2 (canon_hn _ Hg2) (canon_ha _ Hg2) (canon_hc _ Hg2) (canon_hd _ Hg2)).
    Qed.
  End Canon.

  (** The sort at uniform parameters related to themselves has a value. *)
  Lemma sort_value : forall ups, per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      exists a, ⟦ ind_sort D ⟧ decl_env D ups ↘ a.
  Proof.
    intros ups Hg Hu.
    destruct (valid_ind_decl_sort _ HD) as [i HS].
    destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
    assert (HRU0 : RU (decl_env D ups) (decl_env D ups))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem); [ exact Hu | exact Hg ]).
    destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HRU0) as (a & _ & Ea & _ & _); eauto.
  Qed.

  (** Uniform parameters related at their telescope: a PER. *)
  Lemma uparams_rel_env : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      forall RU, EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU -> RU (decl_env D ups) (decl_env D ups').
  Proof. intros * Hg Hu RU HRU; apply (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem); [ exact Hu | exact Hg ]. Qed.

  Lemma uparams_of_env : forall ups ups' RU, EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU ->
      List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      RU (decl_env D ups) (decl_env D ups') -> per_gargs (List.rev (ind_uparams D)) nil nil ups ups'.
  Proof.
    intros * HRU Hu Hu' H.
    assert (HRU' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
    exact (proj2 (rel_gargs_tele _ _ _ _ per_ctx_env_nil_true rev_uparams_sem rev_uparams_ass HRU' nil nil ups ups'
                    ltac:(rewrite List.length_rev; exact Hu) ltac:(rewrite List.length_rev; exact Hu') H)).
  Qed.

  Lemma uparams_sym : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups' ups.
  Proof.
    intros * Hg Hu.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
    assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
    apply (uparams_of_env _ _ RU HRU Hu' Hu); symmetry; exact (uparams_rel_env _ _ Hg Hu _ HRU).
  Qed.

  Lemma uparams_trans : forall ups ups' ups'', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups' ups'' -> per_gargs (List.rev (ind_uparams D)) nil nil ups ups''.
  Proof.
    intros * Hg Hu Hg'.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'; pose proof (length_ups_gargs _ _ Hg' Hu') as Hu''.
    destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
    assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
    apply (uparams_of_env _ _ RU HRU Hu Hu'').
    etransitivity; [ exact (uparams_rel_env _ _ Hg Hu _ HRU) | exact (uparams_rel_env _ _ Hg' Hu' _ HRU) ].
  Qed.

  (** ** The Canonical Model

      A declared member of the group at related parameters is a type of the
      universe the sort denotes, its elements those of the group's
      canonical relations. *)

  Variable (p : qname).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hass : grp_tele_ass D).

  Lemma ind_relate : forall k Mk pm ups ups' ns ns' a, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D ->
      ⟦ ind_sort D ⟧ decl_env D ups ↘ a ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns' ->
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem (univ_idx a)
        ↘ grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) k ups ups' ns ns'.
  Proof.
    intros * HM Hh Hg Hu Ha Hns.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    pose proof (uparams_refl_l _ _ Hg) as Hgd.
    eapply per_univ_elem_indty_canon;
      [ exact Hl | exact Hass | exact Hu | exact Hu' | | (eapply canon_hn; eassumption) | (eapply canon_hn; eassumption)
      | (eapply canon_ha; eassumption) | (eapply canon_ha; eassumption)
      | (eapply canon_hd; eassumption) | (eapply canon_hd; eassumption)
      | (eapply canon_hc; eassumption) | (eapply canon_hc; eassumption) | exact HM | exact Hh | exact Hns ].
    exact (per_gargs_per_top_ps _ _ _ Hg ltac:(rewrite List.length_rev; exact Hu)).
  Qed.

  Section DeclMember.
    Variables (k : nat) (Mk : imember) (pm : qname).
    Hypotheses (HM : ind_member D k = Some Mk) (Hh : im_head Mk = mh_decl pm).

    (** Parameters related over any bases are related over the empty one,
        and split into the uniform and the non-uniform ones. *)
    Lemma params_split_rel : forall ρ ρ' ys ys', per_gargs (List.rev (im_params D Mk)) ρ ρ' ys ys' ->
        List.length ys = im_np D Mk ->
        per_gargs (List.rev (ind_uparams D)) nil nil (List.firstn (ind_nu D) ys) (List.firstn (ind_nu D) ys') /\
        per_gargs (List.rev (im_nparams Mk)) (decl_env D (List.firstn (ind_nu D) ys)) (decl_env D (List.firstn (ind_nu D) ys'))
          (List.skipn (ind_nu D) ys) (List.skipn (ind_nu D) ys') /\
        List.length (List.firstn (ind_nu D) ys) = ind_nu D /\ List.length ys' = im_np D Mk.
    Proof.
      intros * Hg Hlen.
      pose proof (per_gargs_length _ _ _ _ _ Hg) as [Hl' _].
      pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true (rev_params_sem _ _ HM) (rev_params_ass _ _ HM) ρ ρ' nil nil _ _ I I I Hg) as Hg0.
      rewrite <- (List.firstn_skipn (ind_nu D) ys), <- (List.firstn_skipn (ind_nu D) ys') in Hg0.
      rewrite rev_im_params in Hg0.
      assert (H1l : List.length (List.firstn (ind_nu D) ys) = List.length (List.rev (ind_uparams D)))
        by (rewrite List.length_firstn, List.length_rev; unfold im_np, ind_nu in *; lia).
      assert (H1l' : List.length (List.firstn (ind_nu D) ys') = List.length (List.rev (ind_uparams D)))
        by (rewrite List.length_firstn, List.length_rev; unfold im_np, ind_nu in *; lia).
      destruct (per_gargs_app (List.rev (ind_uparams D)) (List.rev (im_nparams Mk)) nil nil
                  (List.firstn (ind_nu D) ys) (List.firstn (ind_nu D) ys') (List.skipn (ind_nu D) ys) (List.skipn (ind_nu D) ys')
                  H1l Hg0 H1l') as [H1 H2].
      repeat split; [ exact H1 | exact H2 | rewrite List.length_firstn; unfold im_np in *; lia | lia ].
    Qed.

    (** The type former at related parameters, at the sort's universe. *)
    Lemma ind_at_params : forall RP ρ ρ' vts vts', EF im_params D Mk ≈ im_params D Mk ∈ per_ctx_env ↘ RP ->
        List.length vts = im_np D Mk -> List.length vts' = im_np D Mk ->
        RP (env_extend_typed ρ vts) (env_extend_typed ρ' vts') ->
        Dom d_ind p k (List.map fst vts) ≈ d_ind p k (List.map fst vts')
          ∈ per_head ((ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) ((ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)
              (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
    Proof.
      intros * HRP Hlen Hlen' HE i0 R0 b b' Eb Eb' HR0.
      assert (HPP : PER RP) by (eapply per_env_PER; exact HRP).
      assert (HEE : RP (env_extend_typed ρ vts) (env_extend_typed ρ vts)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
      (** The parameters' values are related at their telescope. *)
      assert (HRP' : EF List.rev (List.rev (im_params D Mk)) ++ ⋅ ≈ List.rev (List.rev (im_params D Mk)) ++ ⋅ ∈ per_ctx_env ↘ RP)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRP).
      assert (HCr : ⊨ List.rev (List.rev (im_params D Mk)) ++ ⋅) by exact (rev_params_sem _ _ HM).
      destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HCr (rev_params_ass _ _ HM) HRP' ρ ρ' vts vts'
                  ltac:(rewrite List.length_rev, length_im_params; exact Hlen) ltac:(rewrite List.length_rev, length_im_params; exact Hlen') HE)
        as [_ Hg].
      set (ys := List.map fst vts) in *; set (ys' := List.map fst vts') in *.
      assert (Hlys : List.length ys = im_np D Mk) by (unfold ys; rewrite List.length_map; exact Hlen).
      destruct (params_split_rel _ _ _ _ Hg Hlys) as (Hgu & Hgn & Hlu & Hl').
      set (ups := List.firstn (ind_nu D) ys) in *; set (ups' := List.firstn (ind_nu D) ys') in *.
      set (ns := List.skipn (ind_nu D) ys) in *; set (ns' := List.skipn (ind_nu D) ys') in *.
      assert (Hys : ys = ups ++ ns) by (symmetry; apply List.firstn_skipn).
      assert (Hys' : ys' = ups' ++ ns') by (symmetry; apply List.firstn_skipn).
      assert (Hlns : List.length ns = im_nn Mk) by (unfold ns; rewrite List.length_skipn; unfold im_np in *; lia).
      destruct (valid_ind_decl_sort _ HD) as [i HS].
      destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
      pose proof (uparams_refl_l _ _ Hgu) as Hgu0.
      (** The uniform parameters' part of the environment, against their own
          environment. *)
      set (fv := List.firstn (ind_nu D) vts).
      assert (Hwk : ⟪wk_shiftn (List.length (im_nparams Mk))⟫ (env_extend_typed ρ vts) = env_extend_typed ρ fv).
      { rewrite <- (List.firstn_skipn (ind_nu D) vts) at 1; rewrite env_extend_typed_app.
        replace (List.length (im_nparams Mk)) with (List.length (List.skipn (ind_nu D) vts))
          by (rewrite List.length_skipn, length_im_nparams; unfold im_np in *; lia).
        apply eval_wk_shiftn_extend_typed. }
      destruct (rel_wk_shiftn (im_nparams Mk) (ind_uparams D) _ _ HRP HRU) as [_ HwkR].
      pose proof (HwkR _ _ HEE) as Hfv; rewrite Hwk in Hfv.
      assert (Hlfv : List.length fv = List.length (ind_uparams D)) by (unfold fv; rewrite List.length_firstn; unfold im_np, ind_nu in *; lia).
      assert (HRU' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
      destruct (rel_gargs_readable _ _ _ _ per_ctx_env_nil_true rev_uparams_sem rev_uparams_ass HRU' ρ ρ fv fv
                  ltac:(rewrite List.length_rev; exact Hlfv) ltac:(rewrite List.length_rev; exact Hlfv) Hfv) as [Rfv _].
      pose proof (per_gargs_entries_readable _ _ _ _ _ Hgu0) as [Rups _].
      assert (HRUρ : RU (env_extend_typed ρ fv) (decl_env D ups)).
      { assert (Hw' : List.map fst (tele_entries nil (List.rev (ind_uparams D)) ups) = List.map fst fv)
          by (rewrite tele_entries_values; unfold ups, ys, fv; rewrite List.firstn_map; reflexivity).
        unfold decl_env, env_tele.
        exact (closed_env_base _ _ fv fv fv (tele_entries nil (List.rev (ind_uparams D)) ups) ρ ρ ρ nil
                 uparams_ass uparams_sem HRU Hlfv Hlfv eq_refl Hw' Rfv Rups Hfv). }
      destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HRUρ) as (a0 & a & Ea0 & Ea & _).
      (** The index of the sort's universe, at the parameters' values and at
          the uniform ones. *)
      assert (Hub : is_univ b) by exact (sort_wk_univ _ _ _ Eb).
      destruct (per_univ_elem_univ _ _ _ _ HR0 Hub) as [_ ER0].
      rewrite <- length_im_nparams in Eb.
      pose proof (univ_idx_wk _ _ _ _ _ _ _ _ _ (valid_ind_decl_params _ HD _ _ HM) HS HRP HEE Eb ltac:(rewrite Hwk; exact Ea0) Hub) as Hi1.
      pose proof (univ_idx_rel _ _ _ _ _ _ _ _ HRU HS HRUρ Ea0 Ea (sort_univ _ _ Ea0)) as Hi2.
      apply ER0; split;
        [| reflexivity | reflexivity
         | intros Hlc; destruct (level_code_head _ Hlc) as [[? Hx] | [[? Hx] | (? & ? & ? & Hx)]]; discriminate Hx .. ].
      rewrite <- Hi1, <- Hi2.
      (** The type former at the parameters. *)
      assert (Hns : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns').
      { eapply (gargs_tele_canon _ (canon_nparams_rel D ups k) (decl_env D ups)); [ | exact Hgn | rewrite List.length_rev, length_im_nparams; exact Hlns ].
        intros j A pre HA; unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HM HA), (member_nparams_eq _ _ _ HM); reflexivity. }
      rewrite Hys, Hys'.
      eexists; exact (ind_relate _ _ _ _ _ _ _ _ HM Hh Hgu Hlu Ea Hns).
    Qed.

    (** ** The Type Former *)
    Lemma valid_exp_under_ctx_ind : ⋅ ⊨ a_ind p k : ind_ty D Mk.
    Proof.
      destruct (valid_ind_decl_ty _ HD _ _ HM) as [i HT].
      destruct (rel_exp_of_typ_inversion_simple HT) as (R & HR & Hsimp).
      apply (rel_exp_closed_intro _ _ i); [ intros; apply (ind_ty_sub _ _ _ _ Hc HM) | intros; reflexivity |].
      intros ρ ρ'.
      assert (Hρ : R ρ ρ') by (inversion HR; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
      destruct (Hsimp ρ ρ' Hρ) as (a & a' & Ea & Ea' & [R0 HR0]).
      exists a, a', R0, (d_ind p k nil), (d_ind p k nil).
      split; [ exact Ea | split; [ exact Ea' | split; [ exact HR0 | split; [ constructor | split; [ constructor |] ] ] ] ].
      unfold ind_ty in Ea, Ea'; rewrite <- (List.rev_involutive (im_params D Mk)) in Ea, Ea'.
      eapply (ctx_pi_rel_elem (im_np D Mk) (d_ind p k) _ ltac:(intros xs x Hx; eapply eval_app_indty; eassumption)
                (fun _ _ => eq_refl) (List.rev (im_params D Mk)) ⋅ R (rev_params_ass _ _ HM) HR (rev_params_sem _ _ HM) ρ ρ' nil nil);
        [ rewrite List.length_rev, length_im_params; reflexivity | reflexivity | exact Hρ
        | | exact Ea | exact Ea' | exact HR0 | ].
      - (** The parameters are relevant. *)
        intros ts1 A ts2 R1 vts vts' b Heq HR1 Hl1 Hl1' HE1 Eb.
        assert (Hpe : im_params D Mk = List.rev ts2 ++ ce_ass A :: List.rev ts1)
          by (rewrite <- (List.rev_involutive (im_params D Mk)), Heq, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
        destruct (im_params_relevant _ _ HM _ _ _ Hpe) as [i0 HA]; rewrite <- (List.app_nil_r (List.rev ts1)) in HA.
        destruct (rel_param_typed_relevant HA _ HR1 _ _ HE1) as (b0 & Eb0 & Hr).
        assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption); exact Hr.
      - intros R1 vts vts' HR1 Hl1 Hl1' HE1; cbn [List.app].
        rewrite List.rev_involutive, List.app_nil_r in HR1.
        rewrite List.length_rev, length_im_params in Hl1, Hl1'.
        exact (ind_at_params R1 ρ ρ' vts vts' HR1 Hl1 Hl1' HE1).
    Qed.
  End DeclMember.

  Lemma eval_apps_ind : forall k Mk ys xs, ind_member D k = Some Mk -> List.length xs + List.length ys <= im_np D Mk ->
      $*| d_ind p k xs & ys | gc_deps ⍮ gc_stack ↘ d_ind p k (xs ++ ys).
  Proof.
    intros k Mk; induction ys as [| y ys IH]; intros xs HM Hlen; [ rewrite List.app_nil_r; constructor |].
    econstructor; [ eapply eval_app_indty; [ exact Hl | exact HM | cbn in *; lia ] |].
    replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
    apply IH; [ exact HM | rewrite List.length_app; cbn in *; lia ].
  Qed.

  (** ** The Members as Values of the Context of the Members as Variables

      The type of [Self_j], the declared member [j] with the members as
      variables, is a type over the uniform parameters, and the type former
      [j] at uniform parameters is of it there.  So the values of the
      declared members at related uniform parameters, after them, are
      related environments of [grp_selfs_ctx D]. *)
  Section Selfs.
    Hypothesis (Hord : ind_order_ok D).

    Lemma self_ty_sem : forall j Mj, ind_member D j = Some Mj -> exists i : nat, ind_uparams D ⊨ self_ty D Mj : Typeω@i.
    Proof.
      intros * HMj.
      destruct (valid_ind_decl_sort _ HD) as [i HS].
      pose proof (valid_ind_decl_params _ HD _ _ HMj) as HP; unfold im_params in HP.
      pose proof (rel_exp_under_ctx_wk (rel_wk_under_ctx_shiftn _ _ HP) HS) as HSw; cbn [exp_wk] in HSw.
      unfold self_ty, im_nn; eapply rel_exp_ctx_pi; [ exact (member_nparams_ass _ _ HMj) | exact HP | exact HSw ].
    Qed.

    Lemma self_val_rel : forall j Mj, ind_member D j = Some Mj -> j < ind_ndecl D ->
        forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        forall i R a a', ⟦ self_ty D Mj ⟧ decl_env D ups ↘ a -> ⟦ self_ty D Mj ⟧ decl_env D ups' ↘ a' ->
          DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom d_ind p j ups ≈ d_ind p j ups' ∈ R.
    Proof.
      intros * HMj Hj * Hg Hu * Ea Ea' HR.
      assert (Hd : im_is_decl Mj = true) by (apply (proj2 (Hord _ _ HMj)); exact Hj).
      assert (Hh : exists pm, im_head Mj = mh_decl pm)
        by (unfold im_is_decl in Hd; destruct (im_head Mj); [ eauto | discriminate .. ]).
      destruct Hh as [pm Hh].
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
      assert (HCm : ⊨ List.rev (List.rev (im_nparams Mj)) ++ ind_uparams D)
        by (rewrite List.rev_involutive; exact (valid_ind_decl_params _ HD _ _ HMj)).
      unfold self_ty in Ea, Ea'; rewrite <- (List.rev_involutive (im_nparams Mj)) in Ea, Ea'.
      eapply (ctx_pi_rel_elem (im_np D Mj) (d_ind p j) _ ltac:(intros xs x Hx; eapply eval_app_indty; eassumption)
                (fun _ _ => eq_refl) (List.rev (im_nparams Mj)) (ind_uparams D) RU
                ltac:(apply List.Forall_rev, (member_nparams_ass _ _ HMj)) HRU HCm (decl_env D ups) (decl_env D ups') ups ups');
        [ rewrite List.length_rev, length_im_nparams; unfold im_np in *; lia | lia | exact (uparams_rel_env _ _ Hg Hu _ HRU)
        | | exact Ea | exact Ea' | exact HR | ].
      - (** The parameters are relevant. *)
        intros ts1 A ts2 R1 vts vts' b Heq HR1 Hl1 Hl1' HE1 Eb.
        assert (Hpe : im_params D Mj = List.rev ts2 ++ ce_ass A :: (List.rev ts1 ++ ind_uparams D))
          by (unfold im_params; rewrite <- (List.rev_involutive (im_nparams Mj)), Heq, List.rev_app_distr; cbn [List.rev];
              rewrite <- !List.app_assoc; reflexivity).
        destruct (im_params_relevant _ _ HMj _ _ _ Hpe) as [i0 HA].
        destruct (rel_param_typed_relevant HA _ HR1 _ _ HE1) as (b0 & Eb0 & Hr).
        assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption); exact Hr.
      - (** At the parameters' values, the type former, over the uniform
            parameters' environment. *)
        intros R1 vts vts' HR1 Hl1 Hl1' HE1.
        rewrite List.rev_involutive in HR1; fold (im_params D Mj) in HR1.
        rewrite List.length_rev, length_im_nparams in Hl1, Hl1'.
        pose proof (ind_at_params j Mj pm HMj Hh R1 nil nil (tele_entries nil (List.rev (ind_uparams D)) ups ++ vts)
                      (tele_entries nil (List.rev (ind_uparams D)) ups' ++ vts') HR1) as H.
        rewrite !List.map_app, !tele_entries_values, !env_extend_typed_app in H.
        apply H; [ rewrite List.length_app, tele_entries_length; unfold im_np in *; lia
                 | rewrite List.length_app, tele_entries_length; unfold im_np in *; lia | exact HE1 ].
    Qed.

    Lemma grp_selfs_prefix_sem : forall n, n <= ind_ndecl D ->
        ⊨ grp_selfs_from D 0 (List.firstn n (ind_members D)) ++ ind_uparams D.
    Proof.
      induction n as [| n IH]; intros Hn; [ exact uparams_sem |].
      pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn; [| apply List.nth_error_None in HMn; lia ].
      rewrite (firstn_S_nth_error _ _ _ HMn), grp_selfs_from_snoc; cbn [Nat.add List.app].
      pose proof (IH ltac:(lia)) as HC.
      destruct (self_ty_sem _ _ HMn) as [i Hi].
      pose proof (rel_exp_under_ctx_wk (rel_wk_under_ctx_shiftn _ _ HC) Hi) as Hw; cbn [exp_wk] in Hw.
      rewrite length_grp_selfs_from in Hw.
      exact (rel_ctx_wf_ext_typ _ _ _ HC Hw).
    Qed.

    Lemma grp_selfs_ctx_sem : ⊨ grp_selfs_ctx D.
    Proof. unfold grp_selfs_ctx, grp_selfs; exact (grp_selfs_prefix_sem _ (le_n _)). Qed.

    Lemma uparams_refl_r : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups' ups'.
    Proof.
      intros * Hg Hu.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (H12 : RU (decl_env D ups) (decl_env D ups')) by exact (uparams_rel_env _ _ Hg Hu _ HRU).
      assert (H22 : RU (decl_env D ups') (decl_env D ups')) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
      assert (HRU' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
      destruct (rel_gargs_tele _ _ _ _ per_ctx_env_nil_true rev_uparams_sem rev_uparams_ass HRU' nil nil ups' ups'
                  ltac:(rewrite List.length_rev; exact Hu') ltac:(rewrite List.length_rev; exact Hu') H22) as [_ H].
      exact H.
    Qed.

    Lemma selfs_gargs : forall n, n <= ind_ndecl D ->
        forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        per_gargs (List.rev (grp_selfs_from D 0 (List.firstn n (ind_members D)))) (decl_env D ups) (decl_env D ups')
          (List.map (fun j => d_ind p j ups) (List.seq 0 n)) (List.map (fun j => d_ind p j ups') (List.seq 0 n)).
    Proof.
      induction n as [| n IH]; intros Hn ups ups' Hg Hu; [ constructor |].
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof (uparams_refl_r _ _ Hg Hu) as Hgr.
      pose proof (uparams_refl_l _ _ Hg) as Hgl.
      pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn; [| apply List.nth_error_None in HMn; lia ].
      pose proof (IH ltac:(lia) _ _ Hg Hu) as IHn.
      pose proof (IH ltac:(lia) _ _ Hgr Hu') as IHr.
      set (Ψ := grp_selfs_from D 0 (List.firstn n (ind_members D))) in *.
      assert (HlΨ : List.length Ψ = n) by (unfold Ψ; rewrite length_grp_selfs_from, List.length_firstn; lia).
      rewrite (firstn_S_nth_error _ _ _ HMn), grp_selfs_from_snoc; fold Ψ; cbn [Nat.add List.rev].
      rewrite List.seq_S, !List.map_app; cbn [List.map Nat.add].
      rewrite List.length_firstn; replace (Nat.min n (List.length (ind_members D))) with n by lia.
      (** The prefix environments are related at the prefix context. *)
      pose proof (grp_selfs_prefix_sem n ltac:(lia)) as HC; fold Ψ in HC.
      destruct (rel_ctx_wf_per_ctx_env HC) as [RΓ0 HRΓ0].
      assert (Henv : forall ys ys', per_gargs (List.rev (ind_uparams D)) nil nil ys ys' -> List.length ys = ind_nu D ->
                 per_gargs (List.rev Ψ) (decl_env D ys) (decl_env D ys')
                   (List.map (fun j => d_ind p j ys) (List.seq 0 n)) (List.map (fun j => d_ind p j ys') (List.seq 0 n)) ->
                 RΓ0 (components_env D ys (List.rev Ψ) (List.map (fun j => d_ind p j ys) (List.seq 0 n)))
                     (components_env D ys' (List.rev Ψ) (List.map (fun j => d_ind p j ys') (List.seq 0 n)))).
      { intros ys ys' Hgy Hly Hgs.
        pose proof (length_ups_gargs _ _ Hgy Hly) as Hly'.
        rewrite <- !env_tele_uparams by assumption.
        apply (gargs_env_rel _ _ _ _ _ _ HRΓ0 HC); [ rewrite !List.length_app, List.length_map, List.length_seq; unfold ind_nu in *; lia |].
        rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hly | exact Hgy | exact Hgs ]. }
      destruct (self_ty_sem _ _ HMn) as [i Hi].
      destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HC) Hi) as (RΓ & HΓ & i0 & Hwk).
      assert (E0 : RΓ0 <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
      rewrite HlΨ in Hwk.
      assert (Hval : forall ys ys', per_gargs (List.rev (ind_uparams D)) nil nil ys ys' -> List.length ys = ind_nu D ->
                 per_gargs (List.rev Ψ) (decl_env D ys) (decl_env D ys')
                   (List.map (fun j => d_ind p j ys) (List.seq 0 n)) (List.map (fun j => d_ind p j ys') (List.seq 0 n)) ->
                 exists m m', ⟦ (self_ty D Mn)[wk_shiftn n]ʷ ⟧ components_env D ys (List.rev Ψ) (List.map (fun j => d_ind p j ys) (List.seq 0 n)) ↘ m /\
                   ⟦ self_ty D Mn ⟧ decl_env D ys' ↘ m' /\ Dom m ≈ m' ∈ per_univ i).
      { intros ys ys' Hgy Hly Hgs.
        destruct (Hwk _ _ (proj1 (E0 _ _) (Henv _ _ Hgy Hly Hgs))) as (y & y' & Ry & Ey & Ey' & HRy & Hmm).
        assert (Hy1 : y = d_univ i) by (cbn in Ey; inversion Ey; reflexivity).
        destruct Hmm as [Hp | (m & m' & Em & Em' & Hmm)]; [ rewrite Hy1 in Hp; discriminate |].
        replace n with (List.length (List.map (fun j => d_ind p j ys') (List.seq 0 n))) in Em' at 1
          by (rewrite List.length_map, List.length_seq; reflexivity).
        rewrite eval_wk_shiftn_components_env in Em'.
        rewrite Hy1 in HRy.
        destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
        apply ERy in Hmm; destruct Hmm as [Hmm _ _].
        exists m, m'; split; [ exact Em | split; [ exact Em' | exact Hmm ] ]. }
      destruct (Hval _ _ Hg Hu IHn) as (m & m' & Em & Em' & [R1 HR1]).
      destruct (Hval _ _ Hgr Hu' IHr) as (m2 & m2' & Em2 & Em2' & [R2 HR2]).
      assert (m2' = m') as -> by (eapply functional_eval_exp; eassumption).
      (** The type of [Self_n] at the left prefix, related to the one at the
          right prefix through the member's type at the right uniform
          parameters. *)
      pose proof (per_univ_sym _ _ _ _ HR2) as HR2'.
      pose proof (per_univ_trans _ _ _ _ _ _ HR1 (per_univ_elem_resp_iff HR2'
                    ltac:(eapply per_univ_elem_right_irrel; [ exact HR2' | exact (per_univ_sym _ _ _ _ HR1) ]))) as HR12.
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ i R1); [ rewrite List.length_rev, HlΨ, List.length_map, List.length_seq; reflexivity | exact IHn | |].
      - econstructor; [ exact Em | exact Em2 | exact HR12 ].
      - (** The value: the type former at the uniform parameters, of the
            member's type there. *)
        assert (Hn' : n < ind_ndecl D) by lia.
        destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
        assert (HRu : RU (decl_env D ups) (decl_env D ups')) by exact (uparams_rel_env _ _ Hg Hu _ HRU).
        destruct (rel_exp_of_typ_inversion_simple_at HRU Hi _ _ HRu) as (b & b' & Eb & Eb' & [Rb HRb]).
        assert (b' = m') as -> by (eapply functional_eval_exp; eassumption).
        pose proof (self_val_rel _ _ HMn Hn' _ _ Hg Hu _ _ _ _ Eb Eb' HRb) as Hx.
        destruct (Hval _ _ Hgl Hu (IH ltac:(lia) _ _ Hgl Hu)) as (m3 & m3' & Em3 & Em3' & [R3 HR3]).
        assert (m3 = m) as -> by (eapply functional_eval_exp; eassumption).
        assert (m3' = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (E1 : R1 <~> R3) by (eapply per_univ_elem_right_irrel; eassumption).
        assert (E3 : R3 <~> Rb) by (eapply per_univ_elem_right_irrel; [ exact (per_univ_sym _ _ _ _ HR3) | exact HRb ]).
        apply E1, E3; exact Hx.
    Qed.

    (** The values of the declared members at the uniform parameters [ups],
        after them: an environment of [grp_selfs_ctx D]. *)
    Lemma selfs_env_rel : forall RS, EF grp_selfs_ctx D ≈ grp_selfs_ctx D ∈ per_ctx_env ↘ RS ->
        forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        RS (components_env D ups (List.rev (grp_selfs D)) (selfs_vals p D ups))
           (components_env D ups' (List.rev (grp_selfs D)) (selfs_vals p D ups')).
    Proof.
      intros RS HRS ups ups' Hg Hu.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      rewrite <- !env_tele_uparams by assumption; fold (grp_selfs_ctx D).
      apply (gargs_env_rel _ _ _ _ _ _ HRS grp_selfs_ctx_sem).
      - rewrite length_grp_selfs_ctx, List.length_app; unfold selfs_vals; rewrite List.length_map, List.length_seq; lia.
      - unfold grp_selfs_ctx, grp_selfs; rewrite List.rev_app_distr.
        apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg |].
        exact (selfs_gargs _ (le_n _) _ _ Hg Hu).
    Qed.

    (** ** The Substitution of the Members for their Variables

        [grp_sb p D] is a substitution from the uniform parameters into
        the members as variables, built from valid parts: each declared
        member's type former at the uniform parameters is of its type with
        the members as variables. *)
    Hypothesis (Hmv : decl_mvc D).

    Lemma valid_self_apps : forall j Mj, ind_member D j = Some Mj -> j < ind_ndecl D ->
        ind_uparams D ⊨ apps (a_ind p j) (vars_from 0 (ind_nu D)) : self_ty D Mj.
    Proof.
      intros * HMj Hj.
      assert (Hd : im_is_decl Mj = true) by (apply (proj2 (Hord _ _ HMj)); exact Hj).
      assert (Hh : exists pm, im_head Mj = mh_decl pm)
        by (unfold im_is_decl in Hd; destruct (im_head Mj); [ eauto | discriminate .. ]).
      destruct Hh as [pm Hh].
      pose proof (closed_weaken_valid _ _ _ _ uparams_sem (valid_exp_under_ctx_ind _ _ _ HMj Hh)) as HI.
      unfold ind_ty, im_params in HI; rewrite ctx_pi_app in HI; fold (self_ty D Mj) in HI.
      destruct (self_ty_sem _ _ HMj) as [i Hi].
      destruct (closed_app_sem _ _ uparams_ass uparams_sem uparams_sem) as [HUU _].
      pose proof (closed_app_valid _ _ _ _ _ uparams_ass uparams_sem uparams_sem Hi) as HiU.
      pose proof (rel_exp_apps_ctx_pi_n _ (ind_uparams D) (ind_uparams D) _ i (a_ind p j) (vars_from 0 (ind_nu D)) eq_refl
                    uparams_ass HUU HiU HI ltac:(rewrite length_vars_from; reflexivity)) as H.
      rewrite (exp_at_vars _ _ _ (self_ty_scoped _ _ _ Hc HMj) (self_ty_mvc _ _ _ Hc Hmv HMj)) in H.
      rewrite (exp_wk_id_ext (self_ty D Mj) _ wk_shiftn_zero) in H.
      apply H; [| exact (vars_from_scoped 0 (ind_nu D) (ind_nu D) (le_n _)) ].
      intros k N T HN HT.
      pose proof (valid_vars_tele nil (ind_uparams D) uparams_ass (decl_closed_uparams _ Hc) (decl_mvc_uparams _ Hmv) uparams_sem k N T) as Hv.
      cbn [List.length List.app] in Hv; exact (Hv HN HT).
    Qed.

    Lemma nth_rev_grp_selfs : forall n k, n <= ind_ndecl D -> k < n ->
        exists Mk, ind_member D k = Some Mk /\
          List.nth_error (List.rev (grp_selfs_from D 0 (List.firstn n (ind_members D)))) k
            = Some (ce_ass (self_ty D Mk)[wk_shiftn k]ʷ).
    Proof.
      induction n as [| n IH]; intros k Hn Hk; [ lia |].
      pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn; [| apply List.nth_error_None in HMn; lia ].
      rewrite (firstn_S_nth_error _ _ _ HMn), grp_selfs_from_snoc; cbn [Nat.add List.rev].
      assert (HlΨ : List.length (List.rev (grp_selfs_from D 0 (List.firstn n (ind_members D)))) = n)
        by (rewrite List.length_rev, length_grp_selfs_from, List.length_firstn; lia).
      destruct (Nat.lt_ge_cases k n) as [Hkn | Hkn].
      - rewrite List.nth_error_app1 by lia; exact (IH _ ltac:(lia) Hkn).
      - assert (k = n) as -> by lia.
        exists Mn; split; [ exact HMn |].
        rewrite List.nth_error_app2, HlΨ, Nat.sub_diag by lia; cbn.
        rewrite List.length_firstn, Nat.min_l by lia; reflexivity.
    Qed.

    Lemma grp_sb_gsub : gsub (ind_uparams D) (grp_sb p D) (grp_selfs_ctx D).
    Proof.
      unfold grp_sb, grp_selfs_ctx.
      apply gsub_of_list; [ exact (gsub_id _ uparams_sem) | | exact grp_selfs_ctx_sem | | |
                            apply List.Forall_map, List.Forall_forall; intros j0 _; apply exp_scoped_apps;
                            split; [ cbn; auto | exact (vars_from_scoped 0 (ind_nu D) (ind_nu D) (le_n _)) ] ].
      - unfold grp_selfs; generalize 0; induction (List.firstn (ind_ndecl D) (ind_members D)) as [| M ms IH]; intros j;
          cbn [grp_selfs_from]; [ constructor |].
        apply List.Forall_app; split; [ apply IH | constructor; [ eexists; reflexivity | constructor ] ].
      - unfold grp_selfs; rewrite length_grp_sb_list, length_grp_selfs_from, List.length_firstn.
        pose proof (ind_ndecl_le D); lia.
      - intros k N T HN HT.
        rewrite List.nth_error_map in HN.
        destruct (List.nth_error (List.seq 0 (ind_ndecl D)) k) as [j |] eqn:Hj; cbn in HN; [| discriminate ].
        injection HN as <-.
        assert (Hk : k < ind_ndecl D)
          by (rewrite <- (List.length_seq (ind_ndecl D) 0); apply List.nth_error_Some; congruence).
        assert (j = k) as -> by (rewrite (List.nth_error_nth' _ 0 (n := k)) in Hj by (rewrite List.length_seq; exact Hk);
                                 injection Hj as <-; rewrite List.seq_nth by exact Hk; reflexivity).
        apply tele_insts_nth in HT as (A & HA & ->).
        destruct (nth_rev_grp_selfs (ind_ndecl D) k (le_n _) Hk) as (Mk & HMk & HAk).
        unfold grp_selfs in HA; rewrite HAk in HA; injection HA as <-.
        rewrite exp_sub_wk, (exp_sub_sb_eq _ _ Id), exp_sub_id; [ exact (valid_self_apps _ _ HMk Hk) |].
        intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        set (L := List.firstn k (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D)))).
        assert (HL : List.length L = k)
          by (unfold L; rewrite List.length_firstn, length_grp_sb_list; lia).
        replace (x + k) with (List.length L + x) by lia.
        apply sb_of_list_ge.
    Qed.
  End Selfs.
End Sort.

(** ** Valid Filed Groups

    The record a record view is a view of: found at [qr], valid and
    closed. *)
Record valid_rview_record (qr : qname) (R : record_decl) : Prop := mk_valid_rview_record
  { (** [R] is the record filed at [qr] *)
    valid_rview_record_lookup : record_lookup gc_deps gc_stack qr = Some R
    (** It is semantically valid *)
  ; valid_rview_record_valid : valid_record_decl R
    (** It is closed *)
  ; valid_rview_record_closed : record_closed R
    (** It is typed *)
  ; valid_rview_record_typed : record_typed gc_deps gc_stack R }.

(** What the semantic lemmas about a group filed at [p] ask of it: it is
    found there, valid, closed, of a universe as its sort, with the
    conditions of the universe clause, typed, filed at the path of its
    first member, and the records of its record views are valid. *)
Record valid_group (p : qname) (D : ind_decl) : Prop := mk_valid_group
  { (** It is found at [p] *)
    valid_group_lookup : ind_lookup gc_deps gc_stack p = Some D
    (** It is semantically valid *)
  ; valid_group_valid : valid_ind_decl D
    (** It is closed *)
  ; valid_group_closed : decl_closed D
    (** Its sort is a universe *)
  ; valid_group_sort : ind_sort_univ (ind_sort D)
    (** The structural conditions of the universe clause *)
  ; valid_group_ass : grp_tele_ass D
    (** It is typed *)
  ; valid_group_typed : decl_typed gc_deps gc_stack D
    (** It is filed at its first member's path *)
  ; valid_group_mpath : ind_mpath D 0 = Some p
    (** The record of each record view is valid *)
  ; valid_group_records : forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      exists R, valid_rview_record qr R }.

(** The groups the views of a group nest through are valid. *)
Definition containers_valid (D : ind_decl) : Prop :=
  forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
    ind_lookup gc_deps gc_stack qc = Some Dq -> valid_group qc Dq.

End Fixed_GCtx.
