(** * The Eliminator of a Group

    The motive of the block of a member [k] lives in the eliminator's
    context extended by the member's non-uniform parameters and the
    scrutinee ([elim_mctx]), each branch of the block in the context
    extended by the non-uniform parameters, the arguments and the recursive
    results of its constructor ([elim_bctx]), the recursive result of an
    argument recursive in the member [j] at the motive of [j].  The types of
    these telescopes are the group's, instantiated at the uniform
    parameters [Us] the eliminator carries.

    The canonical relations of the group read these types in the empty
    environment, at the values [u0] of [Us]; this file first relates the
    two readings ([cv_nparams], [cv_mctx], [cv_bctx]), and then
    instantiates the eliminator's model ([per_ind_elim_all]) at the three
    links of the judgment's chain.  The elements of a member's type are
    the group's at the bases of their types; the model reads them at any
    bases ([ind_rel_rebase]). *)

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
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Head Variable as a Term

    [B[wk_q ↑]ʷ[Id ,, #0]] is [B] up to the sort of the entry at index [0]:
    [Id ,, #0] substitutes the term [#0] where [Id] has the variable [0].  On a
    context whose head is a term the two denote the same, because the
    environment relation reads only the head's term value and the tail. *)

Definition sb_head_term (σ : sub) : sub := sb_extend (Wk ⨟ σ) (se_exp (sentry_exp (σ 0))).

Definition env_head_term (ρ : env) : env := de_term (ρ 0) :: ρ↯.

Lemma exp_sub_wk_q_var0 : forall B σ, B[wk_q ↑]ʷ[Id ,, #0][σ] = B[sb_head_term σ].
Proof.
  intros; rewrite exp_sub_sub, <- exp_sub_of_wk, exp_sub_sub.
  apply exp_sub_sb_eq; intros [| x]; reflexivity.
Qed.

Lemma exp_wk_q_var0 : forall B, B[wk_q ↑]ʷ[Id ,, #0] = B[sb_head_term Id].
Proof. intros; rewrite <- exp_sub_wk_q_var0, exp_sub_id; reflexivity. Qed.

Lemma sb_wk_head_term : forall σ φ, sb_eq (sb_wk (sb_head_term σ) φ) (sb_head_term (sb_wk σ φ)).
Proof.
  intros σ φ [| x]; cbn; [ rewrite sentry_exp_wk; reflexivity | reflexivity ].
Qed.

Lemma eval_sub_head_term : forall σ ρ ρσ,
    ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ sb_head_term σ ⟧s ρ ↘ env_head_term ρσ.
Proof.
  intros * H [| x]; [| exact (H (S x)) ].
  exists (ρσ 0); split; [ reflexivity | apply (eval_sub_var σ ρ ρσ 0 H) ].
Qed.

(** An environment relation of a context with a term at its head reads only the
    head's value and the tail. *)
Lemma per_ctx_env_head_term : forall {Γ A Γ' A' R},
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' <-> R (env_head_term ρ) (env_head_term ρ').
Proof.
  intros * H; inversion H; subst.
  intros ρ ρ'; apply_relation_equivalence; reflexivity.
Qed.

Lemma per_ctx_env_head_term_l : forall {Γ A Γ' A' R},
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> R (env_head_term ρ) ρ'.
Proof.
  intros * H ρ ρ' Hρ; apply (per_ctx_env_head_term H); exact (proj1 (per_ctx_env_head_term H ρ ρ') Hρ).
Qed.

Lemma per_ctx_env_head_term_r : forall {Γ A Γ' A' R},
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> R ρ (env_head_term ρ').
Proof.
  intros * H ρ ρ' Hρ; apply (per_ctx_env_head_term H); exact (proj1 (per_ctx_env_head_term H ρ ρ') Hρ).
Qed.

Lemma rel_chain_head_term4 : forall {Γ A R a b c d},
    EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R ->
    rel_chain R (a :: b :: c :: d :: nil) ->
    rel_chain R (env_head_term a :: env_head_term b :: c :: d :: nil).
Proof.
  intros * HΓ (Hab & Hbc & Hcd).
  repeat split; [ | | exact Hcd ].
  - apply (per_ctx_env_head_term_l HΓ), (per_ctx_env_head_term_r HΓ), Hab.
  - apply (per_ctx_env_head_term_l HΓ), Hbc.
Qed.

Lemma rel_sub_under_ctx_head_term : forall {Γ' Γ A σ σ'},
    Γ' ⊨ˢ σ ≈ σ' : Γ ▹ A ->
    Γ' ⊨ˢ sb_head_term σ ≈ σ' : Γ ▹ A.
Proof.
  intros * [env_rel HΓ' env_relo HΓA Hσ].
  refine (mk_rel_sub_under_ctx _ _ _ _ env_rel HΓ' env_relo HΓA _).
  intros Γ'' env_rel' HΓ'' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ'' _ Hφ _ _ Hρ) as [a b c d Ha Hb Hc Hd Hchain].
  apply (mk_rel_sub (env_head_term a) (env_head_term b) c d);
    [ rewrite sb_wk_head_term; apply eval_sub_head_term; exact Ha
    | apply eval_sub_head_term; exact Hb | exact Hc | exact Hd |].
  exact (rel_chain_head_term4 HΓA Hchain).
Qed.

Lemma rel_exp_typ_var0 : forall {Γ A B} {i : nat},
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ▹ A ⊨ B[wk_q ↑]ʷ[Id ,, #0] ≈ B : Typeω@i.
Proof.
  intros * HB.
  pose proof (rel_exp_of_typ_inversion HB) as [env_rel [HΓA HBgen]].
  apply rel_exp_of_typ; exists env_rel, HΓA.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HBgen _ _ HΓ' _ _ (rel_sub_under_ctx_head_term Hσ) _ _ _ _ Hρ
              (eval_sub_head_term _ _ _ Hev) Hev') as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hc].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_rel) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρσ' : Dom ρσ ≈ ρσ ∈ env_rel) by solve_per.
  destruct (HBgen _ _ HΓA _ _ (rel_sub_under_ctx_head_term (rel_sub_id (ex_intro _ _ HΓA))) _ _ _ _ Hρσ'
              (eval_sub_head_term _ _ _ (eval_sub_id ρσ)) (eval_sub_id ρσ)) as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hd].
  apply (mk_rel_exp c1 d1 c3 c4);
    [ rewrite exp_sub_wk_q_var0; exact Hc1 | rewrite exp_wk_q_var0; exact Hd1 | exact Hc3 | exact Hc4 |].
  functional_eval_rewrite_clear.
  merge_rel_chain Hc Hd c2.
Qed.

(** ** Substitutions Weakened *)

Lemma eval_sb_wk_of_list : forall Ms σ φ ρ ρσ ms,
    ⟦ sb_wk σ φ ⟧s ρ ↘ ρσ -> ⟦ List.map (fun M => M[φ]ʷ) Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ sb_wk (sb_of_list σ Ms) φ ⟧s ρ ↘ env_args ρσ ms.
Proof.
  induction Ms as [| M Ms IH]; intros * Hσ HMs; inversion HMs; subst; cbn [sb_of_list]; [ exact Hσ |].
  change (env_args ρσ (m :: ms0)) with (env_args (ρσ ↦ m) ms0).
  apply IH; [ apply eval_sub_wk_extend; assumption | assumption ].
Qed.

(** ** The Variables of a Telescope *)

Lemma vars_tele_lookup : forall Φ Δ ρ τ Γ0 n,
    tele_ass Δ -> ctx_mvc Δ -> ctx_scoped n Δ ->
    (forall y, y < n -> sentry_exp (τ y) = (sentry_exp (ρ y))[wk_shiftn (List.length Φ + List.length Δ)]ʷ) ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ τ (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      exists x, N = a_var x /\ Φ ++ tele_sub Δ ρ ++ Γ0 ∋ #x : T.
Proof.
  intros * Hass Hmv Hs Hτ k N T HN HT.
  apply vars_from_nth_error in HN as [Hk ->].
  eexists; split; [ reflexivity |].
  apply tele_insts_nth in HT as (A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HsA : exp_scoped (k + n) A).
  { rewrite HΔeq in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HsA _].
    rewrite List.length_rev in HsA; congruence. }
  assert (HmA : exp_mvc 0 A).
  { unfold ctx_mvc in Hmv; rewrite HΔeq in Hmv; apply List.Forall_app in Hmv as [_ Hmv].
    apply List.Forall_cons_iff in Hmv as [HmA _]; exact HmA. }
  set (s := List.length Φ + List.length l2 + 1).
  replace (A[sb_of_list τ (List.firstn k (vars_from (List.length Φ) (List.length Δ)))])
    with (A[sb_qn k ρ][wk_shiftn s]ʷ).
  - replace (List.length Φ + (List.length Δ - 1 - k)) with (0 + List.length (Φ ++ tele_sub (List.rev l2) (sb_qn (S k) ρ)))
      by (rewrite List.length_app, length_tele_sub, List.length_rev; lia).
    replace (A[sb_qn k ρ][wk_shiftn s]ʷ)
      with (A[sb_qn k ρ][wk_shift]ʷ[wk_shiftn (List.length (Φ ++ tele_sub (List.rev l2) (sb_qn (S k) ρ)))]ʷ)
      by (rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app, length_tele_sub, List.length_rev; unfold s; lia).
    rewrite HΔeq, tele_sub_app; cbn [tele_sub centry_sub List.length]; rewrite List.length_rev, Hl1.
    rewrite <- List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
    apply ctx_lookup_app_r; constructor.
  - rewrite <- exp_sub_of_wk, exp_sub_sub; symmetry; eapply exp_scoped_mvc_agree; [ exact HsA | exact HmA |].
    intros x Hx; cbn [sb_compose].
    destruct (Nat.lt_ge_cases x k) as [Hxk | Hxk].
    + rewrite sb_of_list_firstn_vars by lia; rewrite sb_qn_lt by exact Hxk; cbn; f_equal; unfold s; lia.
    + replace x with (List.length (List.firstn k (vars_from (List.length Φ) (List.length Δ))) + (x - k)) at 1
        by (rewrite List.length_firstn, length_vars_from; lia).
      rewrite sb_of_list_ge, Hτ by lia.
      rewrite sb_qn_ge by exact Hxk.
      rewrite <- sentry_exp_sub, <- sentry_exp_wk, exp_sub_of_wk, exp_wk_wk.
      apply exp_wk_wk_eq; intros z; cbn; unfold s; lia.
Qed.

Lemma eval_var_args : forall B xs k, k < List.length xs ->
    ⟦ a_var k ⟧ env_args B xs ↘ List.nth (List.length xs - 1 - k) xs d_true.
Proof.
  intros * Hk.
  replace (List.nth (List.length xs - 1 - k) xs d_true) with (env_var (env_args B xs) k); [ constructor |].
  rewrite env_var_nth, env_args_rev, List.app_nth1 by (rewrite List.length_rev, List.length_map; lia).
  rewrite List.rev_nth by (rewrite List.length_map; lia).
  rewrite List.length_map, List.map_nth.
  replace (List.length xs - S k) with (List.length xs - 1 - k) by lia; reflexivity.
Qed.

Lemma vars_from_S0 : forall n, vars_from 0 (S n) = a_var n :: vars_from 0 n.
Proof. intros; unfold vars_from; rewrite List.seq_S, List.rev_app_distr; reflexivity. Qed.

(** ** Recursive Results *)

Lemma rec_results_rel_len : forall dr Rel k u u' pre pre' gs vs vs' ihs ihs',
    rec_results_rel dr Rel k u u' pre pre' gs vs vs' ihs ihs' ->
    List.length ihs = cargs_nrec gs /\ List.length ihs' = cargs_nrec gs.
Proof. induction 1; cbn; lia. Qed.

Lemma rec_results_rel_at : forall dr Rel k u u' pre pre' gs vs vs' ihs ihs',
    rec_results_rel dr Rel k u u' pre pre' gs vs vs' ihs ihs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists v v' ih ih', List.nth_error vs (List.length gs1) = Some v /\ List.nth_error vs' (List.length gs1) = Some v' /\
      List.nth_error ihs (cargs_nrec gs1) = Some ih /\ List.nth_error ihs' (cargs_nrec gs1) = Some ih' /\
      rec_result_rel dr Rel k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) t v v' ih ih'.
Proof.
  induction 1 as [pre pre' | pre pre' A gs v v' vs vs' ihs ihs' H IH | pre pre' t0 gs v v' vs vs' ih ih' ihs ihs' Hr H IH];
    intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst.
  - destruct (IH _ _ _ eq_refl) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hr).
    exists x, x', y, y'; cbn; rewrite <- !List.app_assoc in Hr; repeat split; assumption.
  - exists v, v', ih, ih'; cbn; rewrite !List.app_nil_r; repeat split; assumption.
  - destruct (IH _ _ _ eq_refl) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hr0).
    exists x, x', y, y'; cbn; repeat split; assumption.
Qed.

Lemma con_args_rel_at : forall p D okr nr ar dr k u u' pre pre' gs vs vs',
    con_args_rel p D okr nr ar dr k u u' pre pre' gs vs vs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists x x', List.nth_error vs (List.length gs1) = Some x /\ List.nth_error vs' (List.length gs1) = Some x' /\
      rec_arg_rel p D okr nr ar dr k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) t x x'.
Proof.
  induction 1; intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst;
    try match goal with IH : forall _ _ _, _ = _ -> _ |- _ => destruct (IH _ _ _ eq_refl) as (x & x' & Hx & Hx' & Hr0) end.
  - exists x, x'; cbn; rewrite <- !List.app_assoc in Hr0; repeat split; assumption.
  - do 2 eexists; cbn; rewrite !List.app_nil_r; repeat split; eassumption.
  - exists x, x'; cbn; repeat split; assumption.
Qed.

(** ** Relations of Types along Chains *)

(** A type related to the left of a pair is related to anything related
    to its right, at the pair's relation. *)
Lemma univ_connect : forall (i : nat) a b c d R,
    Dom a ≈ b ∈ per_univ i -> DF b ≈ c ∈ per_univ_elem i ↘ R -> Dom d ≈ c ∈ per_univ i ->
    DF a ≈ d ∈ per_univ_elem i ↘ R.
Proof.
  intros * [R1 H1] H2 [R3 H3].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H1 H2) as (R4 & H4 & _).
  destruct (per_univ_elem_sym _ _ _ _ H3) as [H3s _].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H4 H3s) as (R5 & H5 & _).
  eapply per_univ_elem_resp_iff; [ exact H5 |].
  etransitivity; [ symmetry; eapply per_univ_elem_right_irrel; [ exact H4 | exact H5 ] |].
  eapply per_univ_elem_left_irrel; [ exact H4 | exact H2 ].
Qed.

(** The head relation of an instance is that of the type at the values of
    the substitution. *)
Lemma per_head_inst : forall Δ0 Γ0 A (i : nat) τ RΓ0 E E' Eτ Eτ',
    Δ0 ⊨ A : Typeω@i -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨ˢ τ ≈ τ : Δ0 ->
    RΓ0 E E' -> ⟦ τ ⟧s E ↘ Eτ -> ⟦ τ ⟧s E' ↘ Eτ' ->
    (per_head A[τ] A[τ] E E' <~> per_head A A Eτ Eτ').
Proof.
  intros * HA HΓ0 Hτ HE Hev Hev'.
  destruct (rel_exp_of_typ_inversion HA) as (R & HR & Hgen).
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev') as [a b c d Ha Hb Hc Hd Hch].
  assert (Had : Dom a ≈ d ∈ per_univ i) by pairwise.
  destruct Had as [R1 HR1].
  assert (Ch : rel_chain (per_univ_elem i R1) (a :: b :: c :: d :: nil))
    by (eapply per_univ_chain_at_in; [ exact Hch | | | exact HR1 ]; solve_in).
  assert (Hbc : DF b ≈ c ∈ per_univ_elem i ↘ R1) by pairwise.
  etransitivity; [ symmetry; eapply per_head_iff; [ exact Ha | exact Hd | exact HR1 ] |].
  eapply per_head_iff; [ exact Hb | exact Hc | exact Hbc ].
Qed.

Lemma nth_mid : forall (X fa aft ihp : list domain) v,
    List.nth (List.length X + List.length fa) (X ++ fa ++ v :: aft ++ ihp) d_true = v.
Proof.
  intros; rewrite List.app_nth2 by lia; replace (List.length X + List.length fa - List.length X) with (List.length fa) by lia.
  rewrite List.app_nth2 by lia; rewrite Nat.sub_diag; reflexivity.
Qed.

(** The head relation of a valid type at related environments is a PER. *)
Lemma per_head_trans : forall Γ0 T (i : nat) R0 E E', EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ R0 -> Γ0 ⊨ T : Typeω@i -> R0 E E' ->
    forall a b d, Dom a ≈ b ∈ per_head T T E E' -> Dom b ≈ d ∈ per_head T T E E' -> Dom a ≈ d ∈ per_head T T E E'.
Proof.
  intros * HR0 HT HE * Hab Hbd.
  destruct (rel_exp_of_typ_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
  pose proof (per_head_iff Et Et' HR) as ER.
  assert (HP : PER R) by (eapply per_elem_PER; exact HR).
  apply ER; apply ER in Hab, Hbd; etransitivity; eassumption.
Qed.

Lemma per_head_sym : forall Γ0 T (i : nat) R0 E E', EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ R0 -> Γ0 ⊨ T : Typeω@i -> R0 E E' ->
    forall a b, Dom a ≈ b ∈ per_head T T E E' -> Dom b ≈ a ∈ per_head T T E E'.
Proof.
  intros * HR0 HT HE * Hab.
  destruct (rel_exp_of_typ_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
  pose proof (per_head_iff Et Et' HR) as ER.
  assert (HP : PER R) by (eapply per_elem_PER; exact HR).
  apply ER; apply ER in Hab; symmetry; exact Hab.
Qed.

(** ** Branches under a Substitution *)
Lemma brs_lookup_sub_inv : forall Bs σ c n Ba, brs_lookup (brs_sub Bs σ) c = Some (n, Ba) ->
    exists B0, brs_lookup Bs c = Some (n, B0) /\ Ba = B0[sb_qn n σ].
Proof.
  intros * H; rewrite brs_lookup_sub in H.
  destruct (brs_lookup Bs c) as [[n0 B0] |]; cbn in H; [ injection H as <- <-; eauto | discriminate ].
Qed.

Lemma brs_names_sub : forall cs Bs σ, brs_names cs Bs -> brs_names cs (brs_sub Bs σ).
Proof. unfold brs_names, brs_sub; intros * H; rewrite List.map_map; exact H. Qed.

Lemma brs_in_sub : forall Bs σ c n B, In (c, n, B) (brs_sub Bs σ) -> exists B0, In (c, n, B0) Bs.
Proof.
  unfold brs_sub; intros * H; apply List.in_map_iff in H as ([[c0 n0] B0] & He & Hin).
  cbn in He; injection He as -> -> _; eauto.
Qed.

Lemma brs_lookup_pair : forall (Bs Bs' : list (String.string * nat * exp)) c n B, List.map fst Bs = List.map fst Bs' ->
    brs_lookup Bs c = Some (n, B) ->
    exists k B', List.nth_error Bs k = Some (c, n, B) /\ List.nth_error Bs' k = Some (c, n, B') /\ brs_lookup Bs' c = Some (n, B').
Proof.
  induction Bs as [| [[c0 n0] B0] Bs IH]; intros [| [[c1 n1] B1] Bs'] * Hm Hl; cbn in *; try discriminate.
  injection Hm as <- <- Hm.
  destruct (String.eqb_spec c c0) as [-> | Hne].
  - injection Hl as <- <-.
    exists 0, B1; split; [ reflexivity | split; [ reflexivity |] ].
    cbn; destruct (String.eqb_spec c0 c0) as [_ | Hn]; [ reflexivity | contradiction ].
  - destruct (IH _ _ _ _ Hm Hl) as (k & B' & H1 & H2 & H3).
    exists (S k), B'; split; [ exact H1 | split; [ exact H2 |] ].
    cbn; destruct (String.eqb_spec c c0); [ contradiction | exact H3 ].
Qed.

Lemma brs_names_fst' : forall cs (Bs Bs' : list (String.string * nat * exp)), List.map fst Bs = List.map fst Bs' ->
    brs_names cs Bs -> brs_names cs Bs'.
Proof.
  unfold brs_names; intros * Hm H; rewrite H.
  rewrite <- (List.map_map fst fst Bs), <- (List.map_map fst fst Bs'), Hm; reflexivity.
Qed.

(** ** Applying a Variable to the Variables of a Telescope *)
Lemma valid_app_here : forall Ψ A C (i : nat) M, ⊨ Ψ ▹ A -> Ψ ▹ A ⊨ C : Typeω@i ->
    Ψ ⊨ M : Π A C ->
    Ψ ▹ A ⊨ a_app M[wk_shift]ʷ (a_var 0) : C.
Proof.
  intros * HΨA HC HM.
  destruct (rel_ctx_wf_ass_inv HΨA) as [j HA].
  pose proof (rel_wk_under_ctx_shift HΨA) as Hw.
  pose proof (rel_exp_under_ctx_wk Hw HM) as HMw; cbn [exp_wk] in HMw.
  pose proof (rel_exp_under_ctx_wk Hw HA) as HAw; cbn [exp_wk] in HAw.
  pose proof (rel_wk_under_ctx_q Hw HA) as Hwq.
  pose proof (rel_exp_under_ctx_wk Hwq HC) as HCw; cbn [exp_wk] in HCw.
  pose proof (valid_exp_under_ctx_var_here HΨA) as Hv.
  pose proof (rel_exp_under_ctx_app_cong (i := max i j) (rel_exp_cumu_ge (i := j) (j := max i j) ltac:(lia) HAw)
                (rel_exp_cumu_ge (i := i) (j := max i j) ltac:(lia) HCw) HMw Hv) as H.
  eapply rel_exp_under_ctx_subtyp; [ exact H | exact HC |].
  eapply rel_subtyp_under_ctx_refl; exact (rel_exp_typ_var0 HC).
Qed.

Lemma valid_apps_vars : forall n Δ Ψ B (i : nat) M, List.length Δ = n -> tele_ass Δ -> ⊨ Δ ++ Ψ ->
    Δ ++ Ψ ⊨ B : Typeω@i -> Ψ ⊨ M : ctx_pi Δ B ->
    Δ ++ Ψ ⊨ apps M[wk_shiftn n]ʷ (vars_from 0 n) : B.
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HM.
  - destruct Δ; [| discriminate ]; cbn in *.
    rewrite (exp_wk_id_ext M _ wk_shiftn_zero); exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Hn; cbn in Hn.
    unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite ctx_pi_snoc in HM.
    rewrite <- List.app_assoc in HΔ, HB |- *; cbn [List.app] in HΔ, HB |- *.
    pose proof (rel_ctx_wf_app_r _ _ HΔ) as HΨA.
    destruct (rel_exp_ctx_pi _ _ _ _ Hass HΔ HB) as [j HC].
    pose proof (valid_app_here _ _ _ _ _ HΨA HC HM) as HMA.
    pose proof (IH Δ0 _ _ _ _ ltac:(lia) Hass HΔ HB HMA) as H.
    rewrite vars_from_S0; cbn [apps_exp].
    replace (M[wk_shiftn (S n)]ʷ $ #n) with ((M[wk_shift]ʷ $ #0)[wk_shiftn n]ʷ); [ exact H |].
    cbn [exp_wk]; f_equal; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia.
Qed.

Lemma env_entry_args_nth : forall B xs k, k < List.length xs ->
    env_entry (env_args B xs) k = de_term (List.nth (List.length xs - 1 - k) xs d_true).
Proof.
  intros * Hk.
  rewrite env_entry_nth, env_args_rev, List.app_nth1 by (rewrite List.length_rev, List.length_map; lia).
  rewrite List.rev_nth by (rewrite List.length_map; lia).
  rewrite List.length_map.
  replace (List.length xs - S k) with (List.length xs - 1 - k) by lia.
  rewrite List.map_nth; reflexivity.
Qed.

(** The components' substitution of a recursive argument, at an
    environment of the branch's context. *)
Lemma ihs_sub_eval : forall nn Us gs1 aft j B X fa v ihp w,
    List.length X = nn -> List.length fa = List.length gs1 -> List.length ihp = j ->
    ⟦ List.map (fun U => U[wk_shiftn (j + (List.length gs1 + S (List.length aft)) + nn)]ʷ) Us ⟧* gc_deps ⍮ gc_stack
      ⍮ env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ w ->
    ⟦ ihs_sub nn Us (List.length gs1 + S (List.length aft)) (cargs_pat gs1) j ⟧s
      env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ env_args B (w ++ X ++ nonrec_arg_vals gs1 fa).
Proof.
  intros * LX Lfa Lihp Hw x.
  set (pat := cargs_pat gs1).
  set (na := List.length gs1 + S (List.length aft)).
  set (K := List.length (cargs_nonrec gs1)).
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  assert (HK : pat_nargs pat = K) by (unfold pat, K; rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
  assert (Lnv : List.length (nonrec_arg_vals gs1 fa) = K) by (apply length_nonrec_arg_vals; exact Lfa).
  assert (Lw : List.length w = List.length Us) by (rewrite (eval_exps_length _ _ _ Hw), List.length_map; reflexivity).
  set (Ep := env_args B (X ++ fa ++ v :: aft ++ ihp)).
  unfold ihs_sub; cbn [sb_compose sb_of_wk sentry_sub].
  assert (Hs : na - List.length pat + j = List.length (v :: aft ++ ihp)) by (unfold na; cbn; rewrite List.length_app; lia).
  rewrite Hs.
  destruct (Nat.lt_ge_cases x (K + nn)) as [Hx | Hx].
  - assert (Hwp : wk_pat pat x < List.length pat + nn) by (apply wk_pat_bound; lia).
    rewrite sb_qn_lt by exact Hwp; cbn [sentry_sub sb_of_wk eval_sentry].
    unfold Ep; replace (X ++ fa ++ v :: aft ++ ihp) with ((X ++ fa) ++ v :: aft ++ ihp) by (rewrite <- List.app_assoc; reflexivity).
    rewrite env_args_app; cbn [wk_shiftn].
    rewrite (env_args_app B (X ++ fa)), Nat.add_comm, env_entry_args_app.
    rewrite (env_args_app B X), <- (eval_wk_entry _ _ (wk_mono_pat pat)).
    unfold pat; rewrite eval_wk_pat_args by exact Lfa.
    rewrite <- (env_args_app B X).
    apply env_entry_args_lt; rewrite List.length_app; lia.
  - replace x with (pat_nargs pat + (nn + (x - K - nn))) by lia.
    rewrite wk_pat_ge, sb_qn_ge by lia.
    replace (List.length pat + (nn + (x - K - nn)) - (List.length pat + nn)) with (x - K - nn) by lia.
    set (y := x - K - nn).
    replace (pat_nargs pat + (nn + y)) with (List.length (X ++ nonrec_arg_vals gs1 fa) + y) by (rewrite List.length_app; lia).
    rewrite (env_args_app B w), env_entry_args_app.
    destruct (Nat.lt_ge_cases y (List.length Us)) as [Hy | Hy].
    + rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia.
      cbn [sentry_wk sentry_sub eval_sentry].
      destruct (nth_error_lt_some' Us (List.length Us - 1 - y) ltac:(lia)) as [U HU].
      destruct (eval_exps_nth _ _ _ _ _ Hw ltac:(rewrite List.nth_error_map, HU; reflexivity)) as (u & Hu & Eu).
      exists u; split.
      * rewrite env_entry_args_nth by lia; f_equal.
        rewrite Lw; apply List.nth_error_nth; exact Hu.
      * rewrite (List.nth_error_nth _ _ _ HU), exp_sub_of_wk, exp_wk_wk.
        replace (U[wk_compose (wk_shiftn (List.length pat + nn)) (wk_shiftn (List.length (v :: aft ++ ihp)))]ʷ)
          with (U[wk_shiftn (j + (List.length gs1 + S (List.length aft)) + nn)]ʷ); [ exact Eu |].
        apply exp_wk_wk_eq; intros z; cbn; rewrite List.length_app; lia.
    + replace y with (List.length Us + (y - List.length Us)) by lia.
      rewrite sb_of_list_ge; cbn [sentry_wk sentry_sub eval_sentry sb_of_wk sb_id wk_shiftn].
      replace (List.length Us + (y - List.length Us)) with (List.length w + (y - List.length Us)) by lia.
      rewrite env_entry_args_app.
      unfold Ep; symmetry.
      replace (y - List.length Us + (List.length pat + nn) + List.length (v :: aft ++ ihp))
        with (List.length (X ++ fa ++ v :: aft ++ ihp) + (y - List.length Us))
        by (cbn; rewrite !List.length_app; cbn; rewrite List.length_app; lia).
      apply env_entry_args_app.
Qed.

Fixpoint sb_shift_iter (k : nat) (β : sub) : sub :=
  match k with 0 => β | S k => sb_shift_iter k β ⨟ sb_of_wk wk_shift end.
Fixpoint apps_vars_iter (k : nat) (x : exp) : exp :=
  match k with 0 => x | S k => a_app (apps_vars_iter k x)[wk_shift]ʷ (a_var 0) end.

Lemma sb_shift_iter_eq : forall k β, sb_eq (sb_shift_iter k β) (β ⨟ sb_of_wk (wk_shiftn k)).
Proof.
  induction k as [| k IH]; intros β; cbn [sb_shift_iter].
  - intros y; cbn; rewrite (sentry_sub_sb_eq _ _ Id), sentry_sub_id; [ reflexivity |].
    rewrite (sb_of_wk_cong _ _ wk_shiftn_zero); exact sb_of_wk_id.
  - rewrite IH, sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
    rewrite <- sb_of_wk_compose; apply sb_of_wk_cong; intros z; cbn; lia.
Qed.

Lemma apps_vars_iter_eq : forall k x, apps_vars_iter k x = apps x[wk_shiftn k]ʷ (vars_from 0 k).
Proof.
  induction k as [| k IH]; intros x; cbn [apps_vars_iter].
  - cbn; rewrite (exp_wk_id_ext x _ wk_shiftn_zero); reflexivity.
  - rewrite IH, apps_exp_wk.
    replace (vars_from 0 (S k)) with (vars_from 1 k ++ a_var 0 :: nil)
      by (rewrite <- (Nat.add_1_r k), <- (vars_from_app 0 k 1); reflexivity).
    rewrite apps_snoc; f_equal; f_equal.
    + rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia.
    + unfold vars_from; rewrite List.map_map; apply List.map_ext; intros y; cbn; f_equal; lia.
Qed.

(** The type of an argument of a shape at an instance: a [Π] over the
    shape's domains of the member it ends in. *)
Lemma ptyp_ty_at_ctx_pi : forall p D t Us σ,
    ptyp_ty_at p D Us σ t
    = ctx_pi (tele_sub (ptyp_tele t) σ)
        (ind_mty p D (ptyp_mem t) (List.map (fun U => U[wk_shiftn (ptyp_depth t)]ʷ) Us)
           (List.map (fun P => P[sb_qn (ptyp_depth t) σ]) (ptyp_ps t))).
Proof.
  intros p0 D0; induction t as [j Ps | B t IH]; intros *.
  - cbn [ptyp_ty_at ptyp_tele ptyp_doms doms_ctx List.map List.rev tele_sub ctx_pi ptyp_depth List.length ptyp_ps ptyp_mem sb_qn].
    rewrite (List.map_ext (fun U => U[wk_shiftn 0]ʷ) (fun U => U)) by (intros U; apply (exp_wk_id_ext U _ wk_shiftn_zero)).
    rewrite List.map_id; reflexivity.
  - cbn [ptyp_ty_at ptyp_tele ptyp_doms ptyp_depth ptyp_ps ptyp_mem].
    unfold ptyp_tele, ptyp_depth in IH.
    rewrite IH.
    unfold ptyp_tele, ptyp_depth; cbn [ptyp_doms List.length].
    change (doms_ctx (B :: ptyp_doms t)) with (doms_ctx (ptyp_doms t) ++ ce_ass B :: nil).
    rewrite tele_sub_app, ctx_pi_app; cbn [tele_sub ctx_pi List.length sb_qn centry_sub].
    replace (sb_qn (List.length (ptyp_doms t)) (sb_q σ)) with (sb_q (sb_qn (List.length (ptyp_doms t)) σ))
      by (rewrite <- (sb_qn_plus _ 1), Nat.add_1_r; reflexivity).
    rewrite List.map_map, (List.map_ext (fun U => U[wk_shift]ʷ[wk_shiftn (List.length (ptyp_doms t))]ʷ)
                                       (fun U => U[wk_shiftn (S (List.length (ptyp_doms t)))]ʷ))
      by (intros U; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia).
    reflexivity.
Qed.

(** ** The Parameters of a Member, Split at the Uniform Ones *)
Lemma params_valid_split : forall D k Mk Γ Ps, decl_closed D -> ind_member D k = Some Mk ->
    List.length Ps = im_np D Mk ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T -> Γ ⊨ P : T) ->
    (forall j U T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U ->
       List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Γ ⊨ U : T) /\
    (forall j N T, List.nth_error (List.skipn (ind_nu D) Ps) j = Some N ->
       List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) j
         = Some T ->
       Γ ⊨ N : T).
Proof.
  intros * Hc HM Hl HPs.
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in Hl; lia).
  assert (Hti : tele_insts (im_params D Mk) Id Ps
                = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                  ++ tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
  { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
      [ exact (decl_uparams_ass D Hc) | rewrite HUl; reflexivity ]. }
  assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_uparams_ass D Hc); rewrite HUl; unfold ind_nu; lia).
  split; intros j N T HN HT.
  - apply (HPs j); [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HN |].
    rewrite Hti, List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HT.
  - apply (HPs (ind_nu D + j)).
    + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
      rewrite HUl; replace (ind_nu D + j - ind_nu D) with j by lia; exact HN.
    + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + j - ind_nu D) with j by lia; exact HT.
Qed.

Lemma params_valid_join : forall D k Mk Γ Us Ns, decl_closed D -> ind_member D k = Some Mk -> List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊨ U : T) ->
    (forall j N T, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Us) Ns) j = Some T ->
       Γ ⊨ N : T) ->
    forall j P T, List.nth_error (Us ++ Ns) j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id (Us ++ Ns)) j = Some T ->
      Γ ⊨ P : T.
Proof.
  intros * Hc HM HUl HUs HNs j P T HP HT; unfold im_params in HT.
  rewrite tele_insts_app in HT by (try exact (decl_uparams_ass D Hc); exact HUl).
  assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_uparams_ass D Hc); rewrite HUl; unfold ind_nu; lia).
  destruct (Nat.lt_ge_cases j (ind_nu D)) as [Hj | Hj].
  - rewrite List.nth_error_app1 in HP by lia; rewrite List.nth_error_app1 in HT by lia; eauto.
  - rewrite List.nth_error_app2 in HP by lia; rewrite List.nth_error_app2 in HT by lia.
    rewrite HUl in HP; rewrite Hl1 in HT; eauto.
Qed.

(** The member [k]'s type at its parameters as variables, the head of
    its motive's context over the closed parameters, and its instance at
    the uniform parameters [Us]. *)
Lemma mty_vars_inst : forall p D k Mk Us, decl_closed D -> List.length Us = ind_nu D ->
    (ind_mty p D k (ind_uvars D (im_nn Mk) 0) (vars_from 0 (im_nn Mk)))[sb_qn (im_nn Mk) (sb_of_list Id Us)]
    = ind_mty p D k (List.map (fun U => U[wk_shiftn (im_nn Mk)]ʷ) Us) (vars_from 0 (im_nn Mk)).
Proof.
  intros * Hc HUl.
  rewrite ind_mty_sub by (try exact Hc; apply length_ind_uvars); f_equal.
  - unfold ind_uvars; rewrite <- HUl; cbn [Nat.add]; apply vars_from_sb_qn.
  - apply vars_from_sub; lia.
Qed.

Lemma mty_vars_valid : forall p D, valid_group p D -> containers_valid D ->
    forall k Mk, ind_member D k = Some Mk ->
    exists i : nat, im_params D Mk ⊨ ind_mty p D k (ind_uvars D (im_nn Mk) 0) (vars_from 0 (im_nn Mk)) : Typeω@i.
Proof.
  intros p D Hg Hcv k Mk HM.
  pose proof (vgr_valid _ _ Hg) as HD; pose proof (vgr_closed _ _ Hg) as Hc.
  pose proof (dt_mvc _ _ _ (vgr_typed _ _ Hg)) as Hmv.
  pose proof (vid_params _ HD _ _ HM) as HP.
  assert (Hvars : forall j N T, List.nth_error (vars_from 0 (im_np D Mk)) j = Some N ->
             List.nth_error (tele_insts (im_params D Mk) Id (vars_from 0 (im_np D Mk))) j = Some T ->
             im_params D Mk ⊨ N : T).
  { intros j N T HN HT.
    rewrite <- (List.app_nil_l (im_params D Mk)) in HP |- *.
    rewrite <- length_im_params in HN, HT.
    change 0 with (List.length (@nil centry)) in HN, HT.
    exact (valid_vars_tele nil (im_params D Mk) (member_params_ass D Hc _ _ HM) (decl_closed_params D _ _ Hc HM)
             (decl_params_mvc _ _ _ (vgr_typed _ _ Hg) _ _ HM) HP _ _ _ HN HT). }
  destruct (params_valid_split D k Mk (im_params D Mk) (vars_from 0 (im_np D Mk)) Hc HM (length_vars_from _ _) Hvars)
    as [_ HNs].
  assert (Hsk : List.skipn (ind_nu D) (vars_from 0 (im_np D Mk)) = vars_from 0 (im_nn Mk)).
  { unfold im_np; rewrite Nat.add_comm, <- vars_from_app; cbn [Nat.add].
    rewrite skipn_app_len by (rewrite length_vars_from; reflexivity); reflexivity. }
  assert (Hfs : List.firstn (ind_nu D) (vars_from 0 (im_np D Mk)) = ind_uvars D (im_nn Mk) 0).
  { unfold im_np, ind_uvars; rewrite Nat.add_comm, <- vars_from_app; cbn [Nat.add].
    rewrite firstn_app_len by (rewrite length_vars_from; reflexivity); reflexivity. }
  rewrite Hsk, Hfs in HNs.
  destruct (vg_mty_valid p D Hg Hcv k Mk (im_nparams Mk) (im_nn Mk) 0 (vars_from 0 (im_nn Mk)) HM HP
              ltac:(rewrite length_im_nparams; lia) (length_vars_from _ _) HNs) as [i Hi].
  exists i; exact Hi.
Qed.

(** ** The Eliminator of a Valid Group

    A group [D] filed at [p], of a valid family [P], an eliminator's
    context [Γ] and its uniform parameters [Us]. *)
Section GroupElim.
  Variable (P : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups P) (HPD : P p D).
  Let Hvg := valid_groups_valid P HP p D HPD.
  Let Hcv := containers_valid_of_groups P HP p D HPD.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hsu := vgr_sort _ _ Hvg.
  Let Hl := vgr_lookup _ _ Hvg.
  Let Hass := vgr_ass _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := vid_uparams _ HD.

  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).

  (** The uniform parameters. *)
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Let τU := sb_of_list Id Us.

  Lemma gsub_U : gsub Γ τU (ind_uparams D ++ Γ).
  Proof. exact (gsub_closed_inst _ _ _ Ua Usem HΓ HUl HUs). Qed.

  (** The values of [Us] at related environments, related at the uniform
      parameters' telescope in the empty environment. *)
  Lemma us_vals : forall B1 B2, RΓ B1 B2 ->
      exists u1 u2, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 /\ ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 /\
        RU (env_args nil u1) (env_args nil u2).
  Proof.
    intros * HB.
    assert (Hev : forall k N, List.nth_error Us k = Some N -> (exists v, ⟦ N ⟧ B1 ↘ v) /\ (exists v, ⟦ N ⟧ B2 ↘ v)).
    { intros k N HN.
      destruct (nth_error_lt_some' (tele_insts (ind_uparams D) Id Us) k) as [T0 HT0].
      { rewrite length_tele_insts by exact Ua.
        assert (k < List.length Us) by (apply List.nth_error_Some; congruence); unfold ind_nu in HUl; lia. }
      destruct (rel_exp_under_ctx_simple_at HRΓ (HUs _ _ _ HN HT0) _ _ HB) as (v1 & v2 & E1 & E2 & _); eauto. }
    destruct (eval_exps_each Us B1 ltac:(intros; eapply Hev; eassumption)) as [u1 Hu1].
    destruct (eval_exps_each Us B2 ltac:(intros; eapply Hev; eassumption)) as [u2 Hu2].
    exists u1, u2; split; [ exact Hu1 | split; [ exact Hu2 |] ].
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id B1) Hu1) as Hτ1.
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id B2) Hu2) as Hτ2.
    destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
    pose proof (rel_sub_under_ctx_at' (gsub_valid gsub_U) HRΓ HRUΓ _ _ _ _ HB Hτ1 Hτ2) as H12.
    apply (Hres _ _ HRU HRUΓ) in H12.
    pose proof (eval_exps_length _ _ _ Hu1) as L1; pose proof (eval_exps_length _ _ _ Hu2) as L2.
    eapply closed_env_base; [ exact Ua | exact Usem | exact HRU | rewrite L1; exact HUl | rewrite L2; exact HUl | exact H12 ].
  Qed.

  (** The values of [Us] weakened past a telescope, related to those at the
      telescope's base. *)
  Lemma us_wk_vals : forall Ψ RS B zs, EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ RS -> ⊨ Ψ ++ Γ ->
      RS (env_args B zs) (env_args B zs) -> List.length zs = List.length Ψ ->
      exists w u, ⟦ List.map (fun U => U[wk_shiftn (List.length Ψ)]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B zs ↘ w /\
        ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u /\ RU (env_args nil w) (env_args nil u).
  Proof.
    intros * HRS HS HE Hlz.
    pose proof (rel_wk_under_ctx_shiftn _ _ HS) as Hwkj.
    pose proof (rel_wk_shiftn _ _ _ _ HRS HRΓ) as Hwk.
    assert (HB : RΓ B B) by (pose proof (rel_wk_app _ _ _ Hwk _ _ HE) as H; rewrite <- Hlz, eval_wk_shiftn_args in H; exact H).
    destruct (us_vals B B HB) as (u & _ & Hu & _ & _).
    assert (Hev : forall k N, List.nth_error (List.map (fun U => U[wk_shiftn (List.length Ψ)]ʷ) Us) k = Some N ->
               exists v, ⟦ N ⟧ env_args B zs ↘ v).
    { intros k N HN; apply nth_error_map_inv in HN as (N0 & HN0 & ->).
      destruct (nth_error_lt_some' (tele_insts (ind_uparams D) Id Us) k) as [T0 HT0].
      { rewrite length_tele_insts by exact Ua.
        assert (k < List.length Us) by (apply List.nth_error_Some; congruence); unfold ind_nu in HUl; lia. }
      pose proof (rel_exp_under_ctx_wk Hwkj (HUs _ _ _ HN0 HT0)) as HW.
      destruct (rel_exp_under_ctx_simple_at HRS HW _ _ HE) as (v1 & _ & E1 & _); eauto. }
    destruct (eval_exps_each _ _ Hev) as [w Hw].
    exists w, u; split; [ exact Hw | split; [ exact Hu |] ].
    destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
    pose proof (gsub_valid gsub_U) as [R1 H1 R2 H2 Hσ].
    destruct (Hσ _ _ HRS _ (proj2 (rel_wk_morphism _ _ _ (reflexivity _) _ _ (per_ctx_env_right_irrel _ _ _ _ _ H1 HRΓ)) Hwk) _ _ HE)
      as [y1 y2 y3 y4 Hy1 Hy2 Hy3 Hy4 Hch].
    assert (Hev1 : ⟦ sb_wk τU (wk_shiftn (List.length Ψ)) ⟧s env_args B zs ↘ env_args B w).
    { apply eval_sb_wk_of_list; [| exact Hw ].
      pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length Ψ)) (env_args B zs) (wk_mono_shiftn _)) as H.
      rewrite <- Hlz, eval_wk_shiftn_args in H; rewrite <- Hlz; intros x; exact (H x). }
    assert (Hev2 : ⟦ τU ⟧s B ↘ env_args B u) by exact (eval_sb_of_list _ _ _ _ _ (eval_sub_id B) Hu).
    rewrite <- Hlz, eval_wk_shiftn_args in Hy2.
    rewrite <- Hlz in Hy1.
    assert (E1 : env_eq y1 (env_args B w)) by (eapply functional_eval_sub; [ exact Hy1 | rewrite Hlz; exact Hev1 ]).
    assert (E2 : env_eq y2 (env_args B u)) by (eapply functional_eval_sub; eassumption).
    assert (E : R2 <~> RUΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct Hch as (H12 & _).
    apply E in H12.
    pose proof (per_ctx_env_resp_env_eq HRUΓ _ _ _ _ E1 E2 H12) as H12'.
    apply (Hres _ _ HRU HRUΓ) in H12'.
    pose proof (eval_exps_length _ _ _ Hw) as L1; pose proof (eval_exps_length _ _ _ Hu) as L2.
    rewrite List.length_map in L1.
    eapply closed_env_base; [ exact Ua | exact Usem | exact HRU | rewrite L1; exact HUl | rewrite L2; exact HUl | exact H12' ].
  Qed.

  (** The uniform parameters' values, as arguments of their telescope. *)
  Lemma U_gargs : forall a b, RU (env_args nil a) (env_args nil b) -> List.length a = ind_nu D -> List.length b = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil a b.
  Proof. intros * H La Lb; exact (uparams_of_env D HD Hc a b RU HRU La Lb H). Qed.

  (** ** The Canonical Uniform Parameters

      The values [u0] of [Us] at an environment [C1] of [Γ]: the canonical
      relations of the group there, [G] its elements. *)
  Section Base.
    Variable (C1 : env) (u0 : list domain).
    Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).

    Lemma u0_len : List.length u0 = ind_nu D.
    Proof. rewrite (eval_exps_length _ _ _ HUC); exact HUl. Qed.

    Lemma u0_env : RU (env_args nil u0) (env_args nil u0).
    Proof.
      destruct (us_vals C1 C1 HC11) as (u1 & u2 & Hu1 & Hu2 & H12).
      pose proof (functional_eval_exps' _ _ _ _ Hu1 HUC) as ->; pose proof (functional_eval_exps' _ _ _ _ Hu2 HUC) as ->.
      exact H12.
    Qed.

    Lemma u0_gargs : per_gargs (List.rev (ind_uparams D)) nil nil u0 u0.
    Proof. exact (U_gargs _ _ u0_env u0_len u0_len). Qed.

    Let nr := canon_nparams_rel D u0.
    Let ar := canon_args_rel D u0.
    Let dr := canon_doms_rel u0.
    Let Hcp : ind_canon_props D u0 := vg_canon p D Hvg u0 u0_gargs u0_len.
    Let HnP := icp_np_per _ _ Hcp.
    Let HnI := icp_np_iff _ _ Hcp.
    Let HaP := icp_arg_per _ _ Hcp.
    Let HaI := icp_arg_iff _ _ Hcp.
    Let HdP := icp_dom_per _ _ Hcp.
    Let HdI := icp_dom_iff _ _ Hcp.
    Let Had : adm_uparams D u0 nr ar dr u0 := vg_adm p D Hvg u0 u0 u0_gargs u0_len u0_gargs.
    Let G := grp_rel p D u0 nr ar dr.

    (** The environments related to [C1]: their values of [Us] are related
        to [u0], so admissible beside it. *)
    Lemma us_class : forall B, RΓ B C1 -> exists u, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u /\ RU (env_args nil u) (env_args nil u0).
    Proof.
      intros B HB1; destruct (us_vals B C1 HB1) as (u & u' & Hu & Hu' & H).
      pose proof (functional_eval_exps' _ _ _ _ Hu' HUC) as ->; eauto.
    Qed.

    Lemma adm_of_ru : forall w, RU (env_args nil w) (env_args nil u0) -> List.length w = ind_nu D -> adm_uparams D u0 nr ar dr w.
    Proof.
      intros w H Lw.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      exact (vg_adm p D Hvg u0 w u0_gargs u0_len (U_gargs _ _ (symmetry H) u0_len Lw)).
    Qed.

    (** A closed telescope's environment over the values of the uniform
        parameters at an environment, against the canonical one. *)
    Lemma closed_pre_base : forall Pre RK, tele_ass (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
        EF Pre ++ ind_uparams D ≈ Pre ++ ind_uparams D ∈ per_ctx_env ↘ RK ->
        forall B u zs, RU (env_args nil u) (env_args nil u0) -> List.length u = ind_nu D ->
        per_gargs (List.rev Pre) (env_args nil u0) (env_args nil u0) zs zs -> List.length zs = List.length Pre ->
        RK (env_args (env_args B u) zs) (env_args nil (u0 ++ zs)).
    Proof.
      intros * HKa HK HRK * H10 Lu1 Hg00 Lz0.
      assert (HPa : tele_ass Pre) by (apply List.Forall_app in HKa as [H _]; exact H).
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      pose proof (U_gargs _ _ H10 Lu1 u0_len) as Hg10.
      assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK).
      pose proof (per_gargs_base _ _ _ HRU HKr (List.Forall_rev HPa) (env_args nil u0) (env_args nil u0)
                    (env_args nil u) (env_args nil u0) zs zs u0_env (symmetry H10) u0_env Hg00) as Hgb.
      rewrite <- env_args_app.
      eapply (closed_env_base _ _ _ _ nil nil); [ exact HKa | exact HK | exact HRK
                                                | rewrite !List.length_app; unfold ind_nu in Lu1; lia
                                                | rewrite !List.length_app; pose proof u0_len as L0; unfold ind_nu in L0; lia |].
      apply (gargs_env_rel _ _ _ _ _ _ HRK HK); [ rewrite !List.length_app; unfold ind_nu in Lu1; lia |].
      rewrite List.rev_app_distr; apply per_gargs_app_intro;
        [ rewrite List.length_rev; exact Lu1 | exact Hg10 | exact Hgb ].
    Qed.

    (** ** Instances of a Closed Telescope

        Arguments related at a closed telescope over the canonical uniform
        parameters are related at its instance, over any related
        environments whose uniform parameters are related to the canonical
        ones, and conversely. *)
    Lemma cv_gen : forall Pre, tele_ass (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D -> ⊨ tele_sub Pre τU ++ Γ ->
        forall B1 B2 u1 u2, RΓ B1 B2 ->
        ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 ->
        RU (env_args nil u1) (env_args nil u0) -> RU (env_args nil u2) (env_args nil u0) ->
        forall zs zs', per_gargs (List.rev Pre) (env_args nil u0) (env_args nil u0) zs zs' -> List.length zs = List.length Pre ->
          per_gargs (List.rev (tele_sub Pre τU)) B1 B2 zs zs'.
    Proof.
      induction Pre as [| e Pre IH]; intros HKa HK HS * HB Hu1 Hu2 H10 H20 zs zs' Hg Hlz.
      - destruct zs; cbn in Hlz; [| discriminate ]; inversion Hg; subst; constructor.
      - assert (He : exists A, e = ce_ass A) by (inversion HKa as [| ? ? He _]; exact He).
        destruct He as [X ->].
        assert (HKa' : tele_ass (Pre ++ ind_uparams D)) by (inversion HKa; assumption).
        assert (HPa : tele_ass Pre) by (apply List.Forall_app in HKa' as [H _]; exact H).
        pose proof (eval_exps_length _ _ _ Hu1) as Lu1; rewrite HUl in Lu1.
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        destruct (List.exists_last (l := zs) ltac:(intros ->; cbn in Hlz; discriminate)) as (zs0 & x & ->).
        rewrite List.length_app in Hlz; cbn in Hlz.
        assert (Lz0 : List.length zs0 = List.length Pre) by lia; clear Hlz.
        pose proof (per_gargs_length _ _ _ _ _ Hg) as [Lzz _].
        rewrite List.length_app in Lzz; cbn [List.length] in Lzz.
        destruct (List.exists_last (l := zs') ltac:(intros ->; cbn in Lzz; lia)) as (zs0' & x' & ->).
        rewrite List.length_app in Lzz; cbn in Lzz.
        cbn [List.rev] in Hg.
        assert (Lr : List.length zs0 = List.length (List.rev Pre)) by (rewrite List.length_rev; exact Lz0).
        assert (Lr' : List.length zs0' = List.length (List.rev Pre)) by (rewrite List.length_rev; lia).
        destruct (per_gargs_app (List.rev Pre) (ce_ass X :: nil) _ _ zs0 zs0' (x :: nil) (x' :: nil) Lr Hg Lr') as [Hg0 Hgx].
        inversion Hgx as [| ? ? ? ? ? ? ? ? ? R0 HX0 Hx _]; subst.
        cbn [tele_sub centry_sub List.rev List.app] in HS |- *.
        destruct (rel_ctx_wf_ass_inv HS) as [j HXi].
        pose proof (rel_ctx_wf_tail HS) as HS'.
        destruct (rel_ctx_wf_ass_inv HK) as [j' HXc].
        pose proof (rel_ctx_wf_tail HK) as HK'.
        pose proof (IH HKa' HK' HS' _ _ _ _ HB Hu1 Hu2 H10 H20 _ _ Hg0 Lz0) as IHz.
        destruct (rel_ctx_wf_per_ctx_env HS') as [RS HRS].
        assert (HE : RS (env_args B1 zs0) (env_args B2 zs0'))
          by (eapply gargs_env_rel_gen; [ exact HRΓ | exact HRS | exact HS' | exact HB | rewrite length_tele_sub; exact Lz0 | exact IHz ]).
        destruct (rel_exp_of_typ_inversion_simple_at HRS HXi _ _ HE) as (t1 & t2 & Et1 & Et2 & [R12 HR12]).
        assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
        assert (HEE : RS (env_args B1 zs0) (env_args B1 zs0)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
        destruct (rel_ctx_wf_per_ctx_env HK') as [RK HRK].
        assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK').
        pose proof (per_gargs_refl_l _ _ _ HRU HKr (List.Forall_rev HPa) (env_args nil u0) (env_args nil u0) zs0 zs0' u0_env Hg0) as Hg00.
        pose proof (closed_pre_base Pre RK HKa' HK' HRK B1 u1 zs0 H10 Lu1 Hg00 Lz0) as HK1.
        destruct (closed_typ_inst Pre (ind_uparams D) Γ X j' τU RΓ RK RS B1 zs0 (env_args B1 u1) (env_args nil (u0 ++ zs0))
                    HKa' HK' Ua Usem HΓ HRΓ HRK HRS HXc (gsub_valid gsub_U) HEE Lz0
                    (eval_sb_of_list _ _ _ _ _ (eval_sub_id B1) Hu1) HK1)
          as (a & c & Ea & Ec & [R1c HR1c]).
        assert (a = t1) as -> by (eapply functional_eval_exp; eassumption).
        destruct HX0 as [c0 c0' Ec0 Ec0' HR0].
        rewrite <- env_args_app in Ec0.
        assert (c0 = c) as -> by (eapply functional_eval_exp; eassumption).
        assert (E1 : R12 <~> R1c) by (eapply per_univ_elem_right_irrel; [ exact HR12 | exact HR1c ]).
        assert (E2 : R1c <~> R0) by (eapply per_univ_elem_chain_iff; [ exact HR1c | exact HR0 ]).
        destruct (per_univ_elem_to_nat _ _ _ _ HR12) as [n Hn].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R12).
        + rewrite List.length_rev, length_tele_sub; exact Lz0.
        + exact IHz.
        + exact (mk_rel_mod_eval t1 t2 Et1 Et2 Hn).
        + apply E1, E2; exact Hx.
    Qed.

    Lemma cv_gen_rev : forall Pre, tele_ass (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D -> ⊨ tele_sub Pre τU ++ Γ ->
        forall B1 B2 u1, RΓ B1 B2 ->
        ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> RU (env_args nil u1) (env_args nil u0) ->
        forall zs zs', per_gargs (List.rev (tele_sub Pre τU)) B1 B2 zs zs' -> List.length zs = List.length Pre ->
          per_gargs (List.rev Pre) (env_args nil u0) (env_args nil u0) zs zs'.
    Proof.
      induction Pre as [| e Pre IH]; intros HKa HK HS * HB Hu1 H10 zs zs' Hg Hlz.
      - destruct zs; cbn in Hlz; [| discriminate ]; inversion Hg; subst; constructor.
      - assert (He : exists A, e = ce_ass A) by (inversion HKa as [| ? ? He _]; exact He).
        destruct He as [X ->].
        assert (HKa' : tele_ass (Pre ++ ind_uparams D)) by (inversion HKa; assumption).
        assert (HPa : tele_ass Pre) by (apply List.Forall_app in HKa' as [H _]; exact H).
        pose proof (eval_exps_length _ _ _ Hu1) as Lu1; rewrite HUl in Lu1.
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        destruct (List.exists_last (l := zs) ltac:(intros ->; cbn in Hlz; discriminate)) as (zs0 & x & ->).
        rewrite List.length_app in Hlz; cbn in Hlz.
        assert (Lz0 : List.length zs0 = List.length Pre) by lia; clear Hlz.
        pose proof (per_gargs_length _ _ _ _ _ Hg) as [Lzz _].
        rewrite List.length_app in Lzz; cbn [List.length] in Lzz.
        destruct (List.exists_last (l := zs') ltac:(intros ->; cbn in Lzz; lia)) as (zs0' & x' & ->).
        rewrite List.length_app in Lzz; cbn in Lzz.
        cbn [tele_sub centry_sub List.rev List.app] in HS, Hg |- *.
        assert (Lr : List.length zs0 = List.length (List.rev (tele_sub Pre τU))) by (rewrite List.length_rev, length_tele_sub; exact Lz0).
        assert (Lr' : List.length zs0' = List.length (List.rev (tele_sub Pre τU))) by (rewrite List.length_rev, length_tele_sub; lia).
        destruct (per_gargs_app (List.rev (tele_sub Pre τU)) _ _ _ zs0 zs0' (x :: nil) (x' :: nil) Lr Hg Lr') as [Hg0 Hgx].
        inversion Hgx as [| ? ? ? ? ? ? ? ? ? R0 HX0 Hx _]; subst.
        destruct (rel_ctx_wf_ass_inv HS) as [j HXi].
        pose proof (rel_ctx_wf_tail HS) as HS'.
        destruct (rel_ctx_wf_ass_inv HK) as [j' HXc].
        pose proof (rel_ctx_wf_tail HK) as HK'.
        pose proof (IH HKa' HK' HS' _ _ _ HB Hu1 H10 _ _ Hg0 Lz0) as IHz.
        destruct (rel_ctx_wf_per_ctx_env HS') as [RS HRS].
        assert (HE : RS (env_args B1 zs0) (env_args B2 zs0'))
          by (eapply gargs_env_rel_gen; [ exact HRΓ | exact HRS | exact HS' | exact HB | rewrite length_tele_sub; exact Lz0 | exact Hg0 ]).
        assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
        assert (HEE : RS (env_args B1 zs0) (env_args B1 zs0)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
        destruct (rel_ctx_wf_per_ctx_env HK') as [RK HRK].
        assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
        assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK').
        pose proof (per_gargs_refl_l _ _ _ HRU HKr (List.Forall_rev HPa) (env_args nil u0) (env_args nil u0) zs0 zs0' u0_env IHz) as Hg00.
        pose proof (closed_pre_base Pre RK HKa' HK' HRK B1 u1 zs0 H10 Lu1 Hg00 Lz0) as HK1.
        destruct (closed_typ_inst Pre (ind_uparams D) Γ X j' τU RΓ RK RS B1 zs0 (env_args B1 u1) (env_args nil (u0 ++ zs0))
                    HKa' HK' Ua Usem HΓ HRΓ HRK HRS HXc (gsub_valid gsub_U) HEE Lz0
                    (eval_sb_of_list _ _ _ _ _ (eval_sub_id B1) Hu1) HK1)
          as (a & c & Ea & Ec & [R1c HR1c]).
        destruct HX0 as [a0 a0' Ea0 Ea0' HR0].
        assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
        (** The closed entry at the two canonical prefixes. *)
        assert (HKK : RK (env_args nil (u0 ++ zs0)) (env_args nil (u0 ++ zs0'))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRK HK'); [ rewrite !List.length_app; pose proof u0_len as L0; unfold ind_nu in L0; lia |].
          rewrite List.rev_app_distr; apply per_gargs_app_intro;
            [ rewrite List.length_rev; exact u0_len | exact u0_gargs | exact IHz ]. }
        destruct (rel_exp_of_typ_inversion_simple_at HRK HXc _ _ HKK) as (c1 & c1' & Ec1 & Ec1' & [Rc HRc]).
        assert (c1 = c) as -> by (eapply functional_eval_exp; eassumption).
        assert (E1 : R0 <~> R1c) by (eapply per_univ_elem_right_irrel; [ exact HR0 | exact HR1c ]).
        assert (E2 : R1c <~> Rc) by (eapply per_univ_elem_chain_iff; [ exact HR1c | exact HRc ]).
        destruct (per_univ_elem_to_nat _ _ _ _ HRc) as [n Hn].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n Rc).
        + rewrite List.length_rev; exact Lz0.
        + exact IHz.
        + rewrite env_args_app in Ec1, Ec1'; exact (mk_rel_mod_eval c c1' Ec1 Ec1' Hn).
        + apply E2, E1; exact Hx.
    Qed.

    (** ** A Member's Motive Context

        The member [k]'s non-uniform parameters at [Us], and its type
        there: related at the canonical relations, read through the closed
        telescope of its parameters. *)
    Section Member.
      Variable (k : nat) (Mk : imember).
      Hypothesis (HMk : ind_member D k = Some Mk).
      Hypothesis (HMm : ⊨ elim_mctx p D k Mk Us ++ Γ).
      Let T := List.rev (im_nparams Mk).
      Let IT := ind_mty p D k (List.map (fun U => U[wk_shiftn (im_nn Mk)]ʷ) Us) (vars_from 0 (im_nn Mk)).

      Lemma mctx_split : elim_mctx p D k Mk Us ++ Γ = (tele_sub (im_nparams Mk) τU ++ Γ) ▹ IT.
      Proof. reflexivity. Qed.

      Lemma m_HNt : ⊨ tele_sub (im_nparams Mk) τU ++ Γ.
      Proof. exact (rel_ctx_wf_tail HMm). Qed.

      Lemma m_Pa : tele_ass (im_nparams Mk ++ ind_uparams D).
      Proof. exact (member_params_ass D Hc _ _ HMk). Qed.

      Lemma m_Ps : ⊨ im_nparams Mk ++ ind_uparams D.
      Proof. exact (vid_params _ HD _ _ HMk). Qed.

      Lemma m_T_len : List.length T = im_nn Mk.
      Proof. unfold T; rewrite List.length_rev; reflexivity. Qed.

      (** Canonically related non-uniform parameters are related at their
          closed telescope at [u0], and conversely. *)
      Lemma nparams_closed_of_canon : forall ns ns', tele_rel (nr k) T ns ns' ->
          per_gargs (List.rev (im_nparams Mk)) (env_args nil u0) (env_args nil u0) ns ns'.
      Proof.
        intros * Hns.
        destruct (sort_value D HD u0 u0_gargs u0_len) as [a0 Ha0].
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        pose proof (nr_gargs D HD Hc Hsu k Mk HMk u0 u0 a0 u0_gargs u0_len Ha0 (im_nn Mk) ns ns' (le_n _)
                      ltac:(apply tele_rel_pre in Hns; rewrite m_T_len in Hns; exact Hns)) as H.
        rewrite List.firstn_all2 in H by (rewrite List.length_rev; reflexivity); exact H.
      Qed.

      Lemma canon_of_nparams_closed : forall ns ns', List.length ns = im_nn Mk ->
          per_gargs (List.rev (im_nparams Mk)) (env_args nil u0) (env_args nil u0) ns ns' -> tele_rel (nr k) T ns ns'.
      Proof.
        intros * Ln Hg0.
        refine (gargs_tele_canon T (nr k) (env_args nil u0) _ (env_args nil u0) ns ns' Hg0 ltac:(rewrite m_T_len; exact Ln)).
        intros j A pre HA.
        unfold nr, canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HMk HA), <- env_args_app; reflexivity.
      Qed.

      Lemma cv_nparams : forall B1 B2 u1 u2, RΓ B1 B2 ->
          ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 ->
          RU (env_args nil u1) (env_args nil u0) -> RU (env_args nil u2) (env_args nil u0) ->
          forall ns ns', tele_rel (nr k) T ns ns' ->
          per_gargs (List.rev (tele_sub (im_nparams Mk) τU)) B1 B2 ns ns'.
      Proof.
        intros * HB Hu1 Hu2 H10 H20 * Hns.
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        exact (cv_gen (im_nparams Mk) m_Pa m_Ps m_HNt B1 B2 u1 u2 HB Hu1 Hu2 H10 H20 ns ns'
                 (nparams_closed_of_canon _ _ Hns) ltac:(rewrite m_T_len in Ln; rewrite length_im_nparams; exact Ln)).
      Qed.

      Lemma cv_nparams_rev : forall B1 B2 u1, RΓ B1 B2 ->
          ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> RU (env_args nil u1) (env_args nil u0) ->
          forall ns ns', List.length ns = im_nn Mk ->
          per_gargs (List.rev (tele_sub (im_nparams Mk) τU)) B1 B2 ns ns' -> tele_rel (nr k) T ns ns'.
      Proof.
        intros * HB Hu1 H10 * Ln Hg0.
        apply canon_of_nparams_closed; [ exact Ln |].
        exact (cv_gen_rev (im_nparams Mk) m_Pa m_Ps m_HNt B1 B2 u1 HB Hu1 H10 ns ns' Hg0
                 ltac:(rewrite length_im_nparams; exact Ln)).
      Qed.

      (** The relation of the member's type at an environment of the class
          of [C1] and canonically related non-uniform parameters: the
          group's at [k], at the canonical bases. *)
      Lemma mctx_head_rel : forall B1 B2 u1, RΓ B1 B2 ->
          ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> RU (env_args nil u1) (env_args nil u0) ->
          forall RS, EF tele_sub (im_nparams Mk) τU ++ Γ ≈ tele_sub (im_nparams Mk) τU ++ Γ ∈ per_ctx_env ↘ RS ->
          forall ns ns', tele_rel (nr k) T ns ns' -> RS (env_args B1 ns) (env_args B1 ns) ->
          forall t1 t2 (i : uidx) R, ⟦ IT ⟧ env_args B1 ns ↘ t1 -> ⟦ IT ⟧ env_args B2 ns' ↘ t2 ->
          DF t1 ≈ t2 ∈ per_univ_elem i ↘ R -> (R <~> G k u0 u0 ns ns').
      Proof.
        intros * HB Hu1 H10 RS HRS * Hns HEE * Et1 Et2 HR.
        destruct (sort_value D HD u0 u0_gargs u0_len) as [a0 Ha0].
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        pose proof (eval_exps_length _ _ _ Hu1) as Lu1; rewrite HUl in Lu1.
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & Ln' & _).
        rewrite m_T_len in Ln, Ln'.
        destruct (rel_ctx_wf_per_ctx_env m_Ps) as [RK HRK].
        assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
        destruct (mty_vars_valid p D Hvg Hcv k Mk HMk) as [jx HX].
        (** The closed side. *)
        pose proof (params_gargs D HD Hc Hsu k Mk HMk u0 u0 a0 ns ns' u0_gargs u0_len Ha0 Hns) as Hgc.
        assert (HKc : RK (env_args nil (u0 ++ ns)) (env_args nil (u0 ++ ns'))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRK m_Ps); [| exact Hgc ].
          rewrite !List.length_app, length_im_nparams; pose proof u0_len as L0; unfold ind_nu in L0; lia. }
        destruct (rel_exp_of_typ_inversion_simple_at HRK HX _ _ HKc) as (c1 & c2 & Ec1 & Ec2 & [Rc HRc]).
        assert (Ev : forall zs, List.length zs = im_nn Mk -> ⟦ vars_from 0 (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ zs) ↘ zs).
        { intros zs Lz; rewrite env_args_app.
          pose proof (eval_vars_from_args zs (env_args nil u0) nil) as H; rewrite List.app_nil_r in H; cbn [List.length] in H.
          rewrite Lz in H; exact H. }
        pose proof (member_type_rel P p D HP HPD k Mk u0 u0 (im_nparams Mk) RK ns ns' (im_nn Mk) 0 (vars_from 0 (im_nn Mk))
                      ns ns' c1 c2 jx Rc HMk u0_len u0_gargs m_Ps HRK ltac:(rewrite length_im_nparams; exact Ln)
                      ltac:(rewrite length_im_nparams; exact Ln') ltac:(cbn; lia) HKc (Ev _ Ln) (Ev _ Ln') Ec1 Ec2 HRc) as ERc.
        (** The left side, against the closed one. *)
        assert (Hg00 : per_gargs (List.rev (im_nparams Mk)) (env_args nil u0) (env_args nil u0) ns ns)
          by exact (nparams_closed_of_canon _ _ (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk _ _ Hns)).
        pose proof (closed_pre_base (im_nparams Mk) RK m_Pa m_Ps HRK B1 u1 ns H10 Lu1 Hg00
                      ltac:(rewrite length_im_nparams; exact Ln)) as HK1.
        destruct (closed_typ_inst (im_nparams Mk) (ind_uparams D) Γ _ jx τU RΓ RK RS B1 ns (env_args B1 u1)
                    (env_args nil (u0 ++ ns)) m_Pa m_Ps Ua Usem HΓ HRΓ HRK HRS HX (gsub_valid gsub_U) HEE
                    ltac:(rewrite length_im_nparams; exact Ln) (eval_sb_of_list _ _ _ _ _ (eval_sub_id B1) Hu1) HK1)
          as (a & c & Ea & Ec & [R1c HR1c]).
        unfold τU in Ea; rewrite length_im_nparams, (mty_vars_inst p D k Mk Us Hc HUl) in Ea; fold IT in Ea.
        assert (a = t1) as -> by (eapply functional_eval_exp; eassumption).
        assert (c = c1) as -> by (eapply functional_eval_exp; eassumption).
        assert (E1 : R <~> R1c) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HR1c ]).
        assert (E2 : R1c <~> Rc) by (eapply per_univ_elem_chain_iff; [ exact HR1c | exact HRc ]).
        etransitivity; [ exact E1 | etransitivity; [ exact E2 | exact ERc ] ].
      Qed.

      (** The motive's context at two environments of the class of [C1],
          at canonically related non-uniform parameters and elements of
          the member at any bases. *)
      Lemma cv_mctx : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
          forall RM, EF elim_mctx p D k Mk Us ++ Γ ≈ elim_mctx p D k Mk Us ++ Γ ∈ per_ctx_env ↘ RM ->
          forall ns ns' u u' m m', tele_rel (nr k) T ns ns' -> G k u u' ns ns' m m' ->
            RM (env_args B1 (ns ++ m :: nil)) (env_args B2 (ns' ++ m' :: nil)).
      Proof.
        intros * HB1 HB2 RM HRM * Hns Hm.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        assert (HB : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
        destruct (us_class B1 HB1) as (u1 & Hu1 & H10); destruct (us_class B2 HB2) as (u2 & Hu2 & H20).
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _); rewrite m_T_len in Ln.
        pose proof (cv_nparams B1 B2 u1 u2 HB Hu1 Hu2 H10 H20 ns ns' Hns) as Hg.
        assert (LNt : List.length (tele_sub (im_nparams Mk) τU) = im_nn Mk) by (rewrite length_tele_sub; reflexivity).
        pose proof HMm as HM'; rewrite mctx_split in HM'.
        destruct (rel_ctx_wf_ass_inv HM') as [j HIT].
        destruct (rel_ctx_wf_per_ctx_env m_HNt) as [RN HRN].
        assert (HPN : PER RN) by (eapply per_env_PER; exact HRN).
        assert (HE : RN (env_args B1 ns) (env_args B2 ns'))
          by (eapply gargs_env_rel_gen; [ exact HRΓ | exact HRN | exact m_HNt | exact HB | lia | exact Hg ]).
        assert (HEE : RN (env_args B1 ns) (env_args B1 ns)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
        destruct (rel_exp_of_typ_inversion_simple_at HRN HIT _ _ HE) as (t1 & t2 & Et1 & Et2 & [R12 HR12]).
        pose proof (mctx_head_rel B1 B2 u1 HB Hu1 H10 RN HRN ns ns' Hns HEE t1 t2 j R12 Et1 Et2 HR12) as ER.
        eapply gargs_env_rel_gen; [ exact HRΓ | exact HRM | exact HMm | exact HB | rewrite List.length_app, length_elim_mctx; cbn; lia |].
        unfold elim_mctx; cbn [List.rev].
        destruct (per_univ_elem_to_nat _ _ _ _ HR12) as [n Hn].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R12);
          [ rewrite List.length_rev, length_tele_sub; exact Ln | exact Hg | exact (mk_rel_mod_eval _ _ Et1 Et2 Hn) |].
        apply ER.
        exact (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k u u' u0 u0 ns ns' m m' Had Had Had Hm).
      Qed.
    End Member.

    Let tsym := nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI.
    Let ttrans := nparams_rel_trans p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI.
    Let trefl_l := nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI.
    Let trefl_r := nparams_rel_refl_r p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI.
    Let isym := proj1 (ind_rel_sym_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr)).
    Let iidx := ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr).
    Let ins := ind_rel_ns p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr).

    (** ** The Motives

        The motives of the blocks [Bks], each in its member's context, and
        their family [Rel] between [C1] and an environment [C2] related to
        it: the head relation of the motive at the two extended
        environments. *)
    Section Motives.
      Variable (C2 : env).
      Hypothesis (HC12 : RΓ C1 C2).
      Variable (Bks : list eblock) (iA : nat).
      Hypothesis (HBks : forall j Mj, ind_member D j = Some Mj -> exists b, List.nth_error Bks j = Some b).
      Hypothesis (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ).
      Hypothesis (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
                    elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@iA).
      Let Rel := fun j ns m ns' m' =>
        per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
          (env_args C1 (ns ++ m :: nil)) (env_args C2 (ns' ++ m' :: nil)).

      Lemma mctx_at : forall j Mj, ind_member D j = Some Mj -> forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
          forall RM, EF elim_mctx p D j Mj Us ++ Γ ≈ elim_mctx p D j Mj Us ++ Γ ∈ per_ctx_env ↘ RM ->
          forall u u' ns ns' m m', G j u u' ns ns' m m' ->
            RM (env_args B1 (ns ++ m :: nil)) (env_args B2 (ns' ++ m' :: nil)).
      Proof.
        intros * HMj * HB1 HB2 RM HRM * Hm.
        exact (cv_mctx j Mj HMj (HMall _ _ HMj) B1 B2 HB1 HB2 RM HRM ns ns' u u' m m' (ins _ _ _ _ _ _ _ _ HMj Hm) Hm).
      Qed.

      (** The family at related elements does not depend on their
          indices, nor on their bases. *)
      Lemma rel_move : forall j Mj, ind_member D j = Some Mj -> forall u u' ns ns' m m' ns1 ns1',
          G j u u' ns ns' m m' ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns1 -> tele_rel (nr j) (List.rev (im_nparams Mj)) ns' ns1' ->
          (Rel j ns m ns' m' <~> Rel j ns1 m ns1' m').
      Proof.
        intros * HMj * Hm H1 H1'.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        destruct (HBks j Mj HMj) as [b Hb].
        assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
        pose proof (ins _ _ _ _ _ _ _ _ HMj Hm) as Hn.
        pose proof (isym _ _ _ _ _ _ _ Hm) as Hms.
        pose proof (trefl_r _ _ HMj _ _ Hn) as Hn'n'.
        pose proof (iidx _ _ _ _ _ _ _ _ _ _ HMj Hms Hn'n' H1) as Hm2.
        pose proof (iidx _ _ _ _ _ _ _ _ _ _ HMj Hm H1 H1') as Hm3.
        destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
        unfold Rel; rewrite (blocks_motives_nth _ _ _ Hb).
        apply (per_head_of_typ_resp HRM (HAv _ _ _ HMj Hb)).
        apply rel_chain_cons; [ exact (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm) |].
        apply rel_chain_cons; [ exact (mctx_at j Mj HMj C2 C1 HC21 HC11 RM HRM _ _ _ _ _ _ Hm2) |].
        apply rel_chain_of_pair; exact (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm3).
      Qed.
    End Motives.
  End Base.
End GroupElim.

End Fixed_GCtx.
