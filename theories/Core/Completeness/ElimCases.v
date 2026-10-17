(** * The Eliminator of an Inductive Type

    The motive of an elimination lives in its context extended by the
    non-uniform parameters and the scrutinee ([elim_mctx]), each branch in
    the context extended by the non-uniform parameters, the arguments and
    the recursive results of its constructor ([elim_bctx]).  The types of
    these telescopes are the declaration's, instantiated at the uniform
    parameters [Us] of the elimination.

    The canonical relations of the PER clause of the inductive type read
    these types in the empty environment, at the values of [Us]; this file
    first relates the two readings ([cv_nparams], [cv_mctx], [cv_bctx]), and
    then instantiates the eliminator's model ([per_ind_elim_all]) at the
    three links of the judgment's chain. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping IndSyntax GlobalPresup IndTyping MemberLemmas.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases GlobalArgs MemberReps
  VariableCases FunctionCases LevelCases IndSem TeleSem IndCases SubtypingCases.
From Mctt.Core.Semantic Require Import Realizability IndPER IndElim Evaluation.Modules.
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
  intros * [env_rel [HΓ' [env_relo [HΓA Hσ]]]].
  exists env_rel, HΓ', env_relo, HΓA.
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

Lemma ind_args_rel_len : forall p D ups nr ar dr pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
    List.length vs = List.length gs /\ List.length vs' = List.length gs.
Proof. induction 1; cbn; lia. Qed.

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
  -
    replace (List.length Φ + (List.length Δ - 1 - k)) with (0 + List.length (Φ ++ tele_sub (List.rev l2) (sb_qn (S k) ρ)))
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

(** ** Related Inductive Types Have Related Non-Uniform Parameters *)
Lemma ind_univ_inv : forall i R p D w w' X Y, DF d_ind p (w ++ X) ≈ d_ind p (w' ++ Y) ∈ per_univ_elem i ↘ R ->
    List.length w = ind_nu D -> List.length w' = ind_nu D -> ind_lookup gc_deps gc_stack p = Some D ->
    tele_full (ind_nr D w) (List.rev (ind_nparams D)) X Y.
Proof.
  intros * H Hw Hw' Hl.
  basic_invert_per_univ_elem H.
  match goal with H0 : ind_lookup _ _ _ = Some ?D0, H1 : ind_lookup _ _ _ = Some D |- _ => rewrite H1 in H0; injection H0 as <- end.
  destruct (app_split_eq _ _ _ _ x0 ltac:(congruence)) as [-> ->].
  destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
  eapply tele_full_map; [| eassumption ].
  intros k pa pb y y' Hk Hp _ Hr.
  destruct (nparams_lt_ass D k ltac:(assumption) Hk) as [A HA].
  match goal with Hn : forall k A vs vs', _ -> _ -> rel_mod_eval _ _ _ _ _ _ |- _ => destruct (Hn _ _ _ _ HA Hp) as [a a' Ea Ea' HR] end.
  unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA).
  destruct (per_univ_elem_sym _ _ _ _ HR) as [HRs _].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR HRs) as (Raa & HRaa & E).
  eapply per_head_of; [ exact Ea | exact Ea | exact HRaa | apply E; exact Hr ].
Qed.

(** ** The Recursive Results' Context *)
Lemma ihs_ctx_aux_app : forall D A Us na gs1 gs2 pat j,
    ihs_ctx_aux D A Us na pat j (gs1 ++ gs2)
    = ihs_ctx_aux D A Us na (cargs_pat gs1 ++ pat) (j + cargs_nrec gs1) gs2 ++ ihs_ctx_aux D A Us na pat j gs1.
Proof.
  induction gs1 as [| [B | Ps] gs1 IH]; intros; cbn [List.app ihs_ctx_aux cargs_nrec].
  - rewrite List.app_nil_r, Nat.add_0_r; reflexivity.
  - rewrite IH, cargs_pat_cons, <- List.app_assoc; reflexivity.
  - rewrite IH, cargs_pat_cons, <- !List.app_assoc; cbn [List.app].
    replace (S j + cargs_nrec gs1) with (j + S (cargs_nrec gs1)) by lia; reflexivity.
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

(** ** Recursive Results of Function Shapes

    The type of the recursive result of a recursive argument of a simple
    shape is a [Π] over the shape's domains of the motive at the end. *)
Lemma vars_from_S0 : forall n, vars_from 0 (S n) = a_var n :: vars_from 0 n.
Proof. intros; unfold vars_from; rewrite List.seq_S, List.rev_app_distr; reflexivity. Qed.

Lemma ihs_rel_len : forall ups dr Rel pre gs vs vs' ihs ihs', ihs_rel ups dr Rel pre gs vs vs' ihs ihs' ->
    List.length ihs = cargs_nrec gs /\ List.length ihs' = cargs_nrec gs.
Proof. induction 1; cbn; lia. Qed.

Lemma ihs_rel_at : forall ups dr Rel pre gs vs vs' ihs ihs', ihs_rel ups dr Rel pre gs vs vs' ihs ihs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists v v' ih ih', List.nth_error vs (List.length gs1) = Some v /\ List.nth_error vs' (List.length gs1) = Some v' /\
      List.nth_error ihs (cargs_nrec gs1) = Some ih /\ List.nth_error ihs' (cargs_nrec gs1) = Some ih' /\
      ih_rel ups dr Rel (pre ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t v v' ih ih'.
Proof.
  induction 1 as [pre | pre A gs v v' vs vs' ihs ihs' H IH | pre t0 gs v v' vs vs' ih ih' ihs ihs' Hr H IH];
    intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst.
  - destruct (IH _ _ _ eq_refl) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hr).
    exists x, x', y, y'; cbn; rewrite <- List.app_assoc in Hr; repeat split; assumption.
  - exists v, v', ih, ih'; cbn; rewrite List.app_nil_r; repeat split; assumption.
  - destruct (IH _ _ _ eq_refl) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hr0).
    exists x, x', y, y'; cbn; repeat split; assumption.
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

Lemma cargs_nrec_app : forall gs1 gs2, cargs_nrec (gs1 ++ gs2) = cargs_nrec gs1 + cargs_nrec gs2.
Proof. induction gs1 as [| [] gs1 IH]; intros; cbn; rewrite ?IH; lia. Qed.

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
Definition brs_sub (Bs : list (String.string * nat * exp)) (σ : sub) : list (String.string * nat * exp) :=
  List.map (fun b => (fst b, (snd b)[sb_qn (snd (fst b)) σ])) Bs.

Lemma brs_lookup_sub : forall Bs σ c n Ba, brs_lookup (brs_sub Bs σ) c = Some (n, Ba) ->
    exists B0, brs_lookup Bs c = Some (n, B0) /\ Ba = B0[sb_qn n σ].
Proof.
  induction Bs as [| [[c' n'] B'] Bs IH]; cbn; intros * H; [ discriminate |].
  destruct (String.eqb c c'); [ injection H as <- <-; eauto | eauto ].
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

(** The parameters of an elimination, split at the uniform ones. *)
Lemma params_valid_split : forall D Γ Ps, decl_closed D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T -> Γ ⊨ P : T) ->
    (forall k U T, List.nth_error (List.firstn (ind_nu D) Ps) k = Some U ->
       List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) k = Some T -> Γ ⊨ U : T) /\
    (forall k N T, List.nth_error (List.skipn (ind_nu D) Ps) k = Some N ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) k = Some T ->
       Γ ⊨ N : T).
Proof.
  intros * Hc Hl HPs.
  pose proof (decl_closed_nu D Hc) as Hle.
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; lia).
  assert (Hti : tele_insts (ind_params D) Id Ps
                = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                  ++ tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
  { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite params_split; apply tele_insts_app;
      [ apply (decl_uparams_ass D Hc) | rewrite HUl, length_ind_uparams by exact Hle; reflexivity ]. }
  assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
    by (rewrite length_tele_insts by apply (decl_uparams_ass D Hc); rewrite HUl, length_ind_uparams by exact Hle; lia).
  split; intros k N T HN HT.
  - apply (HPs k); [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HN |].
    rewrite Hti, List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HT.
  - apply (HPs (ind_nu D + k)).
    + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
      rewrite HUl; replace (ind_nu D + k - ind_nu D) with k by lia; exact HN.
    + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + k - ind_nu D) with k by lia; exact HT.
Qed.

(** ** The Constructors' Judgments, from the Declaration's

    The context of a constructor's arguments, and its type, are valid once
    the type former is: they are read off the declaration's own
    judgments. *)
(** ** Applying a Variable to the Variables of a Telescope *)
Lemma valid_app_here : forall Ψ A C (i : nat) M, ⊨ Ψ ▹ A -> Ψ ▹ A ⊨ C : Typeω@i -> Ψ ⊨ M : Π A C ->
    Ψ ▹ A ⊨ a_app M[wk_shift]ʷ (a_var 0) : C.
Proof.
  intros * HΨA HC HM.
  destruct (sem_ctx_ass_inv HΨA) as [j HA].
  pose proof (rel_wk_under_ctx_shift HΨA) as Hw.
  pose proof (rel_exp_under_ctx_wk Hw HM) as HMw; cbn [exp_wk] in HMw.
  pose proof (rel_exp_under_ctx_wk Hw HA) as HAw; cbn [exp_wk] in HAw.
  pose proof (rel_wk_under_ctx_q Hw HA) as Hwq.
  pose proof (rel_exp_under_ctx_wk Hwq HC) as HCw; cbn [exp_wk] in HCw.
  pose proof (valid_exp_var_here HΨA) as Hv.
  pose proof (rel_exp_app_cong (i := max i j) (rel_exp_cumu_ge (i := j) (j := max i j) ltac:(lia) HAw) (rel_exp_cumu_ge (i := i) (j := max i j) ltac:(lia) HCw) HMw Hv) as H.
  eapply rel_exp_eq_subtyp; [ exact H | exact HC |].
  eapply subtyp_refl; exact (rel_exp_typ_var0 HC).
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
    pose proof (sem_ctx_app_r _ _ HΔ) as HΨA.
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

Lemma ihs_sub_eval : forall D Us gs1 aft j B X fa v ihp w, decl_closed D -> List.length Us = ind_nu D ->
    List.length X = ind_nn D -> List.length fa = List.length gs1 -> List.length ihp = j ->
    ⟦ List.map (fun U => U[wk_shiftn (j + (List.length gs1 + S (List.length aft)) + ind_nn D)]ʷ) Us ⟧* gc_deps ⍮ gc_stack
      ⍮ env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ w ->
    ⟦ ihs_sub D Us (List.length gs1 + S (List.length aft)) (cargs_pat gs1) j ⟧s
      env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ env_args B (w ++ X ++ nonrec_vals gs1 fa).
Proof.
  intros * Hc HUl LX Lfa Lihp Hw x.
  pose proof (decl_closed_nu D Hc) as Hle.
  set (pat := cargs_pat gs1).
  set (na := List.length gs1 + S (List.length aft)).
  set (K := List.length (cargs_nonrec gs1)).
  assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
  assert (HK : pat_nargs pat = K) by (unfold pat, K; rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
  assert (Lnv : List.length (nonrec_vals gs1 fa) = K) by (apply length_nonrec_vals; exact Lfa).
  assert (Lw : List.length w = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw), List.length_map; exact HUl).
  set (Ep := env_args B (X ++ fa ++ v :: aft ++ ihp)).
  unfold ihs_sub; cbn [sb_compose sb_of_wk sentry_sub].
  assert (Hs : na - List.length pat + j = List.length (v :: aft ++ ihp)) by (unfold na; cbn; rewrite List.length_app; lia).
  rewrite Hs.
  destruct (Nat.lt_ge_cases x (K + ind_nn D)) as [Hx | Hx].
  - assert (Hwp : wk_pat pat x < List.length pat + ind_nn D) by (apply wk_pat_bound; lia).
    rewrite sb_qn_lt by exact Hwp; cbn [sentry_sub sb_of_wk eval_sentry].
    unfold Ep; replace (X ++ fa ++ v :: aft ++ ihp) with ((X ++ fa) ++ v :: aft ++ ihp) by (rewrite <- List.app_assoc; reflexivity).
    rewrite env_args_app; cbn [wk_shiftn].
    rewrite (env_args_app B (X ++ fa)), Nat.add_comm, env_entry_args_app.
    rewrite (env_args_app B X), <- (eval_wk_entry _ _ (wk_mono_pat pat)).
    unfold pat; rewrite eval_wk_pat_args by exact Lfa.
    rewrite <- (env_args_app B X).
    apply env_entry_args_lt; rewrite List.length_app; lia.
  - replace x with (pat_nargs pat + (ind_nn D + (x - K - ind_nn D))) by lia.
    rewrite wk_pat_ge, sb_qn_ge by lia.
    replace (List.length pat + (ind_nn D + (x - K - ind_nn D)) - (List.length pat + ind_nn D)) with (x - K - ind_nn D) by lia.
    set (y := x - K - ind_nn D).
    replace (pat_nargs pat + (ind_nn D + y)) with (List.length (X ++ nonrec_vals gs1 fa) + y) by (rewrite List.length_app; lia).
    rewrite (env_args_app B w), env_entry_args_app.
    destruct (Nat.lt_ge_cases y (ind_nu D)) as [Hy | Hy].
    + rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia.
      cbn [sentry_wk sentry_sub eval_sentry].
      destruct (nth_error_lt_some' Us (List.length Us - 1 - y) ltac:(lia)) as [U HU].
      destruct (IndCases.eval_exps_nth _ _ _ _ _ Hw ltac:(rewrite List.nth_error_map, HU; reflexivity)) as (u & Hu & Eu).
      exists u; split.
      * rewrite env_entry_args_nth by lia; f_equal.
        rewrite Lw, <- HUl; apply List.nth_error_nth; exact Hu.
      * rewrite (List.nth_error_nth _ _ _ HU), exp_sub_of_wk, exp_wk_wk.
        replace (U[wk_compose (wk_shiftn (List.length pat + ind_nn D)) (wk_shiftn (List.length (v :: aft ++ ihp)))]ʷ)
          with (U[wk_shiftn (j + (List.length gs1 + S (List.length aft)) + ind_nn D)]ʷ); [ exact Eu |].
        apply exp_wk_wk_eq; intros z; cbn; rewrite List.length_app; lia.
    + replace y with (List.length Us + (y - ind_nu D)) by lia.
      rewrite sb_of_list_ge; cbn [sentry_wk sentry_sub eval_sentry sb_of_wk sb_id wk_shiftn].
      replace (List.length Us + (y - ind_nu D)) with (List.length w + (y - ind_nu D)) by lia.
      rewrite env_entry_args_app.
      unfold Ep; symmetry.
      replace (y - ind_nu D + (List.length pat + ind_nn D) + List.length (v :: aft ++ ihp)) with (List.length (X ++ fa ++ v :: aft ++ ihp) + (y - ind_nu D))
        by (cbn; rewrite !List.length_app; cbn; rewrite List.length_app; lia).
      apply env_entry_args_app.
Qed.

Fixpoint ihb (k : nat) (β : sub) : sub :=
  match k with 0 => β | S k => ihb k β ⨟ sb_of_wk wk_shift end.
Fixpoint ihx (k : nat) (x : exp) : exp :=
  match k with 0 => x | S k => a_app (ihx k x)[wk_shift]ʷ (a_var 0) end.

Lemma ihb_eq : forall k β, sb_eq (ihb k β) (β ⨟ sb_of_wk (wk_shiftn k)).
Proof.
  induction k as [| k IH]; intros β; cbn [ihb].
  - intros y; cbn; rewrite (sentry_sub_sb_eq _ _ Id), sentry_sub_id; [ reflexivity |].
    rewrite (sb_of_wk_cong _ _ wk_shiftn_zero); exact sb_of_wk_id.
  - rewrite IH, sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
    rewrite <- sb_of_wk_compose; apply sb_of_wk_cong; intros z; cbn; lia.
Qed.

Lemma apps_snoc : forall Ms M N, apps M (Ms ++ N :: nil) = a_app (apps M Ms) N.
Proof. induction Ms as [| M0 Ms IH]; intros; cbn; [ reflexivity | apply IH ]. Qed.

Lemma ihx_eq : forall k x, ihx k x = apps x[wk_shiftn k]ʷ (vars_from 0 k).
Proof.
  induction k as [| k IH]; intros x; cbn [ihx].
  - cbn; rewrite (exp_wk_id_ext x _ wk_shiftn_zero); reflexivity.
  - rewrite IH, apps_exp_wk.
    replace (vars_from 0 (S k)) with (vars_from 1 k ++ a_var 0 :: nil)
      by (rewrite <- (Nat.add_1_r k), <- (vars_from_app 0 k 1); reflexivity).
    rewrite apps_snoc; f_equal; f_equal.
    + rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia.
    + unfold vars_from; rewrite List.map_map; apply List.map_ext; intros y; cbn; f_equal; lia.
Qed.

Lemma ptyp_ty_at_ctx_pi : forall p t Us σ, ptyp_simple t = true ->
    ptyp_ty_at p Us σ t
    = ctx_pi (tele_sub (ptyp_tele t) σ)
        (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ptyp_depth t)]ʷ) Us
                         ++ List.map (fun P => P[sb_qn (ptyp_depth t) σ]) (ptyp_ps t))).
Proof.
  intros p0; induction t as [[| k] Ps | k Ps | B t IH]; intros * Hs; cbn in Hs; try discriminate.
  - cbn [ptyp_ty_at ptyp_tele ptyp_doms doms_ctx List.map List.rev tele_sub ctx_pi ptyp_depth List.length ptyp_ps sb_qn].
    rewrite (List.map_ext (fun U => U[wk_shiftn 0]ʷ) (fun U => U)) by (intros U; apply (exp_wk_id_ext U _ wk_shiftn_zero)).
    rewrite List.map_id; reflexivity.
  - cbn [ptyp_ty_at ptyp_tele ptyp_doms ptyp_depth ptyp_ps].
    unfold ptyp_tele, ptyp_depth in IH.
    rewrite (IH _ _ Hs).
    unfold ptyp_tele, ptyp_depth; cbn [ptyp_doms List.length].
    change (doms_ctx (B :: ptyp_doms t)) with (doms_ctx (ptyp_doms t) ++ ce_ass B :: nil).
    rewrite tele_sub_app, ctx_pi_app; cbn [tele_sub ctx_pi List.length sb_qn centry_sub].
    replace (sb_qn (List.length (ptyp_doms t)) (q σ)) with (q (sb_qn (List.length (ptyp_doms t)) σ)) by (rewrite <- (sb_qn_plus _ 1), Nat.add_1_r; reflexivity).
    rewrite List.map_map, (List.map_ext (fun U => U[wk_shift]ʷ[wk_shiftn (List.length (ptyp_doms t))]ʷ) (fun U => U[wk_shiftn (S (List.length (ptyp_doms t)))]ʷ)) by (intros U; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia).
    reflexivity.
Qed.

Lemma eval_sub_sb_eq : forall σ τ ρ ρσ, sb_eq σ τ -> ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ τ ⟧s ρ ↘ ρσ.
Proof. intros * E H x; rewrite <- (E x); exact (H x). Qed.

Lemma sh_ctx_ass : forall Bs pat, tele_ass (sh_ctx pat Bs).
Proof.
  induction Bs as [| B Bs IH]; intros pat; cbn [sh_ctx]; [ constructor |].
  apply List.Forall_app; split; [ apply IH | constructor; [ eexists; reflexivity | constructor ] ].
Qed.

Section CargsSem.
  Variable (D : ind_decl).
  Hypothesis (HD : sem_core D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)).
  Hypothesis (Hdt : decl_typed gc_deps gc_stack D).

  (** The variables of a closed telescope. *)
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
    - apply valid_exp_var; [| exact HΔ ].
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

  Variable (p : qname).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D).

  (** The type former applied to terms of its parameters' types. *)
  Lemma valid_ind_apps : forall Ψ Ms, ⊨ Ψ -> List.length Ms = ind_np D ->
      (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts (ind_params D) Id Ms) k = Some T -> Ψ ⊨ N : T) ->
      exists j : nat, Ψ ⊨ apps (a_ind p) Ms : Typeω@j.
  Proof.
    intros * HΨ HMl HMs.
    pose proof (decl_closed_params D Hc) as Hass.
    destruct (sd_sort D HD) as [i HS].
    pose proof (sd_params D HD) as HP.
    assert (HB : ind_params D ⊨ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ : Typeω@i).
    { pose proof HP as HP'; rewrite params_split in HP'.
      pose proof (rel_wk_under_ctx_shiftn _ _ HP') as Hw; rewrite length_nparams in Hw.
      pose proof (rel_exp_under_ctx_wk Hw HS) as H; cbn [exp_wk] in H.
      rewrite params_split; exact H. }
    destruct (closed_app_sem _ _ Hass HP HΨ) as [HPΨ _].
    pose proof (closed_app_valid _ _ _ _ _ Hass HP HΨ HB) as HBΨ.
    pose proof (closed_weaken_valid _ _ _ _ HΨ (valid_exp_ind0 D HD Hc Hsu p Hl)) as HM.
    unfold ind_ty in HM.
    pose proof (rel_exp_apps_ctx_pi_n _ (ind_params D) Ψ _ i (a_ind p) Ms eq_refl Hass HPΨ HBΨ HM HMl HMs) as HR.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in HR; cbn [exp_wk exp_sub] in HR.
    - exists i0; exact HR.
    - exists 0; eapply rel_exp_suniv_tm_large; exact HR.
  Qed.

  Lemma cargs_sem_all : forall c gs, ind_con D c = Some gs -> forall gs1 gs2, gs = gs1 ++ gs2 ->
      ⊨ cargs_ctx p D gs1 ++ ind_params D /\
      cargs_ctx p D gs1 ++ ind_params D ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ ind_params D.
  Proof.
    intros c gs Hcon.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof Hdt as (Hass & (Hmv & Hmvs & Hmvc) & Hle & _ & _ & _ & _ & _ & HPl & _).
    pose proof Hc as (_ & _ & Hs & HsS & _).
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_strat cargs_pat List.rev List.map List.app].
      destruct (sem_ctx_per_ctx_env (sd_params _ HD)) as [R HR].
      split; [ exact (sd_params _ HD) |].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) ].
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      destruct (IH _ Heq) as [HΨ IHw].
      rewrite cargs_ctx_snoc, cargs_pat_snoc.
      destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app wk_pat].
      + rewrite cargs_strat_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (sd_arg _ HD _ _ _ _ Hcon HA) as (_ & j & HAv).
        rewrite Heq, <- astrat_prefix in HAv.
        pose proof (rel_exp_under_ctx_wk IHw HAv) as HAw; cbn [exp_wk] in HAw.
        split; [ exact (sem_ctx_ext_typ _ _ _ HΨ HAw) | exact (rel_wk_under_ctx_q IHw HAv) ].
      + rewrite cargs_strat_snoc_rec.
        assert (Hj : exists j : nat, cargs_ctx p D gs1 ++ ind_params D ⊨ ptyp_ty p D (cargs_pat gs1) Ps : Typeω@j).
        { specialize (HPl _ _ _ _ _ Hin Heq).
          set (pat := cargs_pat gs1).
          set (L := List.length (ptyp_doms Ps)).
          set (pat' := List.repeat false L ++ pat).
          assert (Hsimp : ptyp_simple Ps = true) by exact (sd_simple _ HD _ _ _ _ _ Hcon Heq).
          rewrite (ptyp_ty_ctx_pi p D Ps pat Hsimp); fold L pat'.
          set (Φ := sh_ctx pat (ptyp_doms Ps)).
          assert (HlΦ : List.length Φ = L) by (unfold Φ; apply length_sh_ctx).
          assert (HΦa : tele_ass Φ) by apply sh_ctx_ass.
          assert (HΦ : ⊨ Φ ++ cargs_ctx p D gs1 ++ ind_params D).
          { pose proof (sh_sem_gen D HD p c gs Hcon gs1 Ps gs2 Heq HΨ IHw L (le_n _)) as H.
            unfold L in H; rewrite List.firstn_all in H; exact H. }
          assert (HwΦ : Φ ++ cargs_ctx p D gs1 ++ ind_params D ⊨ʷ (wk_pat pat') : ptyp_tele Ps ++ cargs_strat gs1 ++ ind_params D).
          { pose proof (sh_wk_gen D HD p c gs Hcon gs1 Ps gs2 Heq IHw L (le_n _)) as H.
            unfold L in H; rewrite List.firstn_all in H; exact H. }
          assert (Hleaf : exists j : nat, Φ ++ cargs_ctx p D gs1 ++ ind_params D
                         ⊨ ptyp_ty p D pat' (pt_self 0 (ptyp_ps Ps)) : Typeω@j).
          { cbn [ptyp_ty ptyp_ps].
            assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
            assert (Hpat' : List.length pat' = L + List.length gs1) by (unfold pat'; rewrite List.length_app, List.repeat_length; lia).
            assert (Hnargs : pat_nargs pat' = L + List.length (cargs_strat gs1)).
            { unfold pat', pat; rewrite pat_nargs_app, pat_nargs_cargs_pat; f_equal.
              clear; induction L as [| L IH]; cbn; lia. }
            assert (HE : ⊨ (Φ ++ cargs_ctx p D gs1 ++ ind_nparams D) ++ ind_uparams D)
              by (rewrite <- !List.app_assoc, <- params_split; exact HΦ).
            assert (HlE : List.length (Φ ++ cargs_ctx p D gs1 ++ ind_nparams D) = List.length pat' + ind_nn D)
              by (rewrite !List.length_app, length_cargs_ctx, length_nparams, HlΦ, Hpat'; lia).
            assert (Huvars : vars_from (List.length pat' + ind_nn D) (ind_nu D)
                             = vars_from (List.length (Φ ++ cargs_ctx p D gs1 ++ ind_nparams D)) (List.length (ind_uparams D)))
              by (rewrite HlE, length_ind_uparams by exact Hle; reflexivity).
            assert (Hus : ctx_scoped 0 (ind_uparams D)).
            { rewrite params_split in Hs; apply ctx_scoped_app in Hs as [_ Hs']; exact Hs'. }
            assert (Huass : tele_ass (ind_uparams D)) by (apply Forall_skipn'; exact Hass).
            assert (Humv : ctx_mvc (ind_uparams D)) by (apply Forall_skipn'; exact Hmv).
            unfold ind_uvars.
            apply valid_ind_apps; [ exact HΦ | rewrite List.length_app, List.length_map, HPl, length_vars_from; unfold ind_nn in *; unfold ind_np in *; lia |].
            rewrite params_split; intros k N T HN HT.
            rewrite tele_insts_app in HT; [| exact Huass | rewrite length_vars_from, length_ind_uparams by exact Hle; reflexivity ].
            assert (Hl1 : List.length (vars_from (List.length pat' + ind_nn D) (ind_nu D)) = ind_nu D) by apply length_vars_from.
            assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (vars_from (List.length pat' + ind_nn D) (ind_nu D))) = ind_nu D)
              by (rewrite length_tele_insts by exact Huass; rewrite Hl1, length_ind_uparams by exact Hle; lia).
            destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
            - rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
              rewrite Huvars in HN, HT.
              pose proof (valid_vars_tele _ _ Huass Hus Humv HE _ _ _ HN HT) as H.
              rewrite <- !List.app_assoc in H; exact H.
            - rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
              rewrite Hl1 in HN; rewrite Hl2 in HT.
              apply nth_error_map_inv in HN as (P & HPk & ->).
              set (s := L + List.length (cargs_strat gs1) + ind_nn D).
              assert (Hti : tele_insts (ind_nparams D) (sb_of_list Id (vars_from (List.length pat' + ind_nn D) (ind_nu D))) (List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps Ps))
                            = List.map (fun T => T[wk_pat pat']ʷ) (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn s)) (ptyp_ps Ps))).
              { rewrite <- !map_sub_of_wk; symmetry.
                eapply (tele_insts_sub_mvc _ (ind_nu D));
                  [ apply decl_closed_nparams_ass, Hc | apply Forall_firstn'; exact Hmv | apply decl_closed_nparams_scoped, Hc |].
                intros x Hx; rewrite sb_of_list_vars by exact Hx; cbn.
                unfold s; rewrite <- Hnargs.
                replace (x + (pat_nargs pat' + ind_nn D)) with (pat_nargs pat' + (ind_nn D + x)) by lia.
                rewrite wk_pat_ge; f_equal; lia. }
              rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
              assert (Hσ : s = ptyp_depth Ps + List.length (cargs_nonrec gs1) + ind_nn D)
                by (unfold s, ptyp_depth; fold L; rewrite cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
              rewrite Hσ in HT0.
              pose proof (sd_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HPk HT0) as HP0.
              rewrite Heq, <- astrat_prefix in HP0.
              rewrite <- params_split; exact (rel_exp_under_ctx_wk HwΦ HP0). }
          destruct Hleaf as [j0 Hleaf].
          exact (rel_exp_ctx_pi _ _ _ _ HΦa HΦ Hleaf). }
        destruct Hj as [j Hj].
        pose proof (sem_ctx_ext_typ _ _ _ HΨ Hj) as HC.
        split; [ exact HC |].
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HC) IHw).
  Qed.

  Lemma cod_sem : forall c gs, ind_con D c = Some gs ->
      exists j : nat, cargs_ctx p D gs ++ ind_params D ⊨ apps (a_ind p) (ind_pvars D (List.length gs)) : Typeω@j.
  Proof.
    intros c gs Hcon.
    pose proof Hdt as (Hass & (Hmv & _ & _) & _).
    pose proof Hc as (_ & _ & Hs & _).
    destruct (cargs_sem_all c gs Hcon gs nil (eq_sym (List.app_nil_r gs))) as [HΨ _].
    apply valid_ind_apps; [ exact HΨ | unfold ind_pvars; apply length_vars_from |].
    intros k N T HN HT.
    replace (ind_pvars D (List.length gs)) with (vars_from (List.length (cargs_ctx p D gs)) (List.length (ind_params D))) in HN, HT
      by (unfold ind_pvars, ind_np; rewrite length_cargs_ctx; reflexivity).
    exact (valid_vars_tele _ _ Hass Hs Hmv HΨ _ _ _ HN HT).
  Qed.

  Lemma conty_sem : forall c gs, ind_con D c = Some gs -> exists j : nat, ⋅ ⊨ con_ty p D gs : Typeω@j.
  Proof.
    intros c gs Hcon.
    destruct (cargs_sem_all c gs Hcon gs nil (eq_sym (List.app_nil_r gs))) as [HΨ _].
    destruct (cod_sem c gs Hcon) as [j Hj].
    assert (Hass : tele_ass (cargs_ctx p D gs ++ ind_params D))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
    rewrite <- (List.app_nil_r (cargs_ctx p D gs ++ ind_params D)) in HΨ, Hj.
    destruct (rel_exp_ctx_pi _ _ _ _ Hass HΨ Hj) as [j' Hj'].
    exists j'; unfold con_ty; rewrite <- ctx_pi_app; exact Hj'.
  Qed.
End CargsSem.

Lemma sem_decl_of_core : forall D, sem_core D -> decl_closed D -> ind_sort_univ (ind_sort D) ->
    decl_typed gc_deps gc_stack D -> sem_decl D.
Proof.
  intros D HD Hc Hsu Hdt; constructor; [ exact HD | | |].
  - intros p c gs Hl Hcon; exact (proj1 (cargs_sem_all D HD Hc Hsu Hdt p Hl c gs Hcon gs nil (eq_sym (List.app_nil_r gs)))).
  - intros p c gs Hl Hcon; exact (cod_sem D HD Hc Hsu Hdt p Hl c gs Hcon).
  - intros p c gs Hl Hcon; exact (conty_sem D HD Hc Hsu Hdt p Hl c gs Hcon).
Qed.

Section ConApps.
  Variable (D : ind_decl).
  Hypothesis (HD : sem_decl D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)).
  Let HDc : sem_core D := HD.
  Variable (p : qname).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D).

  (** ** A Constructor Applied *)
  Lemma rel_exp_con_apps : forall Γ c gs Ps As, ⊨ Γ -> ind_con D c = Some gs ->
      List.length Ps = ind_np D ->
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T -> Γ ⊨ P : T) ->
      List.length As = List.length gs ->
      (forall k N T, List.nth_error As k = Some N ->
         List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T -> Γ ⊨ N : T) ->
      Γ ⊨ apps (a_con p c) (Ps ++ As) : apps (a_ind p) Ps.
  Proof.
    intros * HΓ Hcon HPl HPs HAl HAs.
    pose proof (sd_cargs D HD p c gs Hl Hcon) as HΨ.
    destruct (sd_conty D HD p c gs Hl Hcon) as [j0 HT0].
    pose proof (valid_exp_con0 D HD Hc Hsu p Hl c gs Hcon HΨ j0 HT0) as HC0.
    pose proof (closed_weaken_valid _ _ _ _ HΓ HC0) as HC.
    unfold con_ty in HC; rewrite <- ctx_pi_app in HC.
    destruct (sd_cod D HD p c gs Hl Hcon) as [j Hj].
    assert (Hass : tele_ass (cargs_ctx p D gs ++ ind_params D))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
    destruct (closed_app_sem _ _ Hass HΨ HΓ) as [HCΓ _].
    pose proof (closed_app_valid _ _ _ _ _ Hass HΨ HΓ Hj) as HB.
    pose proof (rel_exp_apps_ctx_pi_n _ _ _ _ _ _ (Ps ++ As) eq_refl Hass HCΓ HB HC) as HR.
    replace (apps (a_ind p) Ps) with ((apps (a_ind p) (ind_pvars D (List.length gs)))[sb_of_list Id (Ps ++ As)]).
    - apply HR.
      + rewrite !List.length_app, length_cargs_ctx, HPl, HAl; unfold ind_np; lia.
      + rewrite tele_insts_app by (try apply decl_closed_params, Hc; exact HPl).
        intros k N T0 HN HT.
        assert (Hl2 : List.length (tele_insts (ind_params D) Id Ps) = List.length Ps)
          by (rewrite length_tele_insts by apply decl_closed_params, Hc; unfold ind_np in *; lia).
        destruct (Nat.lt_ge_cases k (List.length Ps)) as [Hk | Hk].
        * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; eauto.
        * rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl2 in HT; eauto.
    - rewrite apps_exp_sub; cbn [exp_sub]; f_equal.
      unfold ind_pvars; rewrite <- HAl, <- HPl; apply vars_from_sb_of_list_app.
  Qed.

End ConApps.

Section Elim.
  Variable (D : ind_decl).
  Hypothesis (HD : sem_decl D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)).
  Let HDc : sem_core D := HD.
  Hypothesis (Hdt : decl_typed gc_deps gc_stack D).
  Variable (p : qname).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D).
  Let Hle : ind_nu D <= ind_np D := decl_closed_nu D Hc.
  Let Hsimp := sd_simple D HDc.
  Let Hplen := sd_plen D HDc.
  Let T := List.rev (ind_nparams D).
  Let Ua : tele_ass (ind_uparams D) := decl_uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := uparams_sem D HD.

  Variable (Γ : ctx) (RΓ : relation env).
  Hypothesis (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).

  (** The uniform parameters. *)
  Variable (Us : list exp).
  Hypothesis (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Let τU := sb_of_list Id Us.

  Lemma length_Us : List.length Us = List.length (ind_uparams D).
  Proof. rewrite length_ind_uparams by exact Hle; exact HUl. Qed.

  Lemma gsub_U : gsub Γ τU (ind_uparams D ++ Γ).
  Proof. exact (gsub_closed_inst _ _ _ Ua Usem HΓ length_Us HUs). Qed.

  Lemma Us_eval : forall B, (forall k N, List.nth_error Us k = Some N -> exists v, ⟦ N ⟧ B ↘ v) ->
      exists u, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u.
  Proof. intros; apply eval_exps_each; assumption. Qed.

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
      { rewrite length_tele_insts by exact Ua; pose proof length_Us; assert (k < List.length Us) by (apply List.nth_error_Some; congruence); lia. }
      destruct (rel_exp_under_ctx_simple_at HRΓ (HUs _ _ _ HN HT0) _ _ HB) as (v1 & v2 & E1 & E2 & _); eauto. }
    destruct (Us_eval B1 ltac:(intros; eapply Hev; eassumption)) as [u1 Hu1].
    destruct (Us_eval B2 ltac:(intros; eapply Hev; eassumption)) as [u2 Hu2].
    exists u1, u2; split; [ exact Hu1 | split; [ exact Hu2 |] ].
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id B1) Hu1) as Hτ1.
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id B2) Hu2) as Hτ2.
    destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ Hres].
    destruct (sem_ctx_per_ctx_env HUΓ) as [RUΓ HRUΓ].
    pose proof (rel_sub_under_ctx_at' (gsub_valid gsub_U) HRΓ HRUΓ _ _ _ _ HB Hτ1 Hτ2) as H12.
    apply (Hres _ _ HRU HRUΓ) in H12.
    pose proof (eval_exps_length _ _ _ Hu1) as L1; pose proof (eval_exps_length _ _ _ Hu2) as L2.
    eapply closed_env_base; [ exact Ua | exact Usem | exact HRU | rewrite L1; exact length_Us | rewrite L2; exact length_Us | exact H12 ].
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
      { rewrite length_tele_insts by exact Ua; pose proof length_Us; assert (k < List.length Us) by (apply List.nth_error_Some; congruence); lia. }
      pose proof (rel_exp_under_ctx_wk Hwkj (HUs _ _ _ HN0 HT0)) as HW.
      destruct (rel_exp_under_ctx_simple_at HRS HW _ _ HE) as (v1 & _ & E1 & _); eauto. }
    destruct (eval_exps_each _ _ Hev) as [w Hw].
    exists w, u; split; [ exact Hw | split; [ exact Hu |] ].
    destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ Hres].
    destruct (sem_ctx_per_ctx_env HUΓ) as [RUΓ HRUΓ].
    pose proof (gsub_valid gsub_U) as (R1 & H1 & R2 & H2 & Hσ).
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
    eapply closed_env_base; [ exact Ua | exact Usem | exact HRU | rewrite L1; exact length_Us | rewrite L2; exact length_Us | exact H12' ].
  Qed.

  (** The uniform parameters' values, as arguments of their telescope. *)
  Lemma U_gargs : forall a b, RU (env_args nil a) (env_args nil b) -> List.length a = ind_nu D -> List.length b = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil a b.
  Proof.
    intros * H La Lb.
    assert (HC' : ⊨ List.rev (List.rev (ind_uparams D)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact Usem).
    assert (HR' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
    exact (proj2 (rel_gargs _ _ _ _ per_ctx_env_nil_true HC' (List.Forall_rev Ua) HR' nil nil a b
                    ltac:(rewrite List.length_rev, La, length_ind_uparams by exact Hle; reflexivity)
                    ltac:(rewrite List.length_rev, Lb, length_ind_uparams by exact Hle; reflexivity) H)).
  Qed.

  Lemma nparams_npre_split : forall k, exists Δ, ind_nparams D = Δ ++ npre D k.
  Proof.
    intros; exists (List.rev (List.skipn k (List.rev (ind_nparams D)))).
    unfold npre; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
  Qed.

  Lemma npre_ass : forall k, tele_ass (npre D k ++ ind_uparams D).
  Proof.
    intros; destruct (npre_suffix D k) as [Δ HΔ].
    pose proof (decl_closed_params D Hc) as H; rewrite HΔ in H.
    apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  (** ** The Entries of a Constructor's Telescope

      The relation of an entry, at an environment of the parameters and
      the arguments before it, is the canonical relation there. *)
  Section Entries.
    Variable (c : String.string) (gs : list carg).
    Hypothesis (Hcon : ind_con D c = Some gs).
    Let HΨ := sd_cargs D HD p c gs Hl Hcon.

    Lemma arg_entry_char : forall gs1 A gs2, gs = gs1 ++ ca_arg A :: gs2 ->
        forall ups ns fa, List.length fa = List.length gs1 ->
        (forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
           R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
        forall i R t t', ⟦ A[wk_pat (cargs_pat gs1)]ʷ ⟧ env_args nil (ups ++ ns ++ fa) ↘ t ->
          DF t ≈ t' ∈ per_univ_elem i ↘ R ->
          (R <~> ind_ar D ups ns c (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa)).
    Proof.
      intros * Heq * Hlk Hpre * Et HR.
      assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
        by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      destruct (sd_arg _ HD _ _ _ _ Hcon HA) as (_ & jA & HAv).
      rewrite Heq, <- astrat_prefix in HAv.
      destruct (rel_exp_under_ctx_wk_simple (cargs_wk D HD p c gs Hcon HΨ _ _ Heq) HAv) as (RΓ' & HΓ' & i0 & Hwk).
      pose proof (Hpre _ HΓ') as HE1.
      destruct (Hwk _ _ HE1) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
      assert (Hy : y = d_univ jA) by (cbn in Ey; inversion Ey; reflexivity).
      rewrite Hy in HRy; clear Hy Ey Ey'.
      destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
      apply ERy in Hmm; destruct Hmm as [Rm HRm].
      assert (m = t) as -> by (eapply functional_eval_exp; eassumption).
      rewrite List.app_assoc, env_args_app, eval_wk_pat_args, <- env_args_app, <- List.app_assoc in Em' by exact Hlk.
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRm) HRm) as HRd.
      assert (Hcan : ind_ar D ups ns c (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa) <~> Rm).
      { unfold ind_ar; rewrite (nth_atyp_eq _ _ _ _ _ Hcon HA).
        symmetry; exact (per_head_iff Em' Em' HRd). }
      rewrite Hcan; eapply per_univ_elem_right_irrel; [ exact HR | exact HRm ].
    Qed.

  End Entries.

  (** ** The Substitution of the Elimination's Type *)
  Lemma gsub_tau : ⊨ elim_mctx p D Us ++ Γ -> forall Ns M, List.length Ns = ind_nn D ->
      (forall k N T0, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (ind_nparams D) τU Ns) k = Some T0 -> Γ ⊨ N : T0) ->
      Γ ⊨ M : apps (a_ind p) (Us ++ Ns) ->
      gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D Us ++ Γ).
  Proof.
    intros HM * HNl HNs HMv.
    assert (Hrass : tele_ass (tele_sub (ind_nparams D) τU)) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
    apply gsub_of_list; [ constructor; exact HΓ | apply elim_mctx_ass, Hc | exact HM
                        | rewrite List.length_app, length_elim_mctx; cbn; lia |].
    intros k N T0 HN HT.
    unfold elim_mctx in HT; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_ind_nparams_sub; exact HNl).
    assert (Hl2 : List.length (tele_insts (tele_sub (ind_nparams D) (sb_of_list Id Us)) Id Ns) = ind_nn D)
      by (rewrite length_tele_insts by exact Hrass; rewrite length_ind_nparams_sub; lia).
    destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
    - rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      rewrite tele_insts_tele_sub in HT.
      rewrite (tele_insts_sb_eq _ _ τU) in HT by (intros x; cbn; apply sentry_sub_id).
      exact (HNs _ _ _ HN HT).
    - rewrite List.nth_error_app2 in HN, HT by lia; rewrite HNl in HN; rewrite Hl2 in HT.
      destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      unfold τU; rewrite elim_mctx_head_inst by exact HNl; exact HMv.
  Qed.

  (** ** The Canonical Uniform Parameters *)
  Variable (u0 : list domain) (a0 : domain).
  Hypothesis (Hu0g : per_gargs (List.rev (ind_uparams D)) nil nil u0 u0) (Hu0l : List.length u0 = ind_nu D)
    (Ha0 : ⟦ ind_sort D ⟧ env_args nil u0 ↘ a0).
  Let nr := ind_nr D u0.
  Let ar := ind_ar D u0.

  Let dr := ind_dr u0.

  Lemma u0_canon :
      (forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> PER (nr k vs)) /\
      (forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> (nr k vs <~> nr k vs')) /\
      (forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> PER (ar ms c k vs)) /\
      (forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> (ar ms c k vs <~> ar ms' c k vs')) /\
      (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
         PER (dr (ms ++ ws ++ ys) B)) /\
      (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
         (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B)) /\
      ind_adm D u0 nr ar dr u0.
  Proof. eapply ind_canon; eassumption. Qed.

  Let HnP := proj1 u0_canon.
  Let HnI := proj1 (proj2 u0_canon).
  Let HaP := proj1 (proj2 (proj2 u0_canon)).
  Let HaI := proj1 (proj2 (proj2 (proj2 u0_canon))).
  Let HdP := proj1 (proj2 (proj2 (proj2 (proj2 u0_canon)))).
  Let HdI := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 u0_canon))))).
  Let Had := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 u0_canon))))).

  Lemma nr_pre_refl : forall k vs vs', k <= ind_nn D -> tele_pre nr k vs vs' -> tele_pre nr k vs vs.
  Proof.
    intros; eapply (tnrp_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI); [| eassumption ].
    unfold T; rewrite List.length_rev, length_nparams; assumption.
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
    pose proof (U_gargs _ _ H10 Lu1 Hu0l) as Hg10.
    assert (HU00 : RU (env_args nil u0) (env_args nil u0))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRU Usem); [ rewrite Hu0l, length_ind_uparams by exact Hle; reflexivity | exact Hu0g ]).
    assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK).
    pose proof (per_gargs_base _ _ _ HRU HKr (List.Forall_rev HPa) (env_args nil u0) (env_args nil u0)
                  (env_args nil u) (env_args nil u0) zs zs HU00 (symmetry H10) HU00 Hg00) as Hgb.
    rewrite <- env_args_app.
    eapply (closed_env_base _ _ _ _ nil nil); [ exact HKa | exact HK | exact HRK
                                              | rewrite !List.length_app, length_ind_uparams by exact Hle; lia
                                              | rewrite !List.length_app, length_ind_uparams by exact Hle; lia |].
    apply (gargs_env_rel _ _ _ _ _ _ HRK HK); [ rewrite !List.length_app, length_ind_uparams by exact Hle; lia |].
    rewrite List.rev_app_distr; apply per_gargs_app_intro;
      [ rewrite List.length_rev, length_ind_uparams by exact Hle; exact Lu1 | exact Hg10 | exact Hgb ].
  Qed.

  (** ** The Non-Uniform Parameters *)
  Hypothesis (HNt : ⊨ tele_sub (ind_nparams D) τU ++ Γ).

  Lemma npre_inst_sem : forall k, k <= ind_nn D -> ⊨ tele_sub (npre D k) τU ++ Γ.
  Proof.
    intros k Hk; destruct (nparams_npre_split k) as [Δ HΔ].
    pose proof HNt as H; rewrite HΔ, tele_sub_app, <- List.app_assoc in H.
    exact (sem_ctx_app_r _ _ H).
  Qed.

  Lemma cv_nparams : forall B1 B2 u1 u2, RΓ B1 B2 ->
      ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 ->
      RU (env_args nil u1) (env_args nil u0) -> RU (env_args nil u2) (env_args nil u0) ->
      forall k, k <= ind_nn D -> forall pre pre', tele_pre nr k pre pre' ->
        per_gargs (List.rev (tele_sub (npre D k) τU)) B1 B2 pre pre'.
  Proof.
    intros * HB Hu1 Hu2 H10 H20 k.
    pose proof (eval_exps_length _ _ _ Hu1) as Lu1; rewrite HUl in Lu1.
    assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
    induction k as [| k IH]; intros Hk pre pre' Hp.
    - rewrite tele_pre_iff in Hp; destruct Hp as (Hl1 & Hl2 & _).
      destruct pre, pre'; cbn in *; try discriminate; constructor.
    - pose proof Hp as Hp0; rewrite tele_pre_iff in Hp0; destruct Hp0 as (Hl1 & Hl2 & Hr).
      destruct (nparams_lt_ass D k (decl_closed_params D Hc) ltac:(rewrite List.length_rev, length_nparams; lia)) as [A HA].
      destruct (nth_error_lt_some' pre k ltac:(lia)) as [v Hv0].
      destruct (nth_error_lt_some' pre' k ltac:(lia)) as [v' Hv0'].
      assert (Hvs : pre = List.firstn k pre ++ v :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0), List.firstn_all2 by lia; reflexivity).
      assert (Hvs' : pre' = List.firstn k pre' ++ v' :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0'), List.firstn_all2 by lia; reflexivity).
      set (qs := List.firstn k pre) in *; set (qs' := List.firstn k pre') in *.
      assert (Lq : List.length qs = k) by (unfold qs; rewrite List.length_firstn; lia).
      assert (Lq' : List.length qs' = k) by (unfold qs'; rewrite List.length_firstn; lia).
      assert (Hpq : tele_pre nr k qs qs') by (exact (tele_pre_of_pre _ _ _ _ k Hp ltac:(lia))).
      pose proof (IH ltac:(lia) _ _ Hpq) as IHq.
      rewrite (npre_S _ _ _ HA); cbn [tele_sub centry_sub List.rev]; rewrite length_npre by lia.
      rewrite Hvs, Hvs'.
      set (Δ := tele_sub (npre D k) τU).
      assert (LΔ : List.length Δ = k) by (unfold Δ; rewrite length_tele_sub, length_npre by lia; reflexivity).
      pose proof (npre_inst_sem (S k) Hk) as HSk.
      rewrite (npre_S _ _ _ HA) in HSk; cbn [tele_sub centry_sub List.app] in HSk; rewrite length_npre in HSk by lia.
      fold Δ in HSk.
      destruct (sem_ctx_ass_inv HSk) as [j HBk].
      pose proof (sem_ctx_tail HSk) as HΔ.
      destruct (sem_ctx_per_ctx_env HΔ) as [RΔ HRΔ].
      assert (HE : RΔ (env_args B1 qs) (env_args B2 qs'))
        by (eapply gargs_env_rel_gen; [ exact HRΓ | exact HRΔ | exact HΔ | exact HB | lia | exact IHq ]).
      destruct (rel_exp_of_typ_inversion_simple_at HRΔ HBk _ _ HE) as (t1 & t2 & Et1 & Et2 & [R12 HR12]).
      (** The instance at [B1] against the declaration's type at [u0]. *)
      assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HRΔ).
      assert (HEE : RΔ (env_args B1 qs) (env_args B1 qs)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
      destruct (sem_ctx_per_ctx_env (npre_sem D HD k)) as [RK HRK].
      assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
      assert (Lnk : List.length (npre D k ++ ind_uparams D) = List.length (u0 ++ qs))
        by (rewrite !List.length_app, length_npre, length_ind_uparams by lia; lia).
      assert (Lnk1 : List.length (npre D k ++ ind_uparams D) = List.length (u1 ++ qs))
        by (rewrite !List.length_app, length_npre, length_ind_uparams by lia; lia).
      assert (HK0 : RK (env_args nil (u0 ++ qs)) (env_args nil (u1 ++ qs))).
      { apply (gargs_env_rel _ _ _ _ _ _ HRK (npre_sem D HD k)); [ symmetry; exact Lnk |].
        rewrite rev_npre; apply per_gargs_app_intro;
          [ rewrite List.length_rev, length_ind_uparams by exact Hle; exact Hu0l
          | apply U_gargs; [ symmetry; exact H10 | exact Hu0l | exact Lu1 ] |].
        eapply nr_gargs; [ eassumption .. | apply U_gargs; [ symmetry; exact H10 | exact Hu0l | exact Lu1 ] | exact Hu0l | exact Ha0 | lia |].
        exact (nr_pre_refl k qs qs' ltac:(lia) Hpq). }
      assert (HK1 : RK (env_args (env_args B1 u1) qs) (env_args nil (u0 ++ qs))).
      { rewrite <- env_args_app.
        eapply (closed_env_base _ _ _ _ nil nil); [ exact (npre_ass k) | exact (npre_sem D HD k) | exact HRK
                                                  | symmetry; exact Lnk1 | symmetry; exact Lnk | symmetry; exact HK0 ]. }
      destruct (proj2 (sd_npar _ HD _ _ HA)) as [j' HAv].
      destruct (sem_ctx_per_ctx_env HΓ) as [RΓ0 HRΓ0].
      destruct (closed_typ_inst (npre D k) (ind_uparams D) Γ A j' τU RΓ RK RΔ B1 qs (env_args B1 u1) (env_args nil (u0 ++ qs))
                  (npre_ass k) (npre_sem D HD k) Ua Usem HΓ HRΓ HRK HRΔ HAv (gsub_valid gsub_U) HEE
                  ltac:(rewrite length_npre by lia; exact Lq) (eval_sb_of_list _ _ _ _ _ (eval_sub_id B1) Hu1) HK1)
        as (a & c & Ea & Ec & [R1c HR1c]).
      rewrite length_npre in Ea by lia.
      assert (a = t1) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_elem_sym _ _ _ _ HR1c) as [HRc1 _].
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HRc1 HR1c) as (Rcc & HRcc & _).
      assert (E1 : R12 <~> R1c) by (eapply per_univ_elem_right_irrel; [ exact HR12 | exact HR1c ]).
      assert (E2 : R1c <~> Rcc) by (eapply per_univ_elem_chain_iff; [ exact HR1c | exact HRcc ]).
      destruct (per_univ_elem_to_nat _ _ _ _ HR12) as [n Hn].
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R12).
      + rewrite List.length_rev, LΔ; exact Lq.
      + exact IHq.
      + exact (mk_rel_mod_eval t1 t2 Et1 Et2 Hn).
      + pose proof (Hr k v v' Hv0 Hv0') as Hvv; fold qs in Hvv.
        unfold nr, ind_nr in Hvv; rewrite (nth_ctyp_eq _ _ _ HA) in Hvv.
        apply E1, E2; exact (Hvv _ _ _ _ Ec Ec HRcc).
  Qed.

  (** ** The Scrutinee *)
  Let IT := apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)).

  Lemma eval_IT : forall B ns w, List.length ns = ind_nn D ->
      ⟦ List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B ns ↘ w ->
      ⟦ IT ⟧ env_args B ns ↘ d_ind p (w ++ ns).
  Proof.
    intros * Hln Hw; unfold IT; apply eval_apps_exp; exists (d_ind p nil), (w ++ ns); split; [ constructor | split ].
    - apply eval_exps_app; [ exact Hw |].
      rewrite <- Hln; pose proof (eval_vars_from_args ns B nil) as H; rewrite List.app_nil_r in H; exact H.
    - change (d_ind p (w ++ ns)) with (d_ind p (nil ++ (w ++ ns))); apply (IndCases.eval_apps_ind D p Hl).
      pose proof (eval_exps_length _ _ _ Hw) as Lw; rewrite List.length_map, HUl in Lw.
      cbn; rewrite List.length_app; unfold ind_nn in *; lia.
  Qed.

  Hypothesis (HM : ⊨ elim_mctx p D Us ++ Γ).

  Lemma mctx_split : elim_mctx p D Us ++ Γ = (tele_sub (ind_nparams D) τU ++ Γ) ▹ IT.
  Proof. reflexivity. Qed.

  Lemma cv_mctx : forall B1 B2 u1 u2, RΓ B1 B2 ->
      ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 ->
      RU (env_args nil u1) (env_args nil u0) -> RU (env_args nil u2) (env_args nil u0) ->
      forall RM, EF elim_mctx p D Us ++ Γ ≈ elim_mctx p D Us ++ Γ ∈ per_ctx_env ↘ RM ->
      forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar dr ns m m' ->
        RM (env_args B1 (ns ++ m :: nil)) (env_args B2 (ns' ++ m' :: nil)).
  Proof.
    intros * HB Hu1 Hu2 H10 H20 RM HRM * Hns Hm.
    assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
    pose proof Hns as Hns0; rewrite tele_full_iff in Hns0; destruct Hns0 as (Ln & Ln' & _).
    unfold T in Ln, Ln'; rewrite List.length_rev, length_nparams in Ln, Ln'.
    pose proof (cv_nparams _ _ _ _ HB Hu1 Hu2 H10 H20 (ind_nn D) (le_n _) ns ns'
                  ltac:(apply tele_full_pre in Hns; unfold T in Hns; rewrite List.length_rev, length_nparams in Hns; exact Hns))
      as Hg.
    rewrite npre_full in Hg.
    assert (LNt : List.length (tele_sub (ind_nparams D) τU) = ind_nn D) by apply length_ind_nparams_sub.
    pose proof HM as HM'; rewrite mctx_split in HM'.
    destruct (sem_ctx_ass_inv HM') as [j HIT].
    pose proof (sem_ctx_tail HM') as HNtΓ.
    destruct (sem_ctx_per_ctx_env HNtΓ) as [RN HRN].
    assert (HE : RN (env_args B1 ns) (env_args B2 ns'))
      by (eapply gargs_env_rel_gen; [ exact HRΓ | exact HRN | exact HNtΓ | exact HB | lia | exact Hg ]).
    destruct (rel_exp_of_typ_inversion_simple_at HRN HIT _ _ HE) as (t1 & t2 & Et1 & Et2 & [R12 HR12]).
    (** The type at the left, the type former at the left's uniform
        parameters. *)
    assert (HPN : PER RN) by (eapply per_env_PER; exact HRN).
    assert (HEE : RN (env_args B1 ns) (env_args B1 ns)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
    destruct (us_wk_vals (tele_sub (ind_nparams D) τU) RN B1 ns HRN HNtΓ HEE ltac:(lia)) as (w1 & u1' & Hw1 & Hu1' & Hwu).
    pose proof (functional_eval_exps' _ _ _ _ Hu1 Hu1') as <-.
    rewrite LNt in Hw1.
    pose proof (eval_IT _ _ _ Ln Hw1) as Et1'.
    assert (t1 = d_ind p (w1 ++ ns)) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hw0 : RU (env_args nil u0) (env_args nil w1)) by (etransitivity; [ symmetry; exact H10 | symmetry; exact Hwu ]).
    pose proof (eval_exps_length _ _ _ Hw1) as Lw1; rewrite List.length_map, HUl in Lw1.
    pose proof (tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ Hns) as Hnsns.
    pose proof (ind_relate D HD Hc Hsu p Hl u0 w1 ns ns a0 (U_gargs _ _ Hw0 Hu0l Lw1) Hu0l Ha0 Hnsns) as Hrel.
    assert (E : ind_rel p D u0 nr ar dr ns <~> R12) by (eapply per_univ_elem_chain_iff; [ exact Hrel | exact HR12 ]).
    eapply gargs_env_rel_gen; [ exact HRΓ | exact HRM | exact HM | exact HB | rewrite List.length_app, length_elim_mctx; cbn; lia |].
    unfold elim_mctx; cbn [List.rev].
    destruct (per_univ_elem_to_nat _ _ _ _ HR12) as [n Hn].
    apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R12); [ rewrite List.length_rev, length_ind_nparams_sub; lia | exact Hg | exact (mk_rel_mod_eval _ _ Et1 Et2 Hn) |].
    apply E; exact Hm.
  Qed.

  (** ** Instances of a Closed Telescope

      Arguments related at a closed telescope over the canonical uniform
      parameters are related at its instance, over any related
      environments whose uniform parameters are related to the canonical
      ones. *)
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
      destruct (sem_ctx_ass_inv HS) as [j HXi].
      pose proof (sem_ctx_tail HS) as HS'.
      destruct (sem_ctx_ass_inv HK) as [j' HXc].
      pose proof (sem_ctx_tail HK) as HK'.
      pose proof (IH HKa' HK' HS' _ _ _ _ HB Hu1 Hu2 H10 H20 _ _ Hg0 Lz0) as IHz.
      destruct (sem_ctx_per_ctx_env HS') as [RS HRS].
      assert (HE : RS (env_args B1 zs0) (env_args B2 zs0'))
        by (eapply gargs_env_rel_gen; [ exact HRΓ | exact HRS | exact HS' | exact HB | rewrite length_tele_sub; exact Lz0 | exact IHz ]).
      destruct (rel_exp_of_typ_inversion_simple_at HRS HXi _ _ HE) as (t1 & t2 & Et1 & Et2 & [R12 HR12]).
      assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
      assert (HEE : RS (env_args B1 zs0) (env_args B1 zs0)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
      (** The closed side. *)
      destruct (sem_ctx_per_ctx_env HK') as [RK HRK].
      assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
      pose proof (U_gargs _ _ H10 Lu1 Hu0l) as Hg10.
      assert (HU00 : RU (env_args nil u0) (env_args nil u0))
        by (apply (gargs_env_rel _ _ _ _ _ _ HRU Usem); [ rewrite Hu0l, length_ind_uparams by exact Hle; reflexivity | exact Hu0g ]).
      assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK').
      pose proof (per_gargs_refl_l _ _ _ HRU HKr (List.Forall_rev HPa) (env_args nil u0) (env_args nil u0) zs0 zs0' HU00 Hg0) as Hg00.
      pose proof (per_gargs_base _ _ _ HRU HKr (List.Forall_rev HPa) (env_args nil u0) (env_args nil u0)
                    (env_args nil u1) (env_args nil u0) zs0 zs0 HU00 (symmetry H10) HU00 Hg00) as Hgb.
      assert (HK1 : RK (env_args (env_args B1 u1) zs0) (env_args nil (u0 ++ zs0))).
      { rewrite <- env_args_app.
        eapply (closed_env_base _ _ _ _ nil nil); [ exact HKa' | exact HK' | exact HRK
                                                  | rewrite !List.length_app, length_ind_uparams by exact Hle; lia
                                                  | rewrite !List.length_app, length_ind_uparams by exact Hle; lia |].
        apply (gargs_env_rel _ _ _ _ _ _ HRK HK'); [ rewrite !List.length_app, length_ind_uparams by exact Hle; lia |].
        rewrite List.rev_app_distr; apply per_gargs_app_intro;
          [ rewrite List.length_rev, length_ind_uparams by exact Hle; exact Lu1 | exact Hg10 | exact Hgb ]. }
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

  (** ** A Constructor's Arguments, Canonically *)
  Lemma ind_args_rel_at : forall pre gs vs vs', ind_args_rel p D u0 nr ar dr pre gs vs vs' ->
      forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      exists x x', List.nth_error vs (List.length gs1) = Some x /\ List.nth_error vs' (List.length gs1) = Some x' /\
        ind_shape_rel p D u0 nr ar dr (pre ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t x x'.
  Proof.
    induction 1; intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst;
      try match goal with IH : forall _ _ _, _ = _ -> _ |- _ => destruct (IH _ _ _ eq_refl) as (x & x' & Hx & Hx' & Hr0) end.
    - exists x, x'; cbn; rewrite <- List.app_assoc in Hr0; repeat split; assumption.
    - do 2 eexists; cbn; rewrite List.app_nil_r; repeat split; eassumption.
    - exists x, x'; cbn; repeat split; assumption.
  Qed.

  Section ConGargs.
    Variable (c : String.string) (gs : list carg).
    Hypothesis (Hcon : ind_con D c = Some gs).
    Let HΨ := sd_cargs D HD p c gs Hl Hcon.
    Let HnPs := proj1 u0_canon.

    Lemma cargs_gargs : forall ns nsa nsb vs vs',
        tele_full nr T ns nsa -> tele_full nr T ns nsb ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar dr ns gs vs vs' ->
        forall k, k <= List.length gs ->
        per_gargs (List.rev (cargs_ctx p D (List.firstn k gs))) (env_args nil (u0 ++ nsa)) (env_args nil (u0 ++ nsb))
          (List.firstn k vs) (List.firstn k vs').
    Proof.
      intros * Ha Hb Har Hia.
      pose proof (tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ Ha) as Hnn.
      pose proof (tnr_trans p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ _
                    (tnr_sym p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ Ha) Hb) as Hab.
      pose proof (tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ Hab) as Haa.
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Hlv Hlv'].
      pose proof Ha as HaL; rewrite tele_full_iff in HaL; destruct HaL as (Ln & Lna & _).
      pose proof Hb as Hb0; rewrite tele_full_iff in Hb0; destruct Hb0 as (_ & Lnb & _).
      unfold T in Ln, Lna, Lnb; rewrite List.length_rev, length_nparams in Ln, Lna, Lnb.
      assert (Hpg : per_gargs (List.rev (ind_params D)) nil nil (u0 ++ nsa) (u0 ++ nsb)) by (eapply params_gargs; eassumption).
      induction k as [| k IH]; intros Hk; [ cbn; constructor |].
      destruct (nth_error_lt_some' gs k ltac:(lia)) as [g Hg].
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [x Hx].
      destruct (nth_error_lt_some' vs' k ltac:(lia)) as [x' Hx'].
      assert (Heq : gs = List.firstn k gs ++ g :: List.skipn (S k) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn k gs) = k) by (rewrite List.length_firstn; lia).
      set (gs1 := List.firstn k gs) in *.
      set (fa := List.firstn k vs); set (fa' := List.firstn k vs').
      assert (Lfa : List.length fa = k) by (unfold fa; rewrite List.length_firstn; lia).
      assert (Lfa' : List.length fa' = k) by (unfold fa'; rewrite List.length_firstn; lia).
      pose proof (IH ltac:(lia)) as IHk.
      rewrite (firstn_S_snoc _ _ _ Hg), (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx').
      fold gs1 fa fa'.
      rewrite cargs_ctx_snoc, List.rev_app_distr.
      (** The prefix's context, and the entry's type there. *)
      pose proof (cargs_prefix_sem D p gs HΨ (gs1 ++ g :: nil) (List.skipn (S k) gs)
                    ltac:(rewrite <- List.app_assoc; exact Heq)) as HC1.
      rewrite cargs_ctx_snoc, <- List.app_assoc in HC1.
      pose proof (sem_ctx_app_r _ _ HC1) as HC0.
      destruct (sem_ctx_per_ctx_env HC0) as [R0 HR0].
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      assert (Lc : List.length (u0 ++ nsa ++ fa) = List.length (cargs_ctx p D gs1 ++ ind_params D))
        by (pose proof Hle; rewrite !List.length_app, length_cargs_ctx; unfold ind_nn, ind_np in *; lia).
      assert (HE : R0 (env_args nil (u0 ++ nsa ++ fa)) (env_args nil (u0 ++ nsb ++ fa'))).
      { apply (gargs_env_rel _ _ _ _ _ _ HR0 HC0 Lc).
        rewrite List.rev_app_distr, !List.app_assoc; apply per_gargs_app_intro;
          [ pose proof Hle; rewrite List.length_rev, List.length_app; unfold ind_nn, ind_np in *; lia | exact Hpg |].
        exact IHk. }
      assert (HEE : R0 (env_args nil (u0 ++ nsa ++ fa)) (env_args nil (u0 ++ nsa ++ fa)))
        by (etransitivity; [ exact HE | symmetry; exact HE ]).
      assert (Hpre : forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
                 R (env_args nil (u0 ++ nsa ++ fa)) (env_args nil (u0 ++ nsa ++ fa))).
      { intros R HR; assert (E : R0 <~> R) by (eapply per_ctx_env_right_irrel; eassumption); apply E; exact HEE. }
      (** The non-recursive arguments before, canonically. *)
      set (K := List.length (cargs_nonrec gs1)).
      assert (Hnv : List.firstn K (nonrec_vals gs vs) = nonrec_vals gs1 fa /\ List.firstn K (nonrec_vals gs vs') = nonrec_vals gs1 fa').
      { rewrite <- (List.firstn_skipn k vs), <- (List.firstn_skipn k vs'); fold fa fa'.
        rewrite Heq at 1 2; fold gs1.
        rewrite !nonrec_vals_app by lia.
        rewrite !firstn_app_exact by (apply length_nonrec_vals; lia); split; reflexivity. }
      pose proof Har as Har0; rewrite tele_full_iff in Har0; destruct Har0 as (Lar & Lar' & Harr).
      destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app List.rev] in HC1 |- *.
      - destruct (sem_ctx_ass_inv HC1) as [j HT].
        destruct (rel_exp_of_typ_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
        assert (Et2 : ⟦ A[wk_pat (cargs_pat gs1)]ʷ ⟧ env_args (env_args nil (u0 ++ nsa)) fa ↘ t)
          by (rewrite <- env_args_app, <- List.app_assoc; exact Et).
        assert (Et2' : ⟦ A[wk_pat (cargs_pat gs1)]ʷ ⟧ env_args (env_args nil (u0 ++ nsb)) fa' ↘ t')
          by (rewrite <- env_args_app, <- List.app_assoc; exact Et').
        destruct (per_univ_elem_to_nat _ _ _ _ HR) as [n Hn].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R); [ rewrite List.length_rev, length_cargs_ctx; lia | exact IHk
                                                     | exact (mk_rel_mod_eval _ _ Et2 Et2' Hn) |].
        pose proof (arg_entry_char c gs Hcon gs1 A _ Heq u0 nsa fa (eq_trans Lfa (eq_sym Lk)) Hpre _ _ _ _ Et HR) as ER.
        apply ER.
        (** The canonical relation at [ns], moved to [nsa]. *)
        assert (HxK : List.nth_error (nonrec_vals gs vs) K = Some x /\ List.nth_error (nonrec_vals gs vs') K = Some x').
        { rewrite <- (List.firstn_skipn k vs), <- (List.firstn_skipn k vs'); fold fa fa'.
          rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx').
          rewrite Heq at 1 2; fold gs1.
          rewrite !nonrec_vals_app by lia; cbn [nonrec_vals].
          rewrite !List.nth_error_app2 by (rewrite length_nonrec_vals by lia; unfold K; lia).
          rewrite !length_nonrec_vals by lia; fold K; rewrite Nat.sub_diag; split; reflexivity. }
        pose proof (Harr K x x' (proj1 HxK) (proj2 HxK)) as Hr; rewrite (proj1 Hnv) in Hr.
        assert (HA : List.nth_error (cargs_nonrec gs) K = Some A)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        assert (Hpk : tele_pre (ar ns c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa')).
        { rewrite <- (proj1 Hnv), <- (proj2 Hnv); apply tele_pre_of_full with (T := cargs_nonrec gs); [ exact Har |].
          rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia. }
        assert (Hpkd : tele_pre (ar ns c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa)).
        { eapply (tar_pre_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs Hnn Hcon);
            [ rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia | exact Hpk ]. }
        exact (proj1 (HaI _ _ _ _ _ _ _ _ Ha Hcon HA Hpkd x x') Hr).
      - destruct (sem_ctx_ass_inv HC1) as [j HT].
        destruct (rel_exp_of_typ_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
        assert (Et2 : ⟦ ptyp_ty p D (cargs_pat gs1) Ps ⟧ env_args (env_args nil (u0 ++ nsa)) fa ↘ t)
          by (rewrite <- env_args_app, <- List.app_assoc; exact Et).
        assert (Et2' : ⟦ ptyp_ty p D (cargs_pat gs1) Ps ⟧ env_args (env_args nil (u0 ++ nsb)) fa' ↘ t')
          by (rewrite <- env_args_app, <- List.app_assoc; exact Et').
        destruct (per_univ_elem_to_nat _ _ _ _ HR) as [n Hn].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R); [ rewrite List.length_rev, length_cargs_ctx; lia | exact IHk
                                                     | exact (mk_rel_mod_eval _ _ Et2 Et2' Hn) |].
        assert (Hpk : tele_pre (ar ns c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa)).
        { assert (Hpk0 : tele_pre (ar ns c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa')).
          { rewrite <- (proj1 Hnv), <- (proj2 Hnv); apply tele_pre_of_full with (T := cargs_nonrec gs); [ exact Har |].
            rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia. }
          eapply (tar_pre_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs Hnn Hcon);
            [ rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia | exact Hpk0 ]. }
        assert (HKl : K <= List.length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia).
        pose proof (tarp_inst p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns nsa c gs K _ _ Ha Hcon HKl Hpk) as Hpka.
        pose proof (per_univ_trans _ _ _ _ _ _ HR (per_univ_sym _ _ _ _ HR)) as HRd.
        pose proof (shape_char D HDc Hc Hsu p Hl c gs Hcon HΨ gs1 Ps _ Heq u0 nsa fa a0 Hu0l ltac:(lia) (eq_trans Lfa (eq_sym Lk))
                      Hu0g Ha0 Haa Hpka Hpre (List.length (ptyp_doms Ps)) 0 nil t j R eq_refl (tele_pre_nil _)
                      ltac:(cbn; constructor) ltac:(rewrite List.app_nil_r; exact Et) HRd) as ER.
        rewrite List.app_nil_r in ER; cbn [ptyp_skip] in ER.
        apply ER.
        destruct (ind_args_rel_at _ _ _ _ Hia gs1 Ps _ Heq) as (y & y' & Hy & Hy' & Hrel).
        rewrite Lk in Hy, Hy', Hrel; rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
        fold fa in Hrel.
        rewrite <- (List.app_nil_r (nonrec_vals gs1 fa)) in Hrel |- *.
        refine (proj1 (proj2 (proj2 (ind_rel_move p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI u0 Had)))
                  _ _ _ _ Hrel ns nsa c gs1 Ps _ (nonrec_vals gs1 fa) 0 nil eq_refl Ha ltac:(rewrite <- Heq; exact Hcon)
                  Hpk eq_refl ltac:(lia) (tele_pre_nil _)).
    Qed.
  End ConGargs.

  (** ** The Branch's Type as an Instance of the Motive *)
  Definition bty_args (c : String.string) (gs : list carg) : list exp :=
    let n := (ind_nn D + List.length gs + cargs_nrec gs)%nat in
    vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++
    apps (a_con p c) (List.map (fun U => U[wk_shiftn n]ʷ) Us ++
                      vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ++ vars_from (cargs_nrec gs) (List.length gs)) :: nil.

  Lemma elim_bty_args : forall c gs A,
      elim_bty p D c gs A Us = A[sb_of_list (sb_of_wk (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs))) (bty_args c gs)].
  Proof. reflexivity. Qed.

  Lemma gsub_bty : forall A c gs, ind_con D c = Some gs ->
      ⊨ elim_bctx p D gs A Us ++ Γ ->
      gsub (elim_bctx p D gs A Us ++ Γ)
        (sb_of_list (sb_of_wk (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs))) (bty_args c gs))
        (elim_mctx p D Us ++ Γ).
  Proof.
    intros * Hcon HB.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    set (n := ind_nn D + List.length gs + cargs_nrec gs).
    set (IHs := ihs_ctx_aux D A Us (List.length gs) nil 0 gs).
    set (Cs := tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us))).
    set (Ns := tele_sub (ind_nparams D) (sb_of_list Id Us)).
    assert (HBeq : elim_bctx p D gs A Us ++ Γ = (IHs ++ Cs) ++ Ns ++ Γ) by (unfold elim_bctx; rewrite <- !List.app_assoc; reflexivity).
    assert (HlI : List.length IHs = cargs_nrec gs) by (unfold IHs; apply length_ihs_ctx_aux).
    assert (HlC : List.length Cs = List.length gs) by (unfold Cs; rewrite length_tele_sub, length_cargs_ctx; reflexivity).
    assert (HlN : List.length Ns = ind_nn D) by (unfold Ns; apply length_ind_nparams_sub).
    assert (Hwj : elim_bctx p D gs A Us ++ Γ ⊨ʷ (wk_shiftn n) : Γ).
    { replace n with (List.length (elim_bctx p D gs A Us))
        by (unfold elim_bctx; fold IHs Cs Ns; rewrite !List.length_app, HlI, HlC, HlN; unfold n; lia).
      apply rel_wk_under_ctx_shiftn; exact HB. }
    pose proof (gsub_wk _ _ _ Hwj HB HΓ) as Hg0.
    set (Us' := List.map (fun U => U[wk_shiftn n]ʷ) Us).
    assert (HUs' : forall k U T0, List.nth_error Us' k = Some U ->
               List.nth_error (tele_insts (ind_uparams D) Id Us') k = Some T0 -> elim_bctx p D gs A Us ++ Γ ⊨ U : T0).
    { intros k U' T' HU HT; unfold Us' in *.
      rewrite <- tele_insts_closed_wk in HT by (first [ exact Ua | exact (decl_uparams_closed D Hc) ]).
      apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T0 & HT & ->).
      exact (rel_exp_under_ctx_wk Hwj (HUs _ _ _ HU HT)). }
    assert (Hvars : forall τ, (forall y, y < ind_nu D -> sentry_exp (τ y) = (sentry_exp (sb_of_list Id Us y))[wk_shiftn n]ʷ) ->
               forall k N T0, List.nth_error (vars_from (cargs_nrec gs + List.length gs) (ind_nn D)) k = Some N ->
                 List.nth_error (tele_insts (ind_nparams D) τ (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) k = Some T0 ->
                 elim_bctx p D gs A Us ++ Γ ⊨ N : T0).
    { intros τ Hτ k N T0 HN HT.
      replace (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))
        with (vars_from (List.length (IHs ++ Cs)) (List.length (ind_nparams D))) in HN, HT
        by (rewrite List.length_app, HlI, HlC, length_nparams; reflexivity).
      destruct (vars_tele_lookup (IHs ++ Cs) (ind_nparams D) (sb_of_list Id Us) τ Γ (ind_nu D)
                  (decl_closed_nparams_ass D Hc) (decl_nparams_mvc _ _ _ Hdt) (decl_closed_nparams_scoped D Hc)
                  ltac:(intros y Hy; rewrite Hτ by exact Hy; rewrite List.length_app, HlI, HlC, length_nparams; unfold n; f_equal; f_equal; lia)
                  _ _ _ HN HT) as (x & -> & Hx).
      rewrite HBeq; apply valid_exp_var; [ exact Hx | rewrite <- HBeq; exact HB ]. }
    apply gsub_of_list; [ exact Hg0 | apply elim_mctx_ass, Hc | exact HM
                        | unfold bty_args; rewrite List.length_app, length_vars_from, length_elim_mctx; cbn; lia |].
    intros k N T0 HN HT.
    unfold elim_mctx in HT.
    change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
    assert (Hrass : tele_ass Ns) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
    unfold bty_args in HN, HT; fold n Us' in HN, HT.
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_vars_from; symmetry; exact HlN).
    fold Ns in HT.
    assert (Hl2 : List.length (tele_insts Ns (sb_of_wk (wk_shiftn n)) (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) = ind_nn D)
      by (rewrite length_tele_insts by exact Hrass; rewrite HlN, length_vars_from; lia).
    destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
    - rewrite List.nth_error_app1 in HN by (rewrite length_vars_from; lia); rewrite List.nth_error_app1 in HT by lia.
      unfold Ns in HT; rewrite tele_insts_tele_sub in HT.
      apply (Hvars _ ltac:(intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; reflexivity) k); assumption.
    - rewrite List.nth_error_app2 in HN, HT by (rewrite ?length_vars_from; lia); rewrite length_vars_from in HN; rewrite Hl2 in HT.
      destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
      rewrite (List.map_ext _ (fun U => U[sb_of_wk (wk_shiftn n)]))
        by (intros a; replace (ind_nn D) with (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) at 1
              by apply length_vars_from; exact (exp_shift_past a nil _ _)).
      replace (vars_from 0 (ind_nn D)) with (vars_from 0 (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D))))
        by (rewrite length_vars_from; reflexivity).
      rewrite vars_from_sb_of_list.
      rewrite (List.map_ext (fun U => U[sb_of_wk (wk_shiftn n)]) (fun U => U[wk_shiftn n]ʷ)) by (intros; apply exp_sub_of_wk); fold Us'.
      clear Hk' Hk Hl2 k.
      rewrite (List.app_assoc Us'); apply (rel_exp_con_apps D HD Hc Hsu p Hl _ c gs); [ exact HB | exact Hcon | | | | ].
      + rewrite List.length_app, length_vars_from; unfold Us'; rewrite List.length_map, HUl; unfold ind_nn; lia.
      + rewrite params_split; intros k N T0 HN HT.
        rewrite tele_insts_app in HT;
          [| exact Ua | unfold Us'; rewrite List.length_map, HUl, length_ind_uparams by exact Hle; reflexivity ].
        assert (Hl1 : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_map; exact HUl).
        assert (Hl3 : List.length (tele_insts (ind_uparams D) Id Us') = ind_nu D)
          by (rewrite length_tele_insts by exact Ua; rewrite Hl1, length_ind_uparams by exact Hle; lia).
        destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk2 | Hk2].
        * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; exact (HUs' _ _ _ HN HT).
        * rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl1 in HN; rewrite Hl3 in HT.
          apply (Hvars (sb_of_list Id Us') ltac:(intros y Hy; unfold Us'; rewrite sb_of_list_map by lia; reflexivity) (k - ind_nu D)); [ exact HN | exact HT ].
      + rewrite length_vars_from; reflexivity.
      + intros k N T0 HN HT.
        replace (vars_from (cargs_nrec gs) (List.length gs)) with (vars_from (List.length IHs) (List.length (cargs_ctx p D gs))) in HN, HT
          by (rewrite HlI, length_cargs_ctx; reflexivity).
        destruct (vars_tele_lookup IHs (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)) (sb_of_list Id (Us' ++ vars_from (cargs_nrec gs + List.length gs) (ind_nn D))) (Ns ++ Γ) (ind_np D)
                    (cargs_ctx_aux_ass _ _ _ _) (cargs_ctx_mvc _ _ _ _ _ _ Hdt Hin) (decl_closed_cargs_scoped D Hc _ _ _ Hin)) with (k := k) (N := N) (T := T0)
          as (x & -> & Hx).
        * intros y Hy; rewrite length_cargs_ctx, HlI.
          destruct (Nat.lt_ge_cases y (ind_nn D)) as [Hy1 | Hy1].
          -- rewrite sb_of_list_app, sb_of_list_vars by lia; rewrite sb_qn_lt by exact Hy1; cbn; f_equal; lia.
          -- replace y with (List.length (vars_from (cargs_nrec gs + List.length gs) (ind_nn D)) + (y - ind_nn D)) at 1
               by (rewrite length_vars_from; lia).
             rewrite sb_of_list_app, sb_of_list_ge; unfold Us'; rewrite sb_of_list_map by (rewrite HUl; unfold ind_nn in *; lia).
             rewrite sb_qn_ge by exact Hy1; rewrite <- sentry_exp_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold n; lia.
        * exact HN.
        * exact HT.
        * rewrite HBeq, <- List.app_assoc; apply valid_exp_var; [ exact Hx | rewrite List.app_assoc, <- HBeq; exact HB ].
  Qed.

  (** ** The Arguments Before a Position, Weakened to Their Non-Recursive
      Ones, over [Γ] *)
  Lemma cargs_wk_ext : forall c gs, ind_con D c = Some gs -> forall gs1 gs2, gs = gs1 ++ gs2 ->
      cargs_ctx p D gs1 ++ ind_params D ++ Γ ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ ind_params D ++ Γ.
  Proof.
    intros c gs Hcon.
    pose proof (sd_cargs D HD p c gs Hl Hcon) as HΨ.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_strat cargs_pat List.rev List.map List.app].
      destruct (closed_app_sem _ _ (decl_closed_params D Hc) (sd_params _ HDc) HΓ) as [HPΓ _].
      destruct (sem_ctx_per_ctx_env HPΓ) as [R HR].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) ].
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as IHw.
      pose proof (cargs_prefix_sem D p gs HΨ (gs1 ++ g :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as HC.
      assert (HCa : tele_ass (cargs_ctx p D (gs1 ++ g :: nil) ++ ind_params D))
        by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
      destruct (closed_app_sem _ _ HCa HC HΓ) as [HCΓ _].
      rewrite <- List.app_assoc in HCΓ.
      rewrite cargs_ctx_snoc, cargs_pat_snoc in *.
      destruct g as [A0 | Ps]; cbn [cargs_ctx_aux List.app wk_pat] in *.
      + rewrite cargs_strat_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A0)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (sd_arg _ HDc _ _ _ _ Hcon HA) as (_ & j & HAv).
        assert (HSs : ⊨ astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D)
          by (apply (sd_strat _ HDc _ _ _ Hcon); rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
        rewrite Heq, <- astrat_prefix in HAv, HSs.
        assert (HSa : tele_ass (cargs_strat gs1 ++ ind_params D))
          by (apply List.Forall_app; split; [ rewrite cargs_strat_nonrec; apply List.Forall_rev, tele_ass_map_ass | apply decl_closed_params, Hc ]).
        pose proof (closed_app_valid _ _ _ _ _ HSa HSs HΓ HAv) as HAv'.
        rewrite <- List.app_assoc in HAv'.
        exact (rel_wk_under_ctx_q IHw HAv').
      + rewrite cargs_strat_snoc_rec.
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HCΓ) IHw).
  Qed.

  (** ** The Branches' Contexts

      The recursive results of a constructor's arguments are related at
      the motive's family, read at the environments [C1] and [C2]. *)
  Let tsym := tnr_sym p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI.
  Let ttrans := tnr_trans p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI.
  Let trefl_r := tnr_refl_r p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI.

  Lemma eval_apps_con : forall c gs ys xs, ind_con D c = Some gs -> List.length xs + List.length ys <= ind_np D + List.length gs ->
      $*| d_con p c xs & ys | gc_deps ⍮ gc_stack ↘ d_con p c (xs ++ ys).
  Proof.
    intros c gs; induction ys as [| y ys IH]; intros xs Hcon Hlen; [ rewrite List.app_nil_r; constructor |].
    econstructor; [ eapply eval_app_con; [ exact Hl | exact Hcon | cbn in *; lia ] |].
    replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
    apply IH; [ exact Hcon | rewrite List.length_app; cbn in *; lia ].
  Qed.

  Section Bctx.
    Variable (A : exp) (iA : nat).
    Hypothesis (HAv : elim_mctx p D Us ++ Γ ⊨ A : Typeω@iA).
    Variable (C1 C2 : env).
    Hypothesis (HC12 : RΓ C1 C2) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
    Let Rel := fun ns m ns' m' => per_head A A (env_args C1 (ns ++ m :: nil)) (env_args C2 (ns' ++ m' :: nil)).
    Variable (c : String.string) (gs : list carg).
    Hypothesis (Hcon : ind_con D c = Some gs) (HB : ⊨ elim_bctx p D gs A Us ++ Γ).
    Let HΨ := sd_cargs D HD p c gs Hl Hcon.

    Lemma us_rel : forall B, RΓ B C1 -> exists u, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u /\ RU (env_args nil u) (env_args nil u0).
    Proof.
      intros B HB1; destruct (us_vals B C1 HB1) as (u & u' & Hu & Hu' & H).
      pose proof (functional_eval_exps' _ _ _ _ Hu' HUC) as ->; eauto.
    Qed.

    Lemma bctx_split : elim_bctx p D gs A Us ++ Γ = ihs_ctx_aux D A Us (List.length gs) nil 0 gs ++ cinst Γ p D Us gs.
    Proof. unfold elim_bctx, cinst; rewrite <- !List.app_assoc; reflexivity. Qed.

    Lemma ihs_pre_sem : forall gs1 gs2, gs = gs1 ++ gs2 -> ⊨ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Us gs.
    Proof.
      intros * Heq; pose proof HB as H; rewrite bctx_split in H.
      replace (ihs_ctx_aux D A Us (List.length gs) nil 0 gs)
        with (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1 ++ nil) (0 + cargs_nrec gs1) gs2 ++ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) in H
        by (rewrite <- ihs_ctx_aux_app, <- Heq; reflexivity).
      rewrite <- List.app_assoc in H; exact (sem_ctx_app_r _ _ H).
    Qed.

    (** The arguments, at the closed telescope. *)
    Lemma closed_args_gargs : forall ns X X' vs vs',
        tele_full nr T ns X -> tele_full nr T ns X' ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar dr ns gs vs vs' ->
        forall k, k <= List.length gs ->
        per_gargs (List.rev (cargs_ctx p D (List.firstn k gs) ++ ind_nparams D)) (env_args nil u0) (env_args nil u0)
          (X ++ List.firstn k vs) (X' ++ List.firstn k vs').
    Proof.
      intros * HX HX' Har Hia k Hk.
      pose proof (cargs_gargs c gs Hcon ns X X' vs vs' HX HX' Har Hia k Hk) as Hc1.
      pose proof HX as HX0; rewrite tele_full_iff in HX0; destruct HX0 as (_ & LX & _).
      pose proof HX' as HX0'; rewrite tele_full_iff in HX0'; destruct HX0' as (_ & LX' & _).
      unfold T in LX, LX'; rewrite List.length_rev, length_nparams in LX, LX'.
      assert (Hpg : per_gargs (List.rev (ind_params D)) nil nil (u0 ++ X) (u0 ++ X'))
        by (pose proof (ttrans _ _ _ (tsym _ _ HX) HX') as HXX; eapply params_gargs; eassumption).
      rewrite params_split, List.rev_app_distr in Hpg.
      destruct (per_gargs_app _ _ _ _ u0 u0 X X' ltac:(rewrite List.length_rev, length_ind_uparams by exact Hle; exact Hu0l) Hpg
                  ltac:(rewrite List.length_rev, length_ind_uparams by exact Hle; exact Hu0l)) as [_ Hn].
      rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev, length_nparams; exact LX | exact Hn |].
      rewrite <- !env_args_app; exact Hc1.
    Qed.

    (** ** The Recursive Result of a Recursive Argument

        The recursive result of a recursive argument [x] of shape [t] is of
        a [Π] over the shape's domains, moved by [σ] into the branch's
        context, of the motive at the shape's parameters and [x] applied to
        the domains.  At related environments, it relates recursive results
        related by [ih_rel]: its domains are, after related values of the
        domains before, those of the canonical family [dr], and its end is
        the motive's family [Rel]. *)
    Section Entry.
      #[local] Set Default Proof Using "All".
      Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
      Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
      Let pat := cargs_pat gs1.
      Let K := List.length (cargs_nonrec gs1).
      Let E := ihs_ctx_aux D A Us (List.length gs) nil 0 gs1.
      Let Ctx := E ++ cinst Γ p D Us gs.
      Let j := cargs_nrec gs1.
      Let na := List.length gs.
      Let σ := ihs_sub D Us na pat j.
      Let m := j + na + ind_nn D.
      Let β := sb_of_wk (wk_shiftn m).
      Let idx := j + na - 1 - List.length pat.
      Let L := List.length (ptyp_doms t).
      Let Tg := cargs_strat gs1 ++ ind_params D ++ Γ.

      Lemma e_LE : List.length E = j.
      Proof. apply length_ihs_ctx_aux. Qed.

      Lemma e_Lpat : List.length pat = List.length gs1.
      Proof. apply length_cargs_pat. Qed.

      Lemma e_Lna : na = List.length gs1 + S (List.length gs2).
      Proof. unfold na; rewrite Heq, List.length_app; cbn; lia. Qed.

      Lemma e_HK : K <= List.length (cargs_nonrec gs).
      Proof. unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia. Qed.

      Lemma e_simp : ptyp_simple t = true.
      Proof. exact (Hsimp c gs gs1 t gs2 Hcon Heq). Qed.

      Lemma e_strat : cargs_strat gs1 = astrat gs (List.length (cargs_nonrec gs1)).
      Proof. rewrite Heq; apply astrat_prefix. Qed.

      Lemma entry_eq : ihs_ctx_aux D A Us na nil 0 (gs1 ++ ca_rec t :: nil) = ce_ass (ptyp_ihty A β σ (a_var idx) t) :: E.
      Proof.
        unfold E, β, σ, m, idx, j, na, pat; rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app Nat.add].
        reflexivity.
      Qed.

      Lemma e_HCtx : ⊨ Ctx.
      Proof. exact (ihs_pre_sem gs1 _ Heq). Qed.

      Lemma e_HCtxT : ⊨ (Ctx ▹ ptyp_ihty A β σ (a_var idx) t).
      Proof.
        pose proof (ihs_pre_sem (gs1 ++ ca_rec t :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as H.
        change (List.length gs) with na in H; rewrite entry_eq in H; exact H.
      Qed.

      Lemma e_Ksem : ⊨ cargs_strat gs1 ++ ind_params D.
      Proof. rewrite e_strat; apply (sd_strat _ HDc _ _ _ Hcon); exact e_HK. Qed.

      Lemma e_Kass : tele_ass (cargs_strat gs1 ++ ind_params D).
      Proof.
        apply List.Forall_app; split; [ rewrite cargs_strat_nonrec; apply List.Forall_rev, tele_ass_map_ass | apply decl_closed_params, Hc ].
      Qed.

      Lemma e_Tg : ⊨ Tg.
      Proof.
        destruct (closed_app_sem _ _ e_Kass e_Ksem HΓ) as [H _]; unfold Tg; rewrite <- List.app_assoc in H; exact H.
      Qed.

      (** The components' substitution. *)
      Lemma gsub_sigma : gsub Ctx σ Tg.
      Proof.
        assert (Hp1 : ⊨ cargs_ctx p D gs1 ++ ind_params D) by exact (cargs_prefix_sem D p gs HΨ gs1 _ Heq).
        assert (Hp1a : tele_ass (cargs_ctx p D gs1 ++ ind_params D))
          by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
        destruct (closed_app_sem _ _ Hp1a Hp1 HΓ) as [HΨ1Γ _].
        pose proof (gsub_wk _ _ _ (cargs_wk_ext c gs Hcon gs1 _ Heq) ltac:(rewrite <- List.app_assoc in HΨ1Γ; exact HΨ1Γ) e_Tg) as G0.
        assert (Hτ2 : gsub (cinst Γ p D Us gs1) (sb_qn (List.length pat + ind_nn D) (sb_of_list Id Us))
                        (cargs_ctx p D gs1 ++ ind_params D ++ Γ)).
        { rewrite cinst_eq.
          replace (List.length pat + ind_nn D) with (List.length (cargs_ctx p D gs1 ++ ind_nparams D))
            by (rewrite List.length_app, length_cargs_ctx, length_nparams, e_Lpat; lia).
          rewrite params_split, <- !List.app_assoc, (List.app_assoc (cargs_ctx p D gs1)).
          apply gsub_qn; [ exact gsub_U | apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ] |].
          rewrite params_split in HΨ1Γ; rewrite <- !List.app_assoc in HΨ1Γ |- *; rewrite <- List.app_assoc in HΨ1Γ; exact HΨ1Γ. }
        destruct (gsub_props Hτ2) as [Hτ2v Hτ2l].
        pose proof (gsub_comp _ _ _ _ _ G0 (gsub_sem_ctx _ _ _ Hτ2) Hτ2v Hτ2l) as G1.
        assert (Hw3 : Ctx ⊨ʷ (wk_shiftn (na - List.length pat + j)) : cinst Γ p D Us gs1).
        { pose proof e_HCtx as H0; unfold Ctx in H0 |- *.
          rewrite Heq in H0 |- *; rewrite cinst_split in H0 |- *; rewrite List.app_assoc in H0 |- *.
          match goal with |- ?C ++ _ ⊨ʷ _ : _ => replace (na - List.length pat + j) with (List.length C) end.
          - apply rel_wk_under_ctx_shiftn; exact H0.
          - rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux, e_LE, e_Lna, e_Lpat; cbn; lia. }
        exact (gsub_comp _ _ _ _ _ G1 e_HCtx (rel_sub_of_wk Hw3) (sub_link_wk Hw3)).
      Qed.

      (** The environments of the branch's context there. *)
      Variable (RS : relation env).
      Hypothesis (HRS : EF Ctx ≈ Ctx ∈ per_ctx_env ↘ RS).

      Lemma e_ctx_split : Ctx = (E ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU) ++ Γ.
      Proof. unfold Ctx; rewrite cinst_eq, List.app_assoc; reflexivity. Qed.

      Lemma e_Lm : forall (X fa : list domain) (v : domain) (aft ihp : list domain), List.length X = ind_nn D -> List.length fa = List.length gs1 ->
          List.length aft = List.length gs2 -> List.length ihp = j ->
          List.length (X ++ fa ++ v :: aft ++ ihp) = m.
      Proof. intros; unfold m; rewrite e_Lna; rewrite !List.length_app; cbn; rewrite List.length_app; lia. Qed.

      Lemma side_w : forall B X fa v aft ihp, RΓ B C1 ->
          List.length X = ind_nn D -> List.length fa = List.length gs1 ->
          List.length aft = List.length gs2 -> List.length ihp = j ->
          RS (env_args B (X ++ fa ++ v :: aft ++ ihp)) (env_args B (X ++ fa ++ v :: aft ++ ihp)) ->
          exists w, ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ w /\
            RU (env_args nil w) (env_args nil u0) /\ List.length w = ind_nu D.
      Proof.
        intros * HBC LX Lfa Laft Lihp HE.
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        pose proof HRS as HRS'; rewrite e_ctx_split in HRS'.
        pose proof e_HCtx as HC'; rewrite e_ctx_split in HC'.
        assert (Ll : List.length (X ++ fa ++ v :: aft ++ ihp) = List.length (E ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU)).
        { rewrite (e_Lm _ _ _ _ _ LX Lfa Laft Lihp), List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams, e_LE.
          unfold m, na; lia. }
        destruct (us_wk_vals _ _ B _ HRS' HC' HE Ll) as (w & uB & Hw & HuB & Hwu).
        rewrite <- Ll, (e_Lm _ _ _ _ _ LX Lfa Laft Lihp) in Hw.
        destruct (us_rel B HBC) as (uB' & HuB' & HuB0).
        pose proof (functional_eval_exps' _ _ _ _ HuB HuB') as <-.
        exists w; split; [ exact Hw | split; [ etransitivity; eassumption |] ].
        rewrite (eval_exps_length _ _ _ Hw), List.length_map; exact HUl.
      Qed.

      Lemma sigma_side : forall B X fa v aft ihp w,
          List.length X = ind_nn D -> List.length fa = List.length gs1 ->
          List.length aft = List.length gs2 -> List.length ihp = j ->
          ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ w ->
          ⟦ σ ⟧s env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ env_args B (w ++ X ++ nonrec_vals gs1 fa).
      Proof.
        intros * LX Lfa Laft Lihp Hw.
        assert (Hna : na = List.length gs1 + S (List.length aft)) by (rewrite e_Lna, Laft; reflexivity).
        unfold σ, m in *; rewrite Hna in *.
        exact (ihs_sub_eval D Us gs1 aft j B X fa v ihp w Hc HUl LX Lfa Lihp Hw).
      Qed.

      (** The canonical arguments of the closed telescope of the domains. *)
      Lemma e_canon_gargs : forall k ms ms' ws ws' ys ys', k <= L ->
          tele_full nr T ms ms' -> tele_pre (ar ms c) K ws ws' -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
          per_gargs (List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D)) nil nil
            (u0 ++ ms ++ ws ++ ys) (u0 ++ ms' ++ ws' ++ ys').
      Proof.
        intros * Hk Hm Hw Hy.
        pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Lms & Lms' & _).
        unfold T in Lms, Lms'; rewrite List.length_rev, length_nparams in Lms, Lms'.
        pose proof Hw as Hw0; rewrite tele_pre_iff in Hw0; destruct Hw0 as (Lws & Lws' & _).
        pose proof (params_gargs D HDc Hc Hsu _ _ _ _ _ Hu0g Hu0l Ha0 Hm) as Hpg.
        pose proof (ar_gargs D HDc Hc Hsu _ _ _ _ _ _ _ Hcon Hu0g Hu0l Ha0 Hm K ws ws' e_HK Hw) as Hgv.
        pose proof (dom_gargs D HDc Hc Hsu _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hu0g Hu0l Ha0 Hm Hw k ys ys' Hk Hy) as Hgd.
        rewrite e_strat; unfold astrat, doms_ctx.
        rewrite !List.rev_app_distr, !List.rev_involutive, <- List.firstn_map.
        rewrite (List.app_assoc u0), (List.app_assoc (u0 ++ ms)), (List.app_assoc u0 ms'), (List.app_assoc (u0 ++ ms')).
        pose proof e_HK as HK0.
        apply per_gargs_app_intro;
          [ rewrite !List.length_app, List.length_rev, List.length_firstn, List.length_map, params_split, List.length_app,
              length_nparams, length_ind_uparams by exact Hle; unfold K in *; lia | |].
        - apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams
                                         by exact Hle; lia | exact Hpg | exact Hgv ].
        - rewrite <- !List.app_assoc; exact Hgd.
      Qed.

      Lemma e_dctx : forall k, k <= L -> ⊨ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
      Proof. intros k Hk; rewrite e_strat; exact (sd_dctx _ HDc _ _ _ _ _ k Hcon Heq Hk). Qed.

      Lemma e_dass : forall k, tele_ass (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D).
      Proof. intros; apply List.Forall_app; split; [ apply List.Forall_rev, tele_ass_map_ass | exact e_Kass ]. Qed.

      Lemma e_dlen : forall k, k <= L -> List.length (doms_ctx (List.firstn k (ptyp_doms t))) = k.
      Proof. intros; rewrite doms_ctx_length, List.length_firstn; unfold L in *; lia. Qed.

      (** A side's environment of the closed telescope, against the canonical one. *)
      Lemma closed_link : forall k B w X nvs ys, k <= L -> RU (env_args nil w) (env_args nil u0) -> List.length w = ind_nu D ->
          List.length X = ind_nn D -> List.length nvs = K -> List.length ys = k ->
          per_gargs (List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D)) nil nil
            (u0 ++ X ++ nvs ++ ys) (u0 ++ X ++ nvs ++ ys) ->
          forall RK, EF doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D
                       ≈ doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D ∈ per_ctx_env ↘ RK ->
            RK (env_args (env_args B (w ++ X ++ nvs)) ys) (env_args nil (u0 ++ X ++ nvs ++ ys)).
      Proof.
        intros * Hk Hw Lw LX Lnvs Lys Hg RK HRK.
        set (Pre := doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_nparams D).
        assert (HPe : Pre ++ ind_uparams D = doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D)
          by (unfold Pre; rewrite params_split, <- !List.app_assoc; reflexivity).
        assert (LPre : List.length Pre = List.length (X ++ nvs ++ ys))
          by (unfold Pre; rewrite !List.length_app, e_dlen, length_nparams, cargs_strat_nonrec, List.length_rev, List.length_map by exact Hk; fold K; lia).
        rewrite <- HPe in Hg, HRK.
        rewrite List.rev_app_distr in Hg.
        destruct (per_gargs_app _ _ _ _ u0 u0 (X ++ nvs ++ ys) (X ++ nvs ++ ys)
                    ltac:(rewrite List.length_rev, length_ind_uparams by exact Hle; exact Hu0l) Hg
                    ltac:(rewrite List.length_rev, length_ind_uparams by exact Hle; exact Hu0l)) as [_ Hg1].
        replace (env_args (env_args B (w ++ X ++ nvs)) ys) with (env_args (env_args B w) (X ++ nvs ++ ys))
          by (rewrite <- !env_args_app, <- !List.app_assoc; reflexivity).
        apply (closed_pre_base Pre RK); [ rewrite HPe; apply e_dass | rewrite HPe; apply e_dctx, Hk | exact HRK
                                         | exact Hw | exact Lw | exact Hg1 | exact (eq_sym LPre) ].
      Qed.

      (** The domains' arguments at a side's value of the components. *)
      Lemma side_dom_gargs : forall k B w X nvs ys, k <= L -> RU (env_args nil w) (env_args nil u0) -> List.length w = ind_nu D ->
          List.length X = ind_nn D -> List.length nvs = K ->
          tele_full nr T X X -> tele_pre (ar X c) K nvs nvs -> tele_pre (shape_tr dr X nvs (ptyp_doms t)) k ys ys ->
          per_gargs (List.rev (doms_ctx (List.firstn k (ptyp_doms t)))) (env_args B (w ++ X ++ nvs)) (env_args B (w ++ X ++ nvs)) ys ys.
      Proof.
        intros * Hk Hw Lw LX Lnvs HX Hnvs Hys.
        pose proof (dom_gargs D HDc Hc Hsu _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hu0g Hu0l Ha0 HX Hnvs k ys ys Hk Hys) as Hgd.
        assert (HK0 : ⊨ cargs_strat gs1 ++ ind_params D) by exact e_Ksem.
        destruct (sem_ctx_per_ctx_env HK0) as [RK0 HRK0].
        assert (HPK : PER RK0) by (eapply per_env_PER; exact HRK0).
        pose proof (e_canon_gargs 0 X X nvs nvs nil nil ltac:(lia) HX Hnvs (tele_pre_nil _)) as Hg0.
        cbn [List.firstn doms_ctx List.map List.rev List.app] in Hg0; rewrite List.app_nil_r in Hg0.
        assert (Hc0 : RK0 (env_args B (w ++ X ++ nvs)) (env_args nil (u0 ++ X ++ nvs))).
        { pose proof (closed_link 0 B w X nvs nil ltac:(lia) Hw Lw LX Lnvs eq_refl) as H.
          cbn [List.firstn doms_ctx List.map List.rev List.app env_args List.fold_left] in H; rewrite !List.app_nil_r in H.
          apply H; [ exact Hg0 | exact HRK0 ]. }
        assert (Hcc : RK0 (env_args nil (u0 ++ X ++ nvs)) (env_args nil (u0 ++ X ++ nvs))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRK0 HK0);
            [ rewrite !List.length_app, cargs_strat_nonrec, List.length_rev, List.length_map, params_split, List.length_app,
                length_nparams, length_ind_uparams by exact Hle; fold K; lia | exact Hg0 ]. }
        eapply (per_gargs_base _ _ _ HRK0); [ rewrite List.rev_involutive; apply e_dctx, Hk
                                            | unfold doms_ctx; rewrite List.rev_involutive; apply tele_ass_map_ass
                                            | exact Hcc | symmetry; exact Hc0 | symmetry; exact Hc0 |].
        unfold doms_ctx; rewrite List.rev_involutive, <- List.firstn_map; exact Hgd.
      Qed.

      (** The domain of the [k]-th step at a side, against its canonical
          value. *)
      Lemma dom_link : forall k Bk, List.nth_error (ptyp_doms t) k = Some Bk ->
          forall B X fa v aft ihp w ys a,
          List.length X = ind_nn D -> List.length fa = List.length gs1 ->
          List.length aft = List.length gs2 -> List.length ihp = j -> List.length ys = k ->
          RS (env_args B (X ++ fa ++ v :: aft ++ ihp)) (env_args B (X ++ fa ++ v :: aft ++ ihp)) ->
          ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ w ->
          RU (env_args nil w) (env_args nil u0) -> List.length w = ind_nu D ->
          tele_full nr T X X -> tele_pre (ar X c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa) ->
          tele_pre (shape_tr dr X (nonrec_vals gs1 fa) (ptyp_doms t)) k ys ys ->
          ⟦ Bk[sb_qn k σ] ⟧ env_args (env_args B (X ++ fa ++ v :: aft ++ ihp)) ys ↘ a ->
          exists b (i : nat), ⟦ Bk ⟧ env_args nil (u0 ++ X ++ nonrec_vals gs1 fa ++ ys) ↘ b /\ Dom a ≈ b ∈ per_univ i.
      Proof.
        intros * HBk * LX Lfa Laft Lihp Lys HE Hw HwU Lw HX Hnvs Hys Ea.
        assert (Hk : k < L) by (unfold L; apply List.nth_error_Some; congruence).
        set (Δ := doms_ctx (List.firstn k (ptyp_doms t))).
        assert (LΔ : List.length Δ = k) by (apply e_dlen; lia).
        assert (Lnv : List.length (nonrec_vals gs1 fa) = K) by (apply length_nonrec_vals; exact Lfa).
        destruct (sd_dom _ HDc _ _ _ _ _ _ _ Hcon Heq HBk) as (_ & i0 & HBv).
        rewrite <- e_strat in HBv; fold Δ in HBv.
        pose proof (e_dctx k ltac:(lia)) as HKk; fold Δ in HKk.
        pose proof (e_dass k) as HKka; fold Δ in HKka.
        assert (HΔa : tele_ass Δ) by (unfold Δ, doms_ctx; apply List.Forall_rev, tele_ass_map_ass).
        destruct (closed_app_sem _ _ HKka HKk HΓ) as [HKkΓ _].
        rewrite <- !List.app_assoc in HKkΓ.
        pose proof (closed_app_valid _ _ _ _ _ HKka HKk HΓ HBv) as HBvΓ; rewrite <- !List.app_assoc in HBvΓ.
        pose proof (sigma_side _ _ _ _ _ _ _ LX Lfa Laft Lihp Hw) as Hσe.
        pose proof (side_dom_gargs k B w X (nonrec_vals gs1 fa) ys ltac:(lia) HwU Lw LX Lnv HX Hnvs Hys) as Hgy; fold Δ in Hgy.
        destruct (outer_typ_link Δ Tg Ctx RS σ _ _ Bk Bk i0 HΔa HKkΓ HBvΓ HRS (gsub_valid gsub_sigma) HE Hσe ys Hgy
                    ltac:(rewrite LΔ; exact Lys)) as (a' & b' & Ea' & Eb' & Hab).
        rewrite LΔ in Ea'; assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
        destruct (sem_ctx_per_ctx_env HKk) as [RK HRK].
        pose proof (closed_link k B w X _ ys ltac:(lia) HwU Lw LX Lnv Lys
                      (e_canon_gargs k X X _ _ ys ys ltac:(lia) HX Hnvs Hys) RK HRK) as HEK.
        destruct (rel_exp_of_typ_inversion_simple_at HRK HBv _ _ HEK) as (b1 & b & Eb1 & Eb & Hbb).
        assert (b1 = b') as -> by (eapply functional_eval_exp; eassumption).
        exists b, i0; split; [ exact Eb | etransitivity; [ exact Hab | exact Hbb ] ].
      Qed.

      (** The canonical arguments and the side's, one prefix along. *)
      Lemma side_refl : forall ns X nv nvs k ys0 ys, k <= L ->
          tele_full nr T ns X -> tele_pre (ar ns c) K nv nvs -> tele_pre (shape_tr dr ns nv (ptyp_doms t)) k ys0 ys ->
          tele_full nr T X X /\ tele_pre (ar X c) K nvs nvs /\ tele_pre (shape_tr dr X nvs (ptyp_doms t)) k ys ys.
      Proof.
        intros * Hk HX Hnv Hys.
        split; [ exact (trefl_r _ _ HX) | split ].
        - exact (tarp_refl_r p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns X c gs K nv nvs HX Hcon e_HK Hnv).
        - exact (tsh_refl_inst p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns X c gs gs1 t gs2 nv nvs k ys0 ys
                   HX Hcon Heq Hnv Hk Hys).
      Qed.

      (** The domain of the [k]-th step, at two sides related to the
          canonical arguments [ns], [nv] and [ys1]: the canonical family. *)
      Lemma dom_char : forall k Bk, List.nth_error (ptyp_doms t) k = Some Bk ->
          forall ns B1 X1 fa1 v1 aft1 ihp1 w1 ys1 B2 X2 fa2 v2 aft2 ihp2 w2 ys2 a1 a2 (i : nat) R,
          List.length X1 = ind_nn D -> List.length fa1 = List.length gs1 ->
          List.length aft1 = List.length gs2 -> List.length ihp1 = j -> List.length ys1 = k ->
          List.length X2 = ind_nn D -> List.length fa2 = List.length gs1 ->
          List.length aft2 = List.length gs2 -> List.length ihp2 = j -> List.length ys2 = k ->
          RS (env_args B1 (X1 ++ fa1 ++ v1 :: aft1 ++ ihp1)) (env_args B1 (X1 ++ fa1 ++ v1 :: aft1 ++ ihp1)) ->
          RS (env_args B2 (X2 ++ fa2 ++ v2 :: aft2 ++ ihp2)) (env_args B2 (X2 ++ fa2 ++ v2 :: aft2 ++ ihp2)) ->
          ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B1 (X1 ++ fa1 ++ v1 :: aft1 ++ ihp1) ↘ w1 ->
          ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B2 (X2 ++ fa2 ++ v2 :: aft2 ++ ihp2) ↘ w2 ->
          RU (env_args nil w1) (env_args nil u0) -> List.length w1 = ind_nu D ->
          RU (env_args nil w2) (env_args nil u0) -> List.length w2 = ind_nu D ->
          tele_full nr T ns X1 -> tele_full nr T ns X2 ->
          tele_pre (ar ns c) K (nonrec_vals gs1 fa1) (nonrec_vals gs1 fa2) ->
          tele_pre (shape_tr dr ns (nonrec_vals gs1 fa1) (ptyp_doms t)) k ys1 ys2 ->
          ⟦ Bk[sb_qn k σ] ⟧ env_args (env_args B1 (X1 ++ fa1 ++ v1 :: aft1 ++ ihp1)) ys1 ↘ a1 ->
          ⟦ Bk[sb_qn k σ] ⟧ env_args (env_args B2 (X2 ++ fa2 ++ v2 :: aft2 ++ ihp2)) ys2 ↘ a2 ->
          DF a1 ≈ a2 ∈ per_univ_elem i ↘ R ->
          (R <~> dr (ns ++ nonrec_vals gs1 fa1 ++ ys1) Bk).
      Proof.
        intros * HBk * LX1 Lfa1 Laft1 Lihp1 Lys1 LX2 Lfa2 Laft2 Lihp2 Lys2 HE1 HE2 Hw1 Hw2 HwU1 Lw1 HwU2 Lw2
                 HX1 HX2 Hnv Hys Ea1 Ea2 HR.
        assert (Hk : k < L) by (unfold L; apply List.nth_error_Some; congruence).
        set (nv1 := nonrec_vals gs1 fa1) in *; set (nv2 := nonrec_vals gs1 fa2) in *.
        assert (Lnv1 : List.length nv1 = K) by (apply length_nonrec_vals; exact Lfa1).
        assert (Lnv2 : List.length nv2 = K) by (apply length_nonrec_vals; exact Lfa2).
        assert (Hns : tele_full nr T ns ns) by exact (tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ HX1).
        assert (Hnv11 : tele_pre (ar ns c) K nv1 nv1)
          by exact (tar_pre_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs Hns Hcon K _ _ e_HK Hnv).
        assert (Hys11 : tele_pre (shape_tr dr ns nv1 (ptyp_doms t)) k ys1 ys1)
          by exact (tsh_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs gs1 t gs2 nv1 Hns Hcon Heq Hnv11 k _ _ ltac:(lia) Hys).
        destruct (side_refl ns X1 nv1 nv1 k ys1 ys1 ltac:(lia) HX1 Hnv11 Hys11) as (HX1d & Hnv1d & Hys1d).
        destruct (side_refl ns X2 nv1 nv2 k ys1 ys2 ltac:(lia) HX2 Hnv Hys) as (HX2d & Hnv2d & Hys2d).
        destruct (dom_link k Bk HBk B1 X1 fa1 v1 aft1 ihp1 w1 ys1 a1 LX1 Lfa1 Laft1 Lihp1 Lys1 HE1 Hw1 HwU1 Lw1 HX1d Hnv1d Hys1d Ea1)
          as (b1 & i1 & Eb1 & Hab1).
        destruct (dom_link k Bk HBk B2 X2 fa2 v2 aft2 ihp2 w2 ys2 a2 LX2 Lfa2 Laft2 Lihp2 Lys2 HE2 Hw2 HwU2 Lw2 HX2d Hnv2d Hys2d Ea2)
          as (b2 & i2 & Eb2 & Hab2).
        (** The canonical value. *)
        destruct (sd_dom _ HDc _ _ _ _ _ _ _ Hcon Heq HBk) as (_ & i0 & HBv).
        rewrite <- e_strat in HBv.
        pose proof (e_dctx k ltac:(lia)) as HKk.
        destruct (sem_ctx_per_ctx_env HKk) as [RK HRK].
        assert (Lc : forall (ms ws ys : list domain), List.length ms = ind_nn D -> List.length ws = K -> List.length ys = k ->
                   List.length (u0 ++ ms ++ ws ++ ys) = List.length (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D)).
        { intros * L1 L2 L3; rewrite !List.length_app, e_dlen, cargs_strat_nonrec, List.length_rev, List.length_map, params_split,
            List.length_app, length_nparams, length_ind_uparams by (exact Hle || lia); fold K; lia. }
        assert (LXn : List.length ns = ind_nn D)
          by (pose proof HX1 as H0; rewrite tele_full_iff in H0; destruct H0 as (H0 & _); unfold T in H0; rewrite List.length_rev, length_nparams in H0; exact H0).
        assert (E1 : RK (env_args nil (u0 ++ ns ++ nv1 ++ ys1)) (env_args nil (u0 ++ X1 ++ nv1 ++ ys1)))
          by (apply (gargs_env_rel _ _ _ _ _ _ HRK HKk); [ apply Lc; assumption | exact (e_canon_gargs k _ _ _ _ _ _ ltac:(lia) HX1 Hnv11 Hys11) ]).
        assert (E2 : RK (env_args nil (u0 ++ ns ++ nv1 ++ ys1)) (env_args nil (u0 ++ X2 ++ nv2 ++ ys2)))
          by (apply (gargs_env_rel _ _ _ _ _ _ HRK HKk); [ apply Lc; assumption | exact (e_canon_gargs k _ _ _ _ _ _ ltac:(lia) HX2 Hnv Hys) ]).
        destruct (rel_exp_of_typ_inversion_simple_at HRK HBv _ _ E1) as (c0 & b1' & Ec0 & Eb1' & Hcb1).
        destruct (rel_exp_of_typ_inversion_simple_at HRK HBv _ _ E2) as (c0' & b2' & Ec0' & Eb2' & Hcb2).
        assert (b1' = b1) as -> by (eapply functional_eval_exp; eassumption).
        assert (b2' = b2) as -> by (eapply functional_eval_exp; eassumption).
        assert (c0' = c0) as -> by (eapply functional_eval_exp; eassumption).
        (** The chain. *)
        assert (Ha1c : Dom a1 ≈ c0 ∈ per_univ i1) by (eapply per_univ_trans'; [ exact Hab1 | apply per_univ_sym'; exact Hcb1 ]).
        assert (Hca2 : Dom c0 ≈ a2 ∈ per_univ i0) by (eapply per_univ_trans'; [ exact Hcb2 | apply per_univ_sym'; exact Hab2 ]).
        assert (Hcc : Dom c0 ≈ c0 ∈ per_univ i0) by (eapply per_univ_trans'; [ exact Hcb1 | apply per_univ_sym'; exact Hcb1 ]).
        destruct Ha1c as [R1 HR1]; destruct Hcc as [Rc HRc].
        assert (ER1 : R <~> R1) by (eapply per_univ_elem_right_irrel; eassumption).
        assert (ER2 : R1 <~> Rc) by (eapply per_univ_elem_left_irrel; eassumption).
        pose proof (per_head_iff Ec0 Ec0 HRc) as ER3.
        unfold dr, ind_dr.
        etransitivity; [ exact ER1 | etransitivity; [ exact ER2 | exact ER3 ] ].
      Qed.

      (** ** The End *)
      Let Ps' := List.map (fun P => P[sb_qn L σ]) (ptyp_ps t).
      Let xL := ihx L (a_var idx).
      Let τL := sb_of_list (ihb L β) (Ps' ++ xL :: nil).
      Let ΨL := tele_sub (ptyp_tele t) σ ++ Ctx.

      Lemma e_LΨ : List.length (ptyp_tele t) = L.
      Proof. unfold ptyp_tele; apply doms_ctx_length. Qed.

      Lemma e_tele : ptyp_tele t = doms_ctx (List.firstn L (ptyp_doms t)).
      Proof. unfold ptyp_tele, L; rewrite List.firstn_all; reflexivity. Qed.

      Lemma gsub_qL : gsub ΨL (sb_qn L σ) (ptyp_tele t ++ Tg).
      Proof.
        rewrite <- e_LΨ; apply gsub_qn; [ exact gsub_sigma | unfold ptyp_tele, doms_ctx; apply List.Forall_rev, tele_ass_map_ass |].
        pose proof (e_dctx L (le_n _)) as H; rewrite <- e_tele in H.
        assert (Ha : tele_ass (ptyp_tele t ++ cargs_strat gs1 ++ ind_params D)) by (rewrite e_tele; apply e_dass).
        destruct (closed_app_sem _ _ Ha H HΓ) as [H' _]; unfold Tg; rewrite <- !List.app_assoc in H'; exact H'.
      Qed.

      Lemma e_HΨL : ⊨ ΨL.
      Proof. exact (gsub_sem_ctx _ _ _ gsub_qL). Qed.

      Lemma e_uc : shape_uc D Us (cargs_strat gs1 ++ ind_params D) σ β.
      Proof.
        intros x Hx.
        replace (x + (List.length (cargs_strat gs1 ++ ind_params D) - ind_nu D)) with (pat_nargs pat + (ind_nn D + x))
          by (rewrite List.length_app; unfold pat; rewrite pat_nargs_cargs_pat; unfold ind_nn, ind_np in *; lia).
        unfold σ, ihs_sub, β; cbn [sb_compose sb_of_wk sentry_sub].
        rewrite wk_pat_ge, sb_qn_ge by lia.
        replace (List.length pat + (ind_nn D + x) - (List.length pat + ind_nn D)) with x by lia.
        rewrite !sentry_sub_of_wk, sentry_wk_wk; f_equal; apply sentry_wk_wk_eq; intros z; cbn; unfold m; rewrite e_Lna, e_Lpat; lia.
      Qed.

      Lemma e_ucK : forall k, k <= L ->
          shape_uc D Us (doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D) (sb_qn k σ) (ihb k β).
      Proof.
        induction k as [| k IH]; intros Hk; [ exact e_uc |].
        destruct (nth_error_lt_some' (ptyp_doms t) k ltac:(unfold L in Hk; lia)) as [Bk HBk].
        rewrite (firstn_S_snoc _ _ _ HBk), doms_ctx_snoc; cbn [sb_qn ihb List.app].
        apply shape_uc_pi; [| apply IH; lia ].
        rewrite !List.length_app, params_split, List.length_app, length_ind_uparams by exact Hle; lia.
      Qed.

      Lemma e_base_eq : sb_eq (sb_of_wk (wk_shiftn (m + L))) (ihb L β).
      Proof.
        rewrite ihb_eq; unfold β; rewrite <- sb_of_wk_compose; apply sb_of_wk_cong; intros z; cbn; lia.
      Qed.

      Lemma e_ΨL_split : ΨL = (tele_sub (ptyp_tele t) σ ++ E ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU) ++ Γ.
      Proof. unfold ΨL; rewrite e_ctx_split, <- !List.app_assoc; reflexivity. Qed.

      Lemma e_LΨL : List.length (tele_sub (ptyp_tele t) σ ++ E ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU) = m + L.
      Proof.
        rewrite !List.length_app, !length_tele_sub, e_LΨ, e_LE, List.length_app, length_cargs_ctx, length_nparams; unfold m, na; lia.
      Qed.

      Lemma gsub_base : gsub ΨL (ihb L β) Γ.
      Proof.
        eapply gsub_eq; [| exact e_base_eq ].
        pose proof e_HΨL as H; rewrite e_ΨL_split in H |- *.
        apply gsub_wk; [ rewrite <- e_LΨL; apply rel_wk_under_ctx_shiftn; exact H | exact H | exact HΓ ].
      Qed.

      Lemma e_Ps_valid : forall k P T0, List.nth_error (ptyp_ps t) k = Some P ->
          List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) k = Some T0 ->
          ptyp_tele t ++ cargs_strat gs1 ++ ind_params D ⊨ P : T0.
      Proof.
        intros * HP HT; pose proof (sd_rec _ HDc _ _ _ _ _ _ _ _ Hcon Heq HP HT) as H; rewrite <- e_strat in H; exact H.
      Qed.

      Lemma gsub_nsub : gsub ΨL (sb_of_list (ihb L β) Ps') (tele_sub (ind_nparams D) τU ++ Γ).
      Proof.
        pose proof (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq) as HPl.
        apply gsub_of_list; [ exact gsub_base | apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact HNt
                            | unfold Ps'; rewrite List.length_map, length_tele_sub, length_nparams; exact HPl |].
        intros k N T0 HN HT.
        unfold Ps' in HN; apply nth_error_map_inv in HN as (P & HPk & ->).
        rewrite tele_insts_tele_sub in HT.
        set (σ0 := sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))).
        assert (HT0 : exists T1, List.nth_error (tele_insts (ind_nparams D) σ0 (ptyp_ps t)) k = Some T1).
        { assert (Hk : k < List.length (ptyp_ps t)) by (apply List.nth_error_Some; congruence).
          apply nth_error_lt_some'; rewrite length_tele_insts by (apply decl_closed_nparams_ass, Hc).
          rewrite length_nparams; lia. }
        destruct HT0 as [T1 HT1].
        pose proof (e_Ps_valid _ _ _ HPk HT1) as HP1.
        assert (Ha : tele_ass (ptyp_tele t ++ cargs_strat gs1 ++ ind_params D)) by (rewrite e_tele; apply e_dass).
        assert (Hs : ⊨ ptyp_tele t ++ cargs_strat gs1 ++ ind_params D) by (rewrite e_tele; apply e_dctx, le_n).
        pose proof (closed_app_valid _ _ _ _ _ Ha Hs HΓ HP1) as HP2; rewrite <- !List.app_assoc in HP2.
        pose proof (rel_exp_under_ctx_gsub gsub_qL HP2) as HP3.
        replace T0 with T1[sb_qn L σ]; [ exact HP3 |].
        rewrite <- (tele_insts_sub_mvc (ind_nparams D) (ind_nu D) σ0 _ (sb_qn L σ) (ptyp_ps t)) in HT.
        + apply nth_error_map_inv in HT as (T2 & HT2 & ->); rewrite HT1 in HT2; injection HT2 as ->; reflexivity.
        + apply decl_closed_nparams_ass, Hc.
        + apply (decl_nparams_mvc _ _ _ Hdt).
        + apply decl_closed_nparams_scoped, Hc.
        + intros y Hy; unfold σ0; cbn [sb_of_wk sentry_sub wk_shiftn].
          pose proof (e_ucK L (le_n _) y Hy) as H; rewrite <- e_tele in H.
          etransitivity; [| exact H ]; f_equal; f_equal.
          rewrite !List.length_app, e_LΨ, cargs_strat_nonrec, List.length_rev, List.length_map, params_split, List.length_app,
            length_nparams, length_ind_uparams by exact Hle; unfold ptyp_depth, K; fold L; lia.
      Qed.

      (** The recursive argument, in the branch's context. *)
      Lemma e_lookup : Ctx ∋ #idx : ptyp_ty_at p (List.map (fun U => U[β]) Us) σ t.
      Proof.
        unfold Ctx; rewrite Heq; rewrite cinst_split, List.app_assoc.
        rewrite <- !List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
        set (Lc := tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                    (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))).
        assert (HL : List.length Lc = List.length gs2) by (unfold Lc; rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity).
        replace idx with (0 + List.length (E ++ Lc)) by (rewrite List.length_app, HL, e_LE; unfold idx; rewrite e_Lna, e_Lpat; lia).
        match goal with |- _ ∋ # _ : ?T0 =>
          replace T0 with ((ptyp_ty p D (cargs_pat gs1) t)
                            [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))][wk_shift]ʷ[wk_shiftn (List.length (E ++ Lc))]ʷ)
        end.
        { apply ctx_lookup_app_r; constructor. }
        rewrite ptyp_ty_eq_at, ptyp_ty_at_sub, <- !exp_sub_of_wk, !ptyp_ty_at_sub, !List.map_map.
        rewrite (ptyp_ty_at_sb_eq _ _ _ _ σ); [ f_equal |].
        - unfold ind_uvars.
          rewrite (List.map_ext _ (fun M => M[sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us)][sb_of_wk (wk_shiftn (S (List.length (E ++ Lc))))]))
            by (intros; rewrite !exp_sub_sub; apply exp_sub_sb_eq; intros z; cbn [sb_compose];
                rewrite <- !sentry_sub_sub, (sb_qn_add _ _ _ z), !sentry_sub_of_wk, sentry_wk_wk; apply sentry_wk_wk_eq; intros w; cbn; lia).
          rewrite <- (List.map_map (fun M => M[sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us)])
                        (fun M => M[sb_of_wk (wk_shiftn (S (List.length (E ++ Lc))))])).
          rewrite length_cargs_pat, <- HUl, vars_from_sb_qn, List.map_map.
          apply List.map_ext; intros U; unfold β; rewrite !exp_sub_of_wk, !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn.
          rewrite List.length_app, HL, e_LE; unfold m; rewrite e_Lna; lia.
        - unfold σ, ihs_sub; intros y; cbn [sb_compose].
          rewrite !sentry_sub_sub; apply sentry_sub_sb_eq; intros z; cbn [sb_compose].
          unfold pat; rewrite <- (sb_qn_add _ _ _ z), length_cargs_pat.
          apply sentry_sub_sb_eq; intros w; cbn.
          rewrite List.length_app, HL, e_LE; f_equal; pose proof e_Lna as Hna0; pose proof e_Lpat as Hp0; unfold na, pat in *; lia.
      Qed.

      Lemma e_x_typed : ΨL ⊨ xL : apps (a_ind p) (List.map (fun U => U[ihb L β]) Us ++ Ps').
      Proof.
        pose proof (valid_exp_var e_lookup e_HCtx) as Hlk.
        rewrite (ptyp_ty_at_ctx_pi p t _ σ e_simp) in Hlk.
        unfold ptyp_depth in Hlk; fold L in Hlk.
        pose proof HM as HM'; rewrite mctx_split in HM'.
        destruct (sem_ctx_ass_inv HM') as [jI HIT].
        pose proof (rel_exp_under_ctx_gsub gsub_nsub HIT) as HIT'.
        unfold IT in HIT'; rewrite ind_head_inst in HIT' by (unfold Ps'; rewrite List.length_map; exact (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq)).
        replace (List.map (fun U => U[ihb L β]) Us) with (List.map (fun U => U[wk_shiftn L]ʷ) (List.map (fun U => U[β]) Us)) in HIT' |- *
          by (rewrite List.map_map; apply List.map_ext; intros U; rewrite <- exp_sub_of_wk, exp_sub_sub;
              apply exp_sub_sb_eq; rewrite ihb_eq; reflexivity).
        unfold xL; rewrite ihx_eq.
        apply (valid_apps_vars L (tele_sub (ptyp_tele t) σ) Ctx _ jI (a_var idx));
          [ rewrite length_tele_sub; exact e_LΨ | apply tele_ass_sub; unfold ptyp_tele, doms_ctx; apply List.Forall_rev, tele_ass_map_ass
          | exact e_HΨL | exact HIT' | exact Hlk ].
      Qed.

      Lemma gsub_leaf : gsub ΨL τL (elim_mctx p D Us ++ Γ).
      Proof.
        pose proof HM as HM'; rewrite mctx_split in HM'.
        destruct (sem_ctx_ass_inv HM') as [jI HIT].
        unfold τL; rewrite sb_of_list_app; cbn [sb_of_list].
        rewrite mctx_split.
        eapply gsub_ass; [ exact gsub_nsub | exact HIT |].
        unfold IT; rewrite ind_head_inst by (unfold Ps'; rewrite List.length_map; exact (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq)).
        exact e_x_typed.
      Qed.

      Lemma e_Htg : ⊨ ptyp_tele t ++ Tg.
      Proof.
        pose proof (e_dctx L (le_n _)) as H; rewrite <- e_tele in H.
        assert (Ha : tele_ass (ptyp_tele t ++ cargs_strat gs1 ++ ind_params D)) by (rewrite e_tele; apply e_dass).
        destruct (closed_app_sem _ _ Ha H HΓ) as [H' _]; unfold Tg; rewrite <- !List.app_assoc in H'; exact H'.
      Qed.

      (** The end at a side, against the motive at the parameters it
          evaluates to and the argument applied to the domains. *)
      Lemma leaf_link : forall ns nv0 ys0 bs B X fa v aft ihp w ys f a,
          List.length X = ind_nn D -> List.length fa = List.length gs1 ->
          List.length aft = List.length gs2 -> List.length ihp = j -> List.length ys = L ->
          RS (env_args B (X ++ fa ++ v :: aft ++ ihp)) (env_args B (X ++ fa ++ v :: aft ++ ihp)) ->
          ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ w ->
          RU (env_args nil w) (env_args nil u0) -> List.length w = ind_nu D ->
          tele_full nr T ns X -> tele_pre (ar ns c) K nv0 (nonrec_vals gs1 fa) ->
          tele_pre (shape_tr dr ns nv0 (ptyp_doms t)) L ys0 ys ->
          ⟦ ptyp_ps t ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ ns ++ nv0 ++ ys0) ↘ bs ->
          $*| v & ys | gc_deps ⍮ gc_stack ↘ f ->
          ⟦ A[τL] ⟧ env_args (env_args B (X ++ fa ++ v :: aft ++ ihp)) ys ↘ a ->
          exists Xq b, tele_full nr T bs Xq /\ ⟦ A ⟧ env_args B (Xq ++ f :: nil) ↘ b /\ Dom a ≈ b ∈ per_univ iA.
      Proof.
        intros * LX Lfa Laft Lihp Lys HE Hw HwU Lw HX Hnv Hys Ebs Ef Ea.
        set (Ep := env_args B (X ++ fa ++ v :: aft ++ ihp)) in *.
        set (nvs := nonrec_vals gs1 fa) in *.
        assert (Lnvs : List.length nvs = K) by (apply length_nonrec_vals; exact Lfa).
        assert (Lnv0 : List.length nv0 = K) by (pose proof Hnv as H0; rewrite tele_pre_iff in H0; destruct H0 as (H0 & _); exact H0).
        assert (Lys0 : List.length ys0 = L) by (pose proof Hys as H0; rewrite tele_pre_iff in H0; destruct H0 as (H0 & _); exact H0).
        assert (LXn : List.length ns = ind_nn D)
          by (pose proof HX as H0; rewrite tele_full_iff in H0; destruct H0 as (H0 & _); unfold T in H0; rewrite List.length_rev, length_nparams in H0; exact H0).
        destruct (side_refl ns X nv0 nvs L ys0 ys (le_n _) HX Hnv Hys) as (HXd & Hnvd & Hysd).
        assert (Hns : tele_full nr T ns ns) by exact (tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ HX).
        assert (Hnv0 : tele_pre (ar ns c) K nv0 nv0)
          by exact (tar_pre_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs Hns Hcon K _ _ e_HK Hnv).
        assert (Hys0 : tele_pre (shape_tr dr ns nv0 (ptyp_doms t)) L ys0 ys0)
          by exact (tsh_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs gs1 t gs2 nv0 Hns Hcon Heq Hnv0 L _ _ (le_n _) Hys).
        pose proof (sigma_side _ _ _ _ _ _ _ LX Lfa Laft Lihp Hw) as Hσe.
        set (ρσ := env_args B (w ++ X ++ nvs)) in *.
        pose proof (side_dom_gargs L B w X nvs ys (le_n _) HwU Lw LX Lnvs HXd Hnvd Hysd) as Hgy; rewrite <- e_tele in Hgy.
        assert (HΔa : tele_ass (ptyp_tele t)) by (unfold ptyp_tele, doms_ctx; apply List.Forall_rev, tele_ass_map_ass).
        destruct (sem_ctx_per_ctx_env e_HΨL) as [RSL HRSL].
        pose proof (tele_stage_rel (ptyp_tele t) Tg Ctx σ RS Ep ρσ HΔa e_Htg HRS (gsub_valid gsub_sigma) HE Hσe ys Hgy
                      ltac:(rewrite e_LΨ; exact Lys) RSL HRSL) as HEL.
        (** The closed telescope of the end. *)
        set (KL := ptyp_tele t ++ cargs_strat gs1 ++ ind_params D).
        assert (HKa : tele_ass KL) by (unfold KL; rewrite e_tele; apply e_dass).
        assert (HKs : ⊨ KL) by (unfold KL; rewrite e_tele; apply e_dctx, le_n).
        destruct (sem_ctx_per_ctx_env HKs) as [RK HRK].
        assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
        set (can0 := env_args nil (u0 ++ ns ++ nv0 ++ ys0)).
        set (Es := env_args ρσ ys).
        assert (Lc : forall (ms ws ys' : list domain), List.length ms = ind_nn D -> List.length ws = K -> List.length ys' = L ->
                   List.length (u0 ++ ms ++ ws ++ ys') = List.length KL).
        { intros * L1 L2 L3; unfold KL; rewrite !List.length_app, e_LΨ, cargs_strat_nonrec, List.length_rev, List.length_map, params_split,
            List.length_app, length_nparams, length_ind_uparams by exact Hle; fold K; lia. }
        assert (Hc0s : RK can0 (env_args nil (u0 ++ X ++ nvs ++ ys))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRK HKs); [ apply Lc; assumption |].
          unfold KL; rewrite e_tele; exact (e_canon_gargs L _ _ _ _ _ _ (le_n _) HX Hnv Hys). }
        assert (Hc00 : RK can0 can0) by (etransitivity; [ exact Hc0s | symmetry; exact Hc0s ]).
        assert (HEs : RK Es (env_args nil (u0 ++ X ++ nvs ++ ys))).
        { unfold Es, ρσ, KL in *; rewrite e_tele in HRK.
          apply (closed_link L B w X nvs ys (le_n _) HwU Lw LX Lnvs Lys); [| exact HRK ].
          exact (e_canon_gargs L _ _ _ _ _ _ (le_n _) HXd Hnvd Hysd). }
        assert (HEs0 : RK Es can0) by (etransitivity; [ exact HEs | symmetry; exact Hc0s ]).
        destruct (closed_app_sem _ _ HKa HKs HΓ) as [HKΓ HresK].
        (** The parameters of the end, against the canonical ones. *)
        assert (Hcomp : forall kk P T1, List.nth_error (ptyp_ps t) kk = Some P ->
                   List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) kk = Some T1 ->
                   exists m1 b, ⟦ P[sb_qn L σ] ⟧ env_args Ep ys ↘ m1 /\ ⟦ P ⟧ can0 ↘ b /\ per_head T1 T1 can0 can0 b m1).
        { intros * HP HT1.
          pose proof (e_Ps_valid _ _ _ HP HT1) as HPv; fold KL in HPv.
          pose proof (closed_app_valid _ _ _ _ _ HKa HKs HΓ HPv) as HPvΓ.
          assert (HPvΓ' : ptyp_tele t ++ Tg ⊨ P : T1) by (unfold KL in HPvΓ; unfold Tg; rewrite <- !List.app_assoc in HPvΓ; exact HPvΓ).
          destruct (outer_exp_link (ptyp_tele t) Tg Ctx RS σ Ep ρσ T1 P P HΔa e_Htg HPvΓ' HRS (gsub_valid gsub_sigma) HE Hσe ys Hgy
                      ltac:(rewrite e_LΨ; exact Lys)) as (RΔ & F & m1 & n & HRΔ & HF & Em1 & En & Hmn).
          rewrite e_LΨ in Em1.
          destruct (sem_ctx_per_ctx_env HKΓ) as [RKΓ HRKΓ].
          assert (HRKΓ' : EF ptyp_tele t ++ Tg ≈ ptyp_tele t ++ Tg ∈ per_ctx_env ↘ RKΓ)
            by (unfold Tg; unfold KL in HRKΓ; rewrite <- !List.app_assoc in HRKΓ; exact HRKΓ).
          assert (EΔ : RΔ <~> RKΓ) by (eapply per_ctx_env_right_irrel; [ exact HRΔ | exact HRKΓ' ]).
          assert (HF' : RK F Es) by (apply (HresK _ _ HRK HRKΓ), EΔ; exact HF).
          destruct (presup_rel_exp_under_ctx HPv) as [iT HT].
          destruct (rel_exp_under_ctx_simple_at HRK HPv _ _ HEs0) as (n' & b & En' & Eb & Hnb).
          assert (n' = n) as -> by (eapply functional_eval_exp; eassumption).
          assert (C1' : per_head T1 T1 F Es <~> per_head T1 T1 can0 can0).
          { apply (per_head_of_typ_resp HRK HT).
            apply rel_chain_cons; [ exact HF' |]. apply rel_chain_cons; [ exact HEs0 |]. apply rel_chain_of_pair; exact Hc00. }
          assert (C2' : per_head T1 T1 Es can0 <~> per_head T1 T1 can0 can0).
          { apply (per_head_of_typ_resp HRK HT).
            apply rel_chain_cons; [ exact HEs0 |]. apply rel_chain_cons; [ exact Hc00 |]. apply rel_chain_of_pair; exact Hc00. }
          exists m1, b; split; [ exact Em1 | split; [ exact Eb |] ].
          apply (per_head_sym _ _ _ _ _ _ HRK (rel_exp_under_ctx_refl_left HT) Hc00).
          exact (per_head_trans _ _ _ _ _ _ HRK (rel_exp_under_ctx_refl_left HT) Hc00 _ _ _ (proj1 (C1' _ _) Hmn) (proj1 (C2' _ _) Hnb)). }
        (** Their values. *)
        pose proof (length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq) as HPl.
        assert (HTex : forall kk, kk < ind_nn D ->
                   exists T1, List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) kk = Some T1).
        { intros kk Hkk; apply nth_error_lt_some'.
          rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc); rewrite length_nparams; lia. }
        destruct (IndCases.eval_exps_each Ps' (env_args Ep ys)) as [Xq HXq].
        { intros kk M HM0; unfold Ps' in HM0; rewrite List.nth_error_map in HM0.
          destruct (List.nth_error (ptyp_ps t) kk) as [P |] eqn:HP; cbn in HM0; [ injection HM0 as <- | discriminate ].
          assert (Hkk : kk < ind_nn D) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
          destruct (HTex _ Hkk) as [T1 HT1].
          destruct (Hcomp _ _ _ HP HT1) as (m1 & _ & Em1 & _); eauto. }
        (** The canonical parameters. *)
        assert (Hgall : per_gargs (List.rev (ptyp_tele t ++ astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D)) nil nil
                          (u0 ++ ns ++ nv0 ++ ys0) (u0 ++ ns ++ nv0 ++ ys0)).
        { rewrite <- e_strat, e_tele; exact (e_canon_gargs L _ _ _ _ _ _ (le_n _) Hns Hnv0 Hys0). }
        destruct (rec_closure D HDc Hc c gs gs1 t gs2 Hcon Heq u0 u0 ns ns nv0 nv0 ys0 ys0 Hu0l LXn Lnv0 Lys0 Hu0l LXn Lnv0 Lys0 Hgall)
          as (bs' & _ & Ebs' & _ & _ & Hil).
        pose proof (functional_eval_exps' _ _ _ _ Ebs' Ebs) as ->.
        assert (Htf : tele_full nr T bs Xq).
        { rewrite tele_full_iff; unfold T; rewrite List.length_rev, length_nparams.
          rewrite (eval_exps_length _ _ _ Ebs), (eval_exps_length _ _ _ HXq); unfold Ps'; rewrite List.length_map.
          split; [ exact HPl | split; [ exact HPl |] ].
          intros jj y y' Hy Hy'.
          assert (Hjj : jj < ind_nn D) by (rewrite <- HPl, <- (eval_exps_length _ _ _ Ebs); apply List.nth_error_Some; congruence).
          destruct (nth_error_lt_some' (ptyp_ps t) jj ltac:(lia)) as [P HP].
          destruct (HTex _ Hjj) as [T1 HT1].
          destruct (Hcomp _ _ _ HP HT1) as (m1 & b & Em1 & Eb & Hbm).
          destruct (IndCases.eval_exps_nth _ _ _ _ _ Ebs HP) as (b0 & Hb0 & Eb0).
          destruct (IndCases.eval_exps_nth _ _ _ _ _ HXq ltac:(unfold Ps'; rewrite List.nth_error_map, HP; reflexivity)) as (m2 & Hm2 & Em2).
          assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
          assert (m2 = m1) as -> by (eapply functional_eval_exp; eassumption).
          rewrite Hy in Hb0; injection Hb0 as ->; rewrite Hy' in Hm2; injection Hm2 as ->.
          unfold ptyp_depth in Hil; fold L in Hil |- *.
          apply (Hil _ _ _ HP HT1); exact Hbm. }
        (** The value of the end's substitution. *)
        assert (Lall : List.length (X ++ fa ++ v :: aft ++ ihp ++ ys) = m + L)
          by (rewrite !List.length_app; cbn; rewrite !List.length_app; unfold m; rewrite e_Lna; lia).
        assert (HEpys : env_args Ep ys = env_args B (X ++ fa ++ v :: aft ++ ihp ++ ys))
          by (unfold Ep; rewrite <- env_args_app, <- !List.app_assoc; cbn [List.app]; rewrite <- !List.app_assoc; reflexivity).
        assert (Hβe : ⟦ ihb L β ⟧s env_args Ep ys ↘ B).
        { apply (eval_sub_sb_eq _ _ _ _ e_base_eq).
          pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length (X ++ fa ++ v :: aft ++ ihp ++ ys)))
                        (env_args B (X ++ fa ++ v :: aft ++ ihp ++ ys)) (wk_mono_shiftn _)) as H.
          rewrite eval_wk_shiftn_args, Lall in H; rewrite HEpys; exact H. }
        assert (Ex : ⟦ xL ⟧ env_args Ep ys ↘ f).
        { unfold xL; rewrite ihx_eq; apply eval_apps_exp; exists v, ys; split; [| split; [| exact Ef ] ].
          - cbn [exp_wk]; rewrite HEpys.
            replace (wk_shiftn L idx) with (List.length (X ++ fa ++ v :: aft ++ ihp ++ ys) - 1 - (List.length X + List.length fa))
              by (rewrite Lall; cbn; unfold idx, m; rewrite e_Lna, e_Lpat; lia).
            pose proof (eval_var_args B (X ++ fa ++ v :: aft ++ ihp ++ ys) (List.length (X ++ fa ++ v :: aft ++ ihp ++ ys) - 1 - (List.length X + List.length fa))
                          ltac:(rewrite Lall; pose proof e_Lna; unfold m, na in *; lia)) as H0.
            replace (List.length (X ++ fa ++ v :: aft ++ ihp ++ ys) - 1 - (List.length (X ++ fa ++ v :: aft ++ ihp ++ ys) - 1 - (List.length X + List.length fa)))
              with (List.length X + List.length fa) in H0 by (rewrite Lall; pose proof e_Lna; rewrite List.length_app in Lall; unfold m, na in *; lia).
            rewrite nth_mid in H0; exact H0.
          - pose proof (eval_vars_from_args ys Ep nil) as H0; rewrite List.app_nil_r in H0; cbn [List.length] in H0.
            rewrite Lys in H0; exact H0. }
        assert (Hτe : ⟦ τL ⟧s env_args Ep ys ↘ env_args B (Xq ++ f :: nil)).
        { unfold τL; apply eval_sb_of_list; [ exact Hβe |].
          apply eval_exps_app; [ exact HXq | econstructor; [ exact Ex | constructor ] ]. }
        destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HAv HRSL (gsub_valid gsub_leaf) HEL Hτe) as (a' & b & Ea' & Eb & Hab).
        assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
        exists Xq, b; split; [ exact Htf | split; [ exact Eb | exact Hab ] ].
      Qed.

      (** The type of the recursive result after [k] domains at a side,
          against its canonical value: the motive in [B] at the shape's
          parameters, the domains at the canonical values of the
          components. *)
      Lemma ihty_link : forall n k B X fa v aft ihp w ys f a (i : nat) R, k + n = L ->
          List.length X = ind_nn D -> List.length fa = List.length gs1 ->
          List.length aft = List.length gs2 -> List.length ihp = j -> List.length ys = k -> RΓ B C1 ->
          RS (env_args B (X ++ fa ++ v :: aft ++ ihp)) (env_args B (X ++ fa ++ v :: aft ++ ihp)) ->
          ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_args B (X ++ fa ++ v :: aft ++ ihp) ↘ w ->
          RU (env_args nil w) (env_args nil u0) -> List.length w = ind_nu D ->
          tele_full nr T X X -> tele_pre (ar X c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa) ->
          tele_pre (shape_tr dr X (nonrec_vals gs1 fa) (ptyp_doms t)) k ys ys ->
          $*| v & ys | gc_deps ⍮ gc_stack ↘ f ->
          ind_shape_rel p D u0 nr ar dr (X ++ nonrec_vals gs1 fa ++ ys) (ptyp_skip k t) f f ->
          ⟦ ptyp_ihty A (ihb k β) (sb_qn k σ) (ihx k (a_var idx)) (ptyp_skip k t) ⟧
            env_args (env_args B (X ++ fa ++ v :: aft ++ ihp)) ys ↘ a ->
          DF a ≈ a ∈ per_univ_elem i ↘ R ->
          exists b, eval_ihty gc_deps gc_stack B A (env_args nil (u0 ++ X ++ nonrec_vals gs1 fa ++ ys)) (ptyp_skip k t) f b /\
            Dom a ≈ b ∈ per_univ i.
      Proof.
        pose proof (ind_rel_mv p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen) as imv.
        induction n as [| n IH]; intros * Hkn LX Lfa Laft Lihp Lys HBC HE Hw HwU Lw HX Hnv Hys Ef Hsh Ea HR.
        - assert (Hk : k = L) by lia; rewrite Hk in Lys, Hys, Hsh, Ea |- *; clear Hk Hkn.
          pose proof (ptyp_skip_end t e_simp) as HsL; change (List.length (ptyp_doms t)) with L in HsL.
          rewrite HsL in Hsh, Ea |- *.
          cbn [ptyp_ihty ptyp_ps] in Ea.
          destruct (ind_shape_self_inv _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & Ebs & Hir).
          destruct (leaf_link X (nonrec_vals gs1 fa) ys bs B X fa v aft ihp w ys f a LX Lfa Laft Lihp Lys HE Hw HwU Lw HX Hnv Hys
                      Ebs Ef Ea) as (Xq & b' & Htf & Eb' & Hab').
          destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
          assert (HBB : RΓ B B) by (etransitivity; [ exact HBC | symmetry; exact HBC ]).
          destruct (us_rel B HBC) as (u1 & Hu1 & H10).
          pose proof (cv_mctx B B u1 u1 HBB Hu1 Hu1 H10 H10 RM HRM Xq bs f f (tsym _ _ Htf) (imv _ _ _ _ Hir Htf)) as HEM.
          destruct (rel_exp_of_typ_inversion_simple_at HRM HAv _ _ HEM) as (b1 & b2 & Eb1 & Eb2 & Hb12).
          assert (b1 = b') as -> by (eapply functional_eval_exp; eassumption).
          exists b2; split; [ econstructor; eassumption |].
          eapply per_univ_trans'; [ eexists; exact HR | eapply per_univ_trans'; [ exact Hab' | exact Hb12 ] ].
        - assert (Hk : k < L) by lia.
          destruct (ptyp_skip_lt k t Hk) as (Bk & HBk & Hs).
          rewrite Hs in Hsh, Ea |- *.
          set (t' := ptyp_skip (S k) t) in *.
          cbn [ptyp_ihty] in Ea.
          inversion Ea; subst a.
          match goal with E : ⟦ Bk[sb_qn k σ] ⟧ _ ↘ ?x |- _ => rename x into a1; rename E into Ea1 end.
          basic_invert_per_univ_elem HR.
          match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
          destruct (dom_link k Bk HBk B X fa v aft ihp w ys a1 LX Lfa Laft Lihp Lys HE Hw HwU Lw HX Hnv Hys Ea1) as (b1 & i1 & Eb1 & Hab).
          destruct (per_univ_trans' _ _ _ _ _ (ltac:(eexists; exact equiv_a_a')) Hab) as [Rab HRab].
          assert (Ein : in_rel <~> Rab) by (eapply per_univ_elem_right_irrel; [ exact equiv_a_a' | exact HRab ]).
          eexists; split; [ econstructor; exact Eb1 |].
          eexists; eapply per_univ_elem_pi_canonical; [ exact HRab |].
          intros c0 c0' Hcc.
          assert (Hcc0 : in_rel c0 c0') by (apply Ein; exact Hcc).
          assert (Hc'c' : in_rel c0' c0') by (etransitivity; [ symmetry; exact Hcc0 | exact Hcc0 ]).
          assert (Hdr : dr (X ++ nonrec_vals gs1 fa ++ ys) Bk c0' c0').
          { unfold dr, ind_dr; intros i2 R1 b2 b2' Eb2 Eb2' HR1.
            assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
            assert (b2' = b1) as -> by (eapply functional_eval_exp; eassumption).
            pose proof (per_univ_sym _ _ _ _ HRab) as HRba.
            assert (E1 : Rab <~> R1) by (eapply per_univ_elem_right_irrel; [ exact HRba | exact HR1 ]).
            apply E1, Ein; exact Hc'c'. }
          assert (Hys' : tele_pre (shape_tr dr X (nonrec_vals gs1 fa) (ptyp_doms t)) (S k) (ys ++ c0' :: nil) (ys ++ c0' :: nil)).
          { apply tele_pre_snoc; [ exact Hys |]; unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HBk); exact Hdr. }
          destruct (ind_shape_pi_inv _ _ _ _ _ _ _ _ _ _ _ Hsh c0' c0' Hdr) as (fc & fc' & Efc & Efc' & Hsh').
          assert (fc' = fc) as -> by (eapply functional_eval_app; eassumption).
          destruct (Hcod _ _ Hcc0) as [a2 a2' Ea2 Ea2' Ha22].
          destruct (Hcod _ _ Hc'c') as [a3 a3' Ea3 Ea3' Ha33].
          assert (a3 = a2') as -> by (eapply functional_eval_exp; eassumption).
          assert (a3' = a2') as -> by (eapply functional_eval_exp; eassumption).
          assert (Ef' : $*| v & ys ++ c0' :: nil | gc_deps ⍮ gc_stack ↘ fc)
            by (apply eval_apps_app; exists f; split; [ exact Ef | econstructor; [ exact Efc | constructor ] ]).
          rewrite <- !List.app_assoc in Hsh'; cbn [List.app] in Hsh'.
          rewrite <- env_args_snoc in Ea2'.
          destruct (IH (S k) B X fa v aft ihp w (ys ++ c0' :: nil) fc a2' i _ ltac:(lia) LX Lfa Laft Lihp
                      ltac:(rewrite List.length_app, Lys; cbn; lia) HBC HE Hw HwU Lw HX Hnv Hys' Ef'
                      Hsh' Ea2' Ha33) as (b2 & Eb2 & Ha2b).
          destruct (per_univ_trans' _ _ _ _ _ (ltac:(eexists; exact Ha22)) Ha2b) as [R2 HR2].
          exists a2, b2, R2; split; [ exact Ea2 | split; [| exact HR2 ] ].
          apply (eval_fam_cod_ihfam _ _ _ _ _ _ fc); [ exact Efc |].
          replace (u0 ++ X ++ nonrec_vals gs1 fa ++ ys ++ c0' :: nil) with ((u0 ++ X ++ nonrec_vals gs1 fa ++ ys) ++ c0' :: nil) in Eb2
            by (rewrite <- !List.app_assoc; reflexivity).
          rewrite env_args_snoc in Eb2; exact Eb2.
      Qed.

      (** ** At Two Sides *)
      Section Sides.
        Variable (ns : list domain).
        Variable (B1 B2 : env) (X1 X2 fa1 fa2 aft1 aft2 ihp1 ihp2 w1 w2 : list domain) (v1 v2 : domain).
        Hypothesis (LX1 : List.length X1 = ind_nn D) (LX2 : List.length X2 = ind_nn D)
          (Lfa1 : List.length fa1 = List.length gs1) (Lfa2 : List.length fa2 = List.length gs1)
          (Laft1 : List.length aft1 = List.length gs2) (Laft2 : List.length aft2 = List.length gs2)
          (Lihp1 : List.length ihp1 = j) (Lihp2 : List.length ihp2 = j).
        Let Ep1 := env_args B1 (X1 ++ fa1 ++ v1 :: aft1 ++ ihp1).
        Let Ep2 := env_args B2 (X2 ++ fa2 ++ v2 :: aft2 ++ ihp2).
        Let nv1 := nonrec_vals gs1 fa1.
        Let nv2 := nonrec_vals gs1 fa2.
        Hypothesis (HE1 : RS Ep1 Ep1) (HE2 : RS Ep2 Ep2)
          (Hw1 : ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ Ep1 ↘ w1)
          (Hw2 : ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ Ep2 ↘ w2)
          (HwU1 : RU (env_args nil w1) (env_args nil u0)) (HwU2 : RU (env_args nil w2) (env_args nil u0))
          (Lw1 : List.length w1 = ind_nu D) (Lw2 : List.length w2 = ind_nu D)
          (HX1 : tele_full nr T ns X1) (HX2 : tele_full nr T ns X2)
          (Hnv : tele_pre (ar ns c) K nv1 nv2)
          (HB1 : RΓ B1 C1) (HB2 : RΓ B2 C1).

        Lemma s_Hns : tele_full nr T ns ns.
        Proof. exact (tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ HX1). Qed.

        Lemma s_Hnv11 : tele_pre (ar ns c) K nv1 nv1.
        Proof. exact (tar_pre_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs s_Hns Hcon K _ _ e_HK Hnv). Qed.

        Lemma leaf_char : forall ys1 ys2 f1 f2 bs a1 a2 (i : nat) R,
            List.length ys1 = L -> List.length ys2 = L ->
            tele_pre (shape_tr dr ns nv1 (ptyp_doms t)) L ys1 ys2 ->
            $*| v1 & ys1 | gc_deps ⍮ gc_stack ↘ f1 -> $*| v2 & ys2 | gc_deps ⍮ gc_stack ↘ f2 ->
            ⟦ ptyp_ps t ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ ns ++ nv1 ++ ys1) ↘ bs ->
            ind_rel p D u0 nr ar dr bs f1 f2 ->
            ⟦ A[τL] ⟧ env_args Ep1 ys1 ↘ a1 -> ⟦ A[τL] ⟧ env_args Ep2 ys2 ↘ a2 ->
            DF a1 ≈ a2 ∈ per_univ_elem i ↘ R -> (R <~> Rel bs f1 bs f2).
        Proof.
          intros * Lys1 Lys2 Hys Ef1 Ef2 Ebs Hrr Ea1 Ea2 HR.
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
          assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
          assert (Hys11 : tele_pre (shape_tr dr ns nv1 (ptyp_doms t)) L ys1 ys1)
            by exact (tsh_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI ns c gs gs1 t gs2 nv1 s_Hns Hcon Heq s_Hnv11 L _ _ (le_n _) Hys).
          destruct (leaf_link ns nv1 ys1 bs B1 X1 fa1 v1 aft1 ihp1 w1 ys1 f1 a1 LX1 Lfa1 Laft1 Lihp1 Lys1 HE1 Hw1 HwU1 Lw1 HX1 s_Hnv11 Hys11 Ebs Ef1 Ea1)
            as (Xq1 & A1 & Htf1 & EA1 & Ha1).
          destruct (leaf_link ns nv1 ys1 bs B2 X2 fa2 v2 aft2 ihp2 w2 ys2 f2 a2 LX2 Lfa2 Laft2 Lihp2 Lys2 HE2 Hw2 HwU2 Lw2 HX2 Hnv Hys Ebs Ef2 Ea2)
            as (Xq2 & A2 & Htf2 & EA2 & Ha2).
          destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
          assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
          destruct (us_rel B1 HB1) as (u1 & Hu1 & H10); destruct (us_rel B2 HB2) as (u2 & Hu2 & H20).
          destruct (us_rel C2 ltac:(symmetry; exact HC12)) as (uc2 & Huc2 & Hc20).
          assert (HU00 : RU (env_args nil u0) (env_args nil u0)) by (etransitivity; [ symmetry; exact Hc20 | exact Hc20 ]).
          set (imv := ind_rel_mv p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen).
          set (isym := proj1 (ind_rel_sym_all p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had)).
          pose proof (ttrans _ _ _ (tsym _ _ Htf1) Htf2) as Htf12.
          pose proof (cv_mctx B1 B2 u1 u2 HB12 Hu1 Hu2 H10 H20 RM HRM Xq1 Xq2 f1 f2 Htf12 (imv _ _ _ _ Hrr Htf1)) as L1.
          pose proof (cv_mctx B2 C1 u2 u0 HB2 Hu2 HUC H20 HU00 RM HRM Xq2 bs f2 f1 (tsym _ _ Htf2) (imv _ _ _ _ (isym _ _ _ Hrr) Htf2)) as L2.
          pose proof (cv_mctx C1 C2 u0 uc2 HC12 HUC Huc2 HU00 Hc20 RM HRM bs bs f1 f2
                        (tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI _ _ Htf1) Hrr) as L3.
          destruct (rel_exp_of_typ_inversion_simple_at HRM HAv _ _ L1) as (A1' & A2' & EA1' & EA2' & HA12).
          assert (A1' = A1) as -> by (eapply functional_eval_exp; eassumption).
          assert (A2' = A2) as -> by (eapply functional_eval_exp; eassumption).
          assert (Ha1A2 : Dom a1 ≈ A2 ∈ per_univ iA) by (eapply per_univ_trans'; [ exact Ha1 | exact HA12 ]).
          destruct Ha1A2 as [R' HR']; destruct HA12 as [R12 HR12].
          assert (E1 : R <~> R') by (eapply per_univ_elem_right_irrel; eassumption).
          assert (E2 : R' <~> R12) by (eapply per_univ_elem_left_irrel; [ exact HR' | exact HR12 ]).
          pose proof (per_head_iff EA1 EA2 HR12) as E3.
          assert (Ch : rel_chain RM (env_args B1 (Xq1 ++ f1 :: nil) :: env_args B2 (Xq2 ++ f2 :: nil)
                                     :: env_args C1 (bs ++ f1 :: nil) :: env_args C2 (bs ++ f2 :: nil) :: nil)).
          { apply rel_chain_cons; [ exact L1 |]. apply rel_chain_cons; [ exact L2 |]. apply rel_chain_of_pair; exact L3. }
          pose proof (per_head_of_typ_resp HRM HAv _ _ _ _ Ch) as E4.
          unfold Rel; etransitivity; [ exact E1 | etransitivity; [ exact E2 | etransitivity; [ exact E3 | exact E4 ] ] ].
        Qed.

        Lemma apps_snoc_val : forall f ys g c r, $*| f & ys | gc_deps ⍮ gc_stack ↘ g -> $| g & c | gc_deps ⍮ gc_stack ↘ r ->
            $*| f & ys ++ c :: nil | gc_deps ⍮ gc_stack ↘ r.
        Proof. intros * H1 H2; apply eval_apps_app; exists g; split; [ exact H1 | econstructor; [ exact H2 | constructor ] ]. Qed.

        (** The recursive result after [k] domains. *)
        Lemma rest_char : forall n k ys1 ys2 f1 f2 r1 r2 a1 a2 (i : nat) R, k + n = L ->
            List.length ys1 = k -> List.length ys2 = k ->
            tele_pre (shape_tr dr ns nv1 (ptyp_doms t)) k ys1 ys2 ->
            $*| v1 & ys1 | gc_deps ⍮ gc_stack ↘ f1 -> $*| v2 & ys2 | gc_deps ⍮ gc_stack ↘ f2 ->
            ind_shape_rel p D u0 nr ar dr (ns ++ nv1 ++ ys1) (ptyp_skip k t) f1 f2 ->
            ih_rel u0 dr Rel (ns ++ nv1 ++ ys1) (ptyp_skip k t) f1 f2 r1 r2 ->
            ⟦ ptyp_ihty A (ihb k β) (sb_qn k σ) (ihx k (a_var idx)) (ptyp_skip k t) ⟧ env_args Ep1 ys1 ↘ a1 ->
            ⟦ ptyp_ihty A (ihb k β) (sb_qn k σ) (ihx k (a_var idx)) (ptyp_skip k t) ⟧ env_args Ep2 ys2 ↘ a2 ->
            DF a1 ≈ a2 ∈ per_univ_elem i ↘ R -> R r1 r2.
        Proof.
          induction n as [| n IH]; intros * Hkn Lys1 Lys2 Hys Ef1 Ef2 Hsh Hih Ea1 Ea2 HR.
          - assert (Hk : k = L) by lia; rewrite Hk in Hsh, Hih, Ea1, Ea2, Hys, Lys1, Lys2; clear Hk Hkn.
            pose proof (ptyp_skip_end t e_simp) as HsL; change (List.length (ptyp_doms t)) with L in HsL; rewrite HsL in Hsh, Hih, Ea1, Ea2.
            cbn [ptyp_ihty ptyp_ps] in Ea1, Ea2; cbn [ih_rel] in Hih.
            destruct Hih as (bs & Ebs & Hrr).
            destruct (ind_shape_self_inv _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs' & Ebs' & Hir).
            pose proof (functional_eval_exps' _ _ _ _ Ebs' Ebs) as ->.
            refine (proj2 (leaf_char ys1 ys2 f1 f2 bs a1 a2 i R Lys1 Lys2 Hys Ef1 Ef2 Ebs Hir Ea1 Ea2 HR _ _) Hrr).
          - assert (Hk : k < L) by lia.
            destruct (ptyp_skip_lt k t Hk) as (Bk & HBk & Hs).
            rewrite Hs in Hsh, Hih, Ea1, Ea2.
            remember (ptyp_skip (S k) t) as t' eqn:Ht'.
            cbn [ptyp_ihty] in Ea1, Ea2; cbn [ih_rel] in Hih.
            inversion Ea1; subst a1; inversion Ea2; subst a2.
            match goal with H : ⟦ Bk[sb_qn k σ] ⟧ env_args Ep1 ys1 ↘ _ |- _ => rename H into Eb1 end.
            match goal with H : ⟦ Bk[sb_qn k σ] ⟧ env_args Ep2 ys2 ↘ _ |- _ => rename H into Eb2 end.
            basic_invert_per_univ_elem HR.
            match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
            match goal with H : _ <~> (fun _ _ => forall _ _ _, rel_mod_app _ _ _ _ _) |- _ => rename H into HRE end.
            pose proof (dom_char k Bk HBk ns B1 X1 fa1 v1 aft1 ihp1 w1 ys1 B2 X2 fa2 v2 aft2 ihp2 w2 ys2 _ _ i in_rel
                          LX1 Lfa1 Laft1 Lihp1 Lys1 LX2 Lfa2 Laft2 Lihp2 Lys2 HE1 HE2 Hw1 Hw2 HwU1 Lw1 HwU2 Lw2 HX1 HX2 Hnv Hys
                          Eb1 Eb2 equiv_a_a') as Edr.
            apply HRE; intros x0 x0' Hin.
            pose proof (proj1 (Edr x0 x0') Hin) as Hcc.
            destruct (Hih x0 x0' Hcc) as (fc & fc' & r & r' & Efc & Efc' & Er & Er' & Hih').
            destruct (ind_shape_pi_inv _ _ _ _ _ _ _ _ _ _ _ Hsh x0 x0' Hcc) as (r0 & r0' & Ec & Ec' & Hsh').
            assert (r0 = fc) as -> by (eapply functional_eval_app; eassumption).
            assert (r0' = fc') as -> by (eapply functional_eval_app; eassumption).
            destruct (Hcod x0 x0' Hin) as [a1' a2' Ea1' Ea2' HR'].
            econstructor; [ exact Er | exact Er' |].
            apply (IH (S k) (ys1 ++ x0 :: nil) (ys2 ++ x0' :: nil) fc fc' r r' a1' a2' i (out_rel x0 x0' Hin)); [ lia
              | rewrite List.length_app, Lys1; cbn; lia | rewrite List.length_app, Lys2; cbn; lia
              | | exact (apps_snoc_val _ _ _ _ _ Ef1 Efc) | exact (apps_snoc_val _ _ _ _ _ Ef2 Efc')
              | rewrite <- Ht'; rewrite <- !List.app_assoc in Hsh'; exact Hsh'
              | rewrite <- Ht'; rewrite <- !List.app_assoc in Hih'; exact Hih'
              | rewrite env_args_snoc, <- Ht'; exact Ea1' | rewrite env_args_snoc, <- Ht'; exact Ea2' | exact HR' ].
            apply tele_pre_snoc; [ exact Hys |].
            unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HBk); exact Hcc.
        Qed.
      End Sides.
    End Entry.

    Lemma cv_ihs : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall ns X X' vs vs' ihs ihs',
        tele_full nr T ns X -> tele_full nr T ns X' ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar dr ns gs vs vs' ->
        ihs_rel u0 dr Rel ns gs vs vs' ihs ihs' ->
        per_gargs (List.rev (tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU)) B1 B2 (X ++ vs) (X' ++ vs') ->
        forall k, k <= List.length gs ->
        per_gargs (List.rev (ihs_ctx_aux D A Us (List.length gs) nil 0 (List.firstn k gs)))
          (env_args B1 (X ++ vs)) (env_args B2 (X' ++ vs'))
          (List.firstn (cargs_nrec (List.firstn k gs)) ihs) (List.firstn (cargs_nrec (List.firstn k gs)) ihs').
    Proof.
      intros B1 B2 HB1 HB2 * HX HX' Har Hia Hir Hci.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (ihs_rel_len _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
      pose proof HX as HX0; rewrite tele_full_iff in HX0; destruct HX0 as (Ln & LX & _).
      pose proof HX' as HX0'; rewrite tele_full_iff in HX0'; destruct HX0' as (_ & LX' & _).
      unfold T in Ln, LX, LX'; rewrite List.length_rev, length_nparams in Ln, LX, LX'.
      induction k as [| k IH]; intros Hk; [ cbn; constructor |].
      destruct (nth_error_lt_some' gs k ltac:(lia)) as [g Hg].
      assert (Heq0 : gs = List.firstn k gs ++ g :: List.skipn (S k) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn k gs) = k) by (rewrite List.length_firstn; lia).
      pose proof (IH ltac:(lia)) as IHk.
      rewrite (firstn_S_snoc _ _ _ Hg).
      set (gs1 := List.firstn k gs) in *.
      rewrite cargs_nrec_app.
      destruct g as [B0 | Ps].
      - cbn [cargs_nrec]; rewrite Nat.add_0_r.
        rewrite ihs_ctx_aux_app; cbn [ihs_ctx_aux List.app]; exact IHk.
      - rewrite (entry_eq gs1 Ps _ Heq0).
        replace (cargs_nrec gs1 + cargs_nrec (ca_rec Ps :: nil)) with (S (cargs_nrec gs1)) by (cbn; lia).
        set (gs2 := List.skipn (S k) gs) in *.
        destruct (ihs_rel_at _ _ _ _ _ _ _ _ _ Hir gs1 Ps gs2 Heq0) as (v & v' & ih & ih' & Hv & Hv' & Hih & Hih' & Hrih).
        destruct (ind_args_rel_at _ _ _ _ Hia gs1 Ps gs2 Heq0) as (x & x' & Hx & Hx' & Hrr).
        rewrite Hv in Hx; injection Hx as <-; rewrite Hv' in Hx'; injection Hx' as <-.
        rewrite (firstn_S_snoc _ _ _ Hih), (firstn_S_snoc _ _ _ Hih').
        cbn [List.rev].
        set (E := ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) in *.
        assert (LE : List.length E = cargs_nrec gs1) by apply length_ihs_ctx_aux.
        assert (Lnr : cargs_nrec gs1 <= cargs_nrec gs) by (rewrite Heq0, cargs_nrec_app; lia).
        set (ihp := List.firstn (cargs_nrec gs1) ihs) in *.
        set (ihp' := List.firstn (cargs_nrec gs1) ihs') in *.
        assert (Lihp : List.length ihp = cargs_nrec gs1) by (unfold ihp; rewrite List.length_firstn; lia).
        assert (Lihp' : List.length ihp' = cargs_nrec gs1) by (unfold ihp'; rewrite List.length_firstn; lia).
        pose proof (e_HCtxT gs1 Ps gs2 Heq0) as HCtx2.
        destruct (sem_ctx_ass_inv HCtx2) as [jT HT].
        pose proof (e_HCtx gs1 Ps gs2 Heq0) as HCtx; fold E in HCtx, HCtx2.
        destruct (sem_ctx_per_ctx_env HCtx) as [RS HRS].
        assert (HΔeq : E ++ cinst Γ p D Us gs = (E ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU) ++ Γ)
          by (rewrite cinst_eq, List.app_assoc; reflexivity).
        assert (HEp : RS (env_args B1 ((X ++ vs) ++ ihp)) (env_args B2 ((X' ++ vs') ++ ihp'))).
        { pose proof HRS as HRS'; rewrite HΔeq in HRS'; pose proof HCtx as HCtx'; rewrite HΔeq in HCtx'.
          eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS' HCtx' HB12);
            [ rewrite !List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams; lia |].
          rewrite List.rev_app_distr; apply per_gargs_app_intro;
            [ rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_nparams; lia | exact Hci | exact IHk ]. }
        destruct (rel_exp_of_typ_inversion_simple_at HRS HT _ _ HEp) as (ty & ty' & Et & Et' & [R HR]).
        destruct (per_univ_elem_to_nat _ _ _ _ HR) as [n Hn].
        pose proof Et as EtF; pose proof Et' as EtF'.
        rewrite env_args_app in Et, Et'.
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R); [ rewrite List.length_rev; lia | exact IHk | exact (mk_rel_mod_eval _ _ Et Et' Hn) |].
        (** The sides. *)
        assert (Hsplit : forall (Y ws : list domain) w (ihq : list domain), List.nth_error ws k = Some w -> List.length ws = List.length gs ->
                   (Y ++ ws) ++ ihq = Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq).
        { intros * Hw Lw.
          pose proof (List.firstn_skipn k ws) as Hfs; rewrite (skipn_nth_cons' _ _ _ Hw) in Hfs.
          rewrite <- Hfs at 1; rewrite <- !List.app_assoc; reflexivity. }
        rewrite Lk in Hv, Hv', Hrr, Hrih.
        assert (Lf : forall ws : list domain, List.length ws = List.length gs -> List.length (List.firstn k ws) = List.length gs1)
          by (intros; rewrite List.length_firstn; lia).
        assert (Ls : forall ws : list domain, List.length ws = List.length gs -> List.length (List.skipn (S k) ws) = List.length gs2)
          by (intros; unfold gs2; rewrite !List.length_skipn; lia).
        set (K := List.length (cargs_nonrec gs1)).
        assert (Hnv : forall ws, List.length ws = List.length gs -> List.firstn K (nonrec_vals gs ws) = nonrec_vals gs1 (List.firstn k ws)).
        { intros ws Lw; rewrite <- (List.firstn_skipn k ws) at 1.
          rewrite Heq0 at 1; fold gs1 gs2.
          rewrite nonrec_vals_app by (rewrite List.length_firstn; lia).
          rewrite firstn_app_exact by (apply length_nonrec_vals; rewrite List.length_firstn; lia); reflexivity. }
        assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq0, cargs_nonrec_app, List.length_app; lia).
        assert (Hpk : tele_pre (ar ns c) K (nonrec_vals gs1 (List.firstn k vs)) (nonrec_vals gs1 (List.firstn k vs'))).
        { rewrite <- (Hnv vs Lv), <- (Hnv vs' Lv'); apply tele_pre_of_full with (T := cargs_nonrec gs); [ exact Har | exact HKl ]. }
        assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
        rewrite (Hsplit X vs v ihp Hv Lv) in EtF, HEp.
        rewrite (Hsplit X' vs' v' ihp' Hv' Lv') in EtF', HEp.
        assert (HE1 : RS (env_args B1 (X ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp))
                         (env_args B1 (X ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp)))
          by (etransitivity; [ exact HEp | symmetry; exact HEp ]).
        assert (HE2 : RS (env_args B2 (X' ++ List.firstn k vs' ++ v' :: List.skipn (S k) vs' ++ ihp'))
                         (env_args B2 (X' ++ List.firstn k vs' ++ v' :: List.skipn (S k) vs' ++ ihp')))
          by (etransitivity; [ symmetry; exact HEp | exact HEp ]).
        destruct (side_w gs1 Ps gs2 Heq0 RS HRS B1 X (List.firstn k vs) v (List.skipn (S k) vs) ihp HB1 LX (Lf _ Lv) (Ls _ Lv) Lihp HE1)
          as (w1 & Hw1 & HwU1 & Lw1).
        destruct (side_w gs1 Ps gs2 Heq0 RS HRS B2 X' (List.firstn k vs') v' (List.skipn (S k) vs') ihp' HB2 LX' (Lf _ Lv') (Ls _ Lv') Lihp' HE2)
          as (w2 & Hw2 & HwU2 & Lw2).
        apply (rest_char gs1 Ps gs2 Heq0 RS HRS ns B1 B2 X X' (List.firstn k vs) (List.firstn k vs') (List.skipn (S k) vs) (List.skipn (S k) vs')
                 ihp ihp' w1 w2 v v' LX LX' (Lf _ Lv) (Lf _ Lv') (Ls _ Lv) (Ls _ Lv') Lihp Lihp' HE1 HE2 Hw1 Hw2 HwU1 HwU2 Lw1 Lw2
                 HX HX' Hpk HB1 HB2 (List.length (ptyp_doms Ps)) 0 nil nil v v' ih ih' ty ty' n R);
          [ lia | reflexivity | reflexivity | apply tele_pre_nil | apply eval_apps_nil | apply eval_apps_nil
          | rewrite List.app_nil_r; exact Hrr | rewrite List.app_nil_r; exact Hrih | exact EtF | exact EtF' | exact Hn ].
    Qed.
    Lemma cv_bctx : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall ns X X' vs vs' ihs ihs',
        tele_full nr T ns X -> tele_full nr T ns X' ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar dr ns gs vs vs' ->
        ihs_rel u0 dr Rel ns gs vs vs' ihs ihs' ->
        forall RB, EF elim_bctx p D gs A Us ++ Γ ≈ elim_bctx p D gs A Us ++ Γ ∈ per_ctx_env ↘ RB ->
        RB (env_args B1 (X ++ vs ++ ihs)) (env_args B2 (X' ++ vs' ++ ihs')).
    Proof.
      intros B1 B2 HB1 HB2 * HX HX' Har Hia Hir RB HRB.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (ihs_rel_len _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
      pose proof HX as HX0; rewrite tele_full_iff in HX0; destruct HX0 as (_ & LX & _).
      pose proof HX' as HX0'; rewrite tele_full_iff in HX0'; destruct HX0' as (_ & LX' & _).
      unfold T in LX, LX'; rewrite List.length_rev, length_nparams in LX, LX'.
      destruct (us_rel B1 HB1) as (u1 & Hu1 & H10); destruct (us_rel B2 HB2) as (u2 & Hu2 & H20).
      pose proof (closed_args_gargs _ _ _ _ _ HX HX' Har Hia (List.length gs) (le_n _)) as Hcg.
      rewrite List.firstn_all, !List.firstn_all2 in Hcg by lia.
      assert (HKa : tele_ass ((cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D))
        by (rewrite <- List.app_assoc, <- params_split; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
      assert (HK : ⊨ (cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D) by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
      pose proof (ihs_pre_sem nil gs eq_refl) as HC0; cbn [ihs_ctx_aux List.app] in HC0; rewrite cinst_eq in HC0.
      pose proof (cv_gen _ HKa HK HC0 B1 B2 u1 u2 HB12 Hu1 Hu2 H10 H20 _ _ Hcg
                    ltac:(rewrite !List.length_app, length_cargs_ctx, length_nparams; lia)) as Hci.
      pose proof (cv_ihs B1 B2 HB1 HB2 _ _ _ _ _ _ _ HX HX' Har Hia Hir Hci (List.length gs) (le_n _)) as Hih.
      rewrite List.firstn_all, !List.firstn_all2 in Hih by lia.
      rewrite bctx_split, cinst_eq, List.app_assoc in HRB.
      pose proof HB as HB'; rewrite bctx_split, cinst_eq, List.app_assoc in HB'.
      rewrite (List.app_assoc X), (List.app_assoc X').
      eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRB HB' HB12);
        [ rewrite !List.length_app, length_ihs_ctx_aux, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams; lia |].
      rewrite List.rev_app_distr; apply per_gargs_app_intro;
        [ rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_nparams; lia | exact Hci | exact Hih ].
    Qed.

    (** The values of the branch type's substitution. *)
    Lemma eval_bty : forall B X vs ihs w, List.length X = ind_nn D -> List.length vs = List.length gs ->
        List.length ihs = cargs_nrec gs ->
        ⟦ List.map (fun U => U[wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)]ʷ) Us ⟧* gc_deps ⍮ gc_stack
          ⍮ env_args B (X ++ vs ++ ihs) ↘ w ->
        ⟦ sb_of_list (sb_of_wk (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs))) (bty_args c gs) ⟧s
          env_args B (X ++ vs ++ ihs) ↘ env_args B (X ++ d_con p c (w ++ X ++ vs) :: nil).
    Proof.
      intros * LX Lvs Lih Hw.
      assert (Lall : List.length (X ++ vs ++ ihs) = ind_nn D + List.length gs + cargs_nrec gs)
        by (rewrite !List.length_app; lia).
      apply eval_sb_of_list.
      - pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)) (env_args B (X ++ vs ++ ihs))
                      (wk_mono_shiftn _)) as H.
        assert (Hw' : ⟪wk_shiftn (ind_nn D + List.length gs + cargs_nrec gs)⟫ (env_args B (X ++ vs ++ ihs)) = B)
          by (rewrite <- Lall; apply eval_wk_shiftn_args).
        rewrite Hw' in H; exact H.
      - assert (HX : ⟦ vars_from (cargs_nrec gs + List.length gs) (ind_nn D) ⟧* gc_deps ⍮ gc_stack ⍮ env_args B (X ++ vs ++ ihs) ↘ X).
        { pose proof (eval_vars_from_args X B (vs ++ ihs)) as H.
          rewrite List.length_app, LX, Lvs, Lih in H; rewrite Nat.add_comm; exact H. }
        assert (Hvs : ⟦ vars_from (cargs_nrec gs) (List.length gs) ⟧* gc_deps ⍮ gc_stack ⍮ env_args B (X ++ vs ++ ihs) ↘ vs).
        { pose proof (eval_vars_from_args vs (env_args B X) ihs) as H.
          rewrite Lvs, Lih, <- env_args_app in H; exact H. }
        unfold bty_args; apply eval_exps_app; [ exact HX |].
        econstructor; [| constructor ].
        apply eval_apps_exp; exists (d_con p c nil), (w ++ X ++ vs); split; [ constructor | split ].
        + apply eval_exps_app; [ exact Hw |]. apply eval_exps_app; [ exact HX | exact Hvs ].
        + change (d_con p c (w ++ X ++ vs)) with (d_con p c (nil ++ (w ++ X ++ vs))); apply (eval_apps_con c gs _ _ Hcon).
          pose proof (eval_exps_length _ _ _ Hw) as Lw; rewrite List.length_map, HUl in Lw.
          cbn; rewrite !List.length_app; unfold ind_nn in *; pose proof Hle; lia.
    Qed.

    (** The branch type's head relation is the motive's family at the
        constructor. *)
    Lemma bty_rel : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall ns bs bs' vs vs' ihs ihs',
        tele_full nr T ns ns -> List.length bs = ind_np D -> List.length bs' = ind_np D ->
        tele_full nr T ns (List.skipn (ind_nu D) bs) -> tele_full nr T ns (List.skipn (ind_nu D) bs') ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar dr ns gs vs vs' ->
        ihs_rel u0 dr Rel ns gs vs vs' ihs ihs' ->
        (per_head (elim_bty p D c gs A Us) (elim_bty p D c gs A Us)
           (env_args B1 (List.skipn (ind_nu D) bs ++ vs ++ ihs)) (env_args B2 (List.skipn (ind_nu D) bs' ++ vs' ++ ihs'))
         <~> Rel ns (d_con p c (bs ++ vs)) ns (d_con p c (bs' ++ vs'))).
    Proof.
      intros B1 B2 HB1 HB2 * Hnn Hb Hb' Hs Hs' Har Hia Hir.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      set (X := List.skipn (ind_nu D) bs) in *; set (X' := List.skipn (ind_nu D) bs') in *.
      pose proof Hs as Hs0; rewrite tele_full_iff in Hs0; destruct Hs0 as (_ & LX & _).
      pose proof Hs' as Hs0'; rewrite tele_full_iff in Hs0'; destruct Hs0' as (_ & LX' & _).
      unfold T in LX, LX'; rewrite List.length_rev, length_nparams in LX, LX'.
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (ihs_rel_len _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
      destruct (sem_ctx_per_ctx_env HB) as [RB HRB].
      assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
      pose proof (cv_bctx B1 B2 HB1 HB2 ns X X' vs vs' ihs ihs' Hs Hs' Har Hia Hir RB HRB) as HE.
      pose proof (gsub_bty A c gs Hcon HB) as Hg.
      assert (Lb : List.length (elim_bctx p D gs A Us) = ind_nn D + List.length gs + cargs_nrec gs)
        by (rewrite length_elim_bctx; lia).
      destruct (us_wk_vals (elim_bctx p D gs A Us) RB B1 (X ++ vs ++ ihs) HRB HB
                  ltac:(etransitivity; [ exact HE | symmetry; exact HE ]) ltac:(rewrite Lb, !List.length_app; lia))
        as (w1 & uB1 & Hw1 & _ & _).
      destruct (us_wk_vals (elim_bctx p D gs A Us) RB B2 (X' ++ vs' ++ ihs') HRB HB
                  ltac:(etransitivity; [ symmetry; exact HE | exact HE ]) ltac:(rewrite Lb, !List.length_app; lia))
        as (w2 & uB2 & Hw2 & _ & _).
      rewrite Lb in Hw1, Hw2.
      pose proof (eval_bty B1 X vs ihs w1 LX Lv Li Hw1) as Hev1.
      pose proof (eval_bty B2 X' vs' ihs' w2 LX' Lv' Li' Hw2) as Hev2.
      assert (Lw1 : List.length w1 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw1), List.length_map; exact HUl).
      assert (Lw2 : List.length w2 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw2), List.length_map; exact HUl).
      pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HAv HRB (gsub_valid Hg) HE Hev1 Hev2) as ER1.
      destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
      destruct (us_rel B2 HB2) as (u2 & Hu2 & H20).
      destruct (us_rel C2 ltac:(symmetry; exact HC12)) as (uc2 & Huc2 & Hc20).
      assert (HU00 : RU (env_args nil u0) (env_args nil u0)) by (etransitivity; [ symmetry; exact Hc20 | exact Hc20 ]).
      assert (Lnp : forall w Y : list domain, List.length w = ind_nu D -> List.length Y = ind_nn D -> List.length (w ++ Y) = ind_np D)
        by (intros; rewrite List.length_app; pose proof Hle; unfold ind_nn in *; lia).
      assert (Hm1 : ind_rel p D u0 nr ar dr ns (d_con p c (w1 ++ X ++ vs)) (d_con p c (w2 ++ X' ++ vs'))).
      { rewrite !List.app_assoc; econstructor; [ exact Hnn | exact Hcon | apply Lnp; assumption | apply Lnp; assumption
          | rewrite skipn_app_exact by exact Lw1; exact Hs | rewrite skipn_app_exact by exact Lw2; exact Hs' | exact Har | exact Hia ]. }
      assert (Hm : ind_rel p D u0 nr ar dr ns (d_con p c (bs ++ vs)) (d_con p c (bs' ++ vs'))) by (econstructor; eassumption).
      assert (HmL2 : ind_rel p D u0 nr ar dr ns (d_con p c (bs ++ vs)) (d_con p c (w2 ++ X' ++ vs'))).
      { rewrite (List.app_assoc w2); econstructor; [ exact Hnn | exact Hcon | exact Hb | apply Lnp; assumption
          | exact Hs | rewrite skipn_app_exact by exact Lw2; exact Hs' | exact Har | exact Hia ]. }
      pose proof (proj1 (ind_rel_sym_all p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had)) as isym.
      pose proof (cv_mctx B2 C1 u2 u0 HB2 Hu2 HUC H20 HU00 RM HRM X' ns _ _ (tsym _ _ Hs')
                    (ind_rel_mv p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen _ _ _ _ (isym _ _ _ Hm1) Hs')) as L2.
      pose proof (rel_sub_under_ctx_at' (gsub_valid Hg) HRB HRM _ _ _ _ HE Hev1 Hev2) as L1.
      pose proof (cv_mctx C1 C2 u0 uc2 HC12 HUC Huc2 HU00 Hc20 RM HRM ns ns _ _ Hnn Hm1) as L3.
      assert (Ch1 : rel_chain RM (env_args B1 (X ++ d_con p c (w1 ++ X ++ vs) :: nil) :: env_args B2 (X' ++ d_con p c (w2 ++ X' ++ vs') :: nil)
                                  :: env_args C1 (ns ++ d_con p c (w1 ++ X ++ vs) :: nil) :: env_args C2 (ns ++ d_con p c (w2 ++ X' ++ vs') :: nil) :: nil)).
      { apply rel_chain_cons; [ exact L1 |]. apply rel_chain_cons; [ exact L2 |]. apply rel_chain_of_pair; exact L3. }
      pose proof (per_head_of_typ_resp HRM HAv _ _ _ _ Ch1) as ER2.
      pose proof (cv_mctx C2 C1 uc2 u0 ltac:(symmetry; exact HC12) Huc2 HUC Hc20 HU00 RM HRM ns ns _ _ Hnn (isym _ _ _ HmL2)) as M2.
      pose proof (cv_mctx C1 C2 u0 uc2 HC12 HUC Huc2 HU00 Hc20 RM HRM ns ns _ _ Hnn Hm) as M3.
      assert (Ch2 : rel_chain RM (env_args C1 (ns ++ d_con p c (w1 ++ X ++ vs) :: nil) :: env_args C2 (ns ++ d_con p c (w2 ++ X' ++ vs') :: nil)
                                  :: env_args C1 (ns ++ d_con p c (bs ++ vs) :: nil) :: env_args C2 (ns ++ d_con p c (bs' ++ vs') :: nil) :: nil)).
      { apply rel_chain_cons; [ exact L3 |]. apply rel_chain_cons; [ exact M2 |]. apply rel_chain_of_pair; exact M3. }
      pose proof (per_head_of_typ_resp HRM HAv _ _ _ _ Ch2) as ER3.
      rewrite elim_bty_args.
      etransitivity; [ exact ER1 | etransitivity; [ exact ER2 | exact ER3 ] ].
    Qed.

  End Bctx.


  (** ** The Three Links of an Elimination *)
  Section Stage.
    Variable (A A' : exp) (iA : nat).
    Hypothesis (HA : elim_mctx p D Us ++ Γ ⊨ A ≈ A' : Typeω@iA).
    Variable (C1 C2 : env).
    Hypothesis (HC12 : RΓ C1 C2) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
    Hypothesis (HBc : forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A Us ++ Γ).
    Let HAl := rel_exp_under_ctx_refl_left HA.
    Let Rel := fun ns m ns' m' => per_head A A (env_args C1 (ns ++ m :: nil)) (env_args C2 (ns' ++ m' :: nil)).
    Let isym := proj1 (ind_rel_sym_all p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had).
    Let itrans := proj1 (ind_rel_trans_all p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had).
    Let imv := ind_rel_mv p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen.
    Let trefl_l := tnr_refl_l p D u0 nr ar dr (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI.

    Lemma us_rel' : forall B, RΓ B C1 -> exists u, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u /\ RU (env_args nil u) (env_args nil u0).
    Proof.
      intros B HB1; destruct (us_vals B C1 HB1) as (u & u' & Hu & Hu' & H).
      pose proof (functional_eval_exps' _ _ _ _ Hu' HUC) as ->; eauto.
    Qed.

    (** [cv_mctx] at any two environments of the class of [C1]. *)
    Lemma mctx_at : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall RM, EF elim_mctx p D Us ++ Γ ≈ elim_mctx p D Us ++ Γ ∈ per_ctx_env ↘ RM ->
        forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar dr ns m m' ->
          RM (env_args B1 (ns ++ m :: nil)) (env_args B2 (ns' ++ m' :: nil)).
    Proof.
      intros * HB1 HB2 RM HRM * Hns Hm.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      destruct (us_rel' B1 HB1) as (u1 & Hu1 & H10); destruct (us_rel' B2 HB2) as (u2 & Hu2 & H20).
      exact (cv_mctx B1 B2 u1 u2 ltac:(etransitivity; [ exact HB1 | symmetry; exact HB2 ]) Hu1 Hu2 H10 H20 RM HRM _ _ _ _ Hns Hm).
    Qed.

    Lemma ind_rel_refl_r : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar dr ns m m' -> ind_rel p D u0 nr ar dr ns' m' m'.
    Proof. intros * Hns Hm; apply imv with (ns := ns); [ exact (itrans _ _ _ (isym _ _ _ Hm) _ Hm) | exact Hns ]. Qed.

    Lemma ind_rel_refl_l : forall ns m m', ind_rel p D u0 nr ar dr ns m m' -> ind_rel p D u0 nr ar dr ns m m.
    Proof. intros * Hm; exact (itrans _ _ _ Hm _ (isym _ _ _ Hm)). Qed.

    Lemma mot_mid : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar dr ns m m' ->
        exists a a', ⟦ A ⟧ env_args C1 (ns ++ m :: nil) ↘ a /\ ⟦ A' ⟧ env_args C2 (ns' ++ m' :: nil) ↘ a' /\
          DF a ≈ a' ∈ per_univ_elem iA ↘ Rel ns m ns' m'.
    Proof.
      intros * Hns Hm.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
      pose proof (mctx_at C1 C2 ltac:(etransitivity; [ exact HC12 | symmetry; exact HC12 ]) ltac:(symmetry; exact HC12)
                    RM HRM _ _ _ _ Hns Hm) as HE.
      destruct (rel_exp_of_typ_inversion_simple_at HRM HA _ _ HE) as (a & a' & Ea & Ea' & Haa).
      destruct (rel_exp_of_typ_inversion_simple_at HRM HAl _ _ HE) as (b & d & Eb & Ed & Hbd).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      exists a, a'; split; [ exact Ea | split; [ exact Ea' |] ].
      eapply univ_connect; [ etransitivity; [ exact Hbd | symmetry; exact Hbd ] | exact (per_univ_elem_at_head Ea Ed Hbd) |].
      etransitivity; [ symmetry; exact Haa | exact Hbd ].
    Qed.

    Lemma mot_out : forall Γ' RΓ' σ0 ρ0 ρ0σ0 A0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ ->
        RΓ' ρ0 ρ0 -> ⟦ σ0 ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
        elim_mctx p D Us ++ Γ ⊨ A ≈ A0 : Typeω@iA ->
        forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar dr ns m m' ->
          exists a a', ⟦ A0[sb_qn (S (ind_nn D)) σ0] ⟧ env_args ρ0 (ns ++ m :: nil) ↘ a /\
            ⟦ A0 ⟧ env_args ρ0σ0 (ns' ++ m' :: nil) ↘ a' /\ DF a ≈ a' ∈ per_univ_elem iA ↘ Rel ns m ns' m'.
    Proof.
      intros * HRΓ' Hσ0 Hρ0 Hev0 HρC HA0 * Hns Hm.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
      assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
      destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
      pose proof (trefl_l _ _ Hns) as Hnn.
      pose proof (trefl_r _ _ Hns) as Hnn'.
      pose proof (ind_rel_refl_l _ _ _ Hm) as Hmm.
      pose proof (ind_rel_refl_r _ _ _ _ Hns Hm) as Hmm'.
      pose proof (mctx_at ρ0σ0 ρ0σ0 HρC HρC RM HRM _ _ _ _ Hnn Hmm) as El.
      assert (Ll : List.length (ns ++ m :: nil) = List.length (List.rev (elim_mctx p D Us))).
      { pose proof Hnn as H; rewrite tele_full_iff in H; destruct H as (H & _); unfold T in H.
        rewrite List.length_rev, length_elim_mctx, List.length_app; rewrite List.length_rev, length_nparams in H; cbn; lia. }
      assert (HMr : ⊨ List.rev (List.rev (elim_mctx p D Us)) ++ Γ) by (rewrite List.rev_involutive; exact HM).
      assert (HRMr : EF List.rev (List.rev (elim_mctx p D Us)) ++ Γ ≈ List.rev (List.rev (elim_mctx p D Us)) ++ Γ ∈ per_ctx_env ↘ RM)
        by (rewrite List.rev_involutive; exact HRM).
      pose proof (proj2 (rel_gargs _ _ _ _ HRΓ HMr (List.Forall_rev (elim_mctx_ass p D Us Hc)) HRMr _ _ _ _ Ll Ll El)) as Hg.
      destruct (outer_typ_link (elim_mctx p D Us) Γ Γ' RΓ' σ0 ρ0 ρ0σ0 A0 A0 iA (elim_mctx_ass p D Us Hc) HM
                  (rel_exp_under_ctx_refl_right HA0) HRΓ' Hσ0 Hρ0 Hev0 _ Hg ltac:(rewrite List.length_rev in Ll; exact Ll))
        as (a & b0 & Ea & Eb0 & Hab0).
      rewrite length_elim_mctx in Ea.
      pose proof (mctx_at C1 C2 HC11 HC21 RM HRM _ _ _ _ Hns Hm) as Ebc.
      destruct (rel_exp_of_typ_inversion_simple_at HRM HAl _ _ Ebc) as (b & c0 & Eb & Ec & Hbc).
      pose proof (mctx_at C1 ρ0σ0 HC11 HρC RM HRM _ _ _ _ Hnn Hmm) as E1.
      destruct (rel_exp_of_typ_inversion_simple_at HRM HA0 _ _ E1) as (b' & b0' & Eb' & Eb0' & Hbb0).
      assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
      assert (b0' = b0) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (mctx_at C2 ρ0σ0 HC21 HρC RM HRM _ _ _ _ Hnn' Hmm') as E2.
      destruct (rel_exp_of_typ_inversion_simple_at HRM HA0 _ _ E2) as (c' & d & Ec' & Ed & Hcd).
      assert (c' = c0) as -> by (eapply functional_eval_exp; eassumption).
      exists a, d; split; [ exact Ea | split; [ exact Ed |] ].
      eapply univ_connect; [ etransitivity; [ exact Hab0 | symmetry; exact Hbb0 ] | exact (per_univ_elem_at_head Eb Ec Hbc) |].
      symmetry; exact Hcd.
    Qed.

    Lemma Rel_resp : forall ns1 m1 ns2 m2 ns3 m3 ns4 m4,
        tele_full nr T ns1 ns2 -> tele_full nr T ns2 ns3 -> tele_full nr T ns3 ns4 ->
        ind_rel p D u0 nr ar dr ns1 m1 m2 -> ind_rel p D u0 nr ar dr ns2 m2 m3 -> ind_rel p D u0 nr ar dr ns3 m3 m4 ->
        (Rel ns1 m1 ns2 m2 <~> Rel ns3 m3 ns4 m4).
    Proof.
      intros * H12 H23 H34 M12 M23 M34.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
      assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
      destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
      apply (per_head_of_typ_resp HRM HAl).
      apply rel_chain_cons; [ exact (mctx_at C1 C2 HC11 HC21 RM HRM _ _ _ _ H12 M12) |].
      apply rel_chain_cons; [ exact (mctx_at C2 C1 HC21 HC11 RM HRM _ _ _ _ H23 M23) |].
      apply rel_chain_of_pair; exact (mctx_at C1 C2 HC11 HC21 RM HRM _ _ _ _ H34 M34).
    Qed.

    Lemma Rel_PER : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar dr ns m m' -> PER (Rel ns m ns' m').
    Proof.
      intros * Hns Hm; destruct (mot_mid _ _ _ _ Hns Hm) as (a & a' & _ & _ & H).
      eapply per_elem_PER; exact H.
    Qed.

    Lemma br_mid : forall Bs Bs',
        (forall c gs n B B', ind_con D c = Some gs -> brs_lookup Bs c = Some (n, B) -> brs_lookup Bs' c = Some (n, B') ->
           elim_bctx p D gs A Us ++ Γ ⊨ B ≈ B' : elim_bty p D c gs A Us) ->
        forall c gs n Ba Bb, ind_con D c = Some gs -> brs_lookup Bs c = Some (n, Ba) -> brs_lookup Bs' c = Some (n, Bb) ->
        forall ns bs bs' vs vs' ihs ihs',
          tele_full nr T ns ns -> List.length bs = ind_np D -> List.length bs' = ind_np D ->
          tele_full nr T ns (List.skipn (ind_nu D) bs) -> tele_full nr T ns (List.skipn (ind_nu D) bs') ->
          tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
          ind_args_rel p D u0 nr ar dr ns gs vs vs' ->
          ihs_rel u0 dr Rel ns gs vs vs' ihs ihs' ->
          exists r r', ⟦ Ba ⟧ env_args C1 (List.skipn (ind_nu D) bs ++ vs ++ ihs) ↘ r /\
            ⟦ Bb ⟧ env_args C2 (List.skipn (ind_nu D) bs' ++ vs' ++ ihs') ↘ r' /\
            Rel ns (d_con p c (bs ++ vs)) ns (d_con p c (bs' ++ vs')) r r'.
    Proof.
      intros Bs Bs' HBB * Hcon Hla Hlb * Hnn Hb Hb' Hs Hs' Har Hia Hir.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
      assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
      pose proof (HBc c gs Hcon) as HB.
      destruct (sem_ctx_per_ctx_env HB) as [RB HRB].
      pose proof (cv_bctx A iA HAl C1 C2 HC12 HUC c gs Hcon HB C1 C2 HC11 HC21 ns _ _ vs vs' ihs ihs' Hs Hs' Har Hia Hir RB HRB) as HE.
      destruct (rel_exp_under_ctx_simple_at HRB (HBB _ _ _ _ _ Hcon Hla Hlb) _ _ HE) as (r & r' & Er & Er' & Hrr).
      exists r, r'; split; [ exact Er | split; [ exact Er' |] ].
      exact (proj1 (bty_rel A iA HAl C1 C2 HC12 HUC c gs Hcon HB C1 C2 HC11 HC21 ns bs bs' vs vs' ihs ihs'
                      Hnn Hb Hb' Hs Hs' Har Hia Hir r r') Hrr).
    Qed.

    Lemma br_out : forall Γ' RΓ' σ0 ρ0 ρ0σ0 Bs0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ ->
        RΓ' ρ0 ρ0 -> ⟦ σ0 ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
        (forall c gs n B0, ind_con D c = Some gs -> brs_lookup Bs0 c = Some (n, B0) ->
           n = (ind_nn D + List.length gs + cargs_nrec gs)%nat /\ elim_bctx p D gs A Us ++ Γ ⊨ B0 : elim_bty p D c gs A Us) ->
        forall c gs n Ba Bb, ind_con D c = Some gs -> brs_lookup (brs_sub Bs0 σ0) c = Some (n, Ba) -> brs_lookup Bs0 c = Some (n, Bb) ->
        forall ns bs bs' vs vs' ihs ihs',
          tele_full nr T ns ns -> List.length bs = ind_np D -> List.length bs' = ind_np D ->
          tele_full nr T ns (List.skipn (ind_nu D) bs) -> tele_full nr T ns (List.skipn (ind_nu D) bs') ->
          tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
          ind_args_rel p D u0 nr ar dr ns gs vs vs' ->
          ihs_rel u0 dr Rel ns gs vs vs' ihs ihs' ->
          exists r r', ⟦ Ba ⟧ env_args ρ0 (List.skipn (ind_nu D) bs ++ vs ++ ihs) ↘ r /\
            ⟦ Bb ⟧ env_args ρ0σ0 (List.skipn (ind_nu D) bs' ++ vs' ++ ihs') ↘ r' /\
            Rel ns (d_con p c (bs ++ vs)) ns (d_con p c (bs' ++ vs')) r r'.
    Proof.
      intros * HRΓ' Hσ0 Hρ0 Hev0 HρC HB0s * Hcon Hla Hlb * Hnn Hb Hb' Hs Hs' Har Hia Hir.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
      destruct (brs_lookup_sub _ _ _ _ _ Hla) as (B0 & HlB0 & ->).
      rewrite Hlb in HlB0; injection HlB0 as <-.
      destruct (HB0s _ _ _ _ Hcon Hlb) as [-> HBv].
      pose proof (HBc c gs Hcon) as HB.
      destruct (sem_ctx_per_ctx_env HB) as [RB HRB].
      assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
      set (X := List.skipn (ind_nu D) bs) in *; set (X' := List.skipn (ind_nu D) bs') in *.
      pose proof (cv_bctx A iA HAl C1 C2 HC12 HUC c gs Hcon HB ρ0σ0 ρ0σ0 HρC HρC ns _ _ vs vs' ihs ihs' Hs Hs' Har Hia Hir RB HRB) as HE.
      assert (HEl : RB (env_args ρ0σ0 (X ++ vs ++ ihs)) (env_args ρ0σ0 (X ++ vs ++ ihs))) by (etransitivity; [ exact HE | symmetry; exact HE ]).
      pose proof Hs as Hs0; rewrite tele_full_iff in Hs0; destruct Hs0 as (_ & LX & _).
      unfold T in LX; rewrite List.length_rev, length_nparams in LX.
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
      destruct (ihs_rel_len _ _ _ _ _ _ _ _ _ Hir) as [Li _].
      assert (Ll : List.length (X ++ vs ++ ihs) = List.length (List.rev (elim_bctx p D gs A Us)))
        by (rewrite List.length_rev, length_elim_bctx, !List.length_app; lia).
      assert (HBr : ⊨ List.rev (List.rev (elim_bctx p D gs A Us)) ++ Γ) by (rewrite List.rev_involutive; exact HB).
      assert (HRBr : EF List.rev (List.rev (elim_bctx p D gs A Us)) ++ Γ ≈ List.rev (List.rev (elim_bctx p D gs A Us)) ++ Γ ∈ per_ctx_env ↘ RB)
        by (rewrite List.rev_involutive; exact HRB).
      pose proof (proj2 (rel_gargs _ _ _ _ HRΓ HBr (List.Forall_rev (elim_bctx_ass p D gs A Us Hc)) HRBr _ _ _ _ Ll Ll HEl)) as Hg.
      destruct (outer_exp_link (elim_bctx p D gs A Us) Γ Γ' RΓ' σ0 ρ0 ρ0σ0 (elim_bty p D c gs A Us) Bb Bb
                  (elim_bctx_ass p D gs A Us Hc) HB HBv HRΓ' Hσ0 Hρ0 Hev0 _ Hg ltac:(rewrite List.length_rev in Ll; exact Ll))
        as (RΔ & F & m & n0 & HRΔ & HF & Em & En0 & Hmn).
      assert (ERB : RΔ <~> RB) by (eapply per_ctx_env_right_irrel; eassumption).
      apply ERB in HF.
      destruct (rel_exp_under_ctx_simple_at HRB HBv _ _ HE) as (n1 & r' & En1 & Er' & Hnr).
      assert (n1 = n0) as -> by (eapply functional_eval_exp; eassumption).
      destruct (presup_rel_exp_under_ctx HBv) as [iT HT].
      assert (ER : per_head (elim_bty p D c gs A Us) (elim_bty p D c gs A Us) F (env_args ρ0σ0 (X ++ vs ++ ihs))
                   <~> per_head (elim_bty p D c gs A Us) (elim_bty p D c gs A Us) (env_args ρ0σ0 (X ++ vs ++ ihs)) (env_args ρ0σ0 (X' ++ vs' ++ ihs'))).
      { apply (per_head_of_typ_resp HRB HT).
        apply rel_chain_cons; [ exact HF |]. apply rel_chain_cons; [ exact HEl |]. apply rel_chain_of_pair; exact HE. }
      exists m, r'; split; [ rewrite length_elim_bctx in Em; replace (ind_nn D + List.length gs + cargs_nrec gs) with (cargs_nrec gs + List.length gs + ind_nn D) by lia; exact Em |].
      split; [ exact Er' |].
      apply (proj1 (bty_rel A iA HAl C1 C2 HC12 HUC c gs Hcon HB ρ0σ0 ρ0σ0 HρC HρC ns bs bs' vs vs' ihs ihs'
                      Hnn Hb Hb' Hs Hs' Har Hia Hir m r')).
      eapply (per_head_trans _ _ _ _ _ _ HRB HT HE); [ apply ER; exact Hmn | exact Hnr ].
    Qed.

    (** The eliminator at data moved by a semantic substitution, against
        the eliminator at the data, at related elements. *)
    Lemma elim_shift : forall Bs nm, nm = S (ind_nn D) -> brs_names (ind_cons D) Bs ->
        (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
        (forall c gs n B, ind_con D c = Some gs -> brs_lookup Bs c = Some (n, B) ->
           elim_bctx p D gs A Us ++ Γ ⊨ B : elim_bty p D c gs A Us) ->
        forall Γ' RΓ' σ ρ, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ ⟧s ρ ↘ C1 ->
        forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar dr ns m m' ->
          exists r1 r2, eval_elim gc_deps gc_stack ρ nm A[sb_qn nm σ] (brs_sub Bs σ) m r1 /\
            eval_elim gc_deps gc_stack C1 nm A Bs m' r2 /\ Rel ns m ns' m' r1 r2.
    Proof.
      intros * Hnm HBn Hnb HBv * HRΓ' Hσ Hρ Hev * Hns Hm.
      subst nm.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
      pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd & _).
      assert (Hlk1 : forall c gs n B0, ind_con D c = Some gs -> brs_lookup Bs c = Some (n, B0) ->
                 n = (ind_nn D + List.length gs + cargs_nrec gs)%nat /\ elim_bctx p D gs A Us ++ Γ ⊨ B0 : elim_bty p D c gs A Us)
        by (intros * Hcon Hlb; split; [ exact (Hnb _ _ _ _ Hcon (brs_lookup_in _ _ _ _ Hlb)) | exact (HBv _ _ _ _ Hcon Hlb) ]).
      assert (Hsub : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_sub Bs σ) ->
                 n = (ind_nn D + List.length gs + cargs_nrec gs)%nat)
        by (intros * Hcon Hin; destruct (brs_in_sub _ _ _ _ _ Hin) as [B0 Hin0]; exact (Hnb _ _ _ _ Hcon Hin0)).
      pose proof (per_ind_elim_all p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA (S (ind_nn D))
                    ρ C1 (A[sb_qn (S (ind_nn D)) σ]) A (brs_sub Bs σ) Bs Rel eq_refl Hnd (brs_names_sub _ _ _ HBn) HBn
                    Hsub Hnb
                    (mot_out Γ' RΓ' σ ρ C1 A HRΓ' Hσ Hρ Hev HC11 HAl)
                    (br_out Γ' RΓ' σ ρ C1 Bs HRΓ' Hσ Hρ Hev HC11 Hlk1)) as [PE1 _].
      exact (PE1 _ _ _ Hm _ Hns).
    Qed.

    (** The elimination's four values, related at its type. *)
    Lemma elim_stage : forall Bs Bs' nm Ns M M',
        nm = S (ind_nn D) ->
        brs_names (ind_cons D) Bs -> List.map fst Bs = List.map fst Bs' ->
        (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
        (forall c gs n B B', ind_con D c = Some gs -> brs_lookup Bs c = Some (n, B) -> brs_lookup Bs' c = Some (n, B') ->
           elim_bctx p D gs A Us ++ Γ ⊨ B ≈ B' : elim_bty p D c gs A Us) ->
        List.length Ns = ind_nn D ->
        gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D Us ++ Γ) ->
        Γ ⊨ M ≈ M' : apps (a_ind p) (Us ++ Ns) ->
        forall Γ' RΓ' σ σ' ρ ρ', EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ' : Γ -> RΓ' ρ ρ' ->
        ⟦ σ ⟧s ρ ↘ C1 -> ⟦ σ' ⟧s ρ' ↘ C2 ->
        exists R, rel_exp (A[sb_of_list Id (Ns ++ M :: nil)]) σ ρ C1 (A[sb_of_list Id (Ns ++ M :: nil)]) σ' ρ' C2 (per_univ_elem iA R) /\
          rel_exp (a_elim nm A Bs M) σ ρ C1 (a_elim nm A' Bs' M') σ' ρ' C2 R.
    Proof.
      intros * Hnm HBn HBf Hnb HBB HNl Hg HMM * HRΓ' Hσ Hρ Hev Hev'.
      subst nm.
      pose proof (rel_exp_under_ctx_refl_left HMM) as HMl.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
      assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
      assert (HC22 : RΓ C2 C2) by (etransitivity; [ exact HC21 | exact HC12 ]).
      pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd & _).
      assert (HPΓ' : PER RΓ') by (eapply per_env_PER; exact HRΓ').
      assert (Hρρ : RΓ' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
      assert (Hρ'ρ' : RΓ' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
      (** The scrutinee and its type. *)
      destruct HMM as (RΓm & HRΓm & iM & HMg).
      destruct (HMg _ _ HRΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as (RMe & [t1 t2 t3 t4 Et1 Et2 Et3 Et4 Htc] & [m1 m2 m3 m4 Em1 Em2 Em3 Em4 Hmc]).
      pose proof Et2 as Et2i; apply eval_apps_exp in Et2i as (f2 & ps2 & _ & Eps2 & _).
      apply eval_exps_app_inv in Eps2 as (us2 & ns2 & _ & _ & Hns2).
      pose proof Et3 as Et3i; apply eval_apps_exp in Et3i as (f3 & ps3 & _ & Eps3 & _).
      apply eval_exps_app_inv in Eps3 as (us3 & ns3 & _ & _ & Hns3).
      destruct (us_rel' C2 HC21) as (u3 & Hu3 & H30).
      assert (Lu3 : List.length u3 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hu3); exact HUl).
      assert (Ln2 : List.length ns2 = ind_nn D) by (rewrite (eval_exps_length _ _ _ Hns2); exact HNl).
      assert (Ln3 : List.length ns3 = ind_nn D) by (rewrite (eval_exps_length _ _ _ Hns3); exact HNl).
      assert (Eind : forall B u ns, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ ns ->
                 List.length u = ind_nu D -> List.length ns = ind_nn D ->
                 ⟦ apps (a_ind p) (Us ++ Ns) ⟧ B ↘ d_ind p (u ++ ns)).
      { intros * Hu Hn Lu Ln; apply eval_apps_exp; exists (d_ind p nil), (u ++ ns); split; [ constructor | split ].
        - apply eval_exps_app; assumption.
        - change (d_ind p (u ++ ns)) with (d_ind p (nil ++ (u ++ ns))); apply (IndCases.eval_apps_ind D p Hl).
          cbn; rewrite List.length_app; pose proof Hle; unfold ind_nn in *; lia. }
      assert (t2 = d_ind p (u0 ++ ns2)) as -> by (eapply functional_eval_exp; [ exact Et2 | exact (Eind _ _ _ HUC Hns2 Hu0l Ln2) ]).
      assert (t3 = d_ind p (u3 ++ ns3)) as -> by (eapply functional_eval_exp; [ exact Et3 | exact (Eind _ _ _ Hu3 Hns3 Lu3 Ln3) ]).
      destruct Htc as (_ & Ht23 & _).
      pose proof (ind_univ_inv _ _ _ _ _ _ _ _ Ht23 Hu0l Lu3 Hl) as Hn23.
      pose proof (ind_relate D HD Hc Hsu p Hl u0 u3 ns2 ns3 a0 (U_gargs _ _ (symmetry H30) Hu0l Lu3) Hu0l Ha0 Hn23) as HIR.
      assert (ERM : RMe <~> ind_rel p D u0 nr ar dr ns2) by (eapply per_univ_elem_right_irrel; [ exact Ht23 | exact HIR ]).
      destruct Hmc as (H12 & H23 & H34).
      apply ERM in H12, H23, H34.
      pose proof (trefl_l _ _ Hn23) as Hn22.
      (** The three links. *)
      assert (Hlk1 : forall c gs n B0, ind_con D c = Some gs -> brs_lookup Bs c = Some (n, B0) ->
                 n = (ind_nn D + List.length gs + cargs_nrec gs)%nat /\ elim_bctx p D gs A Us ++ Γ ⊨ B0 : elim_bty p D c gs A Us).
      { intros * Hcon Hlb; split; [ exact (Hnb _ _ _ _ Hcon (brs_lookup_in _ _ _ _ Hlb)) |].
        destruct (brs_lookup_pair _ _ _ _ _ HBf Hlb) as (k & B' & _ & _ & Hlb').
        exact (rel_exp_under_ctx_refl_left (HBB _ _ _ _ _ Hcon Hlb Hlb')). }
      assert (Hlk3 : forall c gs n B0, ind_con D c = Some gs -> brs_lookup Bs' c = Some (n, B0) ->
                 n = (ind_nn D + List.length gs + cargs_nrec gs)%nat /\ elim_bctx p D gs A Us ++ Γ ⊨ B0 : elim_bty p D c gs A Us).
      { intros * Hcon Hlb.
        destruct (brs_lookup_pair _ _ _ _ _ (eq_sym HBf) Hlb) as (k & B & _ & _ & HlB).
        split; [ exact (Hnb _ _ _ _ Hcon (brs_lookup_in _ _ _ _ HlB)) |].
        exact (rel_exp_under_ctx_refl_right (HBB _ _ _ _ _ Hcon HlB Hlb)). }
      assert (HarBs : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs' -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat).
      { intros * Hcon Hin; destruct (brs_in_fst _ _ _ _ _ HBf Hin) as (k & B0 & _ & _ & Hin0); exact (Hnb _ _ _ _ Hcon Hin0). }
      assert (Hsub : forall Bs0 σ0, (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs0 -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
                 forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_sub Bs0 σ0) -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat).
      { intros * H * Hcon Hin; destruct (brs_in_sub _ _ _ _ _ Hin) as [B0 Hin0]; exact (H _ _ _ _ Hcon Hin0). }
      pose proof (brs_names_fst' _ _ _ HBf HBn) as HBn'.
      pose proof (per_ind_elim_all p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA (S (ind_nn D))
                    ρ C1 (A[sb_qn (S (ind_nn D)) σ]) A (brs_sub Bs σ) Bs Rel eq_refl Hnd (brs_names_sub _ _ _ HBn) HBn
                    (Hsub _ _ Hnb) Hnb
                    (mot_out Γ' RΓ' σ ρ C1 A HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HC11 HAl)
                    (br_out Γ' RΓ' σ ρ C1 Bs HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HC11 Hlk1)) as [PE1 _].
      pose proof (per_ind_elim_all p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA (S (ind_nn D))
                    C1 C2 A A' Bs Bs' Rel eq_refl Hnd HBn HBn' Hnb HarBs mot_mid (br_mid Bs Bs' HBB)) as [PE2 _].
      pose proof (per_ind_elim_all p D u0 nr ar dr Hl (decl_closed_params D Hc) HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA (S (ind_nn D))
                    ρ' C2 (A'[sb_qn (S (ind_nn D)) σ']) A' (brs_sub Bs' σ') Bs' Rel eq_refl Hnd (brs_names_sub _ _ _ HBn') HBn'
                    (Hsub _ _ HarBs) HarBs
                    (mot_out Γ' RΓ' σ' ρ' C2 A' HRΓ' (rel_sub_under_ctx_refl_right Hσ) Hρ'ρ' Hev' HC21 HA)
                    (br_out Γ' RΓ' σ' ρ' C2 Bs' HRΓ' (rel_sub_under_ctx_refl_right Hσ) Hρ'ρ' Hev' HC21 Hlk3)) as [PE3 _].
      destruct (PE1 _ _ _ H12 _ Hn22) as (r1 & r2 & Er1 & Er2 & Hr12).
      destruct (PE2 _ _ _ H23 _ Hn23) as (r2' & r3 & Er2' & Er3 & Hr23).
      pose proof (functional_eval_elim _ _ _ _ _ _ _ Er2' Er2) as ->.
      destruct (PE3 _ _ _ (isym _ _ _ H34) _ Hn22) as (r4 & r3' & Er4 & Er3' & Hr43).
      pose proof (functional_eval_elim _ _ _ _ _ _ _ Er3' Er3) as ->.
      (** The type. *)
      pose proof (rel_exp_under_ctx_gsub Hg HAl) as Hty; cbn [exp_sub] in Hty.
      destruct (rel_exp_of_typ_inversion Hty) as (R0 & HR0 & Hgen).
      destruct (rel_exp_implies_rel_typ (Hgen _ _ HRΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')) as [RT HT].
      exists RT; split; [ exact HT |].
      destruct HT as [y1 y2 y3 y4 Ey1 Ey2 Ey3 Ey4 Hyc].
      destruct Hyc as (_ & Hy23 & _).
      pose proof (per_head_iff Ey2 Ey3 Hy23) as ER1.
      assert (Hτ1 : ⟦ sb_of_list Id (Ns ++ M :: nil) ⟧s C1 ↘ env_args C1 (ns2 ++ m2 :: nil))
        by (apply eval_sb_of_list; [ apply eval_sub_id | apply eval_exps_app; [ exact Hns2 | econstructor; [ exact Em2 | constructor ] ] ]).
      destruct (rel_exp_under_ctx_simple_at HRΓ HMl _ _ HC12) as (mx & my & Emx & Emy & Hmxy).
      assert (mx = m2) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (proj2 (per_head_iff Et2 Et3 Ht23 m2 my) Hmxy) as Hmy; apply ERM in Hmy.
      assert (Hτ2 : ⟦ sb_of_list Id (Ns ++ M :: nil) ⟧s C2 ↘ env_args C2 (ns3 ++ my :: nil))
        by (apply eval_sb_of_list; [ apply eval_sub_id | apply eval_exps_app; [ exact Hns3 | econstructor; [ exact Emy | constructor ] ] ]).
      pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HAl HRΓ (gsub_valid Hg) HC12 Hτ1 Hτ2) as ER2.
      pose proof (Rel_resp ns2 m2 ns3 m3 ns2 m2 ns3 my Hn23 (tsym _ _ Hn23) Hn23 H23 (imv _ _ _ _ (isym _ _ _ H23) Hn23) Hmy) as ER3.
      assert (Hfin : forall a b, Rel ns2 m2 ns3 m3 a b -> RT a b) by (intros a b H; apply ER1, ER2, ER3, H).
      pose proof (Rel_PER _ _ _ _ Hn23 H23) as HPR.
      apply (mk_rel_exp r1 r2 r3 r4).
      - cbn [exp_sub]; econstructor; [ exact Em1 | exact Er1 ].
      - econstructor; [ exact Em2 | exact Er2 ].
      - econstructor; [ exact Em3 | exact Er3 ].
      - cbn [exp_sub]; econstructor; [ exact Em4 | exact Er4 ].
      - apply rel_chain_cons; [ apply Hfin | apply rel_chain_cons; [ apply Hfin; exact Hr23 | apply rel_chain_of_pair; apply Hfin ] ].
        + apply (proj1 (Rel_resp ns2 m1 ns2 m2 ns2 m2 ns3 m3 Hn22 Hn22 Hn23 H12 (ind_rel_refl_r _ _ _ _ Hn22 H12) H23 r1 r2)); exact Hr12.
        + symmetry.
          apply (proj1 (Rel_resp ns2 m4 ns2 m3 ns2 m2 ns3 m3 Hn22 Hn22 Hn23 (isym _ _ _ H34) (isym _ _ _ H23) H23 r4 r3)); exact Hr43.
    Qed.
  End Stage.

End Elim.

(** ** The Eliminator, Its Motive, Branches and Scrutinee Varying

    At uniform parameters [Us] and non-uniform ones [Ns], with the
    instance of the motive's context a semantic substitution. *)
Lemma rel_exp_elim_at : forall Γ p D Us Ns M M' nm A A' (i : nat) Bs Bs',
    sem_decl D -> decl_closed D -> ind_sort_univ (ind_sort D) -> decl_typed gc_deps gc_stack D ->
    ind_lookup gc_deps gc_stack p = Some D -> ⊨ Γ ->
    List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T) ->
    List.length Ns = ind_nn D ->
    gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D Us ++ Γ) ->
    Γ ⊨ M ≈ M' : apps (a_ind p) (Us ++ Ns) ->
    nm = S (ind_nn D) ->
    elim_mctx p D Us ++ Γ ⊨ A ≈ A' : Typeω@i ->
    ⊨ elim_mctx p D Us ++ Γ ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A Us ++ Γ) ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', List.nth_error Bs k = Some (c, n, B) -> List.nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs ->
       elim_bctx p D gs A Us ++ Γ ⊨ B ≈ B' : elim_bty p D c gs A Us) ->
    Γ ⊨ a_elim nm A Bs M ≈ a_elim nm A' Bs' M' : A[sb_of_list Id (Ns ++ M :: nil)].
Proof.
  intros * HD Hc Hsu Hdt Hl HΓ HUl HUs HNl Hg HMM Hnm HA HM HBn HBc HBf Hnb HBB.
  pose proof (decl_closed_nu D Hc) as Hle.
  destruct (sem_ctx_per_ctx_env HΓ) as [RΓ HRΓ].
  destruct (sem_ctx_per_ctx_env (uparams_sem D HD)) as [RU HRU].
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
  assert (HNt : ⊨ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ) by exact (sem_ctx_tail HM).
  assert (HBB' : forall c gs n B B', ind_con D c = Some gs -> brs_lookup Bs c = Some (n, B) -> brs_lookup Bs' c = Some (n, B') ->
                   elim_bctx p D gs A Us ++ Γ ⊨ B ≈ B' : elim_bty p D c gs A Us).
  { intros * Hcon HlB HlB'.
    destruct (brs_lookup_pair _ _ _ _ _ HBf HlB) as (k & B'' & Hk & Hk' & HlB'').
    rewrite HlB' in HlB''; injection HlB'' as <-.
    exact (HBB _ _ _ _ _ _ Hk Hk' Hcon). }
  exists RΓ, HRΓ, i.
  intros Γ' RΓ' HRΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HC12 : RΓ ρσ ρ'σ') by (eapply (rel_sub_under_ctx_at' Hσ HRΓ' HRΓ); eassumption).
  assert (HC11 : RΓ ρσ ρσ) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
  destruct (us_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ρσ ρσ HC11) as (u0 & u0' & Hu0 & Hu0' & HU00).
  pose proof (functional_eval_exps' _ _ _ _ Hu0' Hu0) as ->.
  assert (Hu0l : List.length u0 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hu0); exact HUl).
  pose proof (U_gargs D HD Hc RU HRU _ _ HU00 Hu0l Hu0l) as Hu0g.
  destruct (sd_sort D HD) as [j HS].
  destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HU00) as (a0 & _ & Ha0 & _ & _).
  exact (elim_stage D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs u0 a0 Hu0g Hu0l Ha0 HNt HM
           A A' i HA ρσ ρ'σ' HC12 Hu0 HBc Bs Bs' nm Ns M M' Hnm HBn HBf Hnb HBB' HNl Hg HMM
           Γ' RΓ' σ σ' ρ ρ' HRΓ' Hσ Hρ Hev Hev').
Qed.

Lemma rel_exp_elim_cong : forall Γ p D Ps M M' nm A A' (i : nat) Bs Bs',
    sem_decl D -> decl_closed D -> ind_sort_univ (ind_sort D) -> decl_typed gc_deps gc_stack D ->
    ind_lookup gc_deps gc_stack p = Some D -> ⊨ Γ ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T -> Γ ⊨ P : T) ->
    Γ ⊨ M ≈ M' : apps (a_ind p) Ps ->
    nm = S (ind_nn D) ->
    elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊨ A ≈ A' : Typeω@i ->
    ⊨ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', List.nth_error Bs k = Some (c, n, B) -> List.nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs ->
       elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B ≈ B' : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    Γ ⊨ a_elim nm A Bs M ≈ a_elim nm A' Bs' M' : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * HD Hc Hsu Hdt Hl HΓ HPl HPs HMM Hnm HA HM HBn HBc HBf Hnb HBB.
  pose proof (decl_closed_nu D Hc) as Hle.
  set (Us := List.firstn (ind_nu D) Ps) in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HPeq : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
  rewrite HPeq in HMM.
  destruct (params_valid_split D Γ Ps Hc HPl HPs) as [HUs HNs]; fold Us Ns in HUs, HNs.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
  assert (HNl : List.length Ns = ind_nn D) by (unfold Ns; rewrite List.length_skipn; unfold ind_nn; lia).
  eapply rel_exp_elim_at; try eassumption.
  exact (gsub_tau D Hc p Γ HΓ Us HUl HM Ns M HNl HNs (rel_exp_under_ctx_refl_left HMM)).
Qed.



End Fixed_GCtx.
