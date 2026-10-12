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
From Mctt.Core.Syntactic.System Require Import Definitions Scoping IndSyntax GlobalPresup IndTyping.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases GlobalSem MemberReps
  VariableCases FunctionCases LevelCases IndSem TeleSem IndCases.
From Mctt.Core.Semantic Require Import Realizability IndPER IndElim Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Substitutions Weakened *)

Lemma eval_sb_wk_of_list : forall Ms σ φ ρ ρσ ms,
    ⟦ sb_wk σ φ ⟧s ρ ↘ ρσ -> ⟦ List.map (fun M => M[φ]ʷ) Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ sb_wk (sb_of_list σ Ms) φ ⟧s ρ ↘ env_args ρσ ms.
Proof.
  induction Ms as [| M Ms IH]; intros * Hσ HMs; inversion HMs; subst; cbn [sb_of_list]; [ exact Hσ |].
  change (env_args ρσ (m :: ms0)) with (env_args (ρσ ↦ m) ms0).
  apply IH; [ apply eval_sub_wk_extend; assumption | assumption ].
Qed.

Lemma ind_args_rel_len : forall p D ups nr ar ρ gs vs vs', ind_args_rel p D ups nr ar ρ gs vs vs' ->
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
    ⟦ a_var k ⟧ env_args B xs ↘ List.nth (List.length xs - 1 - k) xs d_zero.
Proof.
  intros * Hk.
  replace (List.nth (List.length xs - 1 - k) xs d_zero) with (env_var (env_args B xs) k); [ constructor |].
  rewrite env_var_nth, env_args_rev, List.app_nth1 by (rewrite List.length_rev, List.length_map; lia).
  rewrite List.rev_nth by (rewrite List.length_map; lia).
  rewrite List.length_map, List.map_nth.
  replace (List.length xs - S k) with (List.length xs - 1 - k) by lia; reflexivity.
Qed.

Lemma ihs_rel_len : forall Rel ρ gs vs vs' ihs ihs', ihs_rel Rel ρ gs vs vs' ihs ihs' ->
    List.length ihs = cargs_nrec gs /\ List.length ihs' = cargs_nrec gs.
Proof. induction 1; cbn; lia. Qed.

Lemma ihs_rel_at : forall Rel ρ gs vs vs' ihs ihs', ihs_rel Rel ρ gs vs vs' ihs ihs' ->
    forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
    exists v v' ih ih' bs, List.nth_error vs (List.length gs1) = Some v /\ List.nth_error vs' (List.length gs1) = Some v' /\
      List.nth_error ihs (cargs_nrec gs1) = Some ih /\ List.nth_error ihs' (cargs_nrec gs1) = Some ih' /\
      ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args ρ (nonrec_vals gs1 (List.firstn (List.length gs1) vs)) ↘ bs /\
      Rel bs v bs v' ih ih'.
Proof.
  induction 1 as [ρ | ρ A gs v v' vs vs' ihs ihs' H IH | ρ Ps0 gs v v' vs vs' bs ih ih' ihs ihs' HPs Hr H IH];
    intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst.
  - destruct (IH _ _ _ eq_refl) as (x & x' & y & y' & bs & Hx & Hx' & Hy & Hy' & Ebs & Hr).
    exists x, x', y, y', bs; cbn; repeat split; assumption.
  - exists v, v', ih, ih', bs; cbn; repeat split; assumption.
  - destruct (IH _ _ _ eq_refl) as (x & x' & y & y' & bs0 & Hx & Hx' & Hy & Hy' & Ebs & Hr0).
    exists x, x', y, y', bs0; cbn; repeat split; assumption.
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
    Δ0 ⊨ A : Typeω@i -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨s τ ≈ τ : Δ0 ->
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

(** A type weakened past a telescope, against the type at the base. *)
Lemma wk_typ_link : forall Ψ Γ1 T (j : nat) RS F zs, ⊨ Ψ ++ Γ1 -> Γ1 ⊨ T : Typeω@j ->
    EF Ψ ++ Γ1 ≈ Ψ ++ Γ1 ∈ per_ctx_env ↘ RS -> RS (env_args F zs) (env_args F zs) -> List.length zs = List.length Ψ ->
    exists a b, ⟦ T[wk_shiftn (List.length Ψ)]ʷ ⟧ env_args F zs ↘ a /\ ⟦ T ⟧ F ↘ b /\ Dom a ≈ b ∈ per_univ j.
Proof.
  intros * HS HT HRS HE Hl.
  destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HS) HT) as (R' & HR' & i0 & Hwk).
  assert (ER : RS <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hwk _ _ (proj1 (ER _ _) HE)) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
  rewrite <- Hl, eval_wk_shiftn_args in Em'.
  assert (Hy : y = d_univ j) by (cbn in Ey; inversion Ey; reflexivity).
  rewrite Hy in HRy.
  destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
  apply ERy in Hmm.
  exists m, m'; split; [ exact Em | split; [ exact Em' | exact Hmm ] ].
Qed.

Lemma wk_env_rel : forall Ψ Γ1 RS R1 F F' zs zs', EF Ψ ++ Γ1 ≈ Ψ ++ Γ1 ∈ per_ctx_env ↘ RS ->
    EF Γ1 ≈ Γ1 ∈ per_ctx_env ↘ R1 ->
    RS (env_args F zs) (env_args F' zs') -> List.length zs = List.length Ψ -> List.length zs' = List.length Ψ -> R1 F F'.
Proof.
  intros * HRS HR1 HE Hl Hl'.
  pose proof (rel_wk_app _ _ _ (rel_wk_shiftn _ _ _ _ HRS HR1) _ _ HE) as H.
  rewrite !eval_wk_shiftn in H.
  replace (List.skipn (List.length Ψ) (env_args F zs)) with F in H by (rewrite <- Hl; symmetry; apply skipn_env_args).
  replace (List.skipn (List.length Ψ) (env_args F' zs')) with F' in H by (rewrite <- Hl'; symmetry; apply skipn_env_args).
  exact H.
Qed.

Lemma per_gargs_refl_r : forall ts Tb RTb, EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    forall ρ ρ' xs xs', RTb ρ ρ' -> List.length xs = List.length ts -> per_gargs ts ρ ρ' xs xs' -> per_gargs ts ρ' ρ' xs' xs'.
Proof.
  intros * HTb HC Hts * Hρ Hl Hg.
  destruct (sem_ctx_per_ctx_env HC) as [R HR].
  pose proof (per_gargs_length _ _ _ _ _ Hg) as [L1 _].
  pose proof (gargs_env_rel_gen (List.rev ts) Tb RTb R ρ ρ' xs xs' HTb HR HC Hρ
                ltac:(rewrite List.length_rev; lia) ltac:(rewrite List.rev_involutive; exact Hg)) as HE.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (HE' : R (env_args ρ' xs') (env_args ρ' xs')) by (etransitivity; [ symmetry; exact HE | exact HE ]).
  exact (proj2 (rel_gargs _ _ _ _ HTb HC Hts HR ρ' ρ' xs' xs' ltac:(lia) ltac:(lia) HE')).
Qed.

Lemma cargs_nrec_app : forall gs1 gs2, cargs_nrec (gs1 ++ gs2) = cargs_nrec gs1 + cargs_nrec gs2.
Proof. induction gs1 as [| [] gs1 IH]; intros; cbn; rewrite ?IH; lia. Qed.

Lemma nth_mid : forall (X fa aft ihp : list domain) v,
    List.nth (List.length X + List.length fa) (X ++ fa ++ v :: aft ++ ihp) d_zero = v.
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

(** The values of valid terms at a related environment. *)
Lemma eval_valid_list : forall Ctx RS Δ σ0 Ms E, EF Ctx ≈ Ctx ∈ per_ctx_env ↘ RS -> RS E E ->
    tele_ass Δ -> List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ0 Ms) k = Some T -> Ctx ⊨ N : T) ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ms.
Proof.
  intros * HRS HE HΔ Hl HMs.
  apply eval_exps_each; intros k N HN.
  assert (Hk : k < List.length Ms) by (apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some' (tele_insts Δ σ0 Ms) k) as [T HT]; [ rewrite length_tele_insts by exact HΔ; lia |].
  destruct (rel_exp_under_ctx_simple_at HRS (HMs _ _ _ HN HT) _ _ HE) as (m & _ & Em & _); eauto.
Qed.

(** ** The Constructors' Judgments, from the Declaration's

    The context of a constructor's arguments, and its type, are valid once
    the type former is: they are read off the declaration's own
    judgments. *)
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
      cargs_ctx p D gs1 ++ ind_params D ⊨w (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ ind_params D.
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
        assert (Hj : exists j : nat, cargs_ctx p D gs1 ++ ind_params D
                       ⊨ apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps)
                       : Typeω@j).
        { specialize (HPl _ _ _ _ _ Hin Heq).
          set (pat := cargs_pat gs1).
          unfold ind_uvars.
          assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
          assert (HE : ⊨ (cargs_ctx p D gs1 ++ ind_nparams D) ++ ind_uparams D)
            by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
          assert (HlE : List.length (cargs_ctx p D gs1 ++ ind_nparams D) = List.length pat + ind_nn D)
            by (rewrite List.length_app, length_cargs_ctx, length_nparams, Hpat; reflexivity).
          assert (Huvars : vars_from (List.length pat + ind_nn D) (ind_nu D)
                           = vars_from (List.length (cargs_ctx p D gs1 ++ ind_nparams D)) (List.length (ind_uparams D)))
            by (rewrite HlE, length_ind_uparams by exact Hle; reflexivity).
          assert (Hus : ctx_scoped 0 (ind_uparams D)).
          { rewrite params_split in Hs; apply ctx_scoped_app in Hs as [_ Hs']; exact Hs'. }
          assert (Huass : tele_ass (ind_uparams D)) by (apply Forall_skipn'; exact Hass).
          assert (Humv : ctx_mvc (ind_uparams D)) by (apply Forall_skipn'; exact Hmv).
          apply valid_ind_apps; [ exact HΨ | rewrite List.length_app, List.length_map, HPl, length_vars_from; unfold ind_nn in *; unfold ind_np in *; lia |].
          rewrite params_split; intros k N T HN HT.
          rewrite tele_insts_app in HT; [| exact Huass | rewrite length_vars_from, length_ind_uparams by exact Hle; reflexivity ].
          assert (Hl1 : List.length (vars_from (List.length pat + ind_nn D) (ind_nu D)) = ind_nu D) by apply length_vars_from.
          assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (vars_from (List.length pat + ind_nn D) (ind_nu D))) = ind_nu D)
            by (rewrite length_tele_insts by exact Huass; rewrite Hl1, length_ind_uparams by exact Hle; lia).
          destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
          - rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
            rewrite Huvars in HN, HT.
            pose proof (valid_vars_tele _ _ Huass Hus Humv HE _ _ _ HN HT) as H.
            rewrite <- List.app_assoc in H; exact H.
          - rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
            rewrite Hl1 in HN; rewrite Hl2 in HT.
            apply nth_error_map_inv in HN as (P & HPk & ->).
            set (s := List.length (cargs_strat gs1) + ind_nn D).
            assert (Hti : tele_insts (ind_nparams D) (sb_of_list Id (vars_from (List.length pat + ind_nn D) (ind_nu D))) (List.map (fun P => P[wk_pat pat]ʷ) Ps)
                          = List.map (fun T => T[wk_pat pat]ʷ) (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn s)) Ps)).
            { rewrite <- !map_sub_of_wk; symmetry.
              eapply (tele_insts_sub_mvc _ (ind_nu D));
                [ apply decl_closed_nparams_ass, Hc | apply Forall_firstn'; exact Hmv | apply decl_closed_nparams_scoped, Hc |].
              intros x Hx; rewrite sb_of_list_vars by exact Hx; cbn.
              unfold s; rewrite <- pat_nargs_cargs_pat; fold pat.
              replace (x + (pat_nargs pat + ind_nn D)) with (pat_nargs pat + (ind_nn D + x)) by lia.
              rewrite wk_pat_ge; f_equal; lia. }
            rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
            assert (Hσ : s = List.length (cargs_nonrec gs1) + ind_nn D)
              by (unfold s; rewrite cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
            rewrite Hσ in HT0.
            pose proof (sd_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HPk HT0) as HP0.
            rewrite Heq, <- astrat_prefix in HP0.
            rewrite <- params_split; exact (rel_exp_under_ctx_wk IHw HP0). }
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

    Lemma rec_entry_char : forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
        forall ups ns fa a, List.length ups = ind_nu D -> List.length ns = ind_nn D -> List.length fa = List.length gs1 ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
        tele_full (ind_nr D ups) T ns ns ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa) (nonrec_vals gs1 fa) ->
        (forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
           R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
        forall i R t t',
          ⟦ apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) (ptyp_ps Ps)) ⟧
            env_args nil (ups ++ ns ++ fa) ↘ t ->
          DF t ≈ t' ∈ per_univ_elem i ↘ R ->
          exists bs bs1, ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nonrec_vals gs1 fa) ↘ bs /\
            ⟦ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ fa) ↘ bs1 /\
            tele_full (ind_nr D ups) T bs bs1 /\ t = d_ind p (ups ++ bs1) /\
            (R <~> ind_rel p D ups (ind_nr D ups) (ind_ar D ups) bs).
    Proof.
      intros * Heq * Hlu Hlns Hlk Hgu0 Ha Hnsd INV Hpre * Et HR.
      set (nv := nonrec_vals gs1 fa) in *.
      set (K := List.length (cargs_nonrec gs1)) in *.
      assert (Hlnv : List.length nv = K) by (apply length_nonrec_vals; exact Hlk).
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hgs : per_gargs (List.rev (astrat gs K ++ ind_params D)) nil nil (ups ++ ns ++ nv) (ups ++ ns ++ nv)).
      { unfold astrat; rewrite List.rev_app_distr, List.rev_involutive, (List.app_assoc ups).
        apply per_gargs_app_intro;
          [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams by exact Hle; lia
          | eapply params_gargs; eassumption
          | eapply ar_gargs; eassumption ]. }
      destruct (rec_closure D HD Hc _ _ _ _ _ Hcon Heq ups ups ns ns nv nv Hlu Hlns Hlnv Hlu Hlns Hlnv Hgs)
        as (bs & bs0 & Ebs & _ & _ & Hil).
      set (E1 := env_args nil (ups ++ ns ++ fa)) in *.
      set (E2 := env_args nil (ups ++ ns ++ nv)) in *.
      assert (HwkE : ⟪wk_pat (cargs_pat gs1)⟫ E1 = E2).
      { unfold E1, E2; rewrite (List.app_assoc ups), env_args_app, eval_wk_pat_args by exact Hlk.
        rewrite <- env_args_app, <- List.app_assoc; reflexivity. }
      destruct (sem_ctx_per_ctx_env (cargs_prefix_sem D p gs HΨ _ _ Heq)) as [RΓ' HΓ'].
      pose proof (Hpre _ HΓ') as HE1; fold E1 in HE1.
      assert (HlPs : List.length Ps = ind_nn D) by (eapply length_rec_ps; eassumption).
      assert (HTex : forall m, m < ind_nn D ->
                 exists Tm, List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (K + ind_nn D))) Ps) m = Some Tm).
      { intros m Hm; apply nth_error_lt_some'.
        rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc); rewrite length_nparams; lia. }
      assert (Hlink : forall m P Tm, List.nth_error Ps m = Some P ->
                 List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (K + ind_nn D))) Ps) m = Some Tm ->
                 exists b1 b, ⟦ P[wk_pat (cargs_pat gs1)]ʷ ⟧ E1 ↘ b1 /\ ⟦ P ⟧ E2 ↘ b /\
                   ind_nr D ups m (List.firstn m bs) b b1).
      { intros * HP HTm.
        pose proof (sd_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HP HTm) as HPv.
        rewrite Heq, <- astrat_prefix in HPv.
        destruct (rel_exp_under_ctx_wk_simple (cargs_wk D HD p c gs Hcon HΨ _ _ Heq) HPv) as (RΓ'' & HΓ'' & i1 & Hwk).
        assert (ER : RΓ' <~> RΓ'') by (eapply per_ctx_env_right_irrel; eassumption).
        destruct (Hwk _ _ (proj1 (ER _ _) HE1)) as (u & u' & Ru & Eu & Eu' & HRu & b1 & b & Eb1 & Eb & Hbb).
        rewrite HwkE in Eu', Eb.
        pose proof (Hil _ _ _ HP HTm) as Hcan.
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        pose proof (per_head_iff Eu' Eu' HRuu) as Rel.
        assert (HPu : PER Ru) by (eapply per_elem_PER; exact HRu).
        exists b1, b; split; [ exact Eb1 | split; [ exact Eb | apply Hcan, Rel; symmetry; exact Hbb ] ]. }
      destruct (eval_exps_each (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps) E1) as [bs1 Ebs1].
      { intros m M HM; rewrite List.nth_error_map in HM.
        destruct (List.nth_error Ps m) as [P |] eqn:HP; cbn in HM; [ injection HM as <- | discriminate ].
        assert (Hm : m < ind_nn D) by (rewrite <- HlPs; apply List.nth_error_Some; congruence).
        destruct (HTex _ Hm) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & _ & Eb1 & _); eauto. }
      assert (Htf : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs1).
      { rewrite tele_full_iff, List.length_rev, length_nparams.
        rewrite (eval_exps_length _ _ _ Ebs), (eval_exps_length _ _ _ Ebs1), List.length_map.
        split; [ exact HlPs | split; [ exact HlPs |] ].
        intros j y y' Hy Hy'.
        assert (Hj : j < ind_nn D) by (rewrite <- HlPs, <- (eval_exps_length _ _ _ Ebs); apply List.nth_error_Some; congruence).
        destruct (nth_error_lt_some' Ps j ltac:(lia)) as [P HP].
        destruct (HTex _ Hj) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & b & Eb1 & Eb & Hr).
        destruct (eval_exps_nth _ _ _ _ _ Ebs HP) as (b0 & Hb0 & Eb0).
        destruct (eval_exps_nth _ _ _ _ _ Ebs1 ltac:(rewrite List.nth_error_map, HP; reflexivity)) as (b2 & Hb2 & Eb2).
        assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
        rewrite Hy in Hb0; injection Hb0 as ->; rewrite Hy' in Hb2; injection Hb2 as ->; exact Hr. }
      pose proof (ind_relate D HD Hc Hsu p Hl _ _ _ _ _ Hgu0 Hlu Ha Htf) as Hind.
      pose proof (per_univ_sym _ _ _ _ Hind) as Hind'.
      assert (Et0 : ⟦ apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps) ⟧ E1
                      ↘ d_ind p (ups ++ bs1)).
      { apply eval_apps_exp; exists (d_ind p nil), (ups ++ bs1); split; [ constructor | split ].
        - apply eval_exps_app; [| exact Ebs1 ].
          unfold ind_uvars; rewrite length_cargs_pat.
          unfold E1.
          replace (List.length gs1 + ind_nn D) with (List.length (ns ++ fa)) by (rewrite List.length_app; lia).
          replace (ind_nu D) with (List.length ups) by exact Hlu.
          apply eval_vars_from_args.
        - change (d_ind p (ups ++ bs1)) with (d_ind p (nil ++ (ups ++ bs1))).
          apply (IndCases.eval_apps_ind D p Hl).
          rewrite List.length_app, (eval_exps_length _ _ _ Ebs1), List.length_map; cbn; unfold ind_nn in *; lia. }
      assert (t = d_ind p (ups ++ bs1)) as Ht by (eapply functional_eval_exp; eassumption).
      rewrite Ht in HR.
      exists bs, bs1; split; [ exact Ebs | split; [ exact Ebs1 | split; [ exact Htf | split; [ exact Ht |] ] ] ].
      eapply per_univ_elem_right_irrel; [ exact HR | exact Hind' ].
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

  Lemma u0_canon :
      (forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> PER (nr k vs)) /\
      (forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> (nr k vs <~> nr k vs')) /\
      (forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> PER (ar ms c k vs)) /\
      (forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> (ar ms c k vs <~> ar ms' c k vs')) /\
      ind_adm D u0 nr ar u0.
  Proof. eapply ind_canon; eassumption. Qed.

  Let HnP := proj1 u0_canon.
  Let HnI := proj1 (proj2 u0_canon).
  Let HaP := proj1 (proj2 (proj2 u0_canon)).
  Let HaI := proj1 (proj2 (proj2 (proj2 u0_canon))).
  Let Had := proj2 (proj2 (proj2 (proj2 u0_canon))).

  Lemma nr_pre_refl : forall k vs vs', k <= ind_nn D -> tele_pre nr k vs vs' -> tele_pre nr k vs vs.
  Proof.
    intros; eapply (tnrp_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI); [| eassumption ].
    unfold T; rewrite List.length_rev, length_nparams; assumption.
  Qed.

  (** The canonical relations at uniform parameters related to the
      canonical ones are the canonical ones. *)
  Lemma nr_change_u0 : forall w, per_gargs (List.rev (ind_uparams D)) nil nil u0 w ->
      forall X Y, tele_full (ind_nr D w) T X Y -> tele_full nr T X Y.
  Proof.
    intros w Hg X Y H.
    eapply tele_full_map; [| exact H ].
    intros k pa pb x y Hk _ Hp2 Hr.
    destruct (nparams_lt_ass D k (decl_closed_params D Hc) Hk) as [A HA].
    pose proof (nr_pre_refl k pa pb ltac:(unfold T in Hk; rewrite List.length_rev, length_nparams in Hk; lia) Hp2) as Hpp.
    destruct (canon_hn D HD Hc Hsu u0 a0 Hu0l Ha0 w Hg k A pa pa HA Hpp) as (t & t' & Et & Et' & [R0 HR0]).
    unfold nr, ind_nr in *; rewrite (nth_ctyp_eq _ _ _ HA) in *.
    destruct (per_univ_elem_sym _ _ _ _ HR0) as [HRs _].
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HRs HR0) as (R1 & HR1 & _).
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR0 HRs) as (R2 & HR2 & E2).
    apply (per_head_iff Et Et HR2).
    apply (per_head_iff Et' Et' HR1) in Hr.
    apply E2.
    assert (E : R0 <~> R1) by (eapply per_univ_elem_chain_iff; [ exact HR0 | exact HR1 ]).
    apply E; exact Hr.
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
      forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar ns m m' ->
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
    pose proof (tnr_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI _ _ Hns) as Hnsns.
    pose proof (ind_relate D HD Hc Hsu p Hl u0 w1 ns ns a0 (U_gargs _ _ Hw0 Hu0l Lw1) Hu0l Ha0 Hnsns) as Hrel.
    assert (E : ind_rel p D u0 nr ar ns <~> R12) by (eapply per_univ_elem_chain_iff; [ exact Hrel | exact HR12 ]).
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
  Lemma ind_args_rel_at : forall ρ gs vs vs', ind_args_rel p D u0 nr ar ρ gs vs vs' ->
      forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
      exists x x' bs, List.nth_error vs (List.length gs1) = Some x /\ List.nth_error vs' (List.length gs1) = Some x' /\
        ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args ρ (nonrec_vals gs1 (List.firstn (List.length gs1) vs)) ↘ bs /\
        ind_rel p D u0 nr ar bs x x'.
  Proof.
    induction 1 as [ρ | ρ v gs vs vs' A v' H IH | Ps0 ρ bs v v' gs vs vs' HPs Hr H IH];
      intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst.
    - destruct (IH _ _ _ eq_refl) as (x & x' & bs & Hx & Hx' & Ebs & Hr).
      exists x, x', bs; cbn; split; [ exact Hx | split; [ exact Hx' | split; [ exact Ebs | exact Hr ] ] ].
    - exists v, v', bs; cbn; split; [ reflexivity | split; [ reflexivity | split; assumption ] ].
    - destruct (IH _ _ _ eq_refl) as (x & x' & bs0 & Hx & Hx' & Ebs & Hr0).
      exists x, x', bs0; cbn; split; [ exact Hx | split; [ exact Hx' | split; [ exact Ebs | exact Hr0 ] ] ].
  Qed.

  Section ConGargs.
    Variable (c : String.string) (gs : list carg).
    Hypothesis (Hcon : ind_con D c = Some gs).
    Let HΨ := sd_cargs D HD p c gs Hl Hcon.
    Let HnPs := proj1 u0_canon.

    Lemma cargs_gargs : forall ns nsa nsb vs vs',
        tele_full nr T ns nsa -> tele_full nr T ns nsb ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs' ->
        forall k, k <= List.length gs ->
        per_gargs (List.rev (cargs_ctx p D (List.firstn k gs))) (env_args nil (u0 ++ nsa)) (env_args nil (u0 ++ nsb))
          (List.firstn k vs) (List.firstn k vs').
    Proof.
      intros * Ha Hb Har Hia.
      pose proof (tnr_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI _ _ Ha) as Hnn.
      pose proof (tnr_trans p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI _ _ _
                    (tnr_sym p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI _ _ Ha) Hb) as Hab.
      pose proof (tnr_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI _ _ Hab) as Haa.
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Hlv Hlv'].
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
        { eapply (tar_pre_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI ns c gs Hnn Hcon);
            [ rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia | exact Hpk ]. }
        exact (proj1 (HaI _ _ _ _ _ _ _ _ Ha Hcon HA Hpkd x x') Hr).
      - destruct (sem_ctx_ass_inv HC1) as [j HT].
        destruct (rel_exp_of_typ_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
        assert (Et2 : ⟦ apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps) ⟧ env_args (env_args nil (u0 ++ nsa)) fa ↘ t)
          by (rewrite <- env_args_app, <- List.app_assoc; exact Et).
        assert (Et2' : ⟦ apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps) ⟧ env_args (env_args nil (u0 ++ nsb)) fa' ↘ t')
          by (rewrite <- env_args_app, <- List.app_assoc; exact Et').
        destruct (per_univ_elem_to_nat _ _ _ _ HR) as [n Hn].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R); [ rewrite List.length_rev, length_cargs_ctx; lia | exact IHk
                                                     | exact (mk_rel_mod_eval _ _ Et2 Et2' Hn) |].
        assert (Hpk : tele_pre (ar ns c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa)).
        { assert (Hpk0 : tele_pre (ar ns c) K (nonrec_vals gs1 fa) (nonrec_vals gs1 fa')).
          { rewrite <- (proj1 Hnv), <- (proj2 Hnv); apply tele_pre_of_full with (T := cargs_nonrec gs); [ exact Har |].
            rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia. }
          eapply (tar_pre_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI ns c gs Hnn Hcon);
            [ rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia | exact Hpk0 ]. }
        assert (HKl : K <= List.length (cargs_nonrec gs)) by (rewrite Heq, cargs_nonrec_app, List.length_app; unfold K; lia).
        pose proof (tarp_inst p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI ns nsa c gs K _ _ Ha Hcon HKl Hpk) as Hpka.
        destruct (rec_entry_char c gs Hcon gs1 Ps _ Heq u0 nsa fa a0 Hu0l ltac:(lia) (eq_trans Lfa (eq_sym Lk)) Hu0g Ha0 Haa Hpka Hpre _ _ _ _ Et HR)
          as (bsa & ? & Ebsa & _ & _ & _ & ER).
        apply ER.
        destruct (ind_args_rel_at _ _ _ _ Hia gs1 Ps _ Heq) as (y & y' & bs & Hy & Hy' & Ebs & Hrel).
        rewrite Lk in Hy, Hy', Ebs; rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
        fold fa in Ebs; rewrite <- env_args_app, <- List.app_assoc in Ebs.
        destruct (proj2 (proj2 Had) _ _ _ _ _ _ _ _ _ Ha Hcon Heq Hpk) as (b1 & b2 & Eb1 & Eb2 & Hbb).
        pose proof (functional_eval_exps' _ _ _ _ Eb1 Ebs) as ->.
        pose proof (functional_eval_exps' _ _ _ _ Eb2 Ebsa) as ->.
        exact (ind_rel_mv p D u0 nr ar Hl (decl_closed_params D Hc) HnP HnI HaP HaI Had Hle _ _ _ _ Hrel Hbb).
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
    assert (Hwj : elim_bctx p D gs A Us ++ Γ ⊨w (wk_shiftn n) : Γ).
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

  (** ** The Motive's Instances at the Recursive Arguments *)
  Lemma ih_args_valid : forall c gs gs1 Ps gs2 E, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
      ⊨ E ++ cinst Γ p D Us gs ->
      forall k N T0,
        List.nth_error (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                   [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)
              ++ a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil) k = Some N ->
        List.nth_error (tele_insts (elim_mctx p D Us) (sb_of_wk (wk_shiftn (List.length E + List.length gs + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                   [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)
              ++ a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)) k = Some T0 ->
        E ++ cinst Γ p D Us gs ⊨ N : T0.
  Proof.
    intros * Hcon Heq HΨ.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof Hdt as (Hass & (Hmv & Hmvs & Hmvc) & _ & HΔ & HS & _ & _ & HA & HPl & HP & _).
    pose proof (HPl _ _ _ _ _ Hin Heq) as HPl'.
    set (pat := cargs_pat gs1) in *.
    assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
    set (i := List.length pat) in *.
    set (j := List.length E) in *.
    set (na := List.length gs) in *.
    assert (Hna : na = i + S (List.length gs2)) by (unfold na, i; rewrite Heq, List.length_app; cbn; lia).
    set (m := j + na + ind_nn D).
    set (s := na - i + j).
    set (ρ := sb_qn (i + ind_nn D) (sb_of_list Id Us)).
    set (θ := (sb_of_wk (wk_pat pat) ⨟ ρ) ⨟ sb_of_wk (wk_shiftn s)).
    assert (HPs' : List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps = List.map (fun P => P[θ]) Ps)
      by (apply List.map_ext; intros; apply exp_wk_sub_wk).
    (* the base *)
    assert (Hwm : E ++ cinst Γ p D Us gs ⊨w (wk_shiftn m) : Γ).
    { unfold cinst in HΨ |- *; rewrite !List.app_assoc in HΨ |- *.
      replace m with (List.length ((E ++ tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                                       ++ tele_sub (ind_nparams D) (sb_of_list Id Us)))
        by (rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_nparams; unfold m; lia).
      apply rel_wk_under_ctx_shiftn; exact HΨ. }
    (* the context of the arguments before the recursive one *)
    pose proof (sd_cargs D HD p c gs Hl Hcon) as HΨc.
    pose proof (cargs_prefix_sem D p gs HΨc gs1 (ca_rec Ps :: gs2) Heq) as HΨ1.
    assert (HΨ1a : tele_ass (cargs_ctx p D gs1 ++ ind_params D))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
    destruct (closed_app_sem _ _ HΨ1a HΨ1 HΓ) as [HΨ1Γ _].
    assert (Hτ2 : gsub (cinst Γ p D Us gs1) ρ (cargs_ctx p D gs1 ++ ind_params D ++ Γ)).
    { rewrite cinst_eq; unfold ρ.
      replace (i + ind_nn D) with (List.length (cargs_ctx p D gs1 ++ ind_nparams D))
        by (rewrite List.length_app, length_cargs_ctx, length_nparams; unfold i; lia).
      rewrite params_split, <- !List.app_assoc, (List.app_assoc (cargs_ctx p D gs1)).
      apply gsub_qn; [ exact gsub_U | apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ] |].
      rewrite params_split in HΨ1Γ; rewrite <- !List.app_assoc in HΨ1Γ |- *; rewrite <- List.app_assoc in HΨ1Γ; exact HΨ1Γ. }
    assert (Hw3 : E ++ cinst Γ p D Us gs ⊨w (wk_shiftn s) : cinst Γ p D Us gs1).
    { pose proof HΨ as HΨ'.
      rewrite Heq in HΨ' |- *; rewrite cinst_split in HΨ' |- *; rewrite List.app_assoc in HΨ' |- *.
      replace s with (List.length (E ++ tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                                       (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                                       ++ ce_ass (apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1))
                                                   ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps))
                                            [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))] :: nil))
        by (rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; unfold s, i, j; lia).
      apply rel_wk_under_ctx_shiftn; exact HΨ'. }
    assert (HE1 : ⊨ cinst Γ p D Us gs1) by exact (gsub_sem_ctx _ _ _ Hτ2).
    intros k N T0 HN HT.
    unfold elim_mctx in HT.
    change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R) in HT.
    assert (Hrass : tele_ass (tele_sub (ind_nparams D) (sb_of_list Id Us))) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub, length_nparams, List.length_map; exact HPl').
    assert (Hl1 : List.length (List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps) = ind_nn D) by (rewrite List.length_map; exact HPl').
    assert (Hl2 : List.length (tele_insts (tele_sub (ind_nparams D) (sb_of_list Id Us)) (sb_of_wk (wk_shiftn m))
                                 (List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps)) = ind_nn D)
      by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_nparams, Hl1; lia).
    destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
    - (* a non-uniform parameter *)
      rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      apply nth_error_map_inv in HN as (P & HPk & ->).
      rewrite tele_insts_tele_sub in HT.
      set (σ0 := sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))).
      assert (HT0 : exists T1, List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k = Some T1).
      { destruct (List.nth_error (tele_insts (ind_nparams D) σ0 Ps) k) as [T1 |] eqn:E0; [ eauto |].
        apply List.nth_error_None in E0; rewrite length_tele_insts in E0 by (apply decl_closed_nparams_ass, Hc).
        rewrite length_nparams, HPl' in E0; lia. }
      destruct HT0 as [T1 HT0].
      assert (Hσ0 : σ0 = sb_of_wk (wk_shiftn (List.length (cargs_nonrec gs1) + ind_nn D)))
        by (unfold σ0; rewrite cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
      pose proof (sd_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HPk ltac:(rewrite <- Hσ0; exact HT0)) as HP0.
      rewrite Heq, <- astrat_prefix in HP0.
      pose proof (rel_exp_under_ctx_wk (cargs_wk D HD p c gs Hcon HΨc _ _ Heq) HP0) as HP1.
      pose proof (closed_app_valid _ _ _ _ _ HΨ1a HΨ1 HΓ HP1) as HP2.
      rewrite <- List.app_assoc in HP2.
      pose proof (rel_exp_under_ctx_gsub Hτ2 HP2) as HP3.
      pose proof (rel_exp_under_ctx_wk Hw3 HP3) as HP4.
      replace T0 with (T1[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ); [ exact HP4 |].
      rewrite HPs' in HT; rewrite exp_wk_sub_wk; fold θ.
      rewrite <- (tele_insts_sub_mvc (ind_nparams D) (ind_nu D) σ0 _ θ Ps) in HT.
      + apply nth_error_map_inv in HT as (T2 & HT2 & ->); rewrite HT0 in HT2; injection HT2 as ->; reflexivity.
      + apply decl_closed_nparams_ass, Hc.
      + apply Forall_firstn'; exact Hmv.
      + apply decl_closed_nparams_scoped, Hc.
      + intros x Hx; unfold σ0, θ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        rewrite <- pat_nargs_cargs_pat; fold pat.
        replace (x + (pat_nargs pat + ind_nn D)) with (pat_nargs pat + (ind_nn D + x)) by lia.
        rewrite wk_pat_ge; fold i; unfold ρ; rewrite sb_qn_ge by lia.
        replace (i + (ind_nn D + x) - (i + ind_nn D)) with x by lia.
        rewrite (sb_of_list_nth _ _ _ (a_var 0)) by lia; cbn.
        rewrite !exp_sub_of_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold m, s; lia.
    - (* the recursive argument *)
      rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl1 in HN; rewrite Hl2 in HT.
      destruct (k - ind_nn D) as [| k'] eqn:Hk'; cbn in HN, HT; [| destruct k'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
      rewrite <- Hl1, map_shift_sb_of_list, vars_from_sb_of_list.
      apply valid_exp_var; [| exact HΨ ].
      rewrite Heq; rewrite cinst_split, List.app_assoc.
      rewrite <- !List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
      set (L := tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2)
                  (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))).
      assert (HL : List.length L = List.length gs2) by (unfold L; rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity).
      replace (j + na - 1 - i) with (0 + List.length (E ++ L)) by (rewrite List.length_app, HL; unfold j; lia).
      match goal with |- _ ∋ # _ : ?T =>
        replace T with ((apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1))
                           ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps))
                          [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))][wk_shift]ʷ[wk_shiftn (List.length (E ++ L))]ʷ)
      end.
      { apply ctx_lookup_app_r; constructor. }
      rewrite apps_exp_sub, !apps_exp_wk; cbn [exp_sub exp_wk]; f_equal.
      rewrite !List.map_app, !List.map_map; f_equal.
      + unfold ind_uvars.
        rewrite <- (List.map_map (fun M => M[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))])
                      (fun M => M[wk_shift]ʷ[wk_shiftn (List.length (E ++ L))]ʷ)).
        rewrite (List.map_ext (fun M => M[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))])
                   (fun M => M[sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us)]))
          by (intros; apply exp_sub_sb_eq, sb_qn_add).
        change (vars_from (List.length (cargs_pat gs1) + ind_nn D) (ind_nu D)) with (vars_from (i + ind_nn D) (ind_nu D)).
        rewrite Hpat, <- HUl, vars_from_sb_qn, List.map_map.
        apply List.map_ext; intros U; rewrite exp_sub_of_wk, !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn.
        rewrite List.length_app, HL; unfold m, j; lia.
      + apply List.map_ext; intros P.
        rewrite (exp_sub_sb_eq _ _ ρ) by (unfold ρ; rewrite Hpat; apply sb_qn_add).
        rewrite !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; rewrite List.length_app, HL; unfold s, j; lia.
  Qed.

  Lemma gsub_ih : forall c gs gs1 Ps gs2 E, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
      ⊨ E ++ cinst Γ p D Us gs ->
      gsub (E ++ cinst Γ p D Us gs)
        (sb_of_list (sb_of_wk (wk_shiftn (List.length E + List.length gs + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                 [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)
            ++ a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil))
        (elim_mctx p D Us ++ Γ).
  Proof.
    intros * Hcon Heq HΨ.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & HPl & _).
    pose proof (HPl _ _ _ _ _ Hin Heq) as HPl'.
    assert (Hwm : E ++ cinst Γ p D Us gs ⊨w (wk_shiftn (List.length E + List.length gs + ind_nn D)) : Γ).
    { unfold cinst in HΨ |- *; rewrite !List.app_assoc in HΨ |- *.
      replace (List.length E + List.length gs + ind_nn D)
        with (List.length ((E ++ tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                               ++ tele_sub (ind_nparams D) (sb_of_list Id Us)))
        by (rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_nparams; lia).
      apply rel_wk_under_ctx_shiftn; exact HΨ. }
    apply gsub_of_list; [ exact (gsub_wk _ _ _ Hwm HΨ HΓ) | apply elim_mctx_ass, Hc | exact HM
                        | rewrite List.length_app, List.length_map, length_elim_mctx, HPl'; cbn; lia |].
    exact (ih_args_valid _ _ _ _ _ _ Hcon Heq HΨ).
  Qed.

  (** Its part at the non-uniform parameters. *)
  Lemma ih_pre_valid : forall c gs gs1 Ps gs2 E, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
      ⊨ E ++ cinst Γ p D Us gs ->
      forall k N T0,
        List.nth_error (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                   [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)) k = Some N ->
        List.nth_error (tele_insts (tele_sub (ind_nparams D) τU) (sb_of_wk (wk_shiftn (List.length E + List.length gs + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                   [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps))) k = Some T0 ->
        E ++ cinst Γ p D Us gs ⊨ N : T0.
  Proof.
    intros * Hcon Heq HΨ k N T0 HN HT.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & HPl & _).
    pose proof (HPl _ _ _ _ _ Hin Heq) as HPl'.
    assert (Hrass : tele_ass (tele_sub (ind_nparams D) (sb_of_list Id Us))) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
    assert (Hk : k < ind_nn D) by (rewrite <- HPl', <- (List.length_map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                 [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ)); apply List.nth_error_Some; congruence).
    apply (ih_args_valid _ _ _ _ _ _ Hcon Heq HΨ k).
    - rewrite List.nth_error_app1 by (rewrite List.length_map; lia); exact HN.
    - unfold elim_mctx; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R).
      rewrite tele_insts_app by (try exact Hrass; rewrite length_ind_nparams_sub, List.length_map; exact HPl').
      rewrite List.nth_error_app1; [ exact HT |].
      rewrite length_tele_insts by exact Hrass; rewrite length_ind_nparams_sub, List.length_map; lia.
  Qed.

  Lemma gsub_ih_pre : forall c gs gs1 Ps gs2 E, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
      ⊨ E ++ cinst Γ p D Us gs ->
      gsub (E ++ cinst Γ p D Us gs)
        (sb_of_list (sb_of_wk (wk_shiftn (List.length E + List.length gs + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                 [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps)))
        (tele_sub (ind_nparams D) τU ++ Γ).
  Proof.
    intros * Hcon Heq HΨ.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & HPl & _).
    pose proof (HPl _ _ _ _ _ Hin Heq) as HPl'.
    assert (Hwm : E ++ cinst Γ p D Us gs ⊨w (wk_shiftn (List.length E + List.length gs + ind_nn D)) : Γ).
    { unfold cinst in HΨ |- *; rewrite !List.app_assoc in HΨ |- *.
      replace (List.length E + List.length gs + ind_nn D)
        with (List.length ((E ++ tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)))
                               ++ tele_sub (ind_nparams D) (sb_of_list Id Us)))
        by (rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_nparams; lia).
      apply rel_wk_under_ctx_shiftn; exact HΨ. }
    assert (Hrass : tele_ass (tele_sub (ind_nparams D) (sb_of_list Id Us))) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
    apply gsub_of_list; [ exact (gsub_wk _ _ _ Hwm HΨ HΓ) | exact Hrass | exact HNt
                        | rewrite List.length_map, length_ind_nparams_sub, HPl'; reflexivity |].
    exact (ih_pre_valid _ _ _ _ _ _ Hcon Heq HΨ).
  Qed.

  (** The scrutinee's type in the motive's context, at the instance of a
      recursive result's parameters, is the type of the recursive argument
      weakened past the arguments after it and the results before. *)
  Lemma ih_it_eq : forall gs1 Ps gs2 (E : ctx), List.length (ptyp_ps Ps) = ind_nn D ->
      IT[sb_of_list (sb_of_wk (wk_shiftn (List.length E + List.length (gs1 ++ ca_rec Ps :: gs2) + ind_nn D)))
           (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                 [wk_shiftn (List.length (gs1 ++ ca_rec Ps :: gs2) - List.length (cargs_pat gs1) + List.length E)]ʷ) (ptyp_ps Ps))]
      = (apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) (ptyp_ps Ps)))
          [sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))][wk_shift]ʷ[wk_shiftn (List.length E + List.length gs2)]ʷ.
  Proof.
    intros * HPl'.
    set (gs := gs1 ++ ca_rec Ps :: gs2).
    set (pat := cargs_pat gs1).
    assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
    set (i := List.length pat) in *.
    set (j := List.length E).
    set (na := List.length gs).
    assert (Hna : na = i + S (List.length gs2)) by (unfold na, gs, i; rewrite List.length_app; cbn; lia).
    set (m := j + na + ind_nn D).
    set (s := na - i + j).
    set (ρ := sb_qn (i + ind_nn D) (sb_of_list Id Us)).
    assert (Hl1 : List.length (List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps) = ind_nn D) by (rewrite List.length_map; exact HPl').
    unfold IT; rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
    pose proof (map_shift_sb_of_list Us (List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps) (sb_of_wk (wk_shiftn m))) as E1.
    pose proof (vars_from_sb_of_list (List.map (fun P => P[wk_pat pat]ʷ[ρ][wk_shiftn s]ʷ) Ps) (sb_of_wk (wk_shiftn m))) as E2.
    rewrite Hl1 in E1, E2.
    rewrite E1, E2.
    symmetry.
    rewrite apps_exp_sub, !apps_exp_wk; cbn [exp_sub exp_wk]; f_equal.
    rewrite !List.map_app, !List.map_map; f_equal.
    - unfold ind_uvars.
      rewrite <- (List.map_map (fun M => M[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))])
                    (fun M => M[wk_shift]ʷ[wk_shiftn (List.length E + List.length gs2)]ʷ)).
      rewrite (List.map_ext (fun M => M[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))])
                 (fun M => M[sb_qn (List.length gs1 + ind_nn D) (sb_of_list Id Us)]))
        by (intros; apply exp_sub_sb_eq, sb_qn_add).
      change (vars_from (List.length (cargs_pat gs1) + ind_nn D) (ind_nu D)) with (vars_from (i + ind_nn D) (ind_nu D)).
      rewrite Hpat, <- HUl, vars_from_sb_qn, List.map_map.
      apply List.map_ext; intros U; rewrite exp_sub_of_wk, !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn.
      unfold m, j; lia.
    - apply List.map_ext; intros P.
      rewrite (exp_sub_sb_eq _ _ ρ) by (unfold ρ; rewrite Hpat; apply sb_qn_add).
      rewrite !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold s, j; lia.
  Qed.

  (** ** The Branches' Contexts

      The recursive results of a constructor's arguments are related at
      the motive's family, read at the environments [C1] and [C2]. *)
  Let tsym := tnr_sym p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI.
  Let ttrans := tnr_trans p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI.
  Let trefl_r := tnr_refl_r p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI.

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

    (** The values of a recursive result's non-uniform parameters, related
        to those of the recursive argument's declaration. *)
    Lemma ih_bridge : forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
        forall B, RΓ B C1 ->
        forall ns Xb fa fab vb aft ihp bs RS,
          tele_full nr T ns Xb ->
          List.length fa = List.length gs1 -> List.length fab = List.length gs1 -> List.length aft = List.length gs2 ->
          List.length ihp = cargs_nrec gs1 ->
          tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa) (nonrec_vals gs1 fab) ->
          per_gargs (List.rev (cargs_ctx p D gs1 ++ ind_nparams D)) (env_args nil u0) (env_args nil u0) (Xb ++ fab) (Xb ++ fab) ->
          ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ ns ++ nonrec_vals gs1 fa) ↘ bs ->
          EF ihs_ctx_aux D A Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Us gs
             ≈ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Us gs ∈ per_ctx_env ↘ RS ->
          RS (env_args B (Xb ++ fab ++ vb :: aft ++ ihp)) (env_args B (Xb ++ fab ++ vb :: aft ++ ihp)) ->
          exists Xq,
            ⟦ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                  [wk_shiftn (List.length gs - List.length (cargs_pat gs1)
                                              + List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1))]ʷ) (ptyp_ps Ps) ⟧*
              gc_deps ⍮ gc_stack ⍮ env_args B (Xb ++ fab ++ vb :: aft ++ ihp) ↘ Xq /\
            tele_full nr T bs Xq.
    Proof.
      intros * Heq B HBC * Hns Lfa Lfab Laft Lihp Hpk Hgp Ebs HRS HE.
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
      pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & HPl & _).
      pose proof (HPl _ _ _ _ _ Hin Heq) as HPl'.
      pose proof (ih_it_eq gs1 Ps gs2 (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) HPl') as HIeq.
      rewrite <- Heq in HIeq.
      pose proof (ihs_pre_sem gs1 (ca_rec Ps :: gs2) Heq) as HCtx.
      pose proof (ih_pre_valid _ _ _ _ _ _ Hcon Heq HCtx) as HPv.
      pose proof (gsub_ih_pre _ _ _ _ _ _ Hcon Heq HCtx) as Hg'.
      set (E := ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) in *.
      assert (LE : List.length E = cargs_nrec gs1) by apply length_ihs_ctx_aux.
      set (Ps' := List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                  [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) Ps) in *.
      set (m := List.length E + List.length gs + ind_nn D) in *.
      set (Ep := env_args B (Xb ++ fab ++ vb :: aft ++ ihp)) in *.
      pose proof Hns as Hns0; rewrite tele_full_iff in Hns0; destruct Hns0 as (Ln & LXb & _).
      unfold T in Ln, LXb; rewrite List.length_rev, length_nparams in Ln, LXb.
      assert (Lgs : List.length gs = List.length gs1 + S (List.length gs2)) by (rewrite Heq, List.length_app; cbn; lia).
      assert (Lzs : List.length (Xb ++ fab ++ vb :: aft ++ ihp) = m)
        by (unfold m; rewrite !List.length_app; cbn; rewrite List.length_app; lia).
      (** The values of the recursive result's parameters. *)
      destruct (eval_valid_list _ _ (tele_sub (ind_nparams D) τU) (sb_of_wk (wk_shiftn m)) Ps' Ep HRS HE
                  ltac:(apply tele_ass_sub, decl_closed_nparams_ass, Hc)
                  ltac:(unfold Ps'; rewrite List.length_map, length_ind_nparams_sub; exact HPl') HPv) as [Xq HXq].
      assert (LXq : List.length Xq = ind_nn D) by (rewrite (eval_exps_length _ _ _ HXq); unfold Ps'; rewrite List.length_map; exact HPl').
      assert (Hev : ⟦ sb_of_list (sb_of_wk (wk_shiftn m)) Ps' ⟧s Ep ↘ env_args B Xq).
      { apply eval_sb_of_list; [| exact HXq ].
        pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn m) Ep (wk_mono_shiftn _)) as H.
        assert (Hw : ⟪wk_shiftn m⟫ Ep = B) by (unfold Ep; rewrite <- Lzs; apply eval_wk_shiftn_args).
        rewrite Hw in H; exact H. }
      pose proof (gsub_valid Hg') as Hτ'.
      (** The scrutinee's type there. *)
      pose proof HM as HM'; rewrite mctx_split in HM'.
      destruct (sem_ctx_ass_inv HM') as [jI HIT].
      pose proof (sem_ctx_tail HM') as HNtΓ.
      destruct (sem_ctx_per_ctx_env HNtΓ) as [RN HRN].
      destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HIT HRS Hτ' HE Hev) as (a1 & b1 & Ea1 & Eb1 & Hab1).
      assert (HEN : RN (env_args B Xq) (env_args B Xq)) by (eapply (rel_sub_under_ctx_at' Hτ' HRS HRN); eassumption).
      destruct (us_wk_vals (tele_sub (ind_nparams D) τU) RN B Xq HRN HNtΓ HEN ltac:(rewrite length_ind_nparams_sub; exact LXq))
        as (w & uB & Hw & HuB & Hwu).
      rewrite length_ind_nparams_sub in Hw.
      pose proof (eval_IT _ _ _ LXq Hw) as Eb1'.
      assert (b1 = d_ind p (w ++ Xq)) as -> by (eapply functional_eval_exp; eassumption).
      destruct (us_rel B HBC) as (uB' & HuB' & HuB0).
      pose proof (functional_eval_exps' _ _ _ _ HuB HuB') as <-.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (Hw0 : RU (env_args nil w) (env_args nil u0)) by (etransitivity; [ exact Hwu | exact HuB0 ]).
      assert (Lw : List.length w = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw), List.length_map; exact HUl).
      assert (LuB : List.length uB = ind_nu D) by (rewrite (eval_exps_length _ _ _ HuB); exact HUl).
      (** The recursive argument's type, weakened. *)
      rewrite HIeq in Ea1.
      set (Tc := apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps)) in *.
      set (Te := Tc[sb_qn (List.length gs1) (sb_qn (ind_nn D) (sb_of_list Id Us))]) in *.
      set (L := tele_sub (cargs_ctx_aux p D (true :: cargs_pat gs1) gs2) (sb_qn (S (List.length gs1)) (sb_qn (ind_nn D) (sb_of_list Id Us)))).
      assert (LL : List.length L = List.length gs2) by (unfold L; rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity).
      assert (HCeq : E ++ cinst Γ p D Us gs = (E ++ L ++ ce_ass Te :: nil) ++ cinst Γ p D Us gs1).
      { replace (cinst Γ p D Us gs) with (cinst Γ p D Us (gs1 ++ ca_rec Ps :: gs2)) by (rewrite <- Heq; reflexivity).
        rewrite cinst_split, <- !List.app_assoc; reflexivity. }
      rewrite HCeq in HCtx, HRS.
      assert (HTe : exists j2 : nat, cinst Γ p D Us gs1 ⊨ Te : Typeω@j2).
      { pose proof HCtx as H; rewrite <- !List.app_assoc in H; cbn [List.app] in H.
        rewrite List.app_assoc in H; apply sem_ctx_app_r in H; exact (sem_ctx_ass_inv H). }
      destruct HTe as [j2 HTe].
      assert (EEp : Ep = env_args (env_args B (Xb ++ fab)) (vb :: aft ++ ihp)) by (unfold Ep; rewrite (List.app_assoc Xb fab), env_args_app; reflexivity).
      rewrite EEp in HE.
      destruct (wk_typ_link (E ++ L ++ ce_ass Te :: nil) (cinst Γ p D Us gs1) Te j2 RS (env_args B (Xb ++ fab)) (vb :: aft ++ ihp)
                  HCtx HTe HRS HE ltac:(rewrite !List.length_app, LE, LL; cbn; rewrite List.length_app; lia))
        as (a2 & b2 & Ea2 & Eb2 & Hab2).
      assert (a2 = a1) as ->.
      { eapply functional_eval_exp; [ exact Ea2 |].
        rewrite EEp in Ea1.
        replace (Te[wk_shiftn (List.length (E ++ L ++ ce_ass Te :: nil))]ʷ) with (Te[wk_shift]ʷ[wk_shiftn (List.length E + List.length gs2)]ʷ);
          [ exact Ea1 |].
        rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite !List.length_app, LL; cbn; lia. }
      (** The instance of the declaration's type. *)
      set (Pre := cargs_ctx p D gs1 ++ ind_nparams D).
      assert (HKa : tele_ass (Pre ++ ind_uparams D)).
      { unfold Pre; rewrite <- List.app_assoc, <- params_split.
        apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]. }
      assert (HK : ⊨ Pre ++ ind_uparams D)
        by (unfold Pre; rewrite <- List.app_assoc, <- params_split; exact (cargs_prefix_sem D p gs HΨ gs1 _ Heq)).
      destruct (sem_ctx_per_ctx_env HK) as [RK HRK].
      assert (HKe : exists j3 : nat, Pre ++ ind_uparams D ⊨ Tc : Typeω@j3).
      { pose proof (cargs_prefix_sem D p gs HΨ (gs1 ++ ca_rec Ps :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as H.
        rewrite cargs_ctx_snoc in H; cbn [cargs_ctx_aux List.app] in H.
        apply sem_ctx_ass_inv in H.
        unfold Pre; rewrite <- List.app_assoc, <- params_split; exact H. }
      destruct HKe as [j3 HKe].
      pose proof (cinst_eq Γ p D Us gs1) as Hci.
      destruct (sem_ctx_per_ctx_env (sem_ctx_app_r _ _ HCtx)) as [RS1 HRS1].
      assert (HE1 : RS1 (env_args B (Xb ++ fab)) (env_args B (Xb ++ fab)))
        by (eapply (wk_env_rel _ _ _ _ _ _ _ _ HRS HRS1 HE); rewrite !List.length_app, LE, LL; cbn; rewrite List.length_app; lia).
      rewrite Hci in HRS1.
      assert (Lp : List.length (Xb ++ fab) = List.length Pre)
        by (unfold Pre; rewrite !List.length_app, length_cargs_ctx, length_nparams; lia).
      pose proof (closed_pre_base Pre RK HKa HK HRK B uB (Xb ++ fab) HuB0 LuB Hgp Lp) as HF.
      destruct (closed_typ_inst Pre (ind_uparams D) Γ Tc j3 τU RΓ RK RS1 B (Xb ++ fab) (env_args B uB) (env_args nil (u0 ++ Xb ++ fab))
                  HKa HK Ua Usem HΓ HRΓ HRK HRS1 HKe (gsub_valid gsub_U) HE1 Lp
                  (eval_sb_of_list _ _ _ _ _ (eval_sub_id B) HuB) HF)
        as (a3 & b3 & Ea3 & Eb3 & Hab3).
      assert (a3 = b2) as ->.
      { eapply functional_eval_exp; [ exact Ea3 |].
        replace (Tc[sb_qn (List.length Pre) τU]) with Te; [ exact Eb2 |].
        unfold Te, Pre; apply exp_sub_sb_eq.
        rewrite List.length_app, length_cargs_ctx, length_nparams; intros x; exact (sb_qn_add (List.length gs1) (ind_nn D) τU x). }
      (** The recursive argument's declared type. *)
      assert (Hpre : forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
                 R (env_args nil (u0 ++ Xb ++ fab)) (env_args nil (u0 ++ Xb ++ fab))).
      { intros R HR.
        assert (HK' : ⊨ cargs_ctx p D gs1 ++ ind_params D) by exact (cargs_prefix_sem D p gs HΨ gs1 _ Heq).
        apply (gargs_env_rel _ _ _ _ _ _ HR HK'); [ rewrite !List.length_app, length_cargs_ctx; pose proof Hle; unfold ind_nn, ind_np in *; lia |].
        rewrite params_split, List.app_assoc, List.rev_app_distr.
        apply per_gargs_app_intro; [ rewrite List.length_rev, length_ind_uparams by exact Hle; exact Hu0l | exact Hu0g | exact Hgp ]. }
      assert (HKl : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (tarp_refl_r p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI ns Xb c gs _ _ _ Hns Hcon HKl Hpk) as Hpkb.
      destruct Hab3 as [R3 HR3].
      destruct (per_univ_elem_sym _ _ _ _ HR3) as [HR3s _].
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR3s HR3) as (Rb & HRb & _).
      destruct (rec_entry_char c gs Hcon gs1 Ps gs2 Heq u0 Xb fab a0 Hu0l LXb Lfab Hu0g Ha0 (trefl_r _ _ Hns) Hpkb Hpre _ _ _ _ Eb3 HRb)
        as (bsb & Y & Ebsb & _ & Htf & -> & _).
      (** The chain of types. *)
      destruct Hab1 as [R1 HR1]; destruct Hab2 as [R2 HR2].
      destruct (per_univ_elem_sym _ _ _ _ HR1) as [HR1s _].
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR1s HR2) as (R4 & HR4 & _).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR4 HR3) as (Rch & HRch & _).
      pose proof (ind_univ_inv _ _ _ _ _ _ _ _ HRch Lw Hu0l Hl) as Hqy.
      pose proof (nr_change_u0 w (U_gargs _ _ (symmetry Hw0) Hu0l Lw) _ _ Hqy) as Hqy'.
      destruct (proj2 (proj2 Had) _ _ _ _ _ _ _ _ _ Hns Hcon Heq Hpk) as (b1' & b2' & Eb1'' & Eb2'' & Hbb).
      pose proof (functional_eval_exps' _ _ _ _ Eb1'' Ebs) as ->.
      pose proof (functional_eval_exps' _ _ _ _ Eb2'' Ebsb) as ->.
      exists Xq; split; [ exact HXq |].
      exact (ttrans _ _ _ Hbb (ttrans _ _ _ Htf (tsym _ _ Hqy'))).
    Qed.

    (** The arguments, at the closed telescope. *)
    Lemma closed_args_gargs : forall ns X X' vs vs',
        tele_full nr T ns X -> tele_full nr T ns X' ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs' ->
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

    Lemma ih_entry_eq : forall gs1 Ps,
        ihs_ctx_aux D A Us (List.length gs) nil 0 (gs1 ++ ca_rec Ps :: nil)
        = ce_ass A[sb_of_list (sb_of_wk (wk_shiftn (List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) + List.length gs + ind_nn D)))
              (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                   [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1))]ʷ) (ptyp_ps Ps)
               ++ a_var (List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)]
          :: ihs_ctx_aux D A Us (List.length gs) nil 0 gs1.
    Proof. intros; rewrite ihs_ctx_aux_app, List.app_nil_r, length_ihs_ctx_aux; cbn [ihs_ctx_aux List.app Nat.add]; reflexivity. Qed.

    Lemma cv_ihs : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall ns X X' vs vs' ihs ihs',
        tele_full nr T ns X -> tele_full nr T ns X' ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs' ->
        ihs_rel Rel (env_args nil (u0 ++ ns)) gs vs vs' ihs ihs' ->
        per_gargs (List.rev (tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU)) B1 B2 (X ++ vs) (X' ++ vs') ->
        forall k, k <= List.length gs ->
        per_gargs (List.rev (ihs_ctx_aux D A Us (List.length gs) nil 0 (List.firstn k gs)))
          (env_args B1 (X ++ vs)) (env_args B2 (X' ++ vs'))
          (List.firstn (cargs_nrec (List.firstn k gs)) ihs) (List.firstn (cargs_nrec (List.firstn k gs)) ihs').
    Proof.
      intros B1 B2 HB1 HB2 * HX HX' Har Hia Hir Hci.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (us_rel B2 HB2) as (u2 & Hu2 & H20).
      destruct (us_rel C2 ltac:(symmetry; exact HC12)) as (uc2 & Huc2 & Hc20).
      destruct (us_rel C1 ltac:(etransitivity; [ exact HC12 | symmetry; exact HC12 ])) as (uc1 & Huc1 & Hc10).
      pose proof (functional_eval_exps' _ _ _ _ Huc1 HUC) as ->.
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li Li'].
      pose proof HX as HX0; rewrite tele_full_iff in HX0; destruct HX0 as (Ln & LX & _).
      pose proof HX' as HX0'; rewrite tele_full_iff in HX0'; destruct HX0' as (_ & LX' & _).
      unfold T in Ln, LX, LX'; rewrite List.length_rev, length_nparams in Ln, LX, LX'.
      destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
      pose proof (tnr_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI _ _ HX) as Hnn.
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
      - rewrite ih_entry_eq.
        replace (cargs_nrec gs1 + cargs_nrec (ca_rec Ps :: nil)) with (S (cargs_nrec gs1)) by (cbn; lia).
        set (gs2 := List.skipn (S k) gs) in *.
        destruct (ihs_rel_at _ _ _ _ _ _ _ Hir gs1 Ps gs2 Heq0) as (v & v' & ih & ih' & bs & Hv & Hv' & Hih & Hih' & Ebs & Hrih).
        destruct (ind_args_rel_at _ _ _ _ Hia gs1 Ps gs2 Heq0) as (x & x' & bs0 & Hx & Hx' & Ebs0 & Hrr).
        rewrite Hv in Hx; injection Hx as <-; rewrite Hv' in Hx'; injection Hx' as <-.
        pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->.
        rewrite (firstn_S_snoc _ _ _ Hih), (firstn_S_snoc _ _ _ Hih').
        cbn [List.rev].
        set (E := ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) in *.
        assert (LE : List.length E = cargs_nrec gs1) by apply length_ihs_ctx_aux.
        assert (Lnr : cargs_nrec gs1 <= cargs_nrec gs) by (rewrite Heq0, cargs_nrec_app; lia).
        set (ihp := List.firstn (cargs_nrec gs1) ihs) in *.
        set (ihp' := List.firstn (cargs_nrec gs1) ihs') in *.
        assert (Lihp : List.length ihp = cargs_nrec gs1) by (unfold ihp; rewrite List.length_firstn; lia).
        assert (Lihp' : List.length ihp' = cargs_nrec gs1) by (unfold ihp'; rewrite List.length_firstn; lia).
        (** The context and the environments of the entry. *)
        pose proof (ihs_pre_sem gs1 _ Heq0) as HCtx; fold E in HCtx.
        pose proof (ihs_pre_sem (gs1 ++ ca_rec Ps :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq0)) as HCtx2.
        rewrite ih_entry_eq in HCtx2; fold E in HCtx2; cbn [List.app] in HCtx2.
        destruct (sem_ctx_ass_inv HCtx2) as [j HT].
        destruct (sem_ctx_per_ctx_env HCtx) as [RS HRS].
        assert (HΔeq : E ++ cinst Γ p D Us gs = (E ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU) ++ Γ)
          by (rewrite cinst_eq, List.app_assoc; reflexivity).
        assert (HEp : RS (env_args B1 ((X ++ vs) ++ ihp)) (env_args B2 ((X' ++ vs') ++ ihp'))).
        { pose proof HRS as HRS'; rewrite HΔeq in HRS'; pose proof HCtx as HCtx'; rewrite HΔeq in HCtx'.
          eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS' HCtx' HB12);
            [ rewrite !List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams; lia |].
          rewrite List.rev_app_distr; apply per_gargs_app_intro;
            [ rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_nparams; lia | exact Hci | exact IHk ]. }
        destruct (rel_exp_of_typ_inversion_simple_at HRS HT _ _ HEp) as (t & t' & Et & Et' & [R HR]).
        destruct (per_univ_elem_to_nat _ _ _ _ HR) as [n Hn].
        rewrite env_args_app in Et, Et'.
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R); [ rewrite List.length_rev; lia | exact IHk | exact (mk_rel_mod_eval _ _ Et Et' Hn) |].
        (** The recursive results' relation. *)
        assert (Hsplit : forall (Y ws : list domain) w, List.nth_error ws (List.length gs1) = Some w -> List.length ws = List.length gs ->
                   (Y ++ ws) ++ ihp = Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihp /\
                   (Y ++ ws) ++ ihp' = Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihp').
        { intros * Hw Lw; rewrite Lk in Hw.
          pose proof (List.firstn_skipn k ws) as Hfs; rewrite (skipn_nth_cons' _ _ _ Hw) in Hfs.
          split; rewrite <- Hfs at 1; rewrite <- !List.app_assoc; reflexivity. }
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
        pose proof (tar_pre_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI ns c gs Hnn Hcon K _ _ HKl Hpk) as Hpk1.
        assert (Hcl : forall (ts : ctx), ts = List.rev (cargs_ctx p D gs1 ++ ind_nparams D) ->
                   ⊨ List.rev ts ++ ind_uparams D /\ tele_ass ts).
        { intros ts ->; rewrite List.rev_involutive, <- List.app_assoc, <- params_split; split;
            [ exact (cargs_prefix_sem D p gs HΨ gs1 _ Heq0)
            | apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ] ]. }
        destruct (Hcl _ eq_refl) as [Hcl1 Hcl2].
        assert (HU00 : RU (env_args nil u0) (env_args nil u0)) by (etransitivity; [ symmetry; exact Hc10 | exact Hc10 ]).
        pose proof (closed_args_gargs _ _ _ _ _ HX HX' Har Hia k ltac:(lia)) as Hcg; fold gs1 in Hcg.
        pose proof (per_gargs_refl_l _ _ _ HRU Hcl1 Hcl2 _ _ _ _ HU00 Hcg) as Hgp1.
        assert (Lcx : List.length (X ++ List.firstn k vs) = List.length (List.rev (cargs_ctx p D gs1 ++ ind_nparams D)))
          by (rewrite List.length_rev, !List.length_app, List.length_firstn, length_cargs_ctx, length_nparams; lia).
        pose proof (per_gargs_refl_r _ _ _ HRU Hcl1 Hcl2 _ _ _ _ HU00 Lcx Hcg) as Hgp2.
        assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
        destruct (Hsplit X vs v Hv Lv) as [Hs1 _]; destruct (Hsplit X' vs' v' Hv' Lv') as [_ Hs2].
        assert (HE1 : RS (env_args B1 (X ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp))
                         (env_args B1 (X ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp)))
          by (rewrite <- Hs1; etransitivity; [ exact HEp | symmetry; exact HEp ]).
        assert (HE2 : RS (env_args B2 (X' ++ List.firstn k vs' ++ v' :: List.skipn (S k) vs' ++ ihp'))
                         (env_args B2 (X' ++ List.firstn k vs' ++ v' :: List.skipn (S k) vs' ++ ihp')))
          by (rewrite <- Hs2; etransitivity; [ symmetry; exact HEp | exact HEp ]).
        rewrite <- env_args_app, <- List.app_assoc, Lk in Ebs.
        destruct (ih_bridge gs1 Ps gs2 Heq0 B1 HB1 ns X (List.firstn k vs) (List.firstn k vs) v (List.skipn (S k) vs) ihp bs RS
                    HX (Lf _ Lv) (Lf _ Lv) (Ls _ Lv) Lihp Hpk1 Hgp1 Ebs HRS HE1) as (Xq1 & HXq1 & _).
        destruct (ih_bridge gs1 Ps gs2 Heq0 B2 HB2 ns X' (List.firstn k vs) (List.firstn k vs') v' (List.skipn (S k) vs') ihp' bs RS
                    HX' (Lf _ Lv) (Lf _ Lv') (Ls _ Lv') Lihp' Hpk Hgp2 Ebs HRS HE2) as (Xq2 & HXq2 & Hbr2).
        fold E in HXq1, HXq2.
        (** The values of the substitution. *)
        pose proof (gsub_ih _ _ _ _ _ _ Hcon Heq0 HCtx) as Hgτ; fold E in Hgτ.
        set (m := List.length E + List.length gs + ind_nn D) in *.
        set (idx := List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) in *.
        assert (Lcp : List.length (cargs_pat gs1) = k) by (rewrite length_cargs_pat; exact Lk).
        assert (Hτev : forall B0 Y ws w ihq Xq, List.length Y = ind_nn D -> List.length ws = List.length gs ->
                   List.nth_error ws k = Some w -> List.length ihq = cargs_nrec gs1 ->
                   ⟦ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                  [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) Ps ⟧*
                     gc_deps ⍮ gc_stack ⍮ env_args B0 (Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq) ↘ Xq ->
                   ⟦ sb_of_list (sb_of_wk (wk_shiftn m))
                       (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                  [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) Ps ++ a_var idx :: nil) ⟧s
                     env_args B0 ((Y ++ ws) ++ ihq) ↘ env_args B0 (Xq ++ w :: nil)).
        { intros * LY Lws Hw Lq HXq.
          assert (Hws : (Y ++ ws) ++ ihq = Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq).
          { rewrite <- (List.firstn_skipn k ws) at 1; rewrite (skipn_nth_cons' _ _ _ Hw), <- !List.app_assoc; reflexivity. }
          rewrite Hws.
          assert (Lall : List.length (Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq) = m)
            by (unfold m; rewrite <- Hws, !List.length_app; lia).
          apply eval_sb_of_list.
          - pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn m) (env_args B0 (Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq))
                          (wk_mono_shiftn _)) as H.
            assert (Hw' : ⟪wk_shiftn m⟫ (env_args B0 (Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq)) = B0)
              by (rewrite <- Lall; apply eval_wk_shiftn_args).
            rewrite Hw' in H; exact H.
          - apply eval_exps_app; [ exact HXq |].
            econstructor; [| constructor ].
            pose proof (eval_var_args B0 (Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq) idx ltac:(rewrite Lall; unfold idx, m; lia)) as H.
            replace (List.length (Y ++ List.firstn k ws ++ w :: List.skipn (S k) ws ++ ihq) - 1 - idx)
              with (List.length Y + List.length (List.firstn k ws)) in H
              by (rewrite Lall; unfold idx, m; rewrite List.length_firstn; lia).
            rewrite nth_mid in H; exact H. }
        pose proof (Hτev B1 X vs v ihp Xq1 LX Lv ltac:(rewrite <- Lk; exact Hv) Lihp HXq1) as Hev1.
        pose proof (Hτev B2 X' vs' v' ihp' Xq2 LX' Lv' ltac:(rewrite <- Lk; exact Hv') Lihp' HXq2) as Hev2.
        pose proof (per_head_iff Et Et' HR) as ER1.
        pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HAv HRS (gsub_valid Hgτ) HEp Hev1 Hev2) as ER2.
        (** The chain to the family. *)
        pose proof (rel_sub_under_ctx_at' (gsub_valid Hgτ) HRS HRM _ _ _ _ HEp Hev1 Hev2) as L1.
        pose proof (proj1 (ind_rel_sym_all p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI Had) _ _ _ Hrr) as Hrr'.
        pose proof (ind_rel_mv p D u0 nr ar Hl (decl_closed_params D Hc) HnP HnI HaP HaI Had Hle _ _ _ _ Hrr' Hbr2) as Hrq.
        pose proof (cv_mctx B2 C1 u2 u0 HB2 Hu2 HUC H20 HU00 RM HRM Xq2 bs v' v (tsym _ _ Hbr2) Hrq) as L2.
        pose proof (cv_mctx C1 C2 u0 uc2 HC12 HUC Huc2 HU00 Hc20 RM HRM bs bs v v'
                      (tnr_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI _ _ Hbr2) Hrr) as L3.
        assert (Ch : rel_chain RM (env_args B1 (Xq1 ++ v :: nil) :: env_args B2 (Xq2 ++ v' :: nil)
                                   :: env_args C1 (bs ++ v :: nil) :: env_args C2 (bs ++ v' :: nil) :: nil)).
        { apply rel_chain_cons; [ exact L1 |]. apply rel_chain_cons; [ exact L2 |]. apply rel_chain_of_pair; exact L3. }
        pose proof (per_head_of_typ_resp HRM HAv _ _ _ _ Ch) as ER3.
        replace (env_args B1 ((X ++ vs) ++ ihp)) with (env_args (env_args B1 (X ++ vs)) ihp) in ER2 by (symmetry; apply env_args_app).
        replace (env_args B2 ((X' ++ vs') ++ ihp')) with (env_args (env_args B2 (X' ++ vs')) ihp') in ER2 by (symmetry; apply env_args_app).
        apply (proj2 (ER1 ih ih')), (proj2 (ER2 ih ih')), (proj2 (ER3 ih ih')); exact Hrih.
    Qed.

    Lemma cv_bctx : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall ns X X' vs vs' ihs ihs',
        tele_full nr T ns X -> tele_full nr T ns X' ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
        ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs' ->
        ihs_rel Rel (env_args nil (u0 ++ ns)) gs vs vs' ihs ihs' ->
        forall RB, EF elim_bctx p D gs A Us ++ Γ ≈ elim_bctx p D gs A Us ++ Γ ∈ per_ctx_env ↘ RB ->
        RB (env_args B1 (X ++ vs ++ ihs)) (env_args B2 (X' ++ vs' ++ ihs')).
    Proof.
      intros B1 B2 HB1 HB2 * HX HX' Har Hia Hir RB HRB.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li Li'].
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
        ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs' ->
        ihs_rel Rel (env_args nil (u0 ++ ns)) gs vs vs' ihs ihs' ->
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
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li Li'].
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
      assert (Hm1 : ind_rel p D u0 nr ar ns (d_con p c (w1 ++ X ++ vs)) (d_con p c (w2 ++ X' ++ vs'))).
      { rewrite !List.app_assoc; econstructor; [ exact Hnn | exact Hcon | apply Lnp; assumption | apply Lnp; assumption
          | rewrite skipn_app_exact by exact Lw1; exact Hs | rewrite skipn_app_exact by exact Lw2; exact Hs' | exact Har | exact Hia ]. }
      assert (Hm : ind_rel p D u0 nr ar ns (d_con p c (bs ++ vs)) (d_con p c (bs' ++ vs'))) by (econstructor; eassumption).
      assert (HmL2 : ind_rel p D u0 nr ar ns (d_con p c (bs ++ vs)) (d_con p c (w2 ++ X' ++ vs'))).
      { rewrite (List.app_assoc w2); econstructor; [ exact Hnn | exact Hcon | exact Hb | apply Lnp; assumption
          | exact Hs | rewrite skipn_app_exact by exact Lw2; exact Hs' | exact Har | exact Hia ]. }
      pose proof (proj1 (ind_rel_sym_all p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI Had)) as isym.
      pose proof (cv_mctx B2 C1 u2 u0 HB2 Hu2 HUC H20 HU00 RM HRM X' ns _ _ (tsym _ _ Hs')
                    (ind_rel_mv p D u0 nr ar Hl (decl_closed_params D Hc) HnP HnI HaP HaI Had Hle _ _ _ _ (isym _ _ _ Hm1) Hs')) as L2.
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

    (** The type of the entry of a recursive result in the branch's context,
        at values related to themselves, against the motive at the
        recursive argument and its parameters. *)
    Lemma ih_entry_link : forall ns vs ihs,
        tele_full nr T ns ns ->
        tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs) ->
        ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs ->
        ihs_rel Rel (env_args nil (u0 ++ ns)) gs vs vs ihs ihs ->
        forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
        forall a, ⟦ A[sb_of_list (sb_of_wk (wk_shiftn (List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) + List.length gs + ind_nn D)))
                     (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                  [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1))]ʷ) (ptyp_ps Ps)
                      ++ a_var (List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)] ⟧
              env_args C1 ((ns ++ vs) ++ List.firstn (cargs_nrec gs1) ihs) ↘ a ->
        exists v bs t (j : nat), List.nth_error vs (List.length gs1) = Some v /\
          ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) ↘ bs /\
          ⟦ A ⟧ env_args C1 (bs ++ v :: nil) ↘ t /\ Dom a ≈ t ∈ per_univ j.
    Proof.
      intros ns vs ihs Hns Har Hia Hir gs1 Ps gs2 Heq0 a Ea.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
      destruct (us_rel C1 HC11) as (uc1 & Huc1 & Hc10).
      pose proof (functional_eval_exps' _ _ _ _ Huc1 HUC) as ->.
      assert (HU00 : RU (env_args nil u0) (env_args nil u0)) by (etransitivity; [ symmetry; exact Hc10 | exact Hc10 ]).
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
      destruct (ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li _].
      pose proof Hns as HX0; rewrite tele_full_iff in HX0; destruct HX0 as (Ln & LX & _).
      unfold T in Ln, LX; rewrite List.length_rev, length_nparams in Ln, LX.
      destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
      set (k := List.length gs1).
      assert (Hk : k < List.length gs) by (unfold k; rewrite Heq0, List.length_app; cbn; lia).
      assert (Lk : List.length (List.firstn k gs) = k) by (rewrite List.length_firstn; lia).
      assert (Hfk : List.firstn k gs = gs1) by (unfold k; rewrite Heq0; apply firstn_app_exact; reflexivity).
      (** The instance of the arguments' telescope, and the recursive results before. *)
      pose proof (closed_args_gargs _ _ _ _ _ Hns Hns Har Hia (List.length gs) (le_n _)) as Hcg.
      rewrite List.firstn_all, !List.firstn_all2 in Hcg by lia.
      assert (HKa : tele_ass ((cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D))
        by (rewrite <- List.app_assoc, <- params_split; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_params, Hc ]).
      assert (HK : ⊨ (cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D) by (rewrite <- List.app_assoc, <- params_split; exact HΨ).
      pose proof (ihs_pre_sem nil gs eq_refl) as HC0; cbn [ihs_ctx_aux List.app] in HC0; rewrite cinst_eq in HC0.
      pose proof (cv_gen _ HKa HK HC0 C1 C1 u0 u0 HC11 HUC HUC Hc10 Hc10 _ _ Hcg
                    ltac:(rewrite !List.length_app, length_cargs_ctx, length_nparams; lia)) as Hci.
      pose proof (cv_ihs C1 C1 HC11 HC11 _ _ _ _ _ _ _ Hns Hns Har Hia Hir Hci k ltac:(lia)) as IHk.
      rewrite Hfk in IHk.
      destruct (ihs_rel_at _ _ _ _ _ _ _ Hir gs1 Ps gs2 Heq0) as (v & v' & ih & ih' & bs & Hv & Hv' & Hih & Hih' & Ebs & Hrih).
      destruct (ind_args_rel_at _ _ _ _ Hia gs1 Ps gs2 Heq0) as (x & x' & bs0 & Hx & Hx' & Ebs0 & Hrr).
      rewrite Hv in Hx; injection Hx as <-; rewrite Hv in Hv'; injection Hv' as <-; rewrite Hv in Hx'; injection Hx' as <-.
      pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->.
      fold k in Hv, Ebs.
      set (E := ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) in *.
      assert (LE : List.length E = cargs_nrec gs1) by apply length_ihs_ctx_aux.
      assert (Lnr : cargs_nrec gs1 <= cargs_nrec gs) by (rewrite Heq0, cargs_nrec_app; lia).
      set (ihp := List.firstn (cargs_nrec gs1) ihs) in *.
      assert (Lihp : List.length ihp = cargs_nrec gs1) by (unfold ihp; rewrite List.length_firstn; lia).
      pose proof (ihs_pre_sem gs1 _ Heq0) as HCtx; fold E in HCtx.
      destruct (sem_ctx_per_ctx_env HCtx) as [RS HRS].
      assert (HΔeq : E ++ cinst Γ p D Us gs = (E ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU) ++ Γ)
        by (rewrite cinst_eq, List.app_assoc; reflexivity).
      assert (HEp : RS (env_args C1 ((ns ++ vs) ++ ihp)) (env_args C1 ((ns ++ vs) ++ ihp))).
      { pose proof HRS as HRS'; rewrite HΔeq in HRS'; pose proof HCtx as HCtx'; rewrite HΔeq in HCtx'.
        eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS' HCtx' HC11);
          [ rewrite !List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams; lia |].
        rewrite List.rev_app_distr; apply per_gargs_app_intro;
          [ rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_nparams; lia | exact Hci | exact IHk ]. }
      (** The bridge to the arguments' parameters. *)
      assert (Hsplit : (ns ++ vs) ++ ihp = ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp).
      { pose proof (List.firstn_skipn k vs) as Hfs; rewrite (skipn_nth_cons' _ _ _ Hv) in Hfs.
        rewrite <- Hfs at 1; rewrite <- !List.app_assoc; reflexivity. }
      set (K := List.length (cargs_nonrec gs1)).
      assert (Hnv : List.firstn K (nonrec_vals gs vs) = nonrec_vals gs1 (List.firstn k vs)).
      { rewrite <- (List.firstn_skipn k vs) at 1.
        rewrite Heq0 at 1.
        rewrite nonrec_vals_app by (rewrite List.length_firstn; unfold k; lia).
        rewrite firstn_app_exact by (apply length_nonrec_vals; rewrite List.length_firstn; unfold k; lia); reflexivity. }
      assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq0, cargs_nonrec_app, List.length_app; lia).
      assert (Hpk : tele_pre (ar ns c) K (nonrec_vals gs1 (List.firstn k vs)) (nonrec_vals gs1 (List.firstn k vs))).
      { rewrite <- Hnv; apply tele_pre_of_full with (T := cargs_nonrec gs); [ exact Har | exact HKl ]. }
      assert (Hcl : forall (ts : ctx), ts = List.rev (cargs_ctx p D gs1 ++ ind_nparams D) ->
                 ⊨ List.rev ts ++ ind_uparams D /\ tele_ass ts).
      { intros ts ->; rewrite List.rev_involutive, <- List.app_assoc, <- params_split; split;
          [ exact (cargs_prefix_sem D p gs HΨ gs1 _ Heq0)
          | apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ] ]. }
      destruct (Hcl _ eq_refl) as [Hcl1 Hcl2].
      pose proof (closed_args_gargs _ _ _ _ _ Hns Hns Har Hia k ltac:(lia)) as Hcgk; rewrite Hfk in Hcgk.
      assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
      assert (HE1 : RS (env_args C1 (ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp))
                       (env_args C1 (ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp)))
        by (rewrite <- Hsplit; exact HEp).
      rewrite <- env_args_app, <- List.app_assoc in Ebs.
      destruct (ih_bridge gs1 Ps gs2 Heq0 C1 HC11 ns ns (List.firstn k vs) (List.firstn k vs) v (List.skipn (S k) vs) ihp bs RS
                  Hns ltac:(rewrite List.length_firstn; unfold k; lia) ltac:(rewrite List.length_firstn; unfold k; lia)
                  ltac:(rewrite List.length_skipn; pose proof Lv as Lv0; rewrite Heq0, List.length_app in Lv0; cbn in Lv0; unfold k; lia)
                  Lihp Hpk Hcgk Ebs HRS HE1) as (Xq & HXq & Hbr).
      fold E in HXq.
      (** The values of the substitution. *)
      pose proof (gsub_ih _ _ _ _ _ _ Hcon Heq0 HCtx) as Hgτ; fold E in Hgτ.
      set (m := List.length E + List.length gs + ind_nn D) in *.
      set (idx := List.length E + List.length gs - 1 - List.length (cargs_pat gs1)) in *.
      assert (Lcp : List.length (cargs_pat gs1) = k) by (rewrite length_cargs_pat; reflexivity).
      assert (Lall : List.length (ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp) = m)
        by (unfold m; rewrite <- Hsplit, !List.length_app; lia).
      assert (Hev : ⟦ sb_of_list (sb_of_wk (wk_shiftn m))
                       (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                  [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length E)]ʷ) Ps ++ a_var idx :: nil) ⟧s
                     env_args C1 ((ns ++ vs) ++ ihp) ↘ env_args C1 (Xq ++ v :: nil)).
      { rewrite Hsplit.
        apply eval_sb_of_list.
        - pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn m) (env_args C1 (ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp))
                        (wk_mono_shiftn _)) as H.
          assert (Hw' : ⟪wk_shiftn m⟫ (env_args C1 (ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp)) = C1)
            by (rewrite <- Lall; apply eval_wk_shiftn_args).
          rewrite Hw' in H; exact H.
        - apply eval_exps_app; [ exact HXq |].
          econstructor; [| constructor ].
          pose proof (eval_var_args C1 (ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp) idx ltac:(rewrite Lall; unfold idx, m; lia)) as H.
          replace (List.length (ns ++ List.firstn k vs ++ v :: List.skipn (S k) vs ++ ihp) - 1 - idx)
            with (List.length ns + List.length (List.firstn k vs)) in H
            by (rewrite Lall; unfold idx, m; rewrite List.length_firstn; lia).
          rewrite nth_mid in H; exact H. }
      destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HRS (gsub_valid Hgτ) HEp Hev) as (a' & b & Ea' & Eb & Hab).
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (cv_mctx C1 C1 u0 u0 HC11 HUC HUC HU00 HU00 RM HRM bs Xq v v Hbr Hrr) as HEm.
      destruct (rel_exp_of_typ_inversion_simple_at HRM HAv _ _ HEm) as (t & b' & Et & Eb' & Htb).
      assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
      exists v, bs, t, iA; split; [ exact Hv | split; [ exact Ebs | split; [ exact Et |] ] ].
      eapply per_univ_trans'; [ exact Hab | apply per_univ_sym'; exact Htb ].
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
    Let isym := proj1 (ind_rel_sym_all p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI Had).
    Let itrans := proj1 (ind_rel_trans_all p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI Had).
    Let imv := ind_rel_mv p D u0 nr ar Hl (decl_closed_params D Hc) HnP HnI HaP HaI Had Hle.
    Let trefl_l := tnr_refl_l p D u0 nr ar (decl_closed_params D Hc) HnP HnI HaP HaI.

    Lemma us_rel' : forall B, RΓ B C1 -> exists u, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u /\ RU (env_args nil u) (env_args nil u0).
    Proof.
      intros B HB1; destruct (us_vals B C1 HB1) as (u & u' & Hu & Hu' & H).
      pose proof (functional_eval_exps' _ _ _ _ Hu' HUC) as ->; eauto.
    Qed.

    (** [cv_mctx] at any two environments of the class of [C1]. *)
    Lemma mctx_at : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall RM, EF elim_mctx p D Us ++ Γ ≈ elim_mctx p D Us ++ Γ ∈ per_ctx_env ↘ RM ->
        forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar ns m m' ->
          RM (env_args B1 (ns ++ m :: nil)) (env_args B2 (ns' ++ m' :: nil)).
    Proof.
      intros * HB1 HB2 RM HRM * Hns Hm.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      destruct (us_rel' B1 HB1) as (u1 & Hu1 & H10); destruct (us_rel' B2 HB2) as (u2 & Hu2 & H20).
      exact (cv_mctx B1 B2 u1 u2 ltac:(etransitivity; [ exact HB1 | symmetry; exact HB2 ]) Hu1 Hu2 H10 H20 RM HRM _ _ _ _ Hns Hm).
    Qed.

    Lemma ind_rel_refl_r : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar ns m m' -> ind_rel p D u0 nr ar ns' m' m'.
    Proof. intros * Hns Hm; apply imv with (ns := ns); [ exact (itrans _ _ _ (isym _ _ _ Hm) _ Hm) | exact Hns ]. Qed.

    Lemma ind_rel_refl_l : forall ns m m', ind_rel p D u0 nr ar ns m m' -> ind_rel p D u0 nr ar ns m m.
    Proof. intros * Hm; exact (itrans _ _ _ Hm _ (isym _ _ _ Hm)). Qed.

    Lemma mot_mid : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar ns m m' ->
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

    Lemma mot_out : forall Γ' RΓ' σ0 ρ0 ρ0σ0 A0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨s σ0 ≈ σ0 : Γ ->
        RΓ' ρ0 ρ0 -> ⟦ σ0 ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
        elim_mctx p D Us ++ Γ ⊨ A ≈ A0 : Typeω@iA ->
        forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar ns m m' ->
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
        ind_rel p D u0 nr ar ns1 m1 m2 -> ind_rel p D u0 nr ar ns2 m2 m3 -> ind_rel p D u0 nr ar ns3 m3 m4 ->
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

    Lemma Rel_PER : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D u0 nr ar ns m m' -> PER (Rel ns m ns' m').
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
          ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs' ->
          ihs_rel Rel (env_args nil (u0 ++ ns)) gs vs vs' ihs ihs' ->
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

    Lemma br_out : forall Γ' RΓ' σ0 ρ0 ρ0σ0 Bs0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨s σ0 ≈ σ0 : Γ ->
        RΓ' ρ0 ρ0 -> ⟦ σ0 ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
        (forall c gs n B0, ind_con D c = Some gs -> brs_lookup Bs0 c = Some (n, B0) ->
           n = (ind_nn D + List.length gs + cargs_nrec gs)%nat /\ elim_bctx p D gs A Us ++ Γ ⊨ B0 : elim_bty p D c gs A Us) ->
        forall c gs n Ba Bb, ind_con D c = Some gs -> brs_lookup (brs_sub Bs0 σ0) c = Some (n, Ba) -> brs_lookup Bs0 c = Some (n, Bb) ->
        forall ns bs bs' vs vs' ihs ihs',
          tele_full nr T ns ns -> List.length bs = ind_np D -> List.length bs' = ind_np D ->
          tele_full nr T ns (List.skipn (ind_nu D) bs) -> tele_full nr T ns (List.skipn (ind_nu D) bs') ->
          tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
          ind_args_rel p D u0 nr ar (env_args nil (u0 ++ ns)) gs vs vs' ->
          ihs_rel Rel (env_args nil (u0 ++ ns)) gs vs vs' ihs ihs' ->
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
      destruct (ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
      destruct (ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li _].
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
        forall Γ' RΓ' σ σ' ρ ρ', EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨s σ ≈ σ' : Γ -> RΓ' ρ ρ' ->
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
      pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd).
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
      assert (ERM : RMe <~> ind_rel p D u0 nr ar ns2) by (eapply per_univ_elem_right_irrel; [ exact Ht23 | exact HIR ]).
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
      pose proof (per_ind_elim_all p D u0 nr ar Hl (decl_closed_params D Hc) HnP HnI HaP HaI Had Hle iA (S (ind_nn D))
                    ρ C1 (A[sb_qn (S (ind_nn D)) σ]) A (brs_sub Bs σ) Bs Rel eq_refl Hnd (brs_names_sub _ _ _ HBn) HBn
                    (Hsub _ _ Hnb) Hnb
                    (mot_out Γ' RΓ' σ ρ C1 A HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HC11 HAl)
                    (br_out Γ' RΓ' σ ρ C1 Bs HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HC11 Hlk1)) as [PE1 _].
      pose proof (per_ind_elim_all p D u0 nr ar Hl (decl_closed_params D Hc) HnP HnI HaP HaI Had Hle iA (S (ind_nn D))
                    C1 C2 A A' Bs Bs' Rel eq_refl Hnd HBn HBn' Hnb HarBs mot_mid (br_mid Bs Bs' HBB)) as [PE2 _].
      pose proof (per_ind_elim_all p D u0 nr ar Hl (decl_closed_params D Hc) HnP HnI HaP HaI Had Hle iA (S (ind_nn D))
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



(** ** [ι] *)

Lemma gsub_args : forall Γ p D Us Ns c gs As, decl_closed D -> ⊨ Γ -> ind_con D c = Some gs ->
    List.length Ns = ind_nn D ->
    ⊨ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ -> ⊨ cinst Γ p D Us gs ->
    (forall k N T, List.nth_error Ns k = Some N ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Γ ⊨ N : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T -> Γ ⊨ N : T) ->
    gsub Γ (sb_of_list Id (Ns ++ As)) (cinst Γ p D Us gs).
Proof.
  intros * Hc HΓ Hcon HNl HNt HC HNs HAl HAs.
  assert (HgN : gsub Γ (sb_of_list Id Ns) (tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ)).
  { apply gsub_of_list; [ constructor; exact HΓ | apply tele_ass_sub, decl_closed_nparams_ass, Hc | exact HNt
                        | rewrite length_ind_nparams_sub; exact HNl |].
    intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
    rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT by (intros x; cbn; apply sentry_sub_id).
    exact (HNs _ _ _ HN HT). }
  rewrite sb_of_list_app; unfold cinst in HC |- *.
  apply gsub_of_list; [ exact HgN | apply tele_ass_sub, cargs_ctx_aux_ass | exact HC
                      | rewrite length_tele_sub, length_cargs_ctx; exact HAl |].
  intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
  rewrite (tele_insts_sb_eq _ _ (sb_of_list Id (Us ++ Ns))) in HT; [ exact (HAs _ _ _ HN HT) |].
  rewrite <- HNl; etransitivity; [ apply sb_qn_of_list |].
  etransitivity; [ apply sb_of_list_cong; intros x; cbn; apply sentry_sub_id |].
  rewrite <- sb_of_list_app; reflexivity.
Qed.

Lemma eval_elim_ihs : forall nm A Bs gs As ρ avs ihs, ⟦ As ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ avs ->
    ⟦ihs avs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs -> List.length As = List.length gs ->
    ⟦ elim_ihs nm A Bs gs As ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs.
Proof.
  induction gs as [| [T | Ps] gs IH]; intros [| N As] * HAs Hih Hl; cbn in Hl; try discriminate;
    inversion HAs; subst; inversion Hih; subst; cbn [elim_ihs].
  - constructor.
  - eapply IH; [ eassumption | eassumption | lia ].
  - econstructor; [ econstructor; eassumption | eapply IH; [ eassumption | eassumption | lia ] ].
Qed.

Lemma params_valid_join : forall D Γ Us Ns, decl_closed D -> List.length Us = ind_nu D ->
    (forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T) ->
    (forall k N T, List.nth_error Ns k = Some N ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Γ ⊨ N : T) ->
    forall k P T, List.nth_error (Us ++ Ns) k = Some P -> List.nth_error (tele_insts (ind_params D) Id (Us ++ Ns)) k = Some T -> Γ ⊨ P : T.
Proof.
  intros * Hc HUl HUs HNs k P T HP HT.
  pose proof (decl_closed_nu D Hc) as Hle.
  rewrite params_split, tele_insts_app in HT by (try apply (decl_uparams_ass D Hc); rewrite HUl, length_ind_uparams by exact Hle; reflexivity).
  assert (Hl2 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
    by (rewrite length_tele_insts by apply (decl_uparams_ass D Hc); rewrite HUl, length_ind_uparams by exact Hle; lia).
  destruct (Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HP by lia; rewrite List.nth_error_app1 in HT by lia; exact (HUs _ _ _ HP HT).
  - rewrite List.nth_error_app2 in HP, HT by lia; rewrite HUl in HP; rewrite Hl2 in HT; exact (HNs _ _ _ HP HT).
Qed.

Lemma eval_elim_inv : forall nm A Bs M ρ r, ⟦ a_elim nm A Bs M ⟧ ρ ↘ r ->
    exists m, ⟦ M ⟧ ρ ↘ m /\ ⟦elim m under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma eval_elim_con_inv : forall ρ nm A Bs p c vs r, ⟦elim d_con p c vs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r ->
    exists D gs n B ihs, ind_lookup gc_deps gc_stack p = Some D /\ ind_con D c = Some gs /\ brs_lookup Bs c = Some (n, B) /\
      ⟦ihs List.skipn (ind_np D) vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs /\
      ⟦ B ⟧ env_args ρ (List.skipn (ind_nu D) (List.firstn (ind_np D) vs) ++ List.skipn (ind_np D) vs ++ ihs) ↘ r.
Proof. intros * H; inversion H; subst; do 5 eexists; repeat split; eassumption. Qed.

Lemma eval_apps_con' : forall D p, ind_lookup gc_deps gc_stack p = Some D ->
    forall c gs ys xs, ind_con D c = Some gs -> List.length xs + List.length ys <= ind_np D + List.length gs ->
    $*| d_con p c xs & ys | gc_deps ⍮ gc_stack ↘ d_con p c (xs ++ ys).
Proof.
  intros D p Hl c gs; induction ys as [| y ys IH]; intros xs Hcon Hlen; [ rewrite List.app_nil_r; constructor |].
  econstructor; [ eapply eval_app_con; [ exact Hl | exact Hcon | cbn in *; lia ] |].
  replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
  apply IH; [ exact Hcon | rewrite List.length_app; cbn in *; lia ].
Qed.

Section Iota.
  Variable (Γ : ctx) (p : qname) (D : ind_decl) (Us Ns As : list exp) (c : String.string) (gs : list carg)
    (nm : nat) (A : exp) (i : nat) (Bs : list (String.string * nat * exp)).
  Hypothesis (HD : sem_decl D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)) (Hdt : decl_typed gc_deps gc_stack D)
    (Hl : ind_lookup gc_deps gc_stack p = Some D) (HΓ : ⊨ Γ) (Hcon : ind_con D c = Some gs)
    (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T)
    (HNl : List.length Ns = ind_nn D) (HAl : List.length As = List.length gs)
    (Hnm : nm = S (ind_nn D)) (HA : elim_mctx p D Us ++ Γ ⊨ A : Typeω@i) (HM : ⊨ elim_mctx p D Us ++ Γ)
    (HBn : brs_names (ind_cons D) Bs)
    (HBc : forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A Us ++ Γ)
    (Hnb : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat)
    (HBv : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
             elim_bctx p D gs A Us ++ Γ ⊨ B : elim_bty p D c gs A Us).

  Lemma elim_valid_at : forall Q a, List.length Q = ind_nn D -> gsub Γ (sb_of_list Id (Q ++ a :: nil)) (elim_mctx p D Us ++ Γ) ->
      Γ ⊨ a : apps (a_ind p) (Us ++ Q) -> Γ ⊨ a_elim nm A Bs a : A[sb_of_list Id (Q ++ a :: nil)].
  Proof.
    intros * HQl Hg Ha.
    eapply (rel_exp_elim_at Γ p D Us Q a a nm A A i Bs Bs); try eassumption; [ reflexivity |].
    intros * Hk Hk' Hcon'; rewrite Hk in Hk'; injection Hk' as <-.
    exact (HBv _ _ _ _ Hcon' (List.nth_error_In _ _ Hk)).
  Qed.

  Lemma gsub_iota_ihs : forall rest gs1 E L, gs = gs1 ++ rest -> List.length E = cargs_nrec gs1 -> List.length L = List.length E ->
      ⊨ E ++ cinst Γ p D Us gs ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L)) (E ++ cinst Γ p D Us gs) ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L ++ elim_ihs nm A Bs rest (List.skipn (List.length gs1) As)))
        (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) (List.length E) rest ++ E ++ cinst Γ p D Us gs).
  Proof.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    induction rest as [| [B0 | Ps0] rest IH]; intros gs1 E L Heq HE HL HΨ Hδ; cbn [ihs_ctx_aux List.app].
    - cbn [elim_ihs]; rewrite List.app_nil_r; exact Hδ.
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_arg B0 :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
      replace (S (List.length gs1)) with (List.length (gs1 ++ ca_arg B0 :: nil)) by (rewrite List.length_app; cbn; lia).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_snoc, HE; lia | exact HL | exact HΨ | exact Hδ ].
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      pose proof (gsub_ih D HD Hc Hdt p Hl Γ HΓ Us HUl HUs (List.repeat d_zero (ind_nu D)) (List.repeat_length _ _) HM
                    c gs gs1 Ps0 rest E Hcon Heq HΨ) as Hj.
      pose proof Hdt as (_ & _ & _ & _ & _ & _ & _ & _ & HPl0 & _).
      specialize (HPl0 _ _ _ _ _ Hin Heq).
      pose proof (rel_exp_under_ctx_gsub Hj HA) as HAj; cbn [exp_sub] in HAj.
      rewrite <- List.app_assoc; cbn [List.app].
      replace (Ns ++ As ++ L ++ a_elim nm A Bs a :: elim_ihs nm A Bs rest (List.skipn (S (List.length gs1)) As))
        with (Ns ++ As ++ (L ++ a_elim nm A Bs a :: nil) ++ elim_ihs nm A Bs rest (List.skipn (S (List.length gs1)) As))
        by (rewrite <- !List.app_assoc; reflexivity).
      replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ ca_rec Ps0 :: nil)) by (rewrite cargs_pat_snoc; reflexivity).
      replace (S (List.length gs1)) with (List.length (gs1 ++ ca_rec Ps0 :: nil)) by (rewrite List.length_app; cbn; lia).
      apply (IH (gs1 ++ ca_rec Ps0 :: nil) (_ :: E));
        [ rewrite Heq, <- List.app_assoc; reflexivity | cbn; rewrite cargs_nrec_snoc, HE; lia
        | rewrite List.length_app; cbn; lia | cbn [List.app]; exact (sem_ctx_ext_typ _ _ _ HΨ HAj) |].
      replace (Ns ++ As ++ L ++ a_elim nm A Bs a :: nil) with ((Ns ++ As ++ L) ++ a_elim nm A Bs a :: nil)
        by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (sb_of_list_app (Ns ++ As ++ L) (a_elim nm A Bs a :: nil) Id).
      change (sb_of_list (sb_of_list Id (Ns ++ As ++ L)) (a_elim nm A Bs a :: nil))
        with (sb_of_list Id (Ns ++ As ++ L) ,, a_elim nm A Bs a).
      cbn [List.app]; eapply gsub_ass; [ exact Hδ | exact HAj |].
      rewrite exp_sub_sub.
      match type of Hj with gsub _ (sb_of_list (sb_of_wk (wk_shiftn ?m)) (?Q ++ ?v :: nil)) _ =>
        assert (Hm : m = List.length (Ns ++ As ++ L)) by (rewrite !List.length_app, HNl, HAl, HL; lia);
        assert (Hidx : v[sb_of_list Id (Ns ++ As ++ L)] = a);
        [| assert (Hcomp : sb_eq (sb_of_list (sb_of_wk (wk_shiftn m)) (Q ++ v :: nil) ⨟ sb_of_list Id (Ns ++ As ++ L))
                                 (sb_of_list Id (List.map (fun P => P[sb_of_list Id (Ns ++ As ++ L)]) Q ++ a :: nil)));
           [ rewrite Hm; etransitivity; [ apply sb_of_list_shift_compose |]; rewrite List.map_app; cbn [List.map]; rewrite Hidx; reflexivity
           | rewrite (exp_sub_sb_eq _ _ _ Hcomp);
             set (Q' := List.map (fun P => P[sb_of_list Id (Ns ++ As ++ L)]) Q);
             assert (HQl : List.length Q' = ind_nn D) by (unfold Q'; rewrite !List.length_map; exact HPl0);
             assert (Hg2 : gsub Γ (sb_of_list Id (Q' ++ a :: nil)) (elim_mctx p D Us ++ Γ));
             [ destruct (gsub_props Hδ) as [Hδv Hδl];
               exact (gsub_eq _ _ _ _ (gsub_comp _ _ _ _ _ Hj HΓ Hδv Hδl) Hcomp)
             | apply elim_valid_at; [ exact HQl | exact Hg2 |];
               pose proof (valid_exp_var_here (Γ := tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ) HM) as Hv0;
               pose proof (rel_exp_under_ctx_gsub Hg2 Hv0) as Hv1 ] ] ]
      end.
      + change (exp_sub (a_var ?x) ?s) with (sentry_exp (s x)).
        rewrite (sb_of_list_nth _ _ _ a) by (rewrite !List.length_app, HNl, HAl, HL, Heq, List.length_app, length_cargs_pat; cbn; lia).
        rewrite !List.length_app, HNl, HAl, HL, length_cargs_pat.
        replace (ind_nn D + (List.length gs + List.length E) - 1 - (List.length E + List.length gs - 1 - List.length gs1))
          with (ind_nn D + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
        cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite HNl; replace (ind_nn D + List.length gs1 - ind_nn D) with (List.length gs1) by lia.
        rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact Ha.
      + assert (E1 : (a_var 0)[sb_of_list Id (Q' ++ a :: nil)] = a) by (rewrite sb_of_list_app; reflexivity).
        rewrite E1 in Hv1.
        replace (exp_wk (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D))) wk_shift)
          with ((apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))[wk_shiftn (List.length (a :: nil))]ʷ) in Hv1
          by (apply exp_wk_wk_eq; intros x; cbn; lia).
        rewrite exp_shift_past, elim_mctx_head_inst in Hv1 by exact HQl.
        exact Hv1.
  Qed.

  Lemma gsub_iota :
      (forall k N T, List.nth_error Ns k = Some N ->
         List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Γ ⊨ N : T) ->
      (forall k N T, List.nth_error As k = Some N ->
         List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T -> Γ ⊨ N : T) ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ elim_ihs nm A Bs gs As)) (elim_bctx p D gs A Us ++ Γ).
  Proof.
    intros HNs HAs.
    pose proof (HBc c gs Hcon) as HB.
    assert (HC : ⊨ cinst Γ p D Us gs).
    { unfold elim_bctx in HB; unfold cinst; rewrite <- !List.app_assoc in HB; exact (sem_ctx_app_r _ _ HB). }
    pose proof (gsub_args Γ p D Us Ns c gs As Hc HΓ Hcon HNl (sem_ctx_tail HM) HC HNs HAl HAs) as Hδ.
    rewrite <- (List.app_nil_r As) in Hδ at 1.
    pose proof (gsub_iota_ihs gs nil nil nil eq_refl eq_refl eq_refl HC Hδ) as H.
    cbn [List.app List.skipn List.length cargs_pat] in H.
    unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
  Qed.

  Lemma rel_exp_elim_iota_at :
      (forall k N T, List.nth_error Ns k = Some N ->
         List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T -> Γ ⊨ N : T) ->
      (forall k N T, List.nth_error As k = Some N ->
         List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T -> Γ ⊨ N : T) ->
      forall n B, brs_lookup Bs c = Some (n, B) ->
      Γ ⊨ a_elim nm A Bs (apps (a_con p c) (Us ++ Ns ++ As)) ≈ B[sb_of_list Id (Ns ++ As ++ elim_ihs nm A Bs gs As)]
        : A[sb_of_list Id (Ns ++ apps (a_con p c) (Us ++ Ns ++ As) :: nil)].
  Proof.
    intros HNs HAs n B Hlk.
    pose proof (decl_closed_nu D Hc) as Hle.
    set (Mc := apps (a_con p c) (Us ++ Ns ++ As)).
    assert (HMc : Γ ⊨ Mc : apps (a_ind p) (Us ++ Ns)).
    { unfold Mc; rewrite List.app_assoc.
      apply (rel_exp_con_apps D HD Hc Hsu p Hl Γ c gs (Us ++ Ns) As HΓ Hcon); [ rewrite List.length_app; unfold ind_nn in *; lia | | exact HAl | exact HAs ].
      apply params_valid_join; assumption. }
    pose proof (gsub_tau D Hc p Γ HΓ Us HUl HM Ns Mc HNl HNs HMc) as Hg.
    pose proof (elim_valid_at Ns Mc HNl Hg HMc) as HL.
    pose proof (gsub_iota HNs HAs) as Hgi.
    pose proof (HBv _ _ _ _ Hcon (brs_lookup_in _ _ _ _ Hlk)) as HBv'.
    assert (Lih : List.length (elim_ihs nm A Bs gs As) = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
    pose proof (rel_exp_under_ctx_gsub Hgi HBv') as HR.
    rewrite elim_bty_iota in HR by assumption.
    destruct (sem_ctx_per_ctx_env HΓ) as [RΓ HRΓ].
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    destruct (presup_rel_exp_under_ctx HL) as [iT HT].
    destruct (presup_rel_exp_under_ctx HBv') as [iB HTb].
    apply (rel_exp_under_ctx_of_simple HRΓ HL HR).
    intros ρ ρ' Hρρ'.
    assert (Hρ'ρ' : RΓ ρ' ρ') by (etransitivity; [ symmetry; exact Hρρ' | exact Hρρ' ]).
    destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as (l & l' & El & El' & Hll').
    apply eval_elim_inv in El' as (m & Em & Eel).
    pose proof Em as Em'; unfold Mc in Em'; apply eval_apps_exp in Em' as (f & vall & Ef & Evall & Eapp).
    assert (f = d_con p c nil) as -> by (inversion Ef; reflexivity).
    apply eval_exps_app_inv in Evall as (us' & vrest & -> & Eus & Evrest).
    apply eval_exps_app_inv in Evrest as (ns' & as' & -> & Ens & Eas).
    assert (Lus : List.length us' = ind_nu D) by (rewrite (eval_exps_length _ _ _ Eus); exact HUl).
    assert (Lns : List.length ns' = ind_nn D) by (rewrite (eval_exps_length _ _ _ Ens); exact HNl).
    assert (Las : List.length as' = List.length gs) by (rewrite (eval_exps_length _ _ _ Eas); exact HAl).
    assert (Em2 : $*| d_con p c nil & us' ++ ns' ++ as' | gc_deps ⍮ gc_stack ↘ d_con p c (us' ++ ns' ++ as')).
    { change (d_con p c (us' ++ ns' ++ as')) with (d_con p c (nil ++ (us' ++ ns' ++ as'))).
      apply (eval_apps_con' D p Hl c gs); [ exact Hcon | cbn; rewrite !List.length_app; unfold ind_nn in *; lia ]. }
    assert (m = d_con p c (us' ++ ns' ++ as')) as -> by (eapply (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_eval gc_deps gc_stack)))))); eassumption).
    apply eval_elim_con_inv in Eel as (D' & gs' & n' & B' & ihs & Hl' & Hcon' & Hlk' & Eih & EB).
    rewrite Hl in Hl'; injection Hl' as <-; rewrite Hcon in Hcon'; injection Hcon' as <-.
    rewrite Hlk in Hlk'; injection Hlk' as <- <-.
    assert (Hnp : List.length (us' ++ ns') = ind_np D) by (rewrite List.length_app; unfold ind_nn in *; lia).
    assert (E1 : us' ++ ns' ++ as' = (us' ++ ns') ++ as') by (rewrite List.app_assoc; reflexivity).
    rewrite E1 in EB, Eih.
    rewrite (skipn_app_exact (us' ++ ns') as' _ Hnp) in EB, Eih.
    rewrite (firstn_app_exact (us' ++ ns') as' _ Hnp), (skipn_app_exact us' ns' _ Lus) in EB.
    pose proof (eval_elim_ihs _ _ _ _ _ _ _ _ Eas Eih HAl) as Eihs.
    set (Eτ := env_args ρ' (ns' ++ as' ++ ihs)).
    assert (Hτ : ⟦ sb_of_list Id (Ns ++ As ++ elim_ihs nm A Bs gs As) ⟧s ρ' ↘ Eτ)
      by (apply eval_sb_of_list; [ apply eval_sub_id | apply eval_exps_app; [ exact Ens | apply eval_exps_app; [ exact Eas | exact Eihs ] ] ]).
    destruct (exp_inst_link _ _ _ _ _ _ _ _ _ HBv' HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ) as (r & n0 & Er & En0 & Hrn).
    assert (n0 = l') as -> by (eapply functional_eval_exp; eassumption).
    pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HTb HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ Hτ) as ER.
    rewrite elim_bty_iota in ER by assumption.
    exists l, r; split; [ exact El | split; [ exact Er |] ].
    assert (Hrl : per_head A[sb_of_list Id (Ns ++ Mc :: nil)] A[sb_of_list Id (Ns ++ Mc :: nil)] ρ' ρ' r l')
      by (apply ER; exact Hrn).
    pose proof (per_head_sym _ _ _ _ _ _ HRΓ (rel_exp_under_ctx_refl_left HT) Hρ'ρ' _ _ Hrl) as Hlr.
    assert (EC : per_head A[sb_of_list Id (Ns ++ Mc :: nil)] A[sb_of_list Id (Ns ++ Mc :: nil)] ρ' ρ'
                 <~> per_head A[sb_of_list Id (Ns ++ Mc :: nil)] A[sb_of_list Id (Ns ++ Mc :: nil)] ρ ρ').
    { apply (per_head_of_typ_resp HRΓ HT).
      apply rel_chain_cons; [ exact Hρ'ρ' |]. apply rel_chain_cons; [ symmetry; exact Hρρ' |]. apply rel_chain_of_pair; exact Hρρ'. }
    exact (per_head_trans _ _ _ _ _ _ HRΓ (rel_exp_under_ctx_refl_left HT) Hρρ' _ _ _ Hll' (proj1 (EC _ _) Hlr)).
  Qed.
End Iota.

End Fixed_GCtx.
