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
    two readings ([canonical_nparams], [canonical_mctx], [canonical_bctx]), and then
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
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes CargsRel ViewEquations RviewEnds ViewArgs Con.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Head Variable as a Term

    [B[wk_q ↑]ʷ[Id ,, #0]] is [B] up to the entry at index [0]: [Id ,, #0]
    substitutes the term [#0] where [Id] has the variable [0].  At a
    relevant head the term evaluates to the head's value, stored at the
    declared type; at a propositional one it is kept, [⋆ᵈ⟨#0, ρ⟩], a proof
    that reads back as the head does.  The context PER reads only the
    head's value, its readability and the tail, so the two are related. *)

Definition sb_head_term (σ : sub) : sub := sb_extend (Wk ⨟ σ) (se_exp (sentry_exp (σ 0))).

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

(** The head as a term, in the evaluation of a substitution into
    [Γ ▹{κ} A] at an environment the context PER relates to [ρ']: at a
    head of an evaluated kind the head's value, at a propositional one the
    term kept, which reads back by the premise; either way related to [ρ']
    as the evaluation of the substitution is. *)
Lemma eval_sub_head_term_rel : forall Γ κ A (i : nat) RΓ σ ρ ρσ ρ',
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> Γ ⊨ᵗ A ≈ A at i ->
    ⟦ σ : Γ ▹{κ} A ⟧s ρ ↘ ρσ -> Dom ρσ ≈ ρ' ∈ per_env_extend A A RΓ ->
    proof_readable ⋆ᵈ⟨sentry_exp (σ 0), ρ⟩ ->
    exists ρh, ⟦ sb_head_term σ : Γ ▹{κ} A ⟧s ρ ↘ ρh /\ Dom ρh ≈ ρ' ∈ per_env_extend A A RΓ.
Proof.
  intros * HΓ HA Hσ Hρ Hpr.
  pose proof (per_ctx_env_of_typ (κ := κ) HΓ HA) as HΓA.
  pose proof (rel_type_inversion_simple_at HΓ HA) as HAs.
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
  pose proof Hρ as [Ht Hh _ Hr _ Rr].
  assert (Htt : Dom ρσ↯ ≈ ρσ↯ ∈ RΓ) by (etransitivity; [ exact Ht | symmetry; exact Ht ]).
  pose proof (eval_sub_tail (ce_ass κ A) Γ σ (fun x => σ (S x)) ρ ρσ (fun _ => eq_refl) Hσ) as Hσt.
  destruct (HAs _ _ Htt) as (a & a0 & Ea & Ea0 & [Ra HRa]).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  pose proof (head_propositional_iff (e := ce_ass κ A) HΓ eq_refl HAs Htt Ea) as Ip.
  destruct (HAs _ _ Ht) as (b & b' & Eb & Eb' & [Rb HRb]).
  assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
  destruct (evaluated_kind_or_propositional (domain_kind a)) as [Hev | Er].
  - (** A head of an evaluated kind: its value, stored at the declared
        type. *)
    assert (Hn : ~ head_propositional gc_deps gc_stack (ce_ass κ A) Γ ρσ↯)
      by (rewrite Ip; intros E; rewrite E in Hev; inversion Hev).
    assert (Hn0 : ~ entry_propositional gc_deps gc_stack (Γ ▹{κ} A) ρσ 0)
      by (intros Hp; apply Hn; exact (proj1 (entry_propositional_zero_head _ _ _) Hp)).
    pose proof (eval_sub_var (Γ ▹{κ} A) σ ρ ρσ 0 Hσ ltac:(cbn; lia) Hn0) as Ev; cbn [exp_sub] in Ev.
    exists (ρσ↯ ↦ ρσ 0 ⦂ centry_tag (ce_ass κ A) Γ ρσ↯); split.
    + apply (eval_sub_cons_intro (ce_ass κ A) Γ (sb_head_term σ) (fun x => σ (S x)) _ _ _ (fun _ => eq_refl) Hσt);
        [ intros Hp; contradiction | intros _; cbn; exists (ρσ 0); split; [ reflexivity | exact Ev ] ].
    + destruct (per_head_closure_readable HΓA HΓ Ht Hh) as [Rl _].
      apply per_env_extend_intro; cbn [drop_env List.tl env_entry List.hd]; try assumption.
      * intros _; eexists; reflexivity.
      * split; [ exact Rl | cbn; lia ].
  - (** A propositional head: the term kept. *)
    assert (Hp : head_propositional gc_deps gc_stack (ce_ass κ A) Γ ρσ↯) by (rewrite Ip; exact Er).
    exists (ρσ↯ ↦ ⋆ᵈ⟨sentry_exp (σ 0), ρ⟩ ⦂ centry_tag (ce_ass κ A) Γ ρσ↯); split.
    + apply (eval_sub_cons_intro (ce_ass κ A) Γ (sb_head_term σ) (fun x => σ (S x)) _ _ _ (fun _ => eq_refl) Hσt);
        [ intros _; cbn; reflexivity | intros Hn; contradiction ].
    + pose proof (Hh _ _ _ _ Ea Eb' HRb) as Hh'.
      pose proof (proj1 (per_univ_elem_propositional _ _ _ _ HRb Er _ _) Hh') as [_ Rp'].
      assert (Hm : Dom ⋆ᵈ⟨sentry_exp (σ 0), ρ⟩ ≈ ρ' 0 ∈ per_head A A ρσ↯ ρ'↯)
        by exact (per_head_proof Ea Er Hpr Rp').
      destruct (per_head_closure_readable HΓA HΓ Ht Hm) as [Rl _].
      apply per_env_extend_intro; cbn [drop_env List.tl env_entry List.hd]; try assumption.
      * intros _; eexists; reflexivity.
      * split; [ exact Rl | cbn; lia ].
Qed.

(** A substitution with its head as a term is related to every
    substitution the original is related to. *)
Lemma rel_sub_under_ctx_head_term : forall {Γ' Γ κ A σ σ'} {i : nat},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ' ⊨ˢ σ ≈ σ' : Γ ▹{κ} A ->
    Γ' ⊨ˢ sb_head_term σ ≈ σ' : Γ ▹{κ} A.
Proof.
  intros * HA [env_rel HΓ' env_relo HΓA Hσ Hσs].
  pose proof (rel_type_inversion HA) as [RΓ [HΓ _]].
  pose proof (per_ctx_env_of_typ (κ := κ) HΓ HA) as HΓA'.
  assert (E : env_relo <~> per_env_extend A A RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPo : PER env_relo) by (eapply per_env_PER; exact HΓA).
  assert (Hs0 : sentry_scoped (List.length Γ') (σ 0)) by exact (proj1 (Hσs 0 ltac:(cbn; lia))).
  refine (mk_rel_sub_under_ctx _ _ _ _ env_rel HΓ' env_relo HΓA _ _).
  - intros Γ'' env_rel' HΓ'' φ Hφ Hφb ρ ρ' Hρ.
    destruct (Hσ _ _ HΓ'' _ Hφ Hφb _ _ Hρ) as [a b c d Ha Hb Hc Hd Hchain].
    pose proof (rel_chain_4_commut_left _ _ _ _ _ Hchain) as Hab.
    pose proof (rel_chain_4_related _ _ _ _ _ Hchain) as Hbc.
    pose proof (rel_chain_4_commut_right _ _ _ _ _ Hchain) as Hcd.
    (** The kept heads read back: their free bounds are inside the
        contexts the environments are related at. *)
    assert (Hs0w : exp_scoped (List.length Γ'') (sentry_exp (sb_wk σ φ 0))).
    { unfold sb_wk; rewrite <- sentry_exp_wk.
      exact (exp_scoped_wk _ _ _ _ (sentry_exp_scoped _ _ Hs0) Hφb). }
    pose proof (per_ctx_env_kept_proof_readable _ _ _ _ HΓ'' (exp_scoped_free_bound _ _ Hs0w) _ _ Hρ) as [Rpa _].
    pose proof (per_ctx_env_kept_proof_readable _ _ _ _ HΓ' (exp_scoped_free_bound _ _ (sentry_exp_scoped _ _ Hs0))
                  _ _ (Hφ _ _ Hρ)) as [Rpb _].
    destruct (eval_sub_head_term_rel Γ κ A i RΓ (sb_wk σ φ) ρ a b HΓ HA Ha (proj1 (E _ _) Hab) Rpa) as (ah & Eah & Hah).
    destruct (eval_sub_head_term_rel Γ κ A i RΓ σ (⟪φ⟫ ρ) b c HΓ HA Hb (proj1 (E _ _) Hbc) Rpb) as (bh & Ebh & Hbh).
    apply E in Hah, Hbh.
    apply (mk_rel_sub ah bh c d);
      [ eapply eval_sub_sb_eq; [ symmetry; apply sb_wk_head_term | exact Eah ] | exact Ebh | exact Hc | exact Hd |].
    apply rel_chain_4; [| exact Hbh | exact Hcd ].
    etransitivity; [ exact Hah |]; etransitivity; [ exact Hbc | symmetry; exact Hbh ].
  - intros [| x] Hx; [| exact (Hσs (S x) Hx) ].
    split; [ exact (sentry_exp_scoped _ _ Hs0) | exact (proj2 (Hσs 0 Hx)) ].
Qed.

Lemma rel_exp_typ_var0 : forall {Γ κ A B} {i j : nat},
    Γ ⊨ᵗ A ≈ A at j ->
    Γ ▹{κ} A ⊨ B ≈ B : Typeω@i ->
    Γ ▹{κ} A ⊨ B[wk_q ↑]ʷ[Id ,, #0] ≈ B : Typeω@i.
Proof.
  intros * HA HB.
  pose proof (rel_exp_of_typ_inversion HB) as [env_rel [HΓA HBgen]].
  pose proof (rel_type_inversion HA) as [RΓ [HΓ _]].
  pose proof (per_ctx_env_of_typ (κ := κ) HΓ HA) as HΓA'.
  assert (E : env_rel <~> per_env_extend A A RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPo : PER env_rel) by (eapply per_env_PER; exact HΓA).
  destruct (rel_exp_of_typ_inversion_simple HB) as (Rs & HRs & Hsimp).
  assert (Es : env_rel <~> Rs) by (eapply per_ctx_env_right_irrel; eassumption).
  apply rel_exp_of_typ; exists env_rel, HΓA.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof Hσ as [_ _ _ _ _ Hσs].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_rel) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρσ' : Dom ρσ ≈ ρσ ∈ env_rel) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  (** The head as a term, at [σ]'s evaluation and at the identity's. *)
  pose proof (per_ctx_env_kept_proof_readable _ _ _ _ HΓ'
                (exp_scoped_free_bound _ _ (sentry_exp_scoped _ _ (proj1 (Hσs 0 ltac:(cbn; lia))))) _ _ Hρ) as [Rp _].
  destruct (eval_sub_head_term_rel Γ κ A j RΓ σ ρ ρσ ρ'σ' HΓ HA Hev (proj1 (E _ _) Hρσ) Rp) as (ρh & Eh & Hh).
  pose proof (@eval_sub_id gc_deps gc_stack (Γ ▹{κ} A) ρσ) as Hid.
  assert (Hρσr : Dom ctx_retag (Γ ▹{κ} A) ρσ ≈ ρσ ∈ env_rel) by exact (per_ctx_env_retag_left HΓA _ _ Hρσ').
  assert (Rpi : proof_readable ⋆ᵈ⟨sentry_exp (Id 0), ρσ⟩).
  { assert (Hs : exp_scoped (List.length (Γ ▹{κ} A)) #0) by (cbn; lia).
    pose proof (per_ctx_env_kept_proof_readable _ _ _ _ HΓA (exp_scoped_free_bound _ _ Hs) _ _ Hρσ') as [Rp0 _]; exact Rp0. }
  destruct (eval_sub_head_term_rel Γ κ A j RΓ Id ρσ (ctx_retag (Γ ▹{κ} A) ρσ) ρσ HΓ HA Hid (proj1 (E _ _) Hρσr) Rpi)
    as (ρσh & Eσh & Hσh).
  apply E in Hh, Hσh.
  destruct (HBgen _ _ HΓ' _ _ (rel_sub_under_ctx_head_term HA Hσ) _ _ _ _ Hρ Eh Hev') as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hc].
  destruct (HBgen _ _ HΓA _ _ (rel_sub_under_ctx_head_term HA (rel_sub_id (ex_intro _ _ HΓA))) _ _ _ _ Hρσ' Eσh Hid)
    as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hd].
  (** [B] at the two heads as terms, environments related through [ρσ]. *)
  assert (Hhh : Dom ρh ≈ ρσh ∈ env_rel)
    by (etransitivity; [ exact Hh |]; etransitivity; [ symmetry; exact Hρσ | symmetry; exact Hσh ]).
  destruct (Hsimp _ _ (proj1 (Es _ _) Hhh)) as (e1 & e2 & Ee1 & Ee2 & He12).
  functional_eval_rewrite_clear.
  apply (mk_rel_exp c1 d1 c3 c4);
    [ rewrite exp_sub_wk_q_var0; exact Hc1 | rewrite exp_wk_q_var0; exact Hd1 | exact Hc3 | exact Hc4 |].
  destruct Hc as (C12 & C23 & C34); destruct Hd as (D12 & _ & _).
  assert (Hcd : per_universe_elements (per_univ i) c2 d2)
    by (destruct C12, D12; constructor; first [ exact He12 | assumption ]).
  apply rel_chain_4; [| | exact C34 ].
  - etransitivity; [ exact C12 |]; etransitivity; [ exact Hcd | symmetry; exact D12 ].
  - etransitivity; [ exact D12 |]; etransitivity; [ symmetry; exact Hcd | exact C23 ].
Qed.

(** ** Substitutions Weakened *)

(** An instance weakened is the weakened terms over the weakened base. *)
Lemma sb_wk_of_list_eq : forall Ms σ φ, sb_eq (sb_wk (sb_of_list σ Ms) φ) (sb_of_list (sb_wk σ φ) (List.map (fun M => M[φ]ʷ) Ms)).
Proof.
  induction Ms as [| M Ms IH]; intros; cbn [sb_of_list List.map]; [ reflexivity |].
  etransitivity; [ apply IH | apply sb_of_list_cong; intros [| x]; reflexivity ].
Qed.

(** ** The Variables of a Telescope *)

Lemma vars_tele_lookup : forall Φ Δ ρ τ Γ0 n,
    all_assumptions Δ -> ctx_mvc Δ -> ctx_scoped n Δ ->
    (forall y, y < n -> sentry_exp (τ y) = (sentry_exp (ρ y))[wk_shiftn (List.length Φ + List.length Δ)]ʷ) ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ τ (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      exists x, N = a_var x /\ Φ ++ tele_sub Δ ρ ++ Γ0 ∋ #x : T.
Proof.
  intros * Hass Hmv Hs Hτ k N T HN HT.
  apply vars_from_nth_error in HN as [Hk ->].
  eexists; split; [ reflexivity |].
  apply tele_insts_nth in HT as (κ & A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass κ A :: List.rev l1)
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

(** A variable of an environment extended by typed values: the value it
    points to, whatever its type. *)
Lemma env_var_extend_typed : forall B vts k, k < List.length vts ->
    env_var (env_extend_typed B vts) k = List.nth (List.length vts - 1 - k) (List.map fst vts) d_prop.
Proof.
  intros B vts; induction vts as [| [v t] vts IH] using List.rev_ind; intros k Hk; cbn in Hk; [ lia |].
  rewrite List.length_app in Hk |- *; cbn [List.length] in Hk |- *.
  rewrite env_extend_typed_app; cbn [env_extend_typed List.fold_left extend_env fst snd].
  rewrite List.map_app; cbn [List.map fst].
  destruct k as [| k].
  - rewrite List.app_nth2 by (rewrite List.length_map; lia).
    rewrite List.length_map; replace (List.length vts + 1 - 1 - 0 - List.length vts) with 0 by lia; reflexivity.
  - change (env_var (de_term v t :: env_extend_typed B vts) (S k)) with (env_var (env_extend_typed B vts) k).
    rewrite IH by lia.
    rewrite List.app_nth1 by (rewrite List.length_map; lia).
    f_equal; lia.
Qed.

Corollary eval_var_extend_typed : forall B vts k, k < List.length vts ->
    ⟦ a_var k ⟧ env_extend_typed B vts ↘ List.nth (List.length vts - 1 - k) (List.map fst vts) d_prop.
Proof. intros * Hk; rewrite <- (env_var_extend_typed B vts k Hk); constructor. Qed.

Lemma vars_from_S0 : forall n, vars_from 0 (S n) = a_var n :: vars_from 0 n.
Proof. intros; unfold vars_from; rewrite List.seq_S, List.rev_app_distr; reflexivity. Qed.

(** ** Recursive Results *)

Lemma rec_results_rel_len : forall D dr Rel k u u' pre pre' Ts gs vs vs' ihs ihs',
    rec_results_rel D dr Rel k u u' pre pre' Ts gs vs vs' ihs ihs' ->
    List.length ihs = cargs_nrec D gs /\ List.length ihs' = cargs_nrec D gs.
Proof. induction 1; cbn; rewrite ?List.length_app; lia. Qed.

(** The results of the recursive argument at a position: those of its
    leaf paths, after the results of the arguments before it. *)
Lemma rec_results_rel_at : forall D dr Rel k u u' pre pre' Ts gs vs vs' ihs ihs',
    rec_results_rel D dr Rel k u u' pre pre' Ts gs vs vs' ihs ihs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists v v' rs rs' ih1 ih1' ih2 ih2', List.nth_error vs (List.length gs1) = Some v /\ List.nth_error vs' (List.length gs1) = Some v' /\
      ihs = ih1 ++ rs ++ ih2 /\ ihs' = ih1' ++ rs' ++ ih2' /\
      List.length ih1 = cargs_nrec D gs1 /\ List.length ih1' = cargs_nrec D gs1 /\
      List.length rs = List.length (shape_leaves (rview_leaves D) 0 t) /\ List.length rs' = List.length (shape_leaves (rview_leaves D) 0 t) /\
      rec_result_rel D dr Rel k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) (Ts ++ cargs_nonrec_tele gs1) t v v' rs rs'.
Proof.
  induction 1 as [k u u' pre pre' Ts | k u u' pre pre' Ts rA A gs v v' vs vs' ihs ihs' H IH
                 | k u u' pre pre' Ts t0 gs v v' vs vs' rs rs' ihs ihs' Lr Lr' Hr H IH];
    intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst.
  - destruct (IH _ _ _ eq_refl) as (x & x' & r1 & r1' & a1 & a1' & b1 & b1' & Hx & Hx' & -> & -> & La & La' & Lb & Lb' & Hr).
    exists x, x', r1, r1', a1, a1', b1, b1'; unfold cargs_nonrec_tele in *; cbn in Hr |- *;
      rewrite <- !List.app_assoc in Hr; repeat split; assumption.
  - exists v, v', rs, rs', nil, nil, ihs, ihs'; unfold cargs_nonrec_tele; cbn; rewrite !List.app_nil_r; repeat split; assumption.
  - destruct (IH _ _ _ eq_refl) as (x & x' & r1 & r1' & a1 & a1' & b1 & b1' & Hx & Hx' & -> & -> & La & La' & Lb & Lb' & Hr0).
    exists x, x', r1, r1', (rs ++ a1), (rs' ++ a1'), b1, b1'; cbn [cargs_nrec].
    unfold cargs_nonrec_tele in *; cbn [cargs_nonrec] in Hr0 |- *.
    rewrite !List.length_app, <- !List.app_assoc; repeat split; try assumption; lia.
Qed.

Lemma rec_results_rel_vs_len : forall D dr Rel k u u' pre pre' Ts gs vs vs' ihs ihs',
    rec_results_rel D dr Rel k u u' pre pre' Ts gs vs vs' ihs ihs' ->
    List.length vs = List.length gs /\ List.length vs' = List.length gs.
Proof. induction 1; cbn; lia. Qed.

(** The stored parameters of two related constructors, from their
    arguments' number. *)
Lemma ind_rel_con_len : forall p D okr nr ar dr k u u' ns ns' Mk hd k' c gs bs vs bs' vs',
    ind_rel p D okr nr ar dr k u u' ns ns' (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
    ind_member D k = Some Mk -> im_is_rview Mk = false ->
    ind_con Mk c = Some gs -> List.length vs = List.length gs -> List.length vs' = List.length gs ->
    List.length bs = (im_unu D Mk + im_nn Mk)%nat /\ List.length bs' = (im_unu D Mk + im_nn Mk)%nat.
Proof.
  intros * H HM Hrv Hc Lv Lv'; inversion H; subst;
    [| match goal with H1 : ind_member _ _ = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
         rewrite HM in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end ].
  match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end.
  match goal with H1 : ind_con Mk c = Some ?g1 |- _ => rewrite Hc in H1; injection H1 as <- end.
  match goal with Ha : con_args_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha) as [L0 L0'] end.
  match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => pose proof (f_equal (@List.length domain) E) as E1 end.
  match goal with E : (?a ++ ?b = bs' ++ vs')%list |- _ => pose proof (f_equal (@List.length domain) E) as E2 end.
  rewrite !List.length_app in E1, E2; split; lia.
Qed.

(** At the end of a shape, at a member with a block: one result. *)
Lemma rec_result_self_inv : forall D dr Rel k u u' pre pre' Ts j Mj Ps v v' rs rs', ind_member D j = Some Mj ->
    im_is_rview Mj = false -> rec_result_rel D dr Rel k u u' pre pre' Ts (pt_self j Ps) v v' rs rs' ->
    exists bs bs' ih ih', rs = ih :: nil /\ rs' = ih' :: nil /\ ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u Ts pre ↘ bs /\
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u' Ts pre' ↘ bs' /\ Rel j bs v bs' v' ih ih'.
Proof.
  intros * HM Hrv H; inversion H; subst; [ do 4 eexists; repeat split; eassumption |].
  match goal with H1 : ind_member D j = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
    rewrite HM in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end.
Qed.

(** At the end of a shape, at a record view: its fields' results at the
    projections. *)
Lemma rec_result_rview_inv : forall D dr Rel k u u' pre pre' Ts j Mj qr Is fl c gs Ps v v' rs rs', ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    rec_result_rel D dr Rel k u u' pre pre' Ts (pt_self j Ps) v v' rs rs' ->
    exists ws ws', ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws /\ ⟦projs fl of v' ⟧ gc_deps ⍮ gc_stack ↘ ws' /\
      rec_results_rel D dr Rel j u u' nil nil nil gs ws ws' rs rs'.
Proof.
  intros * HM Hh Hcs H; inversion H; subst.
  - match goal with H1 : ind_member D j = Some ?M1, H2 : im_is_rview ?M1 = false |- _ =>
      rewrite HM in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ H2 Hh) end.
  - match goal with H1 : ind_member D j = Some ?M1, H2 : im_head ?M1 = _, H3 : im_cons ?M1 = _ |- _ =>
      rewrite HM in H1; injection H1 as <-; rewrite Hh in H2; injection H2 as <- <- <-;
      rewrite Hcs in H3; injection H3 as <- <- end.
    do 2 eexists; repeat split; eassumption.
Qed.

(** The members with a block: the first [ind_nblk D], all but the record
    views ([rview_suffix_ok]). *)
Lemma block_not_rview : forall D (Bks0 : list eblock) j Mj b, decl_typed gc_deps gc_stack D ->
    List.length Bks0 = ind_nblk D -> ind_member D j = Some Mj -> List.nth_error Bks0 j = Some b -> im_is_rview Mj = false.
Proof.
  intros * Hdt HL HMj Hb.
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ HMj) as [Hs _].
  destruct (im_is_rview Mj); [| reflexivity ].
  pose proof (Hs eq_refl); apply nth_error_lt_length in Hb; lia.
Qed.

Lemma block_of_nblk : forall D (Bks0 : list eblock), decl_typed gc_deps gc_stack D -> List.length Bks0 = ind_nblk D ->
    forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks0 j = Some b.
Proof.
  intros * Hdt HL * HMj Hrv.
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ HMj) as [_ Hs].
  apply nth_error_lt_some'; destruct (Nat.lt_ge_cases j (ind_nblk D)) as [Hj | Hj]; [ lia |].
  specialize (Hs Hj); congruence.
Qed.

(** What the eliminators give at a member with a block: their values. *)
Lemma member_results_elim_inv : forall p D dr ρa ρb Bksa Bksb ua ub Rel j u u' ns ns' m m' Mj,
    member_results p D dr ρa ρb Bksa Bksb ua ub Rel j u u' ns ns' m m' ->
    ind_member D j = Some Mj -> im_is_rview Mj = false ->
    exists r r', ⟦elim m at j of p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\ ⟦elim m' at j of p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' /\
      Rel j ns m ns' m' r r'.
Proof.
  intros * H HM Hrv; destruct H as [Mj' r r' HM' _ Er Er' Hr | Mj' qr Is fl c gs ws ws' rs rs' HM' Hh _ _ _ _ _ _].
  - exists r, r'; split; [ exact Er | split; [ exact Er' | exact Hr ] ].
  - rewrite HM in HM'; injection HM' as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv Hh).
Qed.

(** Two related elements of a record view: their projections, related as
    the arguments of the view's pseudo-constructor. *)
Lemma ind_rel_rview_inv : forall p D okr nr ar dr j u u' bs bs' v v' Mj qr Is fl c gs, ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    ind_rel p D okr nr ar dr j u u' bs bs' v v' ->
    exists vs vs', ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ vs /\ ⟦projs fl of v' ⟧ gc_deps ⍮ gc_stack ↘ vs' /\
      tele_rel (ar j nil c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') /\
      con_args_rel p D okr nr ar dr j u u' nil nil nil gs vs vs'.
Proof.
  intros * HM Hh Hcs H.
  inversion H; subst;
    try match goal with H1 : ind_member D j = Some ?M1, H2 : im_is_rview ?M1 = false |- _ =>
      rewrite HM in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ H2 Hh) end.
  match goal with H1 : ind_member D j = Some ?M1, H2 : im_head ?M1 = _, H3 : im_cons ?M1 = _ |- _ =>
    rewrite HM in H1; injection H1 as <-; rewrite Hh in H2; injection H2 as <- <- <-;
    rewrite Hcs in H3; injection H3 as <- <- end.
  do 2 eexists; split; [ eassumption | split; [ eassumption | split; eassumption ] ].
Qed.

(** The leaf path at a position of the leaf paths of fields: through the
    projection of a recursive field, after the leaf paths of the fields
    before it. *)
Lemma fields_leaves_nth : forall D fs ns idx l, List.nth_error (fields_leaves (rview_leaves D) ns fs) idx = Some l ->
    exists fs1 f t fs2 idx1 l1, fs = fs1 ++ (f, ca_rec t) :: fs2 /\ idx = cargs_nrec D (List.map snd fs1) + idx1 /\
      l = leaf_proj f (ns ++ fields_args fs1) l1 /\
      List.nth_error (shape_leaves (rview_leaves D) (List.length (ns ++ fields_args fs1)) t) idx1 = Some l1.
Proof.
  intros D; induction fs as [| [g [rA A | t]] fs IH]; intros ns idx l Hl; cbn [fields_leaves] in Hl; [ destruct idx; discriminate | |].
  - destruct (IH _ _ _ Hl) as (fs1 & f & t & fs2 & idx1 & l1 & -> & -> & -> & Hl1).
    exists ((g, ca_arg rA A) :: fs1), f, t, fs2, idx1, l1; cbn [fields_args List.map snd cargs_nrec List.app].
    rewrite <- List.app_assoc in Hl1 |- *; cbn [List.app] in Hl1 |- *; auto.
  - destruct (Nat.lt_ge_cases idx (List.length (shape_leaves (rview_leaves D) (List.length ns) t))) as [Hi | Hi].
    + rewrite List.nth_error_app1 in Hl by (rewrite List.length_map; exact Hi).
      apply nth_error_map_inv in Hl as (l1 & Hl1 & ->).
      exists nil, g, t, fs, idx, l1; cbn [fields_args List.map cargs_nrec List.app]; rewrite List.app_nil_r; auto.
    + rewrite List.nth_error_app2 in Hl by (rewrite List.length_map; exact Hi).
      rewrite List.length_map in Hl.
      destruct (IH _ _ _ Hl) as (fs1 & f & t' & fs2 & idx1 & l1 & -> & Hidx & -> & Hl1).
      exists ((g, ca_rec t) :: fs1), f, t', fs2, idx1, l1; cbn [fields_args List.map snd cargs_nrec List.app].
      rewrite (length_shape_leaves _ t (List.length ns) 0) in Hi, Hidx; repeat split; auto; lia.
Qed.

(** At a domain: the applications at related arguments. *)
Lemma rec_result_pi_inv : forall D dr Rel k u u' pre pre' Ts B t v v' rs rs',
    rec_result_rel D dr Rel k u u' pre pre' Ts (pt_pi B t) v v' rs rs' ->
    forall c c', dr k pre Ts B c c' ->
    exists fc fc' rcs rcs', $| v & c | gc_deps ⍮ gc_stack ↘ fc /\ $| v' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
      List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) rs rcs /\
      List.Forall2 (fun f r => $| f & c' | gc_deps ⍮ gc_stack ↘ r) rs' rcs' /\
      rec_result_rel D dr Rel k u u' (pre ++ c :: nil) (pre' ++ c' :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t fc fc' rcs rcs'.
Proof.
  intros * H c c' Hc; inversion H; subst.
  match goal with Hf : forall _ _, _ -> _ |- _ => pose proof (Hf c c' Hc) as Ha end.
  inversion Ha; subst; do 4 eexists; repeat split; eassumption.
Qed.

(** The results at a domain take relevant arguments. *)
Lemma rec_result_pi_relevant : forall D dr Rel k u u' pre pre' Ts B t v v' rs rs',
    rec_result_rel D dr Rel k u u' pre pre' Ts (pt_pi B t) v v' rs rs' ->
    List.Forall (fun r => arg_kind gc_deps gc_stack r = ak_relevant) rs /\
    List.Forall (fun r => arg_kind gc_deps gc_stack r = ak_relevant) rs'.
Proof. intros * H; inversion H; subst; split; assumption. Qed.

(** ** Values Paired with their Entry Types *)

(** Values related pointwise to types, paired with them. *)
Lemma Forall_combine_of_Forall2 : forall {X Y : Type} (P : X -> Y -> Prop) xs ys,
    List.Forall2 P xs ys -> List.Forall (fun xy => P (fst xy) (snd xy)) (List.combine xs ys).
Proof. induction 1; cbn; constructor; auto. Qed.

(** Pairs satisfying a relation, split apart. *)
Lemma Forall2_of_Forall_pairs : forall {X Y : Type} (P : X -> Y -> Prop) l,
    List.Forall (fun xy => P (fst xy) (snd xy)) l -> List.Forall2 P (List.map fst l) (List.map snd l).
Proof. induction 1; cbn; constructor; auto. Qed.

(** Arguments related to themselves, some of them replaced by other proofs
    that read back at entries whose types are propositions there: related
    to the replaced ones over related bases. *)
Lemma per_tele_args_replace_proofs : forall ts Tb RTb,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> all_assumptions ts ->
    forall ρ ρ' xs ys, RTb ρ ρ' -> per_tele_args ts ρ ρ xs xs -> List.length xs = List.length ys ->
    (forall j x y, List.nth_error xs j = Some x -> List.nth_error ys j = Some y -> x = y \/
       (proof_readable y /\ forall ts1 κ A ts2 a, ts = ts1 ++ ce_ass κ A :: ts2 -> List.length ts1 = j ->
          ⟦ A ⟧ env_tele ρ ts1 (List.firstn j xs) ↘ a -> domain_kind a = ak_propositional)) ->
    per_tele_args ts ρ ρ' xs ys.
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts * Hρ Hgx Hl Hmix.
  - inversion Hgx; subst; destruct ys; cbn in Hl; [ constructor | discriminate ].
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (Hts' : all_assumptions ts) by (inversion Hts; assumption).
    destruct xs as [| x xs], ys as [| y ys]; cbn [List.length] in Hl; try discriminate; [ constructor |].
    inversion Hgx as [| ? ? ? ? ? ? ? ? ? ? Rx HAx Hxx Hgx']; subst.
    cbn [List.rev] in HC; rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ (κ := κ) HTb HAv) as HTb'.
    destruct (rel_type_inversion_simple_at HTb HAv _ _ Hρ) as (a & a' & Ea & Ea' & [R HR]).
    destruct HAx as [a1 a2 Ea1 Ea2 HRx].
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (Ex : R <~> Rx) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HRx ]).
    (** The heads: equal, or proofs of a proposition. *)
    assert (Hxy : R x y).
    { destruct (Hmix 0 x y eq_refl eq_refl) as [<- | (Hry & Hp)]; [ apply Ex; exact Hxx |].
      pose proof (Hp nil κ A ts a eq_refl eq_refl Ea) as Hra.
      pose proof (per_univ_elem_propositional _ _ _ _ HR Hra) as EP.
      pose proof (per_univ_elem_propositional _ _ _ _ HRx Hra) as EPx.
      apply EP; split; [ exact (proj1 (proj1 (EPx _ _) Hxx)) | exact Hry ]. }
    econstructor; [ exact (mk_rel_mod_eval a a' Ea Ea' HR) | exact Hxy |].
    pose proof (entry_readable_of_elem_closure Ea Ea' HR Hxy) as [Rx' Ry'].
    apply (IH _ _ HTb' HC Hts' (ρ ↦ x ⦂ entry_type_closure A ρ) (ρ' ↦ y ⦂ entry_type_closure A ρ')); [ | exact Hgx' | lia | ].
    + apply per_env_extend_intro'; [ exact Hρ | exact (per_head_of Ea Ea' HR Hxy) | exact Rx' | exact Ry' ].
    + intros k x' y' Hx' Hy'.
      destruct (Hmix (S k) x' y' Hx' Hy') as [-> | (Hry' & Hp')]; [ left; reflexivity |].
      right; split; [ exact Hry' |].
      intros ts1 κ' A' ts2 a0 Eq Lt1 Ea0.
      apply (Hp' (ce_ass κ A :: ts1) κ' A' ts2 a0 ltac:(rewrite Eq; reflexivity) ltac:(cbn; lia)).
      exact Ea0.
Qed.

(** The non-recursive arguments before a position are assumptions. *)
Lemma all_assumptions_nonrec_args_prefix : forall gs j, all_assumptions (nonrec_args_prefix gs j).
Proof.
  intros; unfold nonrec_args_prefix; apply List.Forall_rev.
  pose proof (all_assumptions_cargs_nonrec_tele gs) as H; rewrite <- (List.firstn_skipn j (cargs_nonrec_tele gs)) in H.
  apply List.Forall_app in H as [H _]; exact H.
Qed.

(** The context of the non-recursive arguments is the reverse of their
    telescope. *)
Lemma rev_nonrec_args_context : forall gs, List.rev (cargs_nonrec_ctx gs) = cargs_nonrec_tele gs.
Proof.
  unfold cargs_nonrec_tele; induction gs as [| [r A | t] gs IH]; cbn [cargs_nonrec_ctx cargs_nonrec List.map]; [ reflexivity | | exact IH ].
  rewrite List.rev_app_distr, IH; reflexivity.
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
    RΓ0 E E' -> ⟦ τ : Δ0 ⟧s E ↘ Eτ -> ⟦ τ : Δ0 ⟧s E' ↘ Eτ' ->
    (per_head A[τ] A[τ] E E' <~> per_head A A Eτ Eτ').
Proof.
  intros * HA HΓ0 Hτ HE Hev Hev'.
  destruct (rel_exp_of_typ_inversion HA) as (R & HR & Hgen).
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev') as [a b c d Ha Hb Hc Hd Hch].
  apply rel_chain_relevant_univ in Hch.
  assert (Had : Dom a ≈ d ∈ per_univ i) by pairwise.
  destruct Had as [R1 HR1].
  assert (Ch : rel_chain (per_univ_elem i R1) (a :: b :: c :: d :: nil))
    by (eapply per_univ_chain_at_in; [ exact Hch | | | exact HR1 ]; solve_in).
  assert (Hbc : DF b ≈ c ∈ per_univ_elem i ↘ R1) by pairwise.
  etransitivity; [ symmetry; eapply per_head_iff; [ exact Ha | exact Hd | exact HR1 ] |].
  eapply per_head_iff; [ exact Hb | exact Hc | exact Hbc ].
Qed.

Lemma nth_mid : forall (X fa aft ihp : list domain) v,
    List.nth (List.length X + List.length fa) (X ++ fa ++ v :: aft ++ ihp) d_prop = v.
Proof.
  intros; rewrite List.app_nth2 by lia; replace (List.length X + List.length fa - List.length X) with (List.length fa) by lia.
  rewrite List.app_nth2 by lia; rewrite Nat.sub_diag; reflexivity.
Qed.

(** The head relation of a valid type of either sort at related
    environments is a PER. *)
Lemma per_head_trans : forall Γ0 T (i : nat) R0 E E', EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ R0 -> Γ0 ⊨ᵗ T ≈ T at i -> R0 E E' ->
    forall a b d, Dom a ≈ b ∈ per_head T T E E' -> Dom b ≈ d ∈ per_head T T E E' -> Dom a ≈ d ∈ per_head T T E E'.
Proof.
  intros * HR0 HT HE * Hab Hbd.
  destruct (rel_type_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
  pose proof (per_head_iff Et Et' HR) as ER.
  assert (HP : PER R) by (eapply per_elem_PER; exact HR).
  apply ER; apply ER in Hab, Hbd; etransitivity; eassumption.
Qed.

Lemma per_head_sym : forall Γ0 T (i : nat) R0 E E', EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ R0 -> Γ0 ⊨ᵗ T ≈ T at i -> R0 E E' ->
    forall a b, Dom a ≈ b ∈ per_head T T E E' -> Dom b ≈ a ∈ per_head T T E E'.
Proof.
  intros * HR0 HT HE * Hab.
  destruct (rel_type_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
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

Lemma eb_brs_sub : forall b τ, eb_brs (eblock_sub b τ) = brs_sub (eb_brs b) τ.
Proof. intros [] ?; reflexivity. Qed.

Lemma eb_motive_sub : forall b τ, eb_motive (eblock_sub b τ) = (eb_motive b)[sb_qn (eb_binder_count b) τ].
Proof. intros [] ?; reflexivity. Qed.

Lemma eb_binder_count_sub : forall b τ, eb_binder_count (eblock_sub b τ) = eb_binder_count b.
Proof. intros [] ?; reflexivity. Qed.

Lemma nth_error_blocks_sub_inv : forall Bks τ j ba, List.nth_error (blocks_sub Bks τ) j = Some ba ->
    exists b, List.nth_error Bks j = Some b /\ ba = eblock_sub b τ.
Proof.
  intros * H; rewrite nth_error_blocks_sub in H.
  destruct (List.nth_error Bks j) as [b |]; cbn in H; [ injection H as <-; eauto | discriminate ].
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
Lemma valid_app_here : forall Ψ κ A C (i : nat) M, ⊨ Ψ ▹{κ} A -> Ψ ▹{κ} A ⊨ C : Typeω@i ->
    Ψ ⊨ M : a_pi κ ak_relevant A C ->
    Ψ ▹{κ} A ⊨ a_app M[wk_shift]ʷ (a_var 0) : C.
Proof.
  intros * HΨA HC HM.
  destruct (rel_ctx_wf_ass_inv HΨA) as (S & HS & HA).
  pose proof (rel_wk_under_ctx_shift HΨA) as Hw.
  pose proof (rel_exp_under_ctx_wk Hw HM) as HMw; cbn [exp_wk] in HMw.
  pose proof (rel_exp_under_ctx_wk Hw HA) as HAw; cbn [exp_wk] in HAw.
  replace (S[↑]ʷ) with S in HAw by (destruct HS; reflexivity).
  destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS) HA) as [jA HAt].
  pose proof (rel_wk_under_ctx_q (κ := κ) Hw HAt) as Hwq.
  pose proof (rel_exp_under_ctx_wk Hwq HC) as HCw; cbn [exp_wk] in HCw.
  pose proof (valid_exp_under_ctx_var_here HΨA) as Hv.
  (** The application, at the domain's kind. *)
  assert (H : Ψ ▹{κ} A ⊨ M[↑]ʷ $ #0 : C[wk_q ↑]ʷ[Id ,, #0]).
  { assert (Hs : exp_scoped (List.length (Ψ ▹{κ} A)) #0) by (cbn; lia).
    destruct HS as [j | |].
    - exact (rel_exp_under_ctx_app_cong (rel_type_of_typ HAw) (rel_type_kind_of_typ HAw) evaluated_kind_relevant
               evaluated_kind_relevant (rel_type_of_typ HCw) HMw Hv Hs).
    - exact (rel_exp_under_ctx_app_cong_prop HAw HCw HMw Hv Hs Hs).
    - exact (rel_exp_under_ctx_app_cong (rel_type_of_level_sort 0 HAw) (rel_type_kind_of_level_sort HAw) evaluated_kind_level
               evaluated_kind_relevant (rel_type_of_typ HCw) HMw Hv Hs). }
  eapply rel_exp_under_ctx_subtyp; [ exact H | exact (rel_type_of_typ HC) |].
  eapply rel_subtyp_under_ctx_refl; exact (rel_type_of_typ (rel_exp_typ_var0 HAt HC)).
Qed.

(** The type of a member is a relevant type: an inductive or a record
    type. *)
Lemma ind_mty_relevant : forall pq D j Mj Us Ns ρ b, ind_member D j = Some Mj ->
    ⟦ ind_mty pq D j Us Ns ⟧ ρ ↘ b -> domain_kind b = ak_relevant.
Proof.
  intros * HMj Eb; unfold ind_mty, im_ty_at in Eb; rewrite HMj in Eb.
  destruct (im_head Mj).
  - apply eval_apps_exp_ind in Eb as (ns & _ & Hap); rewrite (apps_ind_val _ _ _ _ _ Hap); reflexivity.
  - apply eval_apps_exp_ind in Eb as (ns & _ & Hap); rewrite (apps_ind_val _ _ _ _ _ Hap); reflexivity.
  - apply eval_apps_exp_record in Eb as (ns & _ & Hap); rewrite (apps_record_val _ _ _ _ Hap); reflexivity.
Qed.

(** Nor is it [LevelSort]: it is a member or a record at its parameters. *)
Lemma ind_mty_not_level_sort : forall pq D j Mj Us Ns ρ b, ind_member D j = Some Mj ->
    ⟦ ind_mty pq D j Us Ns ⟧ ρ ↘ b -> not_level_sort b.
Proof.
  intros * HMj Eb; unfold ind_mty, im_ty_at in Eb; rewrite HMj in Eb.
  destruct (im_head Mj).
  - apply eval_apps_exp_ind in Eb as (ns & _ & Hap); rewrite (apps_ind_val _ _ _ _ _ Hap); discriminate.
  - apply eval_apps_exp_ind in Eb as (ns & _ & Hap); rewrite (apps_ind_val _ _ _ _ _ Hap); discriminate.
  - apply eval_apps_exp_record in Eb as (ns & _ & Hap); rewrite (apps_record_val _ _ _ _ Hap); discriminate.
Qed.

(** So a term judgment at it has a type judgment. *)
Corollary presup_rel_exp_under_ctx_mty : forall Γ M M' pq D j Mj Us Ns, ind_member D j = Some Mj ->
    Γ ⊨ M ≈ M' : ind_mty pq D j Us Ns -> exists i, Γ ⊨ᵗ ind_mty pq D j Us Ns ≈ ind_mty pq D j Us Ns at i.
Proof.
  intros * HMj HM; apply (presup_rel_exp_under_ctx HM).
  exact (rel_type_not_level_sort_of_values HM (fun ρ b Eb => ind_mty_not_level_sort _ _ _ _ _ _ _ _ HMj Eb)).
Qed.

(** A valid term of a member's type at related environments: its values,
    related at the type's head, the type being relevant. *)
Lemma rel_exp_under_ctx_simple_at_mty : forall Γ M M' pq D j Mj Us Ns R, ind_member D j = Some Mj ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> Γ ⊨ M ≈ M' : ind_mty pq D j Us Ns ->
    forall ρ ρ', R ρ ρ' ->
      exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head (ind_mty pq D j Us Ns) (ind_mty pq D j Us Ns) ρ ρ'.
Proof.
  intros * HMj HR HM ρ ρ' Hρ.
  destruct (presup_rel_exp_under_ctx_simple_at HR HM) as [i HT].
  destruct (HT _ _ Hρ) as (a & a' & Ea & _ & _).
  exact (rel_exp_under_ctx_simple_at_evaluated HR HM _ _ Hρ
           (rel_typ_evaluated_of_kind (ex_intro _ a (conj Ea (ind_mty_relevant _ _ _ _ _ _ _ _ HMj Ea))) evaluated_kind_relevant)).
Qed.

(** The type of a member is no type of levels. *)
Lemma ind_mty_not_level : forall pq D j Mj Us Ns ρ b, ind_member D j = Some Mj ->
    ⟦ ind_mty pq D j Us Ns ⟧ ρ ↘ b -> ~ level_code b.
Proof.
  intros * HMj Eb (R & a' & [Hl | Hl]); unfold ind_mty, im_ty_at in Eb; rewrite HMj in Eb;
    destruct (im_head Mj);
    first [ apply eval_apps_exp_ind in Eb as (ns & _ & Hap); rewrite (apps_ind_val _ _ _ _ _ Hap) in Hl
          | apply eval_apps_exp_record in Eb as (ns & _ & Hap); rewrite (apps_record_val _ _ _ _ Hap) in Hl ];
    inversion Hl.
Qed.

(** A type of some sort whose values are all relevant and no types of
    levels is a type of a universe: at [Prop] its values would be
    propositions, at [LevelSort] types of levels, so no two environments
    of its context are related. *)
Lemma rel_exp_univ_of_sort_relevant : forall Γ A Srt, type_sort Srt -> Γ ⊨ A : Srt ->
    (forall ρ a, ⟦ A ⟧ ρ ↘ a -> domain_kind a = ak_relevant) ->
    (forall ρ a, ⟦ A ⟧ ρ ↘ a -> ~ level_code a) -> exists i : nat, Γ ⊨ A : Typeω@i.
Proof.
  intros * [i | |] HA Hr Hnl; [ exists i; exact HA | |].
  - exists 0.
    destruct (rel_exp_of_prop_inversion HA) as [RΓ [HRΓ Hgen]].
    refine (mk_rel_exp_under_ctx _ _ _ _ RΓ HRΓ 0 _).
    intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'; exfalso.
    destruct (Hgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 E1 E2 E3 E4 Hc].
    destruct Hc as [H12 _].
    pose proof (Hr _ _ E2) as Hr2; pose proof (per_prop_right _ _ H12) as Hp2; congruence.
  - exists 0.
    destruct (rel_exp_of_level_sort_inversion HA) as [RΓ [HRΓ Hgen]].
    refine (mk_rel_exp_under_ctx _ _ _ _ RΓ HRΓ 0 _).
    intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'; exfalso.
    destruct (Hgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 E1 E2 E3 E4 Hc].
    destruct Hc as [[_ [Hl2 _]] _].
    exact (Hnl _ _ E2 Hl2).
Qed.

Lemma valid_apps_vars : forall n Δ Ψ B (i : nat) M, List.length Δ = n -> all_assumptions Δ -> ⊨ Δ ++ Ψ ->
    Δ ++ Ψ ⊨ B : Typeω@i -> Ψ ⊨ M : ctx_pi Δ B ->
    Δ ++ Ψ ⊨ apps M[wk_shiftn n]ʷ (vars_from 0 n) : B.
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HM.
  - destruct Δ; [| discriminate ]; cbn in *.
    rewrite (exp_wk_id_ext M _ wk_shiftn_zero); exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Hn; cbn in Hn.
    unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ & A & ->) _].
    rewrite ctx_pi_snoc in HM.
    rewrite <- List.app_assoc in HΔ, HB |- *; cbn [List.app] in HΔ, HB |- *.
    pose proof (rel_ctx_wf_app_r _ _ HΔ) as HΨA.
    destruct (rel_exp_ctx_pi _ _ _ _ Hass HΔ HB) as [j HC].
    pose proof (valid_app_here _ _ _ _ _ _ HΨA HC HM) as HMA.
    pose proof (IH Δ0 _ _ _ _ ltac:(lia) Hass HΔ HB HMA) as H.
    rewrite vars_from_S0; cbn [apps_exp].
    replace (M[wk_shiftn (S n)]ʷ $ #n) with ((M[wk_shift]ʷ $ #0)[wk_shiftn n]ʷ); [ exact H |].
    cbn [exp_wk]; f_equal; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia.
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

(** The terms a leaf path reaches its argument at: a variable, applied to
    variables and projected.  Their values are read off the environment, so
    a weakening moves them exactly. *)
Inductive leaf_term : exp -> Prop :=
(** A variable *)
| leaf_term_var : forall n, leaf_term (a_var n)
(** An application of two of them *)
| leaf_term_app : forall x y, leaf_term x -> leaf_term y -> leaf_term (a_app x y)
(** A projection of one *)
| leaf_term_proj : forall f x, leaf_term x -> leaf_term (a_proj f x).

Lemma leaf_term_wk : forall x φ, leaf_term x -> leaf_term x[φ]ʷ.
Proof. intros x φ H; revert φ; induction H; intros φ; cbn [exp_wk]; constructor; auto. Qed.

Lemma leaf_term_apps_vars : forall n x, leaf_term x -> leaf_term (apps_vars_iter n x).
Proof. induction n as [| n IH]; intros x Hx; cbn [apps_vars_iter]; [ exact Hx | constructor; [ apply leaf_term_wk, IH, Hx | constructor ] ]. Qed.

(** The applications of a leaf term take relevant arguments at [ρ]: the
    arguments of a shape's domains, types of a universe.  At a
    proposition the argument would be kept as a proof closing over the
    environment it is evaluated in, which a weakening changes. *)
Fixpoint leaf_apps_relevant (x : exp) (ρ : env) : Prop :=
  match x with
  | a_app f y =>
      leaf_apps_relevant f ρ /\ leaf_apps_relevant y ρ /\ (forall m, ⟦ f ⟧ ρ ↘ m -> arg_kind gc_deps gc_stack m = ak_relevant)
  | a_proj _ y => leaf_apps_relevant y ρ
  | _ => True
  end.

Lemma leaf_term_eval_wk : forall x, leaf_term x -> forall φ ρ v, wk_mono φ ->
    leaf_apps_relevant x (⟪φ⟫ ρ) -> ⟦ x ⟧ ⟪φ⟫ ρ ↘ v -> ⟦ x[φ]ʷ ⟧ ρ ↘ v.
Proof.
  induction 1 as [n | x y Hx IHx Hy IHy | f x Hx IHx]; intros φ ρ v Hφ Hr Ev; cbn [exp_wk leaf_apps_relevant] in Hr |- *;
    inversion Ev; subst.
  - rewrite (eval_wk_eq _ _ Hφ n); apply eval_exp_var.
  - destruct Hr as (Hr & Hry & Hm).
    eapply eval_exp_app; [ apply IHx; eassumption | eassumption | apply IHy; eassumption | eassumption ].
  - destruct Hr as (Hr & Hry & Hm).
    match goal with E : ⟦ x ⟧ _ ↘ ?m, R : arg_kind _ _ ?m = ak_propositional |- _ => rewrite (Hm _ E) in R; discriminate R end.
  - econstructor; [ apply IHx; eassumption | eassumption ].
Qed.

(** A function applied to the values of terms, each partial application
    taking relevant arguments: the terms applied. *)
Lemma eval_app_args_of_apps : forall Ns ρ ns v f, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns -> $*| v & ns | gc_deps ⍮ gc_stack ↘ f ->
    (forall j g, j < List.length ns -> $*| v & List.firstn j ns | gc_deps ⍮ gc_stack ↘ g -> arg_kind gc_deps gc_stack g = ak_relevant) ->
    eval_app_args gc_deps gc_stack v Ns ρ f.
Proof.
  induction Ns as [| N Ns IH]; intros * Hns Hap Hrel; inversion Hns; subst; inversion Hap; subst; [ constructor |].
  eapply eval_app_args_evaluated; [ rewrite (Hrel 0 v ltac:(cbn; lia) ltac:(constructor)); constructor | eassumption | eassumption |].
  eapply IH; [ eassumption | eassumption |].
  intros j g' Hj Hg'; apply (Hrel (S j) g' ltac:(cbn; lia)); cbn [List.firstn]; econstructor; eassumption.
Qed.

(** Each partial application of [v] to [ys] takes relevant arguments, as
    a function of a shape's type does at the shape's domains. *)
Definition apps_relevant (v : domain) (ys : list domain) : Prop :=
  forall j g, j < List.length ys -> $*| v & List.firstn j ys | gc_deps ⍮ gc_stack ↘ g -> arg_kind gc_deps gc_stack g = ak_relevant.

(** A leaf term past [L] domains, at an environment extended by their
    values [ys], stored at any types: its value applied to them. *)
Lemma frame_arg_end_eval : forall x0 L E yts v f, leaf_term x0 -> List.length yts = L ->
    leaf_apps_relevant x0 E -> ⟦ x0 ⟧ E ↘ v -> $*| v & List.map fst yts | gc_deps ⍮ gc_stack ↘ f ->
    apps_relevant v (List.map fst yts) ->
    ⟦ apps_vars_iter L x0 ⟧ env_extend_typed E yts ↘ f.
Proof.
  intros * Hlt Lys Hra Hxv Ef Hrel.
  assert (Ew : ⟪wk_shiftn L⟫ (env_extend_typed E yts) = E) by (rewrite <- Lys; apply eval_wk_shiftn_extend_typed).
  rewrite apps_vars_iter_eq; apply eval_apps_exp; exists v; split.
  - apply (leaf_term_eval_wk _ Hlt (wk_shiftn L) (env_extend_typed E yts) v (wk_mono_shiftn _)); rewrite Ew; assumption.
  - pose proof (eval_vars_from_args yts E nil) as H0; rewrite List.app_nil_r in H0; cbn [List.length] in H0.
    rewrite Lys in H0.
    exact (eval_app_args_of_apps _ _ _ _ _ H0 Ef Hrel).
Qed.

(** Conversely, a weakened leaf term's value is the term's at the weakened
    environment. *)
Lemma leaf_term_eval_unwk : forall x, leaf_term x -> forall φ ρ v, wk_mono φ ->
    leaf_apps_relevant x (⟪φ⟫ ρ) -> ⟦ x[φ]ʷ ⟧ ρ ↘ v -> ⟦ x ⟧ ⟪φ⟫ ρ ↘ v.
Proof.
  induction 1 as [n | x y Hx IHx Hy IHy | f x Hx IHx]; intros φ ρ v Hφ Hr Ev; cbn [exp_wk leaf_apps_relevant] in Hr, Ev;
    inversion Ev; subst.
  - rewrite <- (eval_wk_eq _ _ Hφ n); apply eval_exp_var.
  - destruct Hr as (Hr & Hry & Hm).
    eapply eval_exp_app; [ apply IHx; eassumption | eassumption | apply IHy; eassumption | eassumption ].
  - destruct Hr as (Hr & Hry & Hm).
    match goal with E : ⟦ x[φ]ʷ ⟧ _ ↘ ?m, R : arg_kind _ _ ?m = ak_propositional |- _ =>
      rewrite (Hm _ (IHx φ ρ _ Hφ Hr E)) in R; discriminate R end.
  - econstructor; [ apply IHx; eassumption | eassumption ].
Qed.

(** The applications of a weakened leaf term take relevant arguments where
    the term's do at the weakened environment. *)
Lemma leaf_apps_relevant_wk : forall x, leaf_term x -> forall φ ρ, wk_mono φ ->
    leaf_apps_relevant x (⟪φ⟫ ρ) -> leaf_apps_relevant x[φ]ʷ ρ.
Proof.
  induction 1 as [n | x y Hx IHx Hy IHy | f x Hx IHx]; intros φ ρ Hφ Hr; cbn [exp_wk leaf_apps_relevant] in Hr |- *; [ exact I | | auto ].
  destruct Hr as (Hr & Hry & Hm).
  split; [ apply IHx; assumption | split; [ apply IHy; assumption |] ].
  intros m Em; exact (Hm m (leaf_term_eval_unwk x Hx φ ρ m Hφ Hr Em)).
Qed.

(** A leaf term applied to the variables of the domains past it, at an
    environment extended by their values: its applications take relevant
    arguments, those of its value to the values do. *)
Lemma leaf_apps_relevant_apps_vars : forall yts x0 E v f, leaf_term x0 ->
    leaf_apps_relevant x0 E -> ⟦ x0 ⟧ E ↘ v -> $*| v & List.map fst yts | gc_deps ⍮ gc_stack ↘ f ->
    apps_relevant v (List.map fst yts) ->
    leaf_apps_relevant (apps_vars_iter (List.length yts) x0) (env_extend_typed E yts).
Proof.
  induction yts as [| [y ty] yts IH] using List.rev_ind; intros * Hlt Hr Ev Ef Hrel; [ exact Hr |].
  rewrite List.map_app in Ef, Hrel; cbn [List.map fst] in Ef, Hrel.
  apply eval_apps_app in Ef as (fk & Efk & _).
  assert (Hrelk : apps_relevant v (List.map fst yts)).
  { intros j g Hj Eg; apply (Hrel j g ltac:(rewrite List.length_app; cbn; lia)).
    rewrite List.firstn_app; replace (j - List.length (List.map fst yts)) with 0 by lia; rewrite List.app_nil_r; exact Eg. }
  pose proof (IH x0 E v fk Hlt Hr Ev Efk Hrelk) as Hk.
  rewrite List.length_app, Nat.add_1_r, env_extend_typed_app; cbn [apps_vars_iter leaf_apps_relevant env_extend_typed List.fold_left fst snd].
  assert (Ew : ⟪↑⟫ (extend_env (env_extend_typed E yts) y ty) = env_extend_typed E yts) by (rewrite eval_wk_shift; reflexivity).
  split; [ apply leaf_apps_relevant_wk; [ apply leaf_term_apps_vars, Hlt | exact wk_mono_shift | rewrite Ew; exact Hk ] |].
  split; [ exact I |].
  intros m Em.
  pose proof (frame_arg_end_eval x0 _ E yts v fk Hlt eq_refl Hr Ev Efk Hrelk) as Ek.
  rewrite <- Ew in Ek, Hk.
  pose proof (leaf_term_eval_wk _ (leaf_term_apps_vars _ _ Hlt) ↑ _ _ wk_mono_shift Hk Ek) as Ek'.
  pose proof (functional_eval_exp _ _ _ _ Em Ek') as ->.
  apply (Hrel (List.length (List.map fst yts)) fk ltac:(rewrite List.length_app; cbn; lia)).
  rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn [List.firstn]; rewrite List.app_nil_r; exact Efk.
Qed.

(** The projections of a value at the fields [fs] and more: those of the
    non-recursive fields of [fs] are the values of their projections
    ([fields_args]). *)
Lemma eval_projections_fields : forall fs ρ x m fl' ws, ⟦ x ⟧ ρ ↘ m ->
    ⟦projs List.map fst fs ++ fl' of m ⟧ gc_deps ⍮ gc_stack ↘ ws ->
    ⟦ projections_of (fields_args fs) x ⟧* gc_deps ⍮ gc_stack ⍮ ρ
      ↘ nonrec_arg_vals (List.map snd fs) (List.firstn (List.length fs) ws).
Proof.
  induction fs as [| [g [rA A | t]] fs IH]; intros * Hx Hps; cbn [List.map fst snd fields_args projections_of List.app] in *;
    [ constructor | |]; inversion Hps; subst; cbn [List.length List.firstn nonrec_arg_vals].
  - econstructor; [ econstructor; eassumption | exact (IH _ _ _ _ _ Hx ltac:(eassumption)) ].
  - exact (IH _ _ _ _ _ Hx ltac:(eassumption)).
Qed.

Lemma nonrec_arg_vals_firstn : forall gs1 gs2 vs, List.length vs = List.length (gs1 ++ gs2) ->
    List.firstn (List.length (cargs_nonrec gs1)) (nonrec_arg_vals (gs1 ++ gs2) vs) = nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs).
Proof.
  intros * Hl; rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
  rewrite nonrec_arg_vals_app by (rewrite List.length_firstn, List.length_app in *; lia).
  apply firstn_app_exact; apply length_nonrec_arg_vals; rewrite List.length_firstn, List.length_app in *; lia.
Qed.

(** ** The Type of a Recursive Result, by its Leaf

    The type [a] of the recursive result of an argument [v] of shape [t] of
    the group [D] at the uniform parameters [u], along the leaf path [idx]
    of the shape, the values of the shape's components being [env] (the
    uniform parameters first), the motives [As] in [ρm]: at a member with a
    block, a type related to the motive at the shape's parameters and [v];
    at a domain, a [Π] over a type related to the domain's, whose family at
    each element of the domain is the type of the rest at [v]'s value
    there; at a record view, the type of the field the path goes through,
    at the projection of [v], over the uniform parameters and the
    projections of the non-recursive fields before it.  The leaf is told
    by its index, not by its path: the paths of a record view are its
    fields' moved past the arguments before ([shape_leaves]), and a moved
    term has no evaluation of its own. *)
Inductive leaf_type_at (D : ind_decl) (u : list domain) (ρm : env) (As : list exp) (Tm : nat -> list centry) :
    list domain -> list centry -> ptyp -> domain -> nat -> domain -> Prop :=
(** At the end, at a member with a block: related to the motive at the
    shape's parameters and [v], in the motive's context [Tm j] over
    [ρm] *)
| leaf_type_self : forall pre Ts j Mj Ps v bs b a (i : nat),
    ind_member D j = Some Mj -> im_is_rview Mj = false ->
    ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u Ts pre ↘ bs ->
    ⟦ List.nth j As a_prop ⟧ env_tele ρm (Tm j) (bs ++ v :: nil) ↘ b ->
    Dom a ≈ b ∈ per_univ i ->
    leaf_type_at D u ρm As Tm pre Ts (pt_self j Ps) v 0 a
(** At the end, at a record view: the type along the path [idx] of its
    recursive field after the fields [gs1], at the field's projection *)
| leaf_type_rview : forall pre Ts j Mj qr Is fl c gs gs1 tf gs2 Ps v ws w idx a,
    ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws -> gs = gs1 ++ ca_rec tf :: gs2 ->
    List.nth_error ws (List.length gs1) = Some w ->
    idx < List.length (shape_leaves (rview_leaves D) 0 tf) ->
    leaf_type_at D u ρm As Tm (nonrec_arg_vals gs1 (List.firstn (List.length gs1) ws)) (cargs_nonrec_tele gs1) tf w idx a ->
    leaf_type_at D u ρm As Tm pre Ts (pt_self j Ps) v (cargs_nrec D gs1 + idx) a
(** At a domain: a [Π] over a type related to the domain's, whose family
    at each element of the domain, stored at the [Π]'s domain, is the
    type of the rest at [v]'s value there *)
| leaf_type_pi : forall pre Ts B t v idx b0 b ρF F (i : nat),
    ⟦ B ⟧ components_env D u Ts pre ↘ b0 -> Dom b ≈ b0 ∈ per_univ i ->
    (forall c, per_head B B (components_env D u Ts pre) (components_env D u Ts pre) c c ->
       forall a' fc, ⟦ F ⟧ ρF ↦ c ⦂ entry_type_value b ↘ a' -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
       leaf_type_at D u ρm As Tm (pre ++ c :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t fc idx a') ->
    leaf_type_at D u ρm As Tm pre Ts (pt_pi B t) v idx (Πᵈ{ak_relevant} b ρF F).

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
    change (doms_ctx (B :: ptyp_doms t)) with (doms_ctx (ptyp_doms t) ++ ce_ass ak_relevant B :: nil).
    rewrite tele_sub_app, ctx_pi_app; cbn [tele_sub ctx_pi List.length sb_qn centry_sub].
    replace (sb_qn (List.length (ptyp_doms t)) (sb_q σ)) with (sb_q (sb_qn (List.length (ptyp_doms t)) σ))
      by (rewrite <- (sb_qn_plus _ 1), Nat.add_1_r; reflexivity).
    rewrite List.map_map, (List.map_ext (fun U => U[wk_shift]ʷ[wk_shiftn (List.length (ptyp_doms t))]ʷ)
                                       (fun U => U[wk_shiftn (S (List.length (ptyp_doms t)))]ʷ))
      by (intros U; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia).
    reflexivity.
Qed.

(** The record clause at a constructor, at any other constructor. *)
Ltac record_con_case :=
  match goal with
  | Hp : eval_projs _ _ ?fl (d_con _ _ _ _) _, Hp' : eval_projs _ _ ?fl (d_con _ _ _ _) _ |- _ =>
      destruct (projs_con _ _ _ _ _ _ Hp) as [-> ->]; destruct (projs_con _ _ _ _ _ _ Hp') as [_ ->];
      eapply ind_rel_record; first [ eassumption | apply eval_projs_nil ]
  | Hp : eval_projs _ _ ?fl (d_con _ _ _ _) _ |- _ =>
      destruct (projs_con _ _ _ _ _ _ Hp) as [-> ->];
      eapply ind_rel_record; first [ eassumption | apply eval_projs_nil ]
  end.

(** ** Stored Uniform Parameters

    A constructor's element relation does not read the uniform parameters
    it stores: they may be replaced, on either side. *)
Lemma ind_rel_stored_ups_r : forall p D okr nr ar dr k u u' ns ns' x hd k' c bs bs2 vs Mk,
    ind_member D k = Some Mk ->
    List.length bs = (im_unu D Mk + im_nn Mk)%nat -> List.length bs2 = List.length bs ->
    List.skipn (im_unu D Mk) bs2 = List.skipn (im_unu D Mk) bs ->
    ind_rel p D okr nr ar dr k u u' ns ns' x (d_con hd k' c (bs ++ vs)) ->
    ind_rel p D okr nr ar dr k u u' ns ns' x (d_con hd k' c (bs2 ++ vs)).
Proof.
  intros * HM Hl Hl2 Hs H.
  inversion H; subst; [| record_con_case ].
  match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end.
  match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => apply app_split_eq in E; [| lia ]; destruct E as [-> ->] end.
  eapply ind_rel_con; try eassumption; [ lia | rewrite Hs; assumption | rewrite Hs; assumption ].
Qed.

Lemma ind_rel_stored_ups_l : forall p D okr nr ar dr k u u' ns ns' y hd k' c bs bs2 vs Mk,
    ind_member D k = Some Mk ->
    List.length bs = (im_unu D Mk + im_nn Mk)%nat -> List.length bs2 = List.length bs ->
    List.skipn (im_unu D Mk) bs2 = List.skipn (im_unu D Mk) bs ->
    ind_rel p D okr nr ar dr k u u' ns ns' (d_con hd k' c (bs ++ vs)) y ->
    ind_rel p D okr nr ar dr k u u' ns ns' (d_con hd k' c (bs2 ++ vs)) y.
Proof.
  intros * HM Hl Hl2 Hs H.
  inversion H; subst; [| record_con_case ].
  match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end.
  match goal with E : (?a ++ ?b = bs ++ vs)%list |- _ => apply app_split_eq in E; [| lia ]; destruct E as [-> ->] end.
  eapply ind_rel_con; try eassumption; [ lia | rewrite Hs; assumption | rewrite Hs; assumption | rewrite Hs; assumption ].
Qed.

(** The same, the stored uniform parameters a prefix [cs] of the stored
    values. *)
Lemma app_split_prefix : forall {A : Type} (cs ms bs vs : list A), cs ++ ms = bs ++ vs -> List.length cs <= List.length bs ->
    exists m1, bs = cs ++ m1 /\ ms = m1 ++ vs.
Proof.
  intros A cs; induction cs as [| x cs IH]; intros ms bs vs Heq Hl; [ exists bs; auto |].
  destruct bs as [| y bs]; cbn in Hl; [ lia |].
  cbn in Heq; injection Heq as -> Heq.
  destruct (IH _ _ _ Heq ltac:(lia)) as (m1 & -> & ->); exists m1; auto.
Qed.

Lemma ind_rel_con_prefix_r : forall p D okr nr ar dr k u u' ns ns' x hd k' c cs cs' ms Mk,
    ind_member D k = Some Mk -> List.length cs = im_unu D Mk -> List.length cs' = List.length cs ->
    ind_rel p D okr nr ar dr k u u' ns ns' x (d_con hd k' c (cs ++ ms)) ->
    ind_rel p D okr nr ar dr k u u' ns ns' x (d_con hd k' c (cs' ++ ms)).
Proof.
  intros * HM Hl Hl' H.
  inversion H; subst; [| record_con_case ].
  match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end.
  match goal with E : (?a ++ ?b = cs ++ ms)%list, L : List.length ?a = _ |- _ =>
    destruct (app_split_prefix cs ms a b (eq_sym E) ltac:(lia)) as (m1 & -> & ->) end.
  rewrite List.app_assoc; rewrite List.app_assoc in H.
  match goal with L : List.length (cs ++ m1) = _ |- _ =>
    apply (ind_rel_stored_ups_r p D okr nr ar dr k u u' ns ns' _ hd k' c (cs ++ m1) (cs' ++ m1) vs' Mk HM L) end;
    [ rewrite !List.length_app; lia | | exact H ].
  rewrite !List.skipn_app, (List.skipn_all2 cs'), (List.skipn_all2 cs) by lia; rewrite Hl', Hl, Nat.sub_diag; reflexivity.
Qed.

Lemma ind_rel_con_prefix_l : forall p D okr nr ar dr k u u' ns ns' y hd k' c cs cs' ms Mk,
    ind_member D k = Some Mk -> List.length cs = im_unu D Mk -> List.length cs' = List.length cs ->
    ind_rel p D okr nr ar dr k u u' ns ns' (d_con hd k' c (cs ++ ms)) y ->
    ind_rel p D okr nr ar dr k u u' ns ns' (d_con hd k' c (cs' ++ ms)) y.
Proof.
  intros * HM Hl Hl' H.
  inversion H; subst; [| record_con_case ].
  match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end.
  match goal with E : (?a ++ ?b = cs ++ ms)%list, L : List.length ?a = _ |- _ =>
    destruct (app_split_prefix cs ms a b (eq_sym E) ltac:(lia)) as (m1 & -> & ->) end.
  rewrite List.app_assoc; rewrite List.app_assoc in H.
  match goal with L : List.length (cs ++ m1) = _ |- _ =>
    apply (ind_rel_stored_ups_l p D okr nr ar dr k u u' ns ns' _ hd k' c (cs ++ m1) (cs' ++ m1) vs Mk HM L) end;
    [ rewrite !List.length_app; lia | | exact H ].
  rewrite !List.skipn_app, (List.skipn_all2 cs'), (List.skipn_all2 cs) by lia; rewrite Hl', Hl, Nat.sub_diag; reflexivity.
Qed.

(** ** The Parameters of a Member, Joined at the Uniform Ones

    The converse of [params_valid_split]. *)
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
  exact (mty_vars_valid_at p D Hg Hcv k Mk nil HM (valid_ind_decl_params _ (valid_group_valid _ _ Hg) _ _ HM)).
Qed.

(** ** The Constructors Applied

    The type of a constructor of a member is valid, and so the constructor
    at terms of its parameters' and arguments' types is a term of the
    member's type there. *)
Lemma conty_valid : forall p D, valid_group p D -> containers_valid D ->
    forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    exists i : nat, ⋅ ⊨ con_ty p D k Mk gs : Typeω@i.
Proof.
  intros p D Hg Hcv k Mk c gs HM Hcon.
  pose proof (valid_group_closed _ _ Hg) as Hc.
  pose proof (valid_group_cargs_sem p D Hg Hcv k Mk c gs HM Hcon) as HΨ.
  destruct (mty_vars_valid_at p D Hg Hcv k Mk (cargs_ctx p D Mk gs) HM HΨ) as [j Hj].
  rewrite length_cargs_ctx in Hj.
  assert (Hass : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk))
    by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HM) ]).
  rewrite <- (List.app_nil_r (cargs_ctx p D Mk gs ++ im_params D Mk)) in HΨ, Hj.
  destruct (rel_exp_ctx_pi _ _ _ _ Hass HΨ Hj) as [j' Hj'].
  exists j'; unfold con_ty; rewrite <- ctx_pi_app; exact Hj'.
Qed.

Lemma con_apps_valid : forall P p D, valid_groups P -> P p D ->
    forall Γ0 k Mk c gs Us Ns As, ⊨ Γ0 -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ0 ⊨ U : T) ->
    List.length Ns = im_nn Mk ->
    (forall j N T, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Us) Ns) j = Some T ->
       Γ0 ⊨ N : T) ->
    List.length As = List.length gs ->
    (forall j N T, List.nth_error As j = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T -> Γ0 ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ0)) (Us ++ Ns ++ As) ->
    Γ0 ⊨ apps (a_con p k c) (Us ++ Ns ++ As) : ind_mty p D k Us Ns.
Proof.
  intros P p D HP HPD * HΓ0 HM Hcon HUl HUs HNl HNs HAl HAs HAss.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  pose proof (containers_valid_of_groups P HP p D HPD) as Hcv.
  pose proof (valid_group_closed _ _ Hg) as Hc.
  pose proof (valid_group_cargs_sem p D Hg Hcv k Mk c gs HM Hcon) as HΨ.
  destruct (conty_valid p D Hg Hcv k Mk c gs HM Hcon) as [j0 HT0].
  pose proof (valid_exp_under_ctx_con P p D HP HPD k Mk c gs HM Hcon j0 HT0) as HC0.
  pose proof (closed_weaken_valid _ _ _ _ HΓ0 HC0) as HC.
  unfold con_ty in HC; rewrite <- ctx_pi_app in HC.
  destruct (mty_vars_valid_at p D Hg Hcv k Mk (cargs_ctx p D Mk gs) HM HΨ) as [j Hj].
  rewrite length_cargs_ctx in Hj.
  assert (Hass : all_assumptions (cargs_ctx p D Mk gs ++ im_params D Mk))
    by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HM) ]).
  destruct (closed_app_sem _ _ Hass HΨ HΓ0) as [HCΓ _].
  pose proof (closed_app_valid _ _ _ _ _ Hass HΨ HΓ0 Hj) as HB.
  pose proof (rel_exp_apps_ctx_pi_n _ _ _ _ _ _ ((Us ++ Ns) ++ As) eq_refl Hass HCΓ HB HC) as HR.
  pose proof (params_valid_join D k Mk Γ0 Us Ns Hc HM HUl HUs HNs) as HPs.
  assert (HPl : List.length (Us ++ Ns) = im_np D Mk) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
  replace (ind_mty p D k Us Ns)
    with ((ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list Id ((Us ++ Ns) ++ As)]).
  - rewrite <- List.app_assoc in HR |- *; apply HR.
    + rewrite !List.length_app, length_cargs_ctx, length_im_params, HUl, HNl, HAl; unfold im_np; lia.
    + rewrite List.app_assoc, tele_insts_app by (try exact (member_params_ass D Hc _ _ HM); rewrite length_im_params; exact HPl).
      intros j' N T HN HT.
      assert (Hl2 : List.length (tele_insts (im_params D Mk) Id (Us ++ Ns)) = List.length (Us ++ Ns))
        by (rewrite length_tele_insts by exact (member_params_ass D Hc _ _ HM); rewrite length_im_params; lia).
      destruct (Nat.lt_ge_cases j' (List.length (Us ++ Ns))) as [Hk | Hk].
      * rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia; eauto.
      * rewrite List.nth_error_app2 in HN, HT by lia; rewrite Hl2 in HT; eauto.
    + exact HAss.
  - rewrite ind_mty_sub by (try exact Hc; apply length_ind_uvars).
    rewrite <- List.app_assoc; f_equal.
    + unfold ind_uvars.
      replace (vars_from (List.length gs + im_nn Mk) (ind_nu D)) with (vars_from (List.length (Ns ++ As)) (List.length Us))
        by (rewrite List.length_app, HNl, HAl, HUl; f_equal; lia).
      apply vars_from_sb_of_list_app.
    + replace (vars_from (List.length gs) (im_nn Mk)) with (vars_from (List.length As) (List.length Ns))
        by (rewrite HNl, HAl; reflexivity).
      apply vars_from_sb_of_list_mid.
Qed.

(** ** A Constructor along its Arguments

    The values of a constructor of a member along the arguments it is
    applied to are its [con_value]s: at a view, the container's
    constructor once all the uniform parameters are there. *)
Section ConValueApps.
  Variable (P : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups P) (HPD : P p D).
  Let Hvg := valid_groups_valid P HP p D HPD.
  Let Hcv := containers_valid_of_groups P HP p D HPD.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).

  (** The member a view views is a declared one of the container's group. *)
  Lemma view_target_decl : forall qc kc Is vm, im_head Mk = mh_view qc kc Is vm ->
      exists Dq Mk' pm, ind_lookup gc_deps gc_stack qc = Some Dq /\ ind_member Dq kc = Some Mk' /\ im_head Mk' = mh_decl pm /\
        List.length Is = ind_nu Dq.
  Proof.
    intros * Hh.
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & HMk' & Hkd & HIl & _).
    pose proof (Hcv _ _ _ _ _ _ _ HM Hh Hq) as HgQ.
    pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
    unfold im_is_decl in Hd; destruct (im_head Mk') as [pm | ? ? ? ? | ? ? ?] eqn:Hh'; [| discriminate | discriminate ].
    exists Dq, Mk', pm; auto.
  Qed.

  Lemma con_value_app : forall ys y w u, List.length ys < im_np D Mk + List.length gs ->
      con_value p D k Mk c ys w -> $| w & y | gc_deps ⍮ gc_stack ↘ u -> con_value p D k Mk c (ys ++ y :: nil) u.
  Proof.
    intros * Hlys Hw Happ.
    inversion Hw as [pm xs Hh | qc kc Is vm xs Hh Hlt | qc kc Is vm xs cs Hh Hle Ecs | qr Is fl xs Hh Hlt | qr Is fl xs Hh Hfull]; subst;
      [ | | | (** A record view's pseudo-constructor: on, or the tuple *)
          inversion Happ; subst;
          match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end;
          match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end;
          try congruence;
          match goal with H1 : im_head Mk = mh_record _ _ _ |- _ => rewrite Hh in H1; injection H1 as <- <- <- end;
          [ apply (con_value_rview _ _ _ _ _ qr Is fl); [ exact Hh | rewrite List.length_app; cbn; lia ]
          | apply (con_value_rview_full _ _ _ _ _ qr Is fl); [ exact Hh | rewrite List.length_app; cbn; lia ] ]
      | (** The tuple takes no argument *) inversion Happ ].
    - inversion Happ; subst;
        match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end;
        match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end;
        try congruence.
      exact (con_value_decl _ _ _ _ _ pm _ Hh).
    - inversion Happ; subst;
        match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end;
        match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end;
        try congruence.
      + apply (con_value_view_uparams _ _ _ _ _ qc kc Is vm); [ exact Hh | rewrite List.length_app; cbn; lia ].
      + match goal with H1 : im_head Mk = mh_view _ _ _ _ |- _ => rewrite Hh in H1; injection H1 as <- <- <- <- end.
        match goal with E : ⟦ Is ⟧* _ ⍮ _ ⍮ decl_env D (ys ++ y :: nil) ↘ ?cs0 |- _ => rename cs0 into cups; rename E into Ecups end.
        assert (Hlen : List.length (ys ++ y :: nil) = ind_nu D) by (rewrite List.length_app; cbn; lia).
        replace (d_con qc kc c cups) with (d_con qc kc c (cups ++ List.skipn (ind_nu D) (ys ++ y :: nil)))
          by (rewrite List.skipn_all2, List.app_nil_r by lia; reflexivity).
        apply (con_value_view _ _ _ _ _ qc kc Is vm); [ exact Hh | lia |].
        rewrite List.firstn_all2 by lia; exact Ecups.
    - destruct (view_target_decl _ _ _ _ Hh) as (Dq & Mk' & pm & Hq & HMk' & Hh' & HIl).
      inversion Happ; subst;
        match goal with H1 : ind_lookup _ _ qc = Some ?D1 |- _ => rewrite Hq in H1; injection H1 as <- end;
        match goal with H1 : ind_member Dq kc = Some ?M1 |- _ => rewrite HMk' in H1; injection H1 as <- end;
        try congruence.
      replace ((cs ++ List.skipn (ind_nu D) ys) ++ y :: nil) with (cs ++ List.skipn (ind_nu D) (ys ++ y :: nil))
        by (rewrite List.skipn_app, <- List.app_assoc; f_equal; f_equal;
            replace (ind_nu D - List.length ys) with 0 by lia; reflexivity).
      apply (con_value_view _ _ _ _ _ qc kc Is vm); [ exact Hh | rewrite List.length_app; lia |].
      rewrite List.firstn_app.
      replace (ind_nu D - List.length ys) with 0 by lia; cbn [List.firstn]; rewrite List.app_nil_r.
      exact Ecs.
  Qed.

  Lemma con_value_apps : forall zs ys w l, List.length ys + List.length zs <= im_np D Mk + List.length gs ->
      con_value p D k Mk c ys w -> $*| w & zs | gc_deps ⍮ gc_stack ↘ l -> con_value p D k Mk c (ys ++ zs) l.
  Proof.
    induction zs as [| z zs IH]; intros * Hlen Hw Happ; inversion Happ; subst.
    - rewrite List.app_nil_r; exact Hw.
    - cbn [List.length] in Hlen.
      match goal with H1 : eval_app _ _ w z ?w1, H2 : eval_apps _ _ ?w1 zs l |- _ =>
        pose proof (con_value_app ys z w w1 ltac:(lia) Hw H1) as Hw1;
        pose proof (IH (ys ++ z :: nil) w1 l ltac:(rewrite List.length_app; cbn; lia) Hw1 H2) as H end.
      rewrite <- List.app_assoc in H; exact H.
  Qed.

  (** The kind of the [n]-th value the constructor takes: a parameter's tag
      ([tele_param_kind]), then the argument's, as [con_value_arg_kind]
      reads it off the constructor's values. *)
  Definition con_entry_kind (n : nat) : abs_kind :=
    if Nat.ltb n (im_np D Mk) then tele_param_kind (List.rev (im_params D Mk)) n else con_arg_kind Mk c (n - im_np D Mk).

  (** Past the [n]-th element of the elements past the first [n]: those
      past the first [n + 1]. *)
  Lemma tl_skipn : forall {A} n (l : list A), List.tl (List.skipn n l) = List.skipn (n + 1) l.
  Proof. induction n as [| n IH]; intros [| x l]; cbn; try reflexivity; exact (IH l). Qed.

  (** The kinds of all the values the constructor takes, in order: its
      parameters' tags, then its arguments'. *)
  Definition con_kinds : list abs_kind :=
    List.map (tele_param_kind (List.rev (im_params D Mk))) (List.seq 0 (im_np D Mk)) ++ cargs_kinds gs.

  (** The parameters are taken at evaluated kinds. *)
  Lemma con_kinds_params : forall j, j < im_np D Mk -> evaluated_kind (List.nth j con_kinds ak_relevant).
  Proof.
    intros j Hj; unfold con_kinds.
    rewrite List.app_nth1 by (rewrite List.length_map, List.length_seq; exact Hj).
    rewrite (List.nth_indep _ _ (tele_param_kind (List.rev (im_params D Mk)) 0)) by (rewrite List.length_map, List.length_seq; exact Hj).
    rewrite List.map_nth; apply tele_param_kind_evaluated.
  Qed.

  (** The head of the values past the first [n]: the [n]-th. *)
  Lemma hd_skipn : forall {A} (d : A) n l, List.hd d (List.skipn n l) = List.nth n l d.
  Proof. intros A d; induction n as [| n IH]; intros [| x l]; cbn; try reflexivity; exact (IH l). Qed.

  (** The kind of the [n]-th value is the one [con_value_arg_kind] reads
      off. *)
  Lemma con_kinds_hd : forall n, n < im_np D Mk + List.length gs ->
      List.hd ak_relevant (List.skipn n con_kinds) = con_entry_kind n.
  Proof.
    intros * Hn; rewrite hd_skipn; unfold con_kinds, con_entry_kind.
    destruct (Nat.ltb_spec n (im_np D Mk)).
    - rewrite List.app_nth1 by (rewrite List.length_map, List.length_seq; exact H).
      rewrite (List.nth_indep _ _ (tele_param_kind (List.rev (im_params D Mk)) 0)) by (rewrite List.length_map, List.length_seq; exact H).
      rewrite List.map_nth, List.seq_nth by exact H; reflexivity.
    - rewrite List.app_nth2 by (rewrite List.length_map, List.length_seq; exact H); rewrite List.length_map, List.length_seq.
      unfold con_arg_kind, cargs_kinds; rewrite Hcon.
      destruct (nth_error_lt_some gs (n - im_np D Mk) ltac:(lia)) as [g Hg].
      rewrite (List.nth_error_nth _ _ _ (List.map_nth_error _ _ _ Hg)), Hg; destruct g; reflexivity.
  Qed.

  (** The constructor's values along terms: the values it is applied to,
      the terms' at its relevant entries, the proof at its propositional
      ones. *)
  Lemma con_value_app_args_sorted : forall Ms ys w ρ l,
      List.length ys + List.length Ms <= im_np D Mk + List.length gs ->
      con_value p D k Mk c ys w -> eval_app_args gc_deps gc_stack w Ms ρ l ->
      exists zs, eval_field_vals gc_deps gc_stack (List.skipn (List.length ys) con_kinds) Ms ρ zs /\
        con_value p D k Mk c (ys ++ zs) l.
  Proof.
    induction Ms as [| M Ms IH]; intros * Hlen Hw Ea; inversion Ea; subst.
    - exists nil; split; [ constructor | rewrite List.app_nil_r; exact Hw ].
    - cbn [List.length] in Hlen.
      match goal with Har : evaluated_kind (arg_kind _ _ w), En : ⟦ M ⟧ _ ⍮ _ ⍮ ρ ↘ ?n, Eg : eval_app _ _ w ?n ?g0,
                      Er : eval_app_args _ _ ?g0 Ms ρ l |- _ =>
        destruct (IH (ys ++ n :: nil) g0 ρ l ltac:(rewrite List.length_app; cbn [List.length]; lia)
                    (con_value_app ys n w g0 ltac:(lia) Hw Eg) Er) as (zs & Ezs & Hl0);
        exists (n :: zs); split; [| rewrite <- List.app_assoc in Hl0; exact Hl0 ];
        rewrite (con_value_arg_kind P p D HP HPD k Mk c gs HM Hcon ys w ltac:(lia) Hw) in Har;
        eapply eval_field_vals_evaluated; [ rewrite con_kinds_hd by lia; exact Har | exact En |];
        rewrite List.length_app in Ezs; cbn [List.length] in Ezs;
        rewrite tl_skipn, <- Nat.add_1_r; exact Ezs end.
    - cbn [List.length] in Hlen.
      match goal with Har : arg_kind _ _ w = ak_propositional, Eg : eval_app _ _ w ⋆ᵈ⟨M, ρ⟩ ?g0,
                      Er : eval_app_args _ _ ?g0 Ms ρ l |- _ =>
        destruct (IH (ys ++ ⋆ᵈ⟨M, ρ⟩ :: nil) g0 ρ l ltac:(rewrite List.length_app; cbn [List.length]; lia)
                    (con_value_app ys ⋆ᵈ⟨M, ρ⟩ w g0 ltac:(lia) Hw Eg) Er) as (zs & Ezs & Hl0);
        exists (⋆ᵈ⟨M, ρ⟩ :: zs); split; [| rewrite <- List.app_assoc in Hl0; exact Hl0 ];
        rewrite (con_value_arg_kind P p D HP HPD k Mk c gs HM Hcon ys w ltac:(lia) Hw) in Har;
        eapply eval_field_vals_proof; [ rewrite con_kinds_hd by lia; exact Har |];
        rewrite List.length_app in Ezs; cbn [List.length] in Ezs;
        rewrite tl_skipn, <- Nat.add_1_r; exact Ezs end.
  Qed.

  (** And so at given values of the terms of those sorts: the
      constructor's values along them. *)
  Lemma con_value_app_args_values : forall Ms zs ys w ρ l,
      List.length ys + List.length Ms <= im_np D Mk + List.length gs ->
      con_value p D k Mk c ys w -> eval_field_vals gc_deps gc_stack (List.skipn (List.length ys) con_kinds) Ms ρ zs ->
      eval_app_args gc_deps gc_stack w Ms ρ l -> con_value p D k Mk c (ys ++ zs) l.
  Proof.
    intros * Hlen Hw Ezs Ea.
    destruct (con_value_app_args_sorted Ms ys w ρ l Hlen Hw Ea) as (zs' & Ezs' & Hzs').
    pose proof (functional_eval_field_vals _ _ _ _ _ Ezs Ezs') as ->; exact Hzs'.
  Qed.

  (** The constructor's values along its parameters, which it takes
      relevantly: their values applied. *)
  Lemma con_value_app_args_params : forall Us ys w ρ g,
      List.length ys + List.length Us <= im_np D Mk ->
      con_value p D k Mk c ys w -> eval_app_args gc_deps gc_stack w Us ρ g ->
      exists us, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ us /\ con_value p D k Mk c (ys ++ us) g.
  Proof.
    induction Us as [| U Us IH]; intros * Hlen Hw Ea; inversion Ea; subst.
    - exists nil; split; [ constructor | rewrite List.app_nil_r; exact Hw ].
    - cbn [List.length] in Hlen.
      match goal with En : ⟦ U ⟧ _ ⍮ _ ⍮ ρ ↘ ?n, Eg : eval_app _ _ w ?n ?g0, Er : eval_app_args _ _ ?g0 Us ρ g |- _ =>
        destruct (IH (ys ++ n :: nil) g0 ρ g ltac:(rewrite List.length_app; cbn [List.length]; lia)
                    (con_value_app ys n w g0 ltac:(lia) Hw Eg) Er) as (us & Eus & Hg);
        exists (n :: us); split; [ econstructor; eassumption | rewrite <- List.app_assoc in Hg; exact Hg ] end.
    - cbn [List.length] in Hlen.
      match goal with Har : arg_kind _ _ w = ak_propositional |- _ =>
        rewrite (con_value_arg_kind P p D HP HPD k Mk c gs HM Hcon ys w ltac:(lia) Hw) in Har;
        revert Har; destruct (Nat.ltb_spec (List.length ys) (im_np D Mk)); [ intros Ep; exfalso; exact (tele_param_kind_not_propositional _ _ Ep) | lia ] end.
  Qed.

  (** The value of the constructor applied to all its parameters and
      arguments, at their values of the constructor's sorts. *)
  Lemma con_apps_value : forall ρ Ms zs l, im_is_rview Mk = false ->
      eval_field_vals gc_deps gc_stack con_kinds Ms ρ zs ->
      List.length Ms = im_np D Mk + List.length gs ->
      ⟦ apps (a_con p k c) Ms ⟧ ρ ↘ l ->
      exists cs, List.length cs = im_unu D Mk /\
        l = d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c (cs ++ List.skipn (ind_nu D) zs).
  Proof.
    intros * Hrv Ezs HlM El.
    apply eval_apps_exp in El as (f & Ef & Ea).
    destruct (con_value_start P p D HP HPD k Mk c HM ρ) as (f0 & Ef0 & Hf0).
    pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
    pose proof (Mctt.Core.Completeness.Records.Model.eval_field_vals_length _ _ _ _ Ezs) as Lzs.
    pose proof (con_value_app_args_values Ms zs nil f0 ρ l ltac:(cbn; lia) Hf0 Ezs Ea) as Hl0; cbn [List.app] in Hl0.
    exact (con_value_full p D k Mk c gs zs l Hrv ltac:(lia) Hl0).
  Qed.

  (** The application has values of the constructor's sorts. *)
  Lemma con_apps_sorted : forall ρ Ms l,
      List.length Ms = im_np D Mk + List.length gs ->
      ⟦ apps (a_con p k c) Ms ⟧ ρ ↘ l ->
      exists zs, eval_field_vals gc_deps gc_stack con_kinds Ms ρ zs.
  Proof.
    intros * HlM El.
    apply eval_apps_exp in El as (f & Ef & Ea).
    destruct (con_value_start P p D HP HPD k Mk c HM ρ) as (f0 & Ef0 & Hf0).
    pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
    destruct (con_value_app_args_sorted Ms nil f0 ρ l ltac:(cbn; lia) Hf0 Ea) as (zs & Ezs & _).
    exists zs; exact Ezs.
  Qed.
End ConValueApps.

(** Past the uniform parameters, a member's parameters are relevant
    ([tele_param_kind_nparams]): the kinds its constructor takes there are
    the rest of them, relevant, then the arguments'. *)
Lemma con_kinds_skipn : forall D k Mk gs, decl_typed gc_deps gc_stack D -> ind_member D k = Some Mk ->
    forall n, ind_nu D <= n -> n <= im_np D Mk ->
    List.skipn n (con_kinds D Mk gs) = List.repeat ak_relevant (im_np D Mk - n) ++ cargs_kinds gs.
Proof.
  intros D k Mk gs Hdt HM n Hu Hn; unfold con_kinds.
  replace (im_np D Mk) with (n + (im_np D Mk - n)) at 1 by lia.
  rewrite List.seq_app, List.map_app, <- List.app_assoc, List.skipn_app, List.skipn_all2, List.length_map, List.length_seq, Nat.sub_diag
    by (rewrite List.length_map, List.length_seq; lia).
  cbn [List.skipn List.app]; f_equal.
  apply (List.nth_ext _ _ ak_relevant ak_relevant); [ rewrite List.length_map, List.length_seq, List.repeat_length; reflexivity |].
  intros j Hj; rewrite List.length_map, List.length_seq in Hj.
  rewrite List.nth_repeat, (List.nth_indep _ _ (tele_param_kind (List.rev (im_params D Mk)) 0))
    by (rewrite List.length_map, List.length_seq; exact Hj).
  rewrite List.map_nth, List.seq_nth by exact Hj.
  first [ apply (tele_param_kind_nparams _ _ _ Hdt _ _ _ HM) | symmetry; apply (tele_param_kind_nparams _ _ _ Hdt _ _ _ HM) ]; lia.
Qed.

(** A declared member's constructor along its arguments. *)
Lemma eval_apps_con_decl : forall qh Dq kq Mq pm c gs' ys xs, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm -> ind_con Mq c = Some gs' ->
    List.length xs + List.length ys <= im_np Dq Mq + List.length gs' ->
    $*| d_con qh kq c xs & ys | gc_deps ⍮ gc_stack ↘ d_con qh kq c (xs ++ ys).
Proof.
  intros qh Dq kq Mq pm c gs'; induction ys as [| y ys IH]; intros xs Hq HM Hh Hcon Hlen; [ rewrite List.app_nil_r; constructor |].
  econstructor; [ eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | cbn in Hlen; lia ] |].
  replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
  apply IH; [ exact Hq | exact HM | exact Hh | exact Hcon | rewrite List.length_app; cbn in *; lia ].
Qed.

(** A declared member's constructor takes its parameters relevantly: the
    values of the terms, applied. *)
Lemma eval_app_args_con_decl_params : forall qh Dq kq Mq pm c gs' Ns ρ ns xs, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm -> ind_con Mq c = Some gs' ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns -> List.length xs + List.length Ns <= im_np Dq Mq ->
    eval_app_args gc_deps gc_stack (d_con qh kq c xs) Ns ρ (d_con qh kq c (xs ++ ns)).
Proof.
  intros qh Dq kq Mq pm c gs'; induction Ns as [| N Ns IH]; intros ρ ns xs Hq HM Hh Hcon Ens Hlen;
    inversion Ens as [| ? ? n ? ms En Ems]; subst; [ rewrite List.app_nil_r; constructor |].
  cbn [List.length] in Hlen.
  eapply eval_app_args_evaluated;
    [ cbn [arg_kind]; rewrite Hq, HM; unfold con_param_count; rewrite Hh;
      destruct (Nat.ltb_spec (List.length xs) (im_np Dq Mq)); [ apply tele_param_kind_evaluated | lia ]
    | exact En | eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ] |].
  replace (xs ++ n :: ms) with ((xs ++ n :: nil) ++ ms) by (rewrite <- List.app_assoc; reflexivity).
  apply IH; [ exact Hq | exact HM | exact Hh | exact Hcon | exact Ems | rewrite List.length_app; cbn [List.length]; lia ].
Qed.

(** A declared member's constructor along its parameters: their values,
    applied. *)
Lemma eval_app_args_con_decl_params_inv : forall qh Dq kq Mq pm c gs' Ns ρ xs g, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm -> ind_con Mq c = Some gs' ->
    List.length xs + List.length Ns <= im_np Dq Mq ->
    eval_app_args gc_deps gc_stack (d_con qh kq c xs) Ns ρ g ->
    exists ns, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\ g = d_con qh kq c (xs ++ ns).
Proof.
  intros qh Dq kq Mq pm c gs'; induction Ns as [| N Ns IH]; intros ρ xs g Hq HM Hh Hcon Hlen Ea; inversion Ea; subst.
  - exists nil; rewrite List.app_nil_r; split; [ constructor | reflexivity ].
  - cbn [List.length] in Hlen.
    match goal with En : ⟦ N ⟧ _ ⍮ _ ⍮ ρ ↘ ?n, Eg : eval_app _ _ _ ?n ?g0, Er : eval_app_args _ _ ?g0 Ns ρ g |- _ =>
      assert (Eg0 : $| d_con qh kq c xs & n | gc_deps ⍮ gc_stack ↘ d_con qh kq c (xs ++ n :: nil))
        by (eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ]);
      pose proof (functional_eval_app _ _ _ _ Eg Eg0) as ->;
      destruct (IH ρ (xs ++ n :: nil) g Hq HM Hh Hcon ltac:(rewrite List.length_app; cbn [List.length]; lia) Er)
        as (ns & Ens & ->);
      exists (n :: ns); split; [ econstructor; eassumption | rewrite <- List.app_assoc; reflexivity ] end.
  - cbn [List.length] in Hlen.
    match goal with Har : arg_kind _ _ _ = ak_propositional |- _ =>
      revert Har; cbn [arg_kind]; rewrite Hq, HM; unfold con_param_count; rewrite Hh;
      destruct (Nat.ltb_spec (List.length xs) (im_np Dq Mq)); [ intros Ep; exfalso; exact (tele_param_kind_not_propositional _ _ Ep) | lia ] end.
Qed.

(** The sort of the next value a declared member's constructor takes:
    its entry's. *)
Lemma arg_kind_con_decl : forall qh Dq kq Mq pm c xs, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm ->
    arg_kind gc_deps gc_stack (d_con qh kq c xs) = con_entry_kind Dq Mq c (List.length xs).
Proof. intros * Hq HM Hh; cbn [arg_kind]; rewrite Hq, HM; unfold con_param_count; rewrite Hh; reflexivity. Qed.

(** A declared member's constructor along terms: the values it is
    applied to are of the constructor's sorts. *)
Lemma eval_app_args_con_decl_sorted : forall qh Dq kq Mq pm c gs' Ns ρ xs l, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm -> ind_con Mq c = Some gs' ->
    List.length xs + List.length Ns <= im_np Dq Mq + List.length gs' ->
    eval_app_args gc_deps gc_stack (d_con qh kq c xs) Ns ρ l ->
    exists ns, eval_field_vals gc_deps gc_stack (List.skipn (List.length xs) (con_kinds Dq Mq gs')) Ns ρ ns /\
      l = d_con qh kq c (xs ++ ns).
Proof.
  intros qh Dq kq Mq pm c gs'; induction Ns as [| N Ns IH]; intros ρ xs l Hq HM Hh Hcon Hlen Ea; inversion Ea; subst.
  - exists nil; rewrite List.app_nil_r; split; [ constructor | reflexivity ].
  - cbn [List.length] in Hlen.
    match goal with Har : evaluated_kind (arg_kind _ _ _), En : ⟦ N ⟧ _ ⍮ _ ⍮ ρ ↘ ?n, Eg : eval_app _ _ _ ?n ?g0,
                    Er : eval_app_args _ _ ?g0 Ns ρ l |- _ =>
      assert (Eg0 : $| d_con qh kq c xs & n | gc_deps ⍮ gc_stack ↘ d_con qh kq c (xs ++ n :: nil))
        by (eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ]);
      pose proof (functional_eval_app _ _ _ _ Eg Eg0) as ->;
      destruct (IH ρ (xs ++ n :: nil) l Hq HM Hh Hcon ltac:(rewrite List.length_app; cbn [List.length]; lia) Er)
        as (ns & Ens & ->);
      exists (n :: ns); split; [| rewrite <- List.app_assoc; reflexivity ];
      rewrite (arg_kind_con_decl _ _ _ _ _ _ _ Hq HM Hh) in Har;
      eapply eval_field_vals_evaluated; [ rewrite (con_kinds_hd Dq Mq c gs' Hcon) by lia; exact Har | exact En |];
      rewrite List.length_app in Ens; cbn [List.length] in Ens; rewrite tl_skipn; exact Ens end.
  - cbn [List.length] in Hlen.
    match goal with Har : arg_kind _ _ _ = ak_propositional, Eg : eval_app _ _ _ ⋆ᵈ⟨N, ρ⟩ ?g0, Er : eval_app_args _ _ ?g0 Ns ρ l |- _ =>
      assert (Eg0 : $| d_con qh kq c xs & ⋆ᵈ⟨N, ρ⟩ | gc_deps ⍮ gc_stack ↘ d_con qh kq c (xs ++ ⋆ᵈ⟨N, ρ⟩ :: nil))
        by (eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ]);
      pose proof (functional_eval_app _ _ _ _ Eg Eg0) as ->;
      destruct (IH ρ (xs ++ ⋆ᵈ⟨N, ρ⟩ :: nil) l Hq HM Hh Hcon ltac:(rewrite List.length_app; cbn [List.length]; lia) Er)
        as (ns & Ens & ->);
      exists (⋆ᵈ⟨N, ρ⟩ :: ns); split; [| rewrite <- List.app_assoc; reflexivity ];
      rewrite (arg_kind_con_decl _ _ _ _ _ _ _ Hq HM Hh) in Har;
      eapply eval_field_vals_proof; [ rewrite (con_kinds_hd Dq Mq c gs' Hcon) by lia; exact Har |];
      rewrite List.length_app in Ens; cbn [List.length] in Ens; rewrite tl_skipn; exact Ens end.
Qed.

(** And so at given values of the terms of those sorts: the values it
    is applied to. *)
Lemma eval_app_args_con_decl_values : forall qh Dq kq Mq pm c gs' Ns ρ ns xs l, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm -> ind_con Mq c = Some gs' ->
    eval_field_vals gc_deps gc_stack (List.skipn (List.length xs) (con_kinds Dq Mq gs')) Ns ρ ns ->
    List.length xs + List.length Ns <= im_np Dq Mq + List.length gs' ->
    eval_app_args gc_deps gc_stack (d_con qh kq c xs) Ns ρ l -> l = d_con qh kq c (xs ++ ns).
Proof.
  intros * Hq HM Hh Hcon Ens Hlen Ea.
  destruct (eval_app_args_con_decl_sorted _ _ _ _ _ _ _ _ _ _ _ Hq HM Hh Hcon Hlen Ea) as (ns' & Ens' & ->).
  rewrite (functional_eval_field_vals _ _ _ _ _ Ens Ens'); reflexivity.
Qed.

(** A declared member's constructor along terms: the values it takes
    after the stored values [xs] are those it takes after any [xs'] as
    long, the sort of each argument depending on its position only. *)
Lemma eval_app_args_con_decl_prefix : forall qh Dq kq Mq pm c gs' Ns ρ xs xs' l, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm -> ind_con Mq c = Some gs' ->
    List.length xs' = List.length xs -> List.length xs + List.length Ns <= im_np Dq Mq + List.length gs' ->
    eval_app_args gc_deps gc_stack (d_con qh kq c xs) Ns ρ l ->
    exists ms, l = d_con qh kq c (xs ++ ms) /\ eval_app_args gc_deps gc_stack (d_con qh kq c xs') Ns ρ (d_con qh kq c (xs' ++ ms)).
Proof.
  intros qh Dq kq Mq pm c gs'; induction Ns as [| N Ns IH]; intros ρ xs xs' l Hq HM Hh Hcon HL Hlen Ea;
    inversion Ea; subst.
  - exists nil; rewrite !List.app_nil_r; split; [ reflexivity | constructor ].
  - cbn [List.length] in Hlen.
    match goal with Har : evaluated_kind (arg_kind _ _ _), En : ⟦ N ⟧ _ ⍮ _ ⍮ ρ ↘ ?n, Eg : eval_app _ _ _ ?n ?g,
                    Er : eval_app_args _ _ ?g Ns ρ l |- _ =>
      assert (Eg0 : $| d_con qh kq c xs & n | gc_deps ⍮ gc_stack ↘ d_con qh kq c (xs ++ n :: nil))
        by (eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ]);
      pose proof (functional_eval_app _ _ _ _ Eg Eg0) as ->;
      destruct (IH ρ (xs ++ n :: nil) (xs' ++ n :: nil) l Hq HM Hh Hcon ltac:(rewrite !List.length_app, HL; reflexivity)
                  ltac:(rewrite List.length_app; cbn [List.length]; lia) Er) as (ms & -> & Er');
      exists (n :: ms); rewrite <- !List.app_assoc in *; split; [ reflexivity |];
      eapply eval_app_args_evaluated;
        [ cbn [arg_kind] in Har |- *; rewrite Hq, HM in *; rewrite HL; exact Har | exact En
        | eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ] | exact Er' ] end.
  - cbn [List.length] in Hlen.
    match goal with Har : arg_kind _ _ _ = ak_propositional, Eg : eval_app _ _ _ ⋆ᵈ⟨N, ρ⟩ ?g,
                    Er : eval_app_args _ _ ?g Ns ρ l |- _ =>
      assert (Eg0 : $| d_con qh kq c xs & ⋆ᵈ⟨N, ρ⟩ | gc_deps ⍮ gc_stack ↘ d_con qh kq c (xs ++ ⋆ᵈ⟨N, ρ⟩ :: nil))
        by (eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ]);
      pose proof (functional_eval_app _ _ _ _ Eg Eg0) as ->;
      destruct (IH ρ (xs ++ ⋆ᵈ⟨N, ρ⟩ :: nil) (xs' ++ ⋆ᵈ⟨N, ρ⟩ :: nil) l Hq HM Hh Hcon ltac:(rewrite !List.length_app, HL; reflexivity)
                  ltac:(rewrite List.length_app; cbn [List.length]; lia) Er) as (ms & -> & Er');
      exists (⋆ᵈ⟨N, ρ⟩ :: ms); rewrite <- !List.app_assoc in *; split; [ reflexivity |];
      eapply eval_app_args_proof;
        [ cbn [arg_kind] in Har |- *; rewrite Hq, HM in *; rewrite HL; exact Har
        | eapply eval_app_con; [ exact Hq | exact HM | exact Hh | exact Hcon | lia ] | exact Er' ] end.
Qed.

(** ** A View's Constructor as its Container's

    The constructor of a view at the group's uniform parameters [Us] is the
    container's at the view's instance there ([im_pre]): the two values are
    the container's constructor, their stored uniform parameters apart,
    and the elements of the member's type do not read those. *)
Lemma con_apps_view_valid : forall P p D, valid_groups P -> P p D ->
    forall Γ0 k Mk qc kc Is vm c gs Us Ms Ns, ind_member D k = Some Mk -> im_head Mk = mh_view qc kc Is vm ->
    ind_con Mk c = Some gs -> ⊨ Γ0 -> List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ0 ⊨ U : T) ->
    List.Forall (exp_scoped (List.length Γ0)) Us ->
    List.length Ms = (im_nn Mk + List.length gs)%nat ->
    Γ0 ⊨ apps (a_con p k c) (Us ++ Ms) : ind_mty p D k Us Ns ->
    Γ0 ⊨ apps (a_con qc kc c) (im_pre Mk Us ++ Ms) : ind_mty p D k Us Ns.
Proof.
  intros P p D HP HPD * HM Hh Hcon HΓ0 HUl HUs HUss HMl HL.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  pose proof (containers_valid_of_groups P HP p D HPD) as Hcv.
  pose proof (valid_group_closed _ _ Hg) as Hc; pose proof (valid_group_ass _ _ Hg) as Hass.
  destruct (view_target_decl P p D HP HPD k Mk HM qc kc Is vm Hh) as (Dq & Mk' & pm & Hq & HMk' & Hh' & HIl).
  destruct (view_con_container p D Hass (valid_group_typed _ _ Hg) k Mk qc kc Is vm Dq Mk' c gs HM Hh Hq HMk' Hcon) as (gs' & Hcon' & Hcorr).
  pose proof (cargs_correspond_len _ _ _ Hcorr) as Hlg.
  destruct (group_structure_views _ Hass k Mk qc kc Is vm HM Hh) as (Dq0 & Mc & Hq0 & HMc & Hnn & _).
  rewrite Hq in Hq0; injection Hq0 as <-; rewrite HMk' in HMc; injection HMc as <-.
  assert (Hpre : im_pre Mk Us = List.map (fun I => I[sb_of_list Id Us]) Is) by (unfold im_pre; rewrite Hh; reflexivity).
  assert (Hlpre : forall Vs, List.length (im_pre Mk Vs) = ind_nu Dq) by (intros; unfold im_pre; rewrite Hh, List.length_map; exact HIl).
  assert (Hunu : im_unu Dq Mk' = ind_nu Dq) by (unfold im_unu; rewrite Hh'; reflexivity).
  (** The instance at [Us] is valid. *)
  assert (HIv : forall j I T, List.nth_error Is j = Some I -> List.nth_error (tele_insts (ind_uparams Dq) Id Is) j = Some T ->
             Γ0 ⊨ I[sb_of_list Id Us] : T[sb_of_list Id Us]).
  { intros * HI HT.
    pose proof (valid_group_views_view_is p D Hg Hcv k Mk qc kc Is vm Dq j I T HM Hh Hq HI HT) as H.
    pose proof (closed_app_valid _ _ _ _ _ (uparams_ass D Hc) (valid_ind_decl_uparams _ (valid_group_valid _ _ Hg)) HΓ0 H) as H'.
    exact (rel_exp_under_ctx_gsub (gsub_closed_inst _ _ _ (uparams_ass D Hc) (valid_ind_decl_uparams _ (valid_group_valid _ _ Hg)) HΓ0 HUl HUs HUss) H'). }
  (** At an environment, the two values. *)
  assert (Hval : forall E Us0 Ms0 l cs', ⟦ apps (a_con p k c) (Us0 ++ Ms0) ⟧ E ↘ l -> List.length Us0 = ind_nu D ->
             List.length Ms0 = (im_nn Mk + List.length gs)%nat -> ⟦ im_pre Mk Us0 ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ cs' ->
             exists r cs ms, ⟦ apps (a_con qc kc c) (im_pre Mk Us0 ++ Ms0) ⟧ E ↘ r /\ List.length cs = ind_nu Dq /\
               List.length cs' = ind_nu Dq /\ l = d_con qc kc c (cs ++ ms) /\ r = d_con qc kc c (cs' ++ ms)).
  { intros * El HU0 HM0 Ecs'.
    apply eval_apps_exp in El as (f & Ef & Ea).
    destruct (con_value_start P p D HP HPD k Mk c HM E) as (f0 & Ef0 & Hf0).
    pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
    apply eval_app_args_app in Ea as (g & Eg & Ea).
    destruct (con_value_app_args_params P p D HP HPD k Mk c gs HM Hcon Us0 nil f0 E g
                ltac:(cbn [List.length]; unfold im_np; lia) Hf0 Eg) as (us0 & Eus0 & Hgv); cbn [List.app] in Hgv.
    pose proof (eval_exps_length _ _ _ Eus0) as Lus0.
    (** At all the uniform parameters, the container's constructor at the
        instance. *)
    inversion Hgv as [? ? Hh0 | ? ? ? ? ? Hh0 Hlt | ? ? ? ? ? cs Hh0 Hle Ecs | ? ? ? ? Hh0 _ | ? ? ? ? Hh0 _]; subst;
      rewrite Hh in Hh0; try discriminate Hh0; [ lia |].
    injection Hh0 as <- <- <- <-.
    rewrite List.skipn_all2, List.app_nil_r in Ea by lia.
    pose proof (eval_exps_length _ _ _ Ecs) as Lcs.
    pose proof (eval_exps_length _ _ _ Ecs') as Hlcs'; rewrite Hlpre in Hlcs'.
    destruct (eval_app_args_con_decl_prefix qc Dq kc Mk' pm c gs' Ms0 E cs cs' l Hq HMk' Hh' Hcon' ltac:(lia)
                ltac:(unfold im_np in *; lia) Ea) as (ms & -> & Ea').
    exists (d_con qc kc c (cs' ++ ms)), cs, ms; split; [| repeat split; first [ lia | reflexivity ] ].
    apply eval_apps_exp; exists (d_con qc kc c nil); split.
    - eapply eval_exp_con; [ exact Hq | exact HMk' | unfold im_starts, im_is_decl; rewrite Hh'; reflexivity ].
    - apply eval_app_args_app; exists (d_con qc kc c cs'); split; [| exact Ea' ].
      exact (eval_app_args_con_decl_params qc Dq kc Mk' pm c gs' (im_pre Mk Us0) E cs' nil Hq HMk' Hh' Hcon' Ecs'
               ltac:(cbn [List.length]; rewrite Hlpre; unfold im_np; lia)). }
  destruct HL as [RΓ0 HRΓ0 i Hgen].
  refine (mk_rel_exp_under_ctx _ _ _ _ RΓ0 HRΓ0 i _).
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (Hgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as (R & HT & Hor).
  exists R; split; [ exact HT | right ].
  pose proof HT as HT0.
  destruct HT as [t1 t2 t3 t4 Et1 Et2 Et3 Et4 Htc].
  (** The element relation, the container's. *)
  destruct Htc as (_ & Ht23 & _).
  assert (Hrv : im_is_rview Mk = false) by (unfold im_is_rview; rewrite Hh; reflexivity).
  destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM Hrv Et2) as (cs2 & bs2 & Ecs2 & _ & ->).
  destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM Hrv Et3) as (cs3 & bs3 & Ecs3 & _ & ->).
  (** The type is an inductive one, relevant. *)
  destruct (rel_exp_or_prop_evaluated HT0 (ex_intro _ _ (conj Et2 evaluated_kind_relevant)) Hor) as [l1 l2 l3 l4 El1 El2 El3 El4 Hlc].
  (** The instance, moved by the substitutions, at the outer environments. *)
  rewrite (ind_mty_sub _ _ _ _ _ σ Hc HUl) in Et1; rewrite (ind_mty_sub _ _ _ _ _ σ' Hc HUl) in Et4.
  destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM Hrv Et1) as (cs1 & bs1 & Ecs1 & _ & ->).
  destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM Hrv Et4) as (cs4 & bs4 & Ecs4 & _ & ->).
  unfold im_ref in Ht23; rewrite Hh in Ht23; cbn [fst snd] in Ht23.
  pose proof (eval_exps_length _ _ _ Ecs2) as Hl2; pose proof (eval_exps_length _ _ _ Ecs3) as Hl3; rewrite Hlpre in Hl2, Hl3.
  destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ Ht23 Hq Hl2 Hl3) as [_ _ _ _ _ _ _ HER].
  (** The instance's values at the four environments. *)
  assert (Hinst : forall Vs E, (forall j I T, List.nth_error Is j = Some I -> List.nth_error (tele_insts (ind_uparams Dq) Id Is) j = Some T ->
                     exists v, ⟦ I[sb_of_list Id Vs] ⟧ E ↘ v) ->
             exists cs, ⟦ im_pre Mk Vs ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ cs).
  { intros Vs E HV; apply eval_exps_each; intros j N HN.
    unfold im_pre in HN; rewrite Hh in HN; apply nth_error_map_inv in HN as (I & HI & ->).
    destruct (nth_error_lt_some' (tele_insts (ind_uparams Dq) Id Is) j) as [T HT].
    { rewrite length_tele_insts by exact (uparams_ass Dq (valid_group_closed _ _ (Hcv _ _ _ _ _ _ _ HM Hh Hq))).
      assert (j < List.length Is) by (apply List.nth_error_Some; congruence); unfold ind_nu in HIl; lia. }
    exact (HV _ _ _ HI HT). }
  assert (Hsub : forall τ, List.map (fun N => N[τ]) (im_pre Mk Us) = im_pre Mk (List.map (fun U => U[τ]) Us))
    by (intros; apply (im_pre_sub D k Mk Us); assumption).
  assert (HMl' : forall τ, List.length (List.map (fun M => M[τ]) Ms) = (im_nn Mk + List.length gs)%nat)
    by (intros; rewrite List.length_map; exact HMl).
  assert (HUl' : forall τ, List.length (List.map (fun U => U[τ]) Us) = ind_nu D) by (intros; rewrite List.length_map; exact HUl).
  rewrite apps_exp_sub, List.map_app in El1, El4; cbn [exp_sub] in El1, El4.
  destruct (Hval _ _ _ _ _ El1 (HUl' σ) (HMl' σ) Ecs1) as (r1 & ds1 & ms1 & Er1 & Lds1 & Lcs1 & -> & ->).
  destruct (Hval _ _ _ _ _ El2 HUl HMl Ecs2) as (r2 & ds2 & ms2 & Er2 & Lds2 & Lcs2 & -> & ->).
  destruct (Hval _ _ _ _ _ El3 HUl HMl Ecs3) as (r3 & ds3 & ms3 & Er3 & Lds3 & Lcs3 & -> & ->).
  destruct (Hval _ _ _ _ _ El4 (HUl' σ') (HMl' σ') Ecs4) as (r4 & ds4 & ms4 & Er4 & Lds4 & Lcs4 & -> & ->).
  (** Moving the stored uniform parameters of related elements. *)
  assert (Hsw : forall a1 a2 a1' a2' n1 n2, List.length a1 = ind_nu Dq -> List.length a2 = ind_nu Dq ->
             List.length a1' = ind_nu Dq -> List.length a2' = ind_nu Dq ->
             R (d_con qc kc c (a1 ++ n1)) (d_con qc kc c (a2 ++ n2)) -> R (d_con qc kc c (a1' ++ n1)) (d_con qc kc c (a2' ++ n2))).
  { intros * L1 L2 L1' L2' H.
    apply HER; apply HER in H.
    eapply ind_rel_con_prefix_l; [ exact HMk' | rewrite Hunu; exact L1 | lia |].
    eapply ind_rel_con_prefix_r; [ exact HMk' | rewrite Hunu; exact L2 | lia | exact H ]. }
  destruct Hlc as (H12 & H23 & H34).
  apply (mk_rel_exp (d_con qc kc c (cs1 ++ ms1)) (d_con qc kc c (cs2 ++ ms2)) (d_con qc kc c (cs3 ++ ms3)) (d_con qc kc c (cs4 ++ ms4))).
  - rewrite apps_exp_sub, List.map_app, Hsub; cbn [exp_sub]; exact Er1.
  - exact Er2.
  - exact Er3.
  - rewrite apps_exp_sub, List.map_app, Hsub; cbn [exp_sub]; exact Er4.
  - repeat split; eapply Hsw; [ | | | | eassumption | | | | | eassumption | | | | | eassumption ]; assumption.
Qed.

(** The constructor of a member as the group reads it ([im_ref]: the
    container's at a view) at the member's instance of the uniform
    parameters ([im_pre]), the non-uniform ones and the arguments. *)
Lemma con_apps_ref_valid : forall P p D, valid_groups P -> P p D ->
    forall Γ0 k Mk c gs Us Ns As, ⊨ Γ0 -> ind_member D k = Some Mk -> im_is_rview Mk = false -> ind_con Mk c = Some gs ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ0 ⊨ U : T) ->
    List.length Ns = im_nn Mk ->
    (forall j N T, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Us) Ns) j = Some T ->
       Γ0 ⊨ N : T) ->
    List.length As = List.length gs ->
    (forall j N T, List.nth_error As j = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) j = Some T -> Γ0 ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ0)) (Us ++ Ns ++ As) ->
    Γ0 ⊨ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Us ++ Ns ++ As) : ind_mty p D k Us Ns.
Proof.
  intros P p D HP HPD * HΓ0 HM Hrv Hcon HUl HUs HNl HNs HAl HAs HAss.
  pose proof (con_apps_valid P p D HP HPD Γ0 k Mk c gs Us Ns As HΓ0 HM Hcon HUl HUs HNl HNs HAl HAs HAss) as H.
  unfold im_ref; destruct (im_head Mk) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; cbn [fst snd].
  - unfold im_pre; rewrite Hh; exact H.
  - exact (con_apps_view_valid P p D HP HPD Γ0 k Mk qc kc Is vm c gs Us (Ns ++ As) Ns HM Hh Hcon HΓ0 HUl HUs
             (proj1 (proj1 (List.Forall_app _ _ _) HAss)) ltac:(rewrite List.length_app, HNl, HAl; reflexivity) H).
  - exfalso; exact (not_rview_record _ _ _ _ Hrv Hh).
Qed.

(** ** Instances of a Closed Telescope at Equal Terms

    An extension of a substitution [τ'] by a term of the entry's type at a
    substitution [τ] related to [τ']: its head commutes with the
    substitutions too ([sub_link_ass] at [τ = τ']). *)
Lemma sub_link_ass_cross : forall {Γ Δ τ τ' κ B} {i : nat} {N},
    Γ ⊨ˢ τ ≈ τ' : Δ -> sub_link Γ Δ τ' ->
    Δ ⊨ᵗ B ≈ B at i -> rel_type_evaluated Δ B -> Γ ⊨ N : B[τ] ->
    sub_link Γ (Δ ▹{κ} B) (τ' ,, N).
Proof.
  intros * Hτj Hl HB HBr HN Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  destruct HBr as (r & Hr & HBk).
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  pose proof (per_ctx_env_of_typ (κ := κ) HΔ HB) as HΔB'.
  assert (E : RΔB <~> per_env_extend B B RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  pose proof (rel_type_inversion HB) as [R0 [HΔ0 HBgen]].
  pose proof (rel_type_inversion_simple_at HΔ HB) as HBs.
  destruct (rel_sub_under_ctx_simple Hτj) as (RΓ0 & HRΓ0 & RΔ0 & HRΔ0 & Hs).
  assert (EΓ : RΓ0 <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs ρσ ρσ ltac:(apply EΓ; exact Hρσ)) as (eτ & eτ' & Eτ & Eτ' & Hττ').
  assert (EΔ : RΔ0 <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply EΔ in Hττ'.
  (** [B] is of the evaluated kind [r] at [e1], so the extension holds the
      term's value. *)
  pose proof (L _ Eτ') as He1t.
  assert (He1e1 : RΔ e1 e1) by (etransitivity; [ exact He1t | symmetry; exact He1t ]).
  destruct (HBk _ HΔ _ _ He1e1) as (b & Eb & Hrb).
  assert (Hn1 : ~ head_propositional gc_deps gc_stack (ce_ass κ B) Δ e1)
    by exact (head_not_propositional (e := ce_ass κ B) HΔ eq_refl HBs He1e1 Eb ltac:(rewrite Hrb; exact Hr)).
  (** [B[τ]] is of an evaluated kind at [ρσ]: its value is [B]'s at [τ]'s. *)
  destruct (HBgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσ Eτ Eτ') as [x1 c0 x30 x40 Hx1 Hc0 Hx30 Hx40 Hxc0].
  assert (Hrx1 : evaluated_kind (domain_kind x1)).
  { assert (Hττ : RΔ eτ eτ) by (etransitivity; [ exact Hττ' | symmetry; exact Hττ' ]).
    destruct (HBk _ HΔ _ _ Hττ) as (c1 & Ec1 & Hrc1).
    assert (c1 = c0) as -> by (eapply functional_eval_exp; eassumption).
    destruct Hxc0 as [[Rx Hx] _]; rewrite (per_univ_elem_kind _ _ _ _ Hx), Hrc1; exact Hr. }
  pose proof HN as [RΓ2 HΓ2 j HNgen].
  destruct (HNgen _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρ Hev Hev) as [R1 [HTy Hor]].
  destruct (rel_exp_or_prop_evaluated HTy (ex_intro _ x1 (conj Hx1 Hrx1)) Hor) as [n1 n2 n3 n4 Hn1e Hn2e Hn3e Hn4e Hnc].
  destruct HTy as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbc].
  exists (e1 ↦ n1 ⦂ centry_tag (ce_ass κ B) Δ e1); split.
  - apply (eval_sub_sb_eq (symmetry (sb_extend_compose _ _ _))); apply eval_sub_extend; assumption.
  - intros e2 He2.
    pose proof (eval_sub_head_exp _ _ _ _ _ _ He2 eq_refl) as Ee2h; rewrite ctx_entry_tag_head in Ee2h.
    destruct (eval_sub_extend_inv _ _ _ _ _ _ He2) as [Ht2 Hh2].
    pose proof (L _ Ht2) as Ht.
    assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]).
    destruct (HBs _ _ Ht) as (b5 & b6 & Hb5 & Hb6 & [R2 Hb56]).
    pose proof (per_univ_elem_kind _ _ _ _ Hb56) as Er56.
    assert (b5 = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hn2 : ~ head_propositional gc_deps gc_stack (ce_ass κ B) Δ e2↯)
      by (eapply (head_not_propositional (e := ce_ass κ B) HΔ eq_refl HBs He22 Hb6); rewrite <- Er56, Hrb; exact Hr).
    assert (Hm2 : ⟦ N ⟧ ρσ ↘ e2 0) by (apply Hh2; rewrite entry_propositional_zero_head; exact Hn2).
    assert (n2 = e2 0) as Hm by (eapply functional_eval_exp; eassumption).
    apply E.
    destruct (HBgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσ Eτ Ht2) as [x1' c x3 x4 Hx1' Hc Hx3 Hx4 Hxc].
    destruct Hxc as [[Rx Hxc] [[Rcx Hcx3] _]].
    assert (x1' = x1) as -> by (eapply functional_eval_exp; eassumption).
    assert (b2 = x1) as -> by (eapply functional_eval_exp; eassumption).
    destruct Hbc as [_ [Hb23 _]].
    assert (Hn12 : R1 n1 n2) by (destruct Hnc as [? _]; assumption).
    (** The heads at the relation of [B] at [τ]'s value and [e2]'s tail,
        moved to [e1] and [e2]'s tail along the context PER. *)
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Hxc Hcx3) as (R13 & H13 & _).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hb23 H13) as E1.
    pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hcx3 H13) as E2.
    assert (Hh0 : Dom n1 ≈ (e2 0) ∈ per_head B B eτ e2↯)
      by (eapply per_head_of; [ exact Hc | exact Hx3 | exact Hcx3 | rewrite <- Hm; apply E2, E1; exact Hn12 ]).
    assert (He2τ : RΔ e2↯ eτ)
      by (etransitivity; [ symmetry; exact Ht |]; etransitivity; [ exact He1t | symmetry; exact Hττ' ]).
    assert (Hh : Dom n1 ≈ (e2 0) ∈ per_head B B e1 e2↯).
    { apply (per_head_of_type_resp HΔ HB e1 e2↯ eτ e2↯); [| exact Hh0 ].
      apply rel_chain_4; [ exact Ht | exact He2τ | symmetry; exact He2τ ]. }
    destruct (per_head_closure_readable HΔB' HΔ Ht Hh) as [Hr1 Hr2].
    apply per_env_extend_intro.
    + exact Ht.
    + exact Hh.
    + intros (a0 & Ea0 & Hp); cbn in Ea0; functional_eval_rewrite_clear;
        exfalso; match goal with Hk : evaluated_kind ?κ0 |- _ => apply (evaluated_kind_not_propositional κ0 Hk); congruence end.
    + intros (a0 & Ea0 & Hp); functional_eval_rewrite_clear;
        exfalso; match goal with Hk : evaluated_kind ?κ0 |- _ => apply (evaluated_kind_not_propositional κ0 Hk); congruence end.
    + split; [ exact Hr1 | cbn; lia ].
    + rewrite Ee2h; split; [ exact Hr2 | cbn; lia ].
Qed.

(** Two instances of a closed telescope [C] of relevant types at terms
    equal at the left one's types: related, and the right one commutes
    with substitutions. *)
Lemma closed_inst_cross : forall C Γ Ms Ms', all_assumptions C -> ⊨ C -> ⊨ Γ ->
    (exists l, rel_params_evaluated ⋅ C l) ->
    List.length Ms = List.length C -> List.length Ms' = List.length C ->
    (forall k N N' T, List.nth_error Ms k = Some N -> List.nth_error Ms' k = Some N' ->
       List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N ≈ N' : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ms -> List.Forall (exp_scoped (List.length Γ)) Ms' ->
    Γ ⊨ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms' : C ++ Γ /\ sub_link Γ (C ++ Γ) (sb_of_list Id Ms').
Proof.
  induction C as [| e C IH]; intros Γ Ms Ms' HCa HC HΓ [l Hrl] Hl Hl' HMs HMss HMss'.
  - destruct Ms, Ms'; cbn in Hl, Hl'; try discriminate; cbn.
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
    split; [ exact (rel_sub_id (ex_intro _ _ HR)) | exact sub_link_id ].
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (HCa' : all_assumptions C) by (inversion HCa; assumption).
    pose proof (Hrl nil κ A C eq_refl) as HA; rewrite List.app_nil_r in HA.
    assert (Hrl' : exists l, rel_params_evaluated ⋅ C l)
      by (exists l; intros Δ1 κ' T Δ2 ->; exact (Hrl (ce_ass κ A :: Δ1) κ' T Δ2 eq_refl)).
    pose proof (rel_ctx_wf_tail HC) as HC'.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms0 & M & ->).
    destruct (List.exists_last (l := Ms') ltac:(intros ->; cbn in Hl'; discriminate)) as (Ms0' & M' & ->).
    rewrite List.length_app in Hl, Hl'; cbn in Hl, Hl'.
    assert (Hl0 : List.length Ms0 = List.length C) by lia.
    assert (Hl0' : List.length Ms0' = List.length C) by lia.
    assert (Hti : tele_insts (ce_ass κ A :: C) Id (Ms0 ++ M :: nil) = tele_insts C Id Ms0 ++ A[sb_of_list Id Ms0] :: nil).
    { change (ce_ass κ A :: C) with ((ce_ass κ A :: nil) ++ C).
      rewrite tele_insts_app by (try exact HCa'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts C Id Ms0) = List.length C) by (rewrite length_tele_insts by exact HCa'; lia).
    apply List.Forall_app in HMss as [HMss0 HMs1]; apply List.Forall_app in HMss' as [HMss0' HMs1'].
    inversion HMs1 as [| ? ? HMsc _]; inversion HMs1' as [| ? ? HMsc' _]; subst.
    destruct (IH Γ Ms0 Ms0' HCa' HC' HΓ Hrl' Hl0 Hl0') as [Hr Hlk]; [| exact HMss0 | exact HMss0' |].
    { intros k N N' T HN HN' HT.
      assert (Hk : k < List.length C) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite List.nth_error_app1 by lia; exact HN'
                     | rewrite Hti, List.nth_error_app1 by lia; exact HT ]. }
    assert (HMM : Γ ⊨ M ≈ M' : A[sb_of_list Id Ms0]).
    { apply (HMs (List.length C)); [ rewrite List.nth_error_app2, Hl0, Nat.sub_diag by lia; reflexivity
                                   | rewrite List.nth_error_app2, Hl0', Nat.sub_diag by lia; reflexivity |].
      rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity. }
    assert (HAv : rel_param_typed (C ++ Γ) A l)
      by (destruct HA as [HA | HA]; [ left | right ]; exact (closed_app_valid _ _ _ _ _ HCa' HC' HΓ HA)).
    rewrite !sb_of_list_app; cbn [sb_of_list List.app].
    split.
    + exact (rel_sub_under_ctx_extend Hr (rel_param_typed_type _ _ _ HAv) HMM HMsc HMsc').
    + exact (sub_link_ass_cross Hr Hlk (rel_param_typed_type _ _ _ HAv) (rel_param_typed_evaluated HAv)
               (rel_exp_under_ctx_refl_right HMM)).
Qed.

Lemma eval_apps_functional : forall f ys r1 r2, $*| f & ys | gc_deps ⍮ gc_stack ↘ r1 -> $*| f & ys | gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof.
  intros f ys; revert f; induction ys as [| y ys IH]; intros f r1 r2 H1 H2; inversion H1; subst; inversion H2; subst; [ reflexivity |].
  match goal with Ha : eval_app _ _ f y ?a, Hb : eval_app _ _ f y ?b |- _ => pose proof (functional_eval_app _ _ _ _ Ha Hb) as -> end.
  eauto.
Qed.

(** One more argument, at a partial application taking a relevant one. *)
Lemma apps_relevant_snoc : forall v ys y f, apps_relevant v ys -> $*| v & ys | gc_deps ⍮ gc_stack ↘ f ->
    arg_kind gc_deps gc_stack f = ak_relevant -> apps_relevant v (ys ++ y :: nil).
Proof.
  intros * Hr Ef Hf j g Hj Eg; rewrite List.length_app in Hj; cbn [List.length] in Hj.
  destruct (Nat.lt_ge_cases j (List.length ys)) as [Hlt | Hge].
  - rewrite List.firstn_app, (proj2 (Nat.sub_0_le j (List.length ys))), List.app_nil_r in Eg by lia.
    exact (Hr j g Hlt Eg).
  - assert (j = List.length ys) as -> by lia.
    rewrite List.firstn_app, Nat.sub_diag, List.firstn_all, List.app_nil_r in Eg.
    rewrite (eval_apps_functional _ _ _ _ Eg Ef); exact Hf.
Qed.

(** The value of the constructor of a member as the group reads it, at
    the member's instance of some uniform parameters and further
    arguments [Ms], at their values of the constructor's sorts: the
    constructor at some stored uniform parameters and those values. *)
Lemma con_ref_apps_value : forall P p D, valid_groups P -> P p D ->
    forall k Mk c gs ρ Us0 Ms zs l, ind_member D k = Some Mk -> im_is_rview Mk = false -> ind_con Mk c = Some gs ->
    List.length Us0 = ind_nu D ->
    eval_field_vals gc_deps gc_stack (List.skipn (ind_nu D) (con_kinds D Mk gs)) Ms ρ zs ->
    List.length Ms = (im_nn Mk + List.length gs)%nat ->
    ⟦ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Us0 ++ Ms) ⟧ ρ ↘ l ->
    exists cs, List.length cs = im_unu D Mk /\ l = d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c (cs ++ zs).
Proof.
  intros P p D HP HPD * HM Hrv Hcon HU0 Ezs HMl El.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  pose proof (Mctt.Core.Completeness.Records.Model.eval_field_vals_length _ _ _ _ Ezs) as Hlzs.
  unfold im_ref in *; unfold im_unu; destruct (im_head Mk) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; cbn [fst snd] in *;
    [| | exfalso; exact (not_rview_record _ _ _ _ Hrv Hh) ].
  - unfold im_pre in El; rewrite Hh in El.
    (** The uniform parameters' values, from the application. *)
    pose proof El as El0; apply eval_apps_exp in El0 as (f & Ef & Ea).
    destruct (con_value_start P p D HP HPD k Mk c HM ρ) as (f0 & Ef0 & Hf0).
    pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
    apply eval_app_args_app in Ea as (g & Eg & _).
    destruct (con_value_app_args_params P p D HP HPD k Mk c gs HM Hcon Us0 nil f0 ρ g
                ltac:(cbn [List.length]; unfold im_np; lia) Hf0 Eg) as (us0 & Eus0 & _).
    pose proof (eval_exps_length _ _ _ Eus0) as Hlus.
    destruct (con_apps_value P p D HP HPD k Mk c gs HM Hcon ρ (Us0 ++ Ms) (us0 ++ zs) l Hrv
                ltac:(apply Mctt.Core.Completeness.Records.Model.eval_field_vals_app; [| rewrite HU0; exact Ezs ];
                      apply Mctt.Core.Completeness.Records.Model.eval_field_vals_of_exps; [| exact Eus0 ];
                      intros j Hj; apply (con_kinds_params D Mk gs); pose proof (eval_exps_length _ _ _ Eus0);
                      unfold im_np in *; lia)
                ltac:(rewrite List.length_app, HU0, HMl; unfold im_np; lia) El)
      as (cs & Hlcs & ->).
    unfold im_ref in *; unfold im_unu in Hlcs; rewrite Hh in *; cbn [fst snd] in *.
    rewrite List.skipn_app, (List.skipn_all2 us0) by (rewrite (eval_exps_length _ _ _ Eus0); lia).
    rewrite (eval_exps_length _ _ _ Eus0), HU0, Nat.sub_diag; cbn [List.skipn List.app].
    exists cs; split; [ exact Hlcs | reflexivity ].
  - destruct (view_target_decl P p D HP HPD k Mk HM qc kc Is vm Hh) as (Dq & Mk' & pm & Hq & HMk' & Hh' & HIl).
    destruct (view_con_container p D (valid_group_ass _ _ Hg) (valid_group_typed _ _ Hg) k Mk qc kc Is vm Dq Mk' c gs HM Hh Hq HMk' Hcon)
      as (gs' & Hcon' & Hcorr).
    pose proof (cargs_correspond_len _ _ _ Hcorr) as Hlg.
    destruct (group_structure_views _ (valid_group_ass _ _ Hg) k Mk qc kc Is vm HM Hh) as (Dq0 & Mc & Hq0 & HMc & Hnn & _).
    rewrite Hq in Hq0; injection Hq0 as <-; rewrite HMk' in HMc; injection HMc as <-.
    assert (Ef0 : ⟦ a_con qc kc c ⟧ ρ ↘ d_con qc kc c nil)
      by (eapply eval_exp_con; [ exact Hq | exact HMk' | unfold im_starts, im_is_decl; rewrite Hh'; reflexivity ]).
    apply eval_apps_exp in El as (f & Ef & Ea).
    pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
    assert (Hlpre : List.length (im_pre Mk Us0) = ind_nu Dq) by (unfold im_pre; rewrite Hh, List.length_map; exact HIl).
    apply eval_app_args_app in Ea as (g & Eg & Ea).
    destruct (eval_app_args_con_decl_params_inv qc Dq kc Mk' pm c gs' (im_pre Mk Us0) ρ nil g Hq HMk' Hh' Hcon'
                ltac:(cbn [List.length]; rewrite Hlpre; unfold im_np; lia) Eg) as (us0 & Eus0 & ->).
    pose proof (eval_exps_length _ _ _ Eus0) as Hlus; cbn [List.app] in Ea.
    (** The container's arguments are of the view's sorts. *)
    assert (Hsort : List.skipn (List.length us0) (con_kinds Dq Mk' gs') = List.skipn (ind_nu D) (con_kinds D Mk gs)).
    { pose proof (containers_valid_of_groups P HP p D HPD _ _ _ _ _ _ _ HM Hh Hq) as HgQ.
      rewrite (con_kinds_skipn _ _ _ _ (valid_group_typed _ _ HgQ) HMk') by (unfold im_np in *; lia).
      rewrite (con_kinds_skipn _ _ _ _ (valid_group_typed _ _ Hg) HM) by (unfold im_np in *; lia).
      rewrite (cargs_correspond_kinds _ _ _ Hcorr); unfold im_np; f_equal; f_equal; lia. }
    rewrite (eval_app_args_con_decl_values qc Dq kc Mk' pm c gs' Ms ρ zs us0 l Hq HMk' Hh' Hcon'
               ltac:(rewrite Hsort; exact Ezs) ltac:(unfold im_np in *; lia) Ea).
    exists us0; split; [ lia | reflexivity ].
Qed.

(** The further arguments of such an application have values of the
    constructor's sorts. *)
Lemma con_ref_apps_sorted : forall P p D, valid_groups P -> P p D ->
    forall k Mk c gs ρ Us0 Ms l, ind_member D k = Some Mk -> im_is_rview Mk = false -> ind_con Mk c = Some gs ->
    List.length Us0 = ind_nu D -> List.length Ms = (im_nn Mk + List.length gs)%nat ->
    ⟦ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Us0 ++ Ms) ⟧ ρ ↘ l ->
    exists zs, eval_field_vals gc_deps gc_stack (List.skipn (ind_nu D) (con_kinds D Mk gs)) Ms ρ zs.
Proof.
  intros P p D HP HPD * HM Hrv Hcon HU0 HMl El.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  unfold im_ref in *; destruct (im_head Mk) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; cbn [fst snd] in *;
    [| | exfalso; exact (not_rview_record _ _ _ _ Hrv Hh) ].
  - unfold im_pre in El; rewrite Hh in El.
    apply eval_apps_exp in El as (f & Ef & Ea).
    destruct (con_value_start P p D HP HPD k Mk c HM ρ) as (f0 & Ef0 & Hf0).
    pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
    apply eval_app_args_app in Ea as (g & Eg & Ea).
    destruct (con_value_app_args_params P p D HP HPD k Mk c gs HM Hcon Us0 nil f0 ρ g
                ltac:(cbn [List.length]; unfold im_np; lia) Hf0 Eg) as (us0 & Eus0 & Hg0).
    pose proof (eval_exps_length _ _ _ Eus0) as Hlus; cbn [List.app] in Hg0.
    destruct (con_value_app_args_sorted P p D HP HPD k Mk c gs HM Hcon Ms us0 g ρ l
                ltac:(rewrite Hlus, HU0, HMl; unfold im_np; lia) Hg0 Ea) as (zs & Ezs & _).
    rewrite Hlus, HU0 in Ezs; exists zs; exact Ezs.
  - destruct (view_target_decl P p D HP HPD k Mk HM qc kc Is vm Hh) as (Dq & Mk' & pm & Hq & HMk' & Hh' & HIl).
    destruct (view_con_container p D (valid_group_ass _ _ Hg) (valid_group_typed _ _ Hg) k Mk qc kc Is vm Dq Mk' c gs HM Hh Hq HMk' Hcon)
      as (gs' & Hcon' & Hcorr).
    pose proof (cargs_correspond_len _ _ _ Hcorr) as Hlg.
    destruct (group_structure_views _ (valid_group_ass _ _ Hg) k Mk qc kc Is vm HM Hh) as (Dq0 & Mc & Hq0 & HMc & Hnn & _).
    rewrite Hq in Hq0; injection Hq0 as <-; rewrite HMk' in HMc; injection HMc as <-.
    assert (Ef0 : ⟦ a_con qc kc c ⟧ ρ ↘ d_con qc kc c nil)
      by (eapply eval_exp_con; [ exact Hq | exact HMk' | unfold im_starts, im_is_decl; rewrite Hh'; reflexivity ]).
    apply eval_apps_exp in El as (f & Ef & Ea).
    pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
    assert (Hlpre : List.length (im_pre Mk Us0) = ind_nu Dq) by (unfold im_pre; rewrite Hh, List.length_map; exact HIl).
    apply eval_app_args_app in Ea as (g & Eg & Ea).
    destruct (eval_app_args_con_decl_params_inv qc Dq kc Mk' pm c gs' (im_pre Mk Us0) ρ nil g Hq HMk' Hh' Hcon'
                ltac:(cbn [List.length]; rewrite Hlpre; unfold im_np; lia) Eg) as (us0 & Eus0 & ->).
    pose proof (eval_exps_length _ _ _ Eus0) as Hlus; cbn [List.app] in Ea.
    assert (Hsort : List.skipn (List.length us0) (con_kinds Dq Mk' gs') = List.skipn (ind_nu D) (con_kinds D Mk gs)).
    { pose proof (containers_valid_of_groups P HP p D HPD _ _ _ _ _ _ _ HM Hh Hq) as HgQ.
      rewrite (con_kinds_skipn _ _ _ _ (valid_group_typed _ _ HgQ) HMk') by (unfold im_np in *; lia).
      rewrite (con_kinds_skipn _ _ _ _ (valid_group_typed _ _ Hg) HM) by (unfold im_np in *; lia).
      rewrite (cargs_correspond_kinds _ _ _ Hcorr); unfold im_np; f_equal; f_equal; lia. }
    destruct (eval_app_args_con_decl_sorted qc Dq kc Mk' pm c gs' Ms ρ us0 l Hq HMk' Hh' Hcon'
                ltac:(unfold im_np in *; lia) Ea) as (zs & Ezs & _).
    exists zs; rewrite <- Hsort; exact Ezs.
Qed.

(** ** Substitutions Built from Valid Parts, Moved

    A closed telescope over [Γ] gives the telescope alone; the target of
    a substitution moves along an equation of contexts; the front of a
    list fills the context below the list's rest; and the list's last
    term is of its entry's type. *)
(** An entry of the front [C] of [C ++ Γ] that is a proposition is one
    of [C]: its type reads the entries after it in [C] only. *)
Lemma entry_propositional_app_front : forall C Γ ρ x, x < List.length C ->
    entry_propositional gc_deps gc_stack (C ++ Γ) ρ x -> entry_propositional gc_deps gc_stack C ρ x.
Proof.
  intros * Hx [T HT E HE a Ea Hp]; econstructor; [ | | exact Ea | exact Hp ].
  - unfold ctx_entry_type in *; rewrite List.nth_error_app1 in HT by lia; exact HT.
  - intros y Hy; apply HE; rewrite !List.length_skipn, List.length_app in *; lia.
Qed.

(** The identity weakening from [C ++ Γ] to a closed telescope [C] of
    assumptions is valid: it reads the front of an environment. *)
Lemma rel_wk_under_ctx_closed_drop : forall C Γ, all_assumptions C -> ⊨ C -> ⊨ Γ -> C ++ Γ ⊨ʷ wk_id : C.
Proof.
  intros * Ha HC HΓ.
  destruct (closed_app_sem _ _ Ha HC HΓ) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC]; destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  eapply rel_wk_under_ctx_intro; [ exact HRCΓ | exact HRC | | |].
  - split; [ exact (rel_wk_mono _ _ _ (rel_wk_id RC)) |].
    intros ρ ρ' Hρ; rewrite !eval_wk_id; exact (Hres _ _ HRC HRCΓ _ _ Hρ).
  - intros x Hx; cbn; rewrite List.length_app; lia.
  - intros ρ ρ' Hρ x Hx; rewrite eval_wk_id; cbn [wk_id].
    assert (HT : ctx_entry_type (C ++ Γ) x = ctx_entry_type C x)
      by (unfold ctx_entry_type; rewrite List.nth_error_app1 by lia; reflexivity).
    destruct (ctx_entry_type C x) as [T |] eqn:ET.
    + rewrite (entry_propositional_local (C ++ Γ) RCΓ ρ ρ' x T HRCΓ Hρ HT).
      exact (iff_sym (entry_propositional_local C RC ρ ρ' x T HRC (Hres _ _ HRC HRCΓ _ _ Hρ) ET)).
    + split; intros [T' HT']; congruence.
Qed.

(** A closed telescope [C] of assumptions in front of a valid context [Γ]:
    the identity is a valid substitution from [C ++ Γ] to [C], the entries
    of [Γ] dropped, since [C]'s types mention none of them. *)
Lemma gsub_closed_drop : forall C Γ, all_assumptions C -> ⊨ C -> ⊨ Γ -> gsub (C ++ Γ) Id C.
Proof.
  intros * Ha HC HΓ.
  eapply gsub_eq; [| exact sb_of_wk_id ].
  apply gsub_wk; [ exact (rel_wk_under_ctx_closed_drop _ _ Ha HC HΓ) | exact (proj1 (closed_app_sem _ _ Ha HC HΓ)) | exact HC ].
Qed.

Lemma rel_ext_under_ctx_closed : forall C Γ Ψ Ψ', all_assumptions C -> ⊨ C -> ⊨ Γ -> all_assumptions Ψ -> all_assumptions Ψ' ->
    C ⊨ˣ Ψ ≈ Ψ' -> C ++ Γ ⊨ˣ Ψ ≈ Ψ'.
Proof.
  intros * Ha HC HΓ HΨa HΨa' H.
  pose proof (rel_ext_under_ctx_gsub _ _ _ _ _ (gsub_closed_drop _ _ Ha HC HΓ) HΨa HΨa' H) as H'.
  rewrite !tele_sub_id in H'; exact H'.
Qed.

(** A link of a valid substitution at an equal target: the values at
    the two targets agree, their entries being propositions alike. *)
Lemma sub_link_conv_tgt : forall Γ Δ Δ' τ, sub_link Γ Δ τ -> Γ ⊨ˢ τ ≈ τ : Δ -> ⊨ Δ -> ⊨ Δ ≈ Δ' -> sub_link Γ Δ' τ.
Proof.
  intros * Hl Hτ HΔ Heq Γ' R' HΓ' σ σ' Hσ RΔ' HRΔ' ρ ρσ Hρ Hev.
  destruct (rel_ctx_wf_per_ctx_env HΔ) as [RΔ HRΔ].
  pose proof Heq as [Rx HRx].
  assert (Ex : RΔ <~> Rx) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HRΔ).
  destruct (Hl _ _ HΓ' _ _ Hσ _ HRΔ _ _ Hρ Hev) as (e1 & He1 & H).
  (** The value of [τ] at [ρσ], at the first target. *)
  pose proof Hτ as [RΓ HΓ RΔ0 HΔ0 _].
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  destruct (rel_sub_under_ctx_simple Hτ) as (RΓ1 & HRΓ1 & RΔ1 & HRΔ1 & Hs).
  assert (EΓ : RΓ1 <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs ρσ ρσ ltac:(apply EΓ; exact Hρσ)) as (e0 & e0' & E0 & _ & _).
  pose proof (H _ E0) as H10.
  assert (He1e1 : RΔ e1 e1) by (etransitivity; [ exact H10 | symmetry; exact H10 ]).
  assert (He0e0 : RΔ e0 e0) by (etransitivity; [ symmetry; exact H10 | exact H10 ]).
  exists (ctx_retag Δ' e1); split; [ exact (eval_sub_conv_tgt _ _ _ _ _ _ HRx (proj1 (Ex _ _) He1e1) He1) |].
  intros e2 He2.
  pose proof (eval_sub_conv_tgt _ _ _ _ _ _ HRx (proj1 (Ex _ _) He0e0) E0) as E0'.
  pose proof (functional_eval_sub _ _ _ _ _ E0' He2) as Hag.
  pose proof (proj1 (per_ctx_env_eq_iff _ _ _ _ Heq HRΔ HRΔ' _ _) H10) as H10'.
  pose proof (per_ctx_env_retag HRΔ' _ _ H10') as H10r.
  exact (per_ctx_env_resp_agree HRΔ' _ _ _ _ ltac:(intros y _; reflexivity) Hag H10r).
Qed.

Lemma gsub_conv_tgt : forall Γ τ Δ Δ', gsub Γ τ Δ -> ⊨ Δ' -> ⊨ Δ ≈ Δ' -> gsub Γ τ Δ'.
Proof.
  intros * Hg HΔ' Heq.
  destruct (gsub_props Hg) as [Hv Hl]; destruct (gsub_sem Hg) as [HΓ HΔ].
  destruct (rel_ctx_wf_per_ctx_env HΔ') as [R' HR'].
  eapply gsub_eq; [| exact (sb_compose_id_left τ) ].
  eapply gsub_comp; [ exact (gsub_id _ HΔ') | exact HΓ | exact (rel_sub_under_ctx_conv_tgt _ _ _ _ _ _ Hv HR' Heq)
                    | exact (sub_link_conv_tgt _ _ _ _ Hl Hv HΔ Heq) ].
Qed.

Lemma gsub_of_list_prefix : forall Ψ σ Ms Ns Δ G, List.length Ns = List.length Δ ->
    gsub Ψ (sb_of_list σ (Ms ++ Ns)) (Δ ++ G) -> gsub Ψ (sb_of_list σ Ms) G.
Proof.
  intros * Hl Hg.
  destruct (gsub_props Hg) as [Hv Hk]; destruct (gsub_sem Hg) as [HΨ HΔG].
  pose proof (rel_wk_under_ctx_shiftn _ _ HΔG) as Hw.
  eapply gsub_eq; [ eapply gsub_comp; [ exact (gsub_wk _ _ _ Hw HΔG (rel_ctx_wf_app_r _ _ HΔG)) | exact HΨ | exact Hv | exact Hk ] |].
  rewrite <- Hl; apply sb_shift_of_list_app.
Qed.

Lemma gsub_last_typed : forall Ψ σ Ms N κ T G, gsub Ψ (sb_of_list σ (Ms ++ N :: nil)) (G ▹{κ} T) -> Ψ ⊨ N : T[sb_of_list σ Ms].
Proof.
  intros * Hg.
  destruct (gsub_sem Hg) as [_ HGT].
  assert (Hx : G ▹{κ} T ⊨ #0 : T[wk_shift]ʷ) by (apply valid_exp_under_ctx_vlookup; [ constructor | exact HGT ]).
  pose proof (rel_exp_under_ctx_gsub Hg Hx) as H.
  rewrite sb_of_list_app in H; cbn [sb_of_list exp_sub sb_extend sentry_exp] in H.
  rewrite <- exp_sub_of_wk, exp_sub_sub in H.
  rewrite (exp_sub_sb_eq T _ (sb_of_list σ Ms)) in H by (intros z; reflexivity).
  exact H.
Qed.

(** ** The Eliminator of a Valid Group

    A group [D] filed at [p], of a valid family [P], an eliminator's
    context [Γ] and its uniform parameters [Us]. *)
(** An entry of a reversed list [l] before [C], [|l| - 1 - j] entries in:
    the [j]-th of [l], with the reversed first [j] of [l] before [C] after
    it. *)
Lemma rev_app_entry_split : forall {A} (l C Δ1 Δ2 : list A) j e, j < List.length l ->
    List.rev l ++ C = Δ1 ++ e :: Δ2 -> List.length Δ1 = List.length l - 1 - j ->
    List.nth_error l j = Some e /\ Δ2 = List.rev (List.firstn j l) ++ C.
Proof.
  intros * Hj Heq HΔ1.
  destruct (nth_error_lt_some' l j Hj) as [e0 He0].
  destruct (List.nth_error_split _ _ He0) as (l1 & l2 & -> & Hl1).
  rewrite List.rev_app_distr, <- List.app_assoc in Heq; cbn [List.rev] in Heq; rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
  rewrite List.length_app in HΔ1; cbn [List.length] in HΔ1.
  destruct (app_split_eq _ _ _ _ Heq ltac:(rewrite List.length_rev; lia)) as [_ He].
  injection He as -> <-; split; [ exact He0 |].
  rewrite List.firstn_app, (proj2 (Nat.sub_0_le j (List.length l1))), List.app_nil_r, List.firstn_all2 by lia; reflexivity.
Qed.

(** Environments extended by the same values agree past them where the
    environments do. *)
Lemma env_extend_typed_agree : forall n A A' vts, env_agree_upto n A A' ->
    env_agree_upto (List.length vts + n) (env_extend_typed A vts) (env_extend_typed A' vts).
Proof.
  intros n A A' vts; induction vts as [| [v t] vts IH] using List.rev_ind; intros H y Hy; [ exact (H y Hy) |].
  rewrite List.length_app in Hy; cbn [List.length] in Hy.
  rewrite !env_extend_typed_app; cbn [env_extend_typed List.fold_left extend_env fst snd].
  destruct y as [| y]; [ reflexivity |].
  cbn [env_entry List.nth]; exact (IH H y ltac:(lia)).
Qed.

(** Two extensions by the same values, at any types, agree up to
    retagging on the new entries. *)
Lemma env_agree_retagged_typed : forall ρ1 ρ2 vts1 vts2, List.map fst vts1 = List.map fst vts2 ->
    env_agree_retagged (List.length vts1) (env_extend_typed ρ1 vts1) (env_extend_typed ρ2 vts2).
Proof.
  intros ρ1 ρ2 vts1; induction vts1 as [| [v1 t1] vts1 IH] using List.rev_ind; intros vts2 Heq x Hx; [ cbn in Hx; lia |].
  destruct vts2 as [| [v2 t2] vts2 _] using List.rev_ind.
  { rewrite List.map_app in Heq; cbn in Heq; destruct (List.map fst vts1); discriminate. }
  rewrite !List.map_app in Heq; cbn [List.map fst] in Heq; apply List.app_inj_tail in Heq as [Heq Hv]; subst v2.
  rewrite !env_extend_typed_app; cbn [env_extend_typed List.fold_left extend_env fst snd].
  rewrite List.length_app in Hx; cbn [List.length] in Hx.
  destruct x as [| x]; [ exists t2, gunit_default; reflexivity |].
  exact (IH vts2 Heq x ltac:(lia)).
Qed.

(** An entry of an extension by typed values, among the new ones. *)
Lemma env_entry_extend_typed_lt : forall ρ vts x, x < List.length vts ->
    exists v t, List.nth_error vts (List.length vts - 1 - x) = Some (v, t) /\ env_entry (env_extend_typed ρ vts) x = de_term v t.
Proof.
  intros ρ vts; induction vts as [| [v t] vts IH] using List.rev_ind; intros x Hx; [ cbn in Hx; lia |].
  rewrite List.length_app in Hx |- *; cbn [List.length] in Hx |- *.
  rewrite env_extend_typed_app; cbn [env_extend_typed List.fold_left extend_env fst snd].
  destruct x as [| x].
  - exists v, t; split; [| reflexivity ].
    rewrite List.nth_error_app2 by lia; replace (List.length vts + 1 - 1 - 0 - List.length vts) with 0 by lia; reflexivity.
  - destruct (IH x ltac:(lia)) as (v' & t' & Hn & He); exists v', t'; split; [| exact He ].
    rewrite List.nth_error_app1 by lia; replace (List.length vts + 1 - 1 - S x) with (List.length vts - 1 - x) by lia; exact Hn.
Qed.

(** An environment whose first [n] entries are terms: entry by entry, the
    extension of its tail past them by those terms at their types. *)
Lemma env_typed_prefix : forall n ρ, (forall x, x < n -> exists v t, env_entry ρ x = de_term v t) ->
    exists vts, List.length vts = n /\ forall x, env_entry ρ x = env_entry (env_extend_typed (List.skipn n ρ) vts) x.
Proof.
  induction n as [| n IH]; intros ρ H.
  - exists nil; split; [ reflexivity | intros x; reflexivity ].
  - destruct (H 0 ltac:(lia)) as (v & t & Hv).
    destruct (IH (List.tl ρ)) as (vts & Lv & Hag).
    { intros x Hx; exact (H (S x) ltac:(lia)). }
    exists (vts ++ (v, t) :: nil); split; [ rewrite List.length_app, Lv; cbn; lia |].
    assert (Esk : List.skipn (S n) ρ = List.skipn n (List.tl ρ)) by (destruct ρ; cbn; [ destruct n; reflexivity | reflexivity ]).
    intros [| x]; rewrite env_extend_typed_app, Esk; cbn [env_extend_typed List.fold_left fst snd extend_env env_entry List.tl].
    + exact Hv.
    + exact (Hag x).
Qed.

(** The heads of an extension of an environment of [Γ] by readable typed
    values of a telescope of assumptions [K] read back at [K ++ Γ]. *)
Lemma env_heads_readable_tele_ext : forall K Γ ρ vts, all_assumptions K -> List.length vts = List.length K ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts -> env_heads_readable Γ ρ ->
    env_heads_readable (K ++ Γ) (env_extend_typed ρ vts).
Proof.
  intros * HK Hl Hr HΓ x e Hx.
  destruct (Nat.lt_ge_cases x (List.length K)) as [Hlt | Hge].
  - destruct (env_entry_extend_typed_lt ρ vts x ltac:(lia)) as (v & t & Hn & ->).
    split; [| cbn; lia ].
    pose proof (proj1 (List.Forall_forall _ _) Hr _ (List.nth_error_In _ _ Hn)) as H; exact H.
  - pose proof (env_entry_extend_typed_app ρ vts (x - List.length K)) as E.
    replace (List.length vts + (x - List.length K)) with x in E by lia; rewrite E.
    rewrite List.nth_error_app2 in Hx by lia.
    replace (List.length (List.skipn (S x) (K ++ Γ))) with (List.length (List.skipn (S (x - List.length K)) Γ))
      by (rewrite !List.length_skipn, List.length_app; lia).
    exact (HΓ _ _ Hx).
Qed.

(** The instance at [τ] of a telescope [Pre] of parameter types
    ([rel_param_typed]) over [C0]: a telescope of parameter types over
    [Γ]. *)
Lemma tele_sub_evaluated_over : forall Pre C0 Γ τ, all_assumptions Pre -> all_assumptions C0 -> ⊨ Pre ++ C0 -> ⊨ Γ ->
    gsub Γ τ (C0 ++ Γ) ->
    (forall Δ1 κ T Δ2, Pre = Δ1 ++ ce_ass κ T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ C0) T i) ->
    forall Δ1 κ T Δ2, tele_sub Pre τ = Δ1 ++ ce_ass κ T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i.
Proof.
  induction Pre as [| e Pre IH]; intros C0 Γ τ HPa HCa HP HΓ Hg Hrel Δ1 κ T Δ2 Heq; [ destruct Δ1; discriminate Heq |].
  assert (He : exists κ0 B, e = ce_ass κ0 B) by (inversion HPa as [| ? ? He _]; exact He).
  destruct He as (κ0 & B & ->).
  assert (HPa' : all_assumptions Pre) by (inversion HPa; assumption).
  pose proof (rel_ctx_wf_tail HP) as HP'.
  cbn [tele_sub centry_sub] in Heq.
  destruct Δ1 as [| e1 Δ1]; cbn [List.app] in Heq.
  - injection Heq as Hκ HeT Heq; subst T Δ2.
    destruct (Hrel nil κ0 B Pre eq_refl) as [i HB].
    exists i.
    assert (HPC : all_assumptions (Pre ++ C0)) by (apply List.Forall_app; split; assumption).
    destruct (closed_app_sem _ _ HPC HP' HΓ) as [HPCΓ _].
    rewrite <- List.app_assoc in HPCΓ.
    destruct HB as [HB | HB]; [ left | right ];
      pose proof (closed_app_valid _ _ _ _ _ HPC HP' HΓ HB) as HB'; rewrite <- List.app_assoc in HB';
      exact (rel_exp_under_ctx_gsub (gsub_qn Pre Γ τ (C0 ++ Γ) Hg HPa' HPCΓ) HB').
  - injection Heq as HeT Heq.
    exact (IH C0 Γ τ HPa' HCa HP' HΓ Hg
             (fun Δ1' κ' T' Δ2' E => Hrel (ce_ass κ0 B :: Δ1') κ' T' Δ2' ltac:(rewrite E; reflexivity)) Δ1 κ T Δ2 Heq).
Qed.

Section GroupElim.
  Variable (P : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups P) (HPD : P p D).
  Let Hvg := valid_groups_valid P HP p D HPD.
  Let Hcv := containers_valid_of_groups P HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hsu := valid_group_sort _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Ua : all_assumptions (ind_uparams D) := uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := valid_ind_decl_uparams _ HD.

  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).

  (** The uniform parameters. *)
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T)
    (HUss : List.Forall (exp_scoped (List.length Γ)) Us).
  Let τU := sb_of_list Id Us.

  Lemma gsub_U : gsub Γ τU (ind_uparams D ++ Γ).
  Proof. exact (gsub_closed_inst _ _ _ Ua Usem HΓ HUl HUs HUss). Qed.

  (** The values of [Us] at related environments, and of the instance. *)
  Lemma uniform_params_instance_values : forall B1 B2, RΓ B1 B2 -> closed_instance_values (ind_uparams D) Γ Us RU B1 B2.
  Proof.
    exact (closed_instance_values_of_sub _ _ _ _ _ Ua Usem HΓ HRΓ HRU (valid_ind_decl_uparams_evaluated _ HD) (gsub_valid gsub_U) HUl).
  Qed.

  (** The values of [Us] at related environments, related at the uniform
      parameters' telescope in the empty environment. *)
  Lemma us_vals : forall B1 B2, RΓ B1 B2 ->
      exists u1 u2, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 /\ ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 /\
        RU (decl_env D u1) (decl_env D u2).
  Proof.
    intros * HB.
    destruct (uniform_params_instance_values B1 B2 HB) as [u1 u2 Hu1 Hu2 H12 _ _].
    exists u1, u2; split; [ exact Hu1 | split; [ exact Hu2 | exact H12 ] ].
  Qed.

  (** The instance's value at an environment of [Γ]: the terms' values. *)
  Lemma uniform_params_sub_eval : forall B1 B2 u1, RΓ B1 B2 -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 ->
      ⟦ τU : ind_uparams D ++ Γ ⟧s B1 ↘ env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ B1) u1.
  Proof.
    intros * HB Hu.
    destruct (uniform_params_instance_values B1 B2 HB) as [u1' u2 Hu1 _ _ Hs _].
    pose proof (functional_eval_exps' _ _ _ _ Hu1 Hu) as ->; exact Hs.
  Qed.

  (** The instance at [Us] of a member's non-uniform parameters: parameter
      types over [Γ]. *)
  Lemma nparams_sub_evaluated : forall m Mm, ind_member D m = Some Mm ->
      forall Δ1 κ T Δ2, tele_sub (im_nparams Mm) τU = Δ1 ++ ce_ass κ T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i.
  Proof.
    intros * HMm.
    apply (tele_sub_evaluated_over _ (ind_uparams D) Γ τU (decl_closed_nparams_ass D Hc _ _ HMm) Ua
             (valid_ind_decl_params _ HD _ _ HMm) HΓ gsub_U).
    intros Δ1 κ T Δ2 E; apply (im_params_evaluated D HD m Mm HMm Δ1 κ T (Δ2 ++ ind_uparams D)).
    unfold im_params; rewrite E, <- List.app_assoc; reflexivity.
  Qed.

  (** A member's motive context at [Us]: parameter types over [Γ], the
      non-uniform parameters' instance and the member's type, a type of a
      universe. *)
  Lemma mctx_evaluated : forall m Mm, ind_member D m = Some Mm -> ⊨ elim_mctx p D m Mm Us ++ Γ ->
      forall Δ1 κ T Δ2, elim_mctx p D m Mm Us = Δ1 ++ ce_ass κ T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i.
  Proof.
    intros * HMm HMa Δ1 κ T Δ2 Heq; unfold elim_mctx in Heq, HMa.
    destruct Δ1 as [| e Δ1]; cbn [List.app] in Heq, HMa.
    - injection Heq as Hκ HeT Heq; subst T Δ2; destruct (rel_ctx_wf_ass_inv HMa) as (S & HS & HIT).
      destruct (rel_exp_univ_of_sort_relevant _ _ _ (sort_kind_type_sort _ _ HS) HIT
                  (fun ρ0 a Ea => ind_mty_relevant _ _ _ _ _ _ _ _ HMm Ea)
                  (fun ρ0 a Ea => ind_mty_not_level _ _ _ _ _ _ _ _ HMm Ea)) as [i Hi].
      exists i; left; exact Hi.
    - injection Heq as HeT Heq.
      exact (nparams_sub_evaluated m Mm HMm Δ1 κ T Δ2 Heq).
  Qed.

  (** The values of [Us] weakened past a telescope, related to those at the
      telescope's base. *)
  Lemma us_wk_vals : forall Ψ RS E, EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ RS -> ⊨ Ψ ++ Γ -> RS E E ->
      exists w u, ⟦ List.map (fun U => U[wk_shiftn (List.length Ψ)]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ w /\
        ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ⟪wk_shiftn (List.length Ψ)⟫ E ↘ u /\ RU (decl_env D w) (decl_env D u).
  Proof.
    intros * HRS HS HE.
    set (B := ⟪wk_shiftn (List.length Ψ)⟫ E).
    pose proof (rel_wk_shiftn _ _ _ _ HRS HRΓ) as Hwk.
    assert (HB : RΓ B B) by exact (rel_wk_app _ _ _ Hwk _ _ HE).
    destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
    assert (HPU : PER RUΓ) by (eapply per_env_PER; exact HRUΓ).
    pose proof (gsub_valid gsub_U) as [R1 H1 R2 H2 Hσ _].
    destruct (Hσ _ _ HRS _ (proj2 (rel_wk_morphism _ _ _ (reflexivity _) _ _ (per_ctx_env_right_irrel _ _ _ _ _ H1 HRΓ)) Hwk)
                ltac:(intros x Hx; cbn; rewrite List.length_app; lia) _ _ HE)
      as [y1 y2 y3 y4 Hy1 Hy2 Hy3 Hy4 Hch].
    assert (E2 : R2 <~> RUΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct Hch as (H12 & _); apply E2 in H12.
    (** No uniform parameter is a proposition at the instance's values. *)
    pose proof (closed_evaluated_over _ _ Ua Usem HΓ (valid_ind_decl_uparams_evaluated _ HD)) as Hrel'.
    pose proof (evaluated_entries_not_propositional _ _ _ Ua Hrel' HRUΓ _ _ H12) as Hnp1.
    pose proof (evaluated_entries_not_propositional _ _ _ Ua Hrel' HRUΓ y2 y1 ltac:(symmetry; exact H12)) as Hnp2.
    assert (HlU : List.length (List.rev (ind_uparams D)) = List.length Us) by (rewrite List.length_rev; exact (eq_sym HUl)).
    assert (HlU' : List.length (List.rev (ind_uparams D)) = List.length (List.map (fun U => U[wk_shiftn (List.length Ψ)]ʷ) Us))
      by (rewrite List.length_map; exact HlU).
    assert (Hnp1' : forall x, x < List.length (List.rev (ind_uparams D)) ->
                      ~ entry_propositional gc_deps gc_stack (List.rev (List.rev (ind_uparams D)) ++ Γ) y1 x)
      by (intros x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx; exact (Hnp1 x Hx)).
    assert (Hnp2' : forall x, x < List.length (List.rev (ind_uparams D)) ->
                      ~ entry_propositional gc_deps gc_stack (List.rev (List.rev (ind_uparams D)) ++ Γ) y2 x)
      by (intros x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx; exact (Hnp2 x Hx)).
    (** The weakened instance's values: the weakened terms', over [B]. *)
    pose proof (eval_sub_sb_eq (sb_wk_of_list_eq Us Id (wk_shiftn (List.length Ψ))) Hy1) as Hy1'.
    rewrite <- (List.rev_involutive (ind_uparams D)) in Hy1'.
    assert (Hb1 : ⟦ sb_wk Id (wk_shiftn (List.length Ψ)) : Γ ⟧s E ↘ ctx_retag Γ B).
    { pose proof (@eval_sub_of_wk gc_deps gc_stack Γ (wk_shiftn (List.length Ψ)) E (wk_mono_shiftn _)) as H.
      eapply eval_sub_sb_eq; [| exact H ]; intros x; reflexivity. }
    destruct (eval_sb_of_list_inv _ _ _ _ _ _ _ HlU' Hy1' Hnp1' Hb1) as (w & Ew & Hagw).
    (** The instance's values at [B]: the terms'. *)
    rewrite <- (List.rev_involutive (ind_uparams D)) in Hy2.
    destruct (eval_sb_of_list_inv _ _ _ _ _ _ _ HlU Hy2 Hnp2' (@eval_sub_id gc_deps gc_stack Γ B)) as (u & Eu & Hagu).
    rewrite List.length_rev in Hagw, Hagu.
    exists w, u; split; [ exact Ew | split; [ exact Eu |] ].
    pose proof (eval_exps_length _ _ _ Ew) as L1; pose proof (eval_exps_length _ _ _ Eu) as L2.
    rewrite List.length_map in L1.
    assert (H12' : RUΓ (env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ B) w)
                       (env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ B) u))
      by (eapply (per_ctx_env_resp_agree HRUΓ); [ rewrite List.length_app; exact Hagw | rewrite List.length_app; exact Hagu | exact H12 ]).
    apply (Hres _ _ HRU HRUΓ) in H12'.
    rewrite !env_extend_tagged_typed in H12'.
    assert (Lw : List.length (List.rev (ind_uparams D)) = List.length w) by (rewrite List.length_rev, L1; exact (eq_sym HUl)).
    assert (Lu : List.length (List.rev (ind_uparams D)) = List.length u) by (rewrite List.length_rev, L2; exact (eq_sym HUl)).
    pose proof (closed_env_tele _ _ _ _ _ _ nil nil Ua Usem HRU
                  ltac:(rewrite tagged_entries_length by exact Lw; rewrite L1; exact HUl)
                  ltac:(rewrite tagged_entries_length by exact Lu; rewrite L2; exact HUl) H12') as H0.
    rewrite !tagged_entries_fst in H0 by assumption; exact H0.
  Qed.

  (** Terms [Vs] of the uniform parameters' types, as an instance that
      commutes with substitutions: their values moved by [σ] at [ρ], against
      their values at the value of [σ]. *)
  Lemma vals_sub_link : forall Vs, List.length Vs = ind_nu D ->
      Γ ⊨ˢ sb_of_list Id Vs ≈ sb_of_list Id Vs : ind_uparams D ++ Γ ->
      sub_link Γ (ind_uparams D ++ Γ) (sb_of_list Id Vs) ->
      forall Γ' RΓ' σ ρ C u, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ C ->
      ⟦ Vs ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ u ->
      exists w, ⟦ List.map (fun V => V[σ]) Vs ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ w /\ RU (decl_env D w) (decl_env D u).
  Proof.
    intros * HVl Hv Hlk * HRΓ' Hσ Hρ Hev Hu.
    assert (HC : RΓ C C) by (eapply (rel_sub_under_ctx_at' Hσ HRΓ' HRΓ); eassumption).
    (** The instance's values at [C]. *)
    destruct (closed_instance_values_of_sub _ _ _ _ _ Ua Usem HΓ HRΓ HRU (valid_ind_decl_uparams_evaluated _ HD) Hv HVl C C HC)
      as [u1 u2 Hu1 _ _ Hs1 _].
    pose proof (functional_eval_exps' _ _ _ _ Hu1 Hu) as ->.
    destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
    destruct (Hlk _ _ HRΓ' _ _ Hσ _ HRUΓ _ _ Hρ Hev) as (e1 & Ee1 & He1).
    pose proof (He1 _ Hs1) as H12.
    (** No uniform parameter is a proposition at [e1]: it holds the moved
        terms' values. *)
    pose proof (closed_evaluated_over _ _ Ua Usem HΓ (valid_ind_decl_uparams_evaluated _ HD)) as Hrel'.
    pose proof (evaluated_entries_not_propositional _ _ _ Ua Hrel' HRUΓ _ _ H12) as Hnp.
    assert (Ee1' : ⟦ sb_of_list σ (List.map (fun V => V[σ]) Vs) : List.rev (List.rev (ind_uparams D)) ++ Γ ⟧s ρ ↘ e1).
    { rewrite List.rev_involutive; eapply eval_sub_sb_eq; [| exact Ee1 ].
      symmetry; etransitivity; [ apply sb_of_list_cong; intros x; reflexivity | symmetry; apply sb_of_list_compose_gen ]. }
    destruct (eval_sb_of_list_inv (List.map (fun V => V[σ]) Vs) (List.rev (ind_uparams D)) σ Γ ρ e1 C
                ltac:(rewrite List.length_rev, List.length_map; exact (eq_sym HVl)) Ee1'
                ltac:(intros x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx; exact (Hnp x Hx)) Hev)
      as (w & Hw & Hag).
    exists w; split; [ exact Hw |].
    rewrite List.length_rev in Hag.
    assert (H12' : RUΓ (env_extend_tagged Γ (List.rev (ind_uparams D)) C w)
                       (env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ C) u))
      by (eapply (per_ctx_env_resp_agree HRUΓ); [ rewrite List.length_app; exact Hag | intros y _; reflexivity | exact H12 ]).
    apply (Hres _ _ HRU HRUΓ) in H12'.
    pose proof (eval_exps_length _ _ _ Hw) as L1; pose proof (eval_exps_length _ _ _ Hu) as L2.
    rewrite List.length_map in L1.
    rewrite !env_extend_tagged_typed in H12'.
    assert (Lw : List.length (List.rev (ind_uparams D)) = List.length w) by (rewrite List.length_rev, L1; exact (eq_sym HVl)).
    assert (Lu : List.length (List.rev (ind_uparams D)) = List.length u) by (rewrite List.length_rev, L2; exact (eq_sym HVl)).
    pose proof (closed_env_tele _ _ _ _ _ _ nil nil Ua Usem HRU
                  ltac:(rewrite tagged_entries_length by exact Lw; rewrite L1; exact HVl)
                  ltac:(rewrite tagged_entries_length by exact Lu; rewrite L2; exact HVl) H12') as H0.
    rewrite !tagged_entries_fst in H0 by assumption; exact H0.
  Qed.

  (** The instances of a member's non-uniform parameters and of its
      motive's context at terms of their types. *)
  Lemma gsub_ns : forall m Mm, ind_member D m = Some Mm -> ⊨ elim_mctx p D m Mm Us ++ Γ ->
      forall Ns, List.length Ns = im_nn Mm ->
      (forall j N T0, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams Mm) τU Ns) j = Some T0 -> Γ ⊨ N : T0) ->
      List.Forall (exp_scoped (List.length Γ)) Ns ->
      gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) τU ++ Γ).
  Proof.
    intros * HMm HMa * HNl HNs HNss.
    apply gsub_of_list; [ apply gsub_id; exact HΓ | apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMm)
                        | exact (rel_ctx_wf_tail HMa) | rewrite length_tele_sub; exact HNl | | exact HNss ].
    intros j N T0 HN HT; rewrite tele_insts_tele_sub in HT.
    rewrite (tele_insts_sb_eq _ _ τU) in HT by (intros x; cbn; apply sentry_sub_id).
    exact (HNs _ _ _ HN HT).
  Qed.

  Lemma gsub_tau : forall m Mm, ind_member D m = Some Mm -> ⊨ elim_mctx p D m Mm Us ++ Γ ->
      forall Ns M, List.length Ns = im_nn Mm ->
      (forall j N T0, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams Mm) τU Ns) j = Some T0 -> Γ ⊨ N : T0) ->
      Γ ⊨ M : ind_mty p D m Us Ns ->
      List.Forall (exp_scoped (List.length Γ)) (Ns ++ M :: nil) ->
      gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D m Mm Us ++ Γ).
  Proof.
    intros * HMm HMa * HNl HNs HMv HNss.
    assert (Hrass : all_assumptions (tele_sub (im_nparams Mm) τU)) by (apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMm)).
    apply gsub_of_list; [ apply gsub_id; exact HΓ | exact (elim_mctx_ass p D m Mm Us Hc HMm) | exact HMa
                        | rewrite List.length_app, length_elim_mctx; cbn; lia | | exact HNss ].
    intros j N T0 HN HT.
    unfold elim_mctx in HT; change (ce_ass ?κ0 ?H0 :: ?R) with ((ce_ass κ0 H0 :: nil) ++ R) in HT.
    rewrite tele_insts_app in HT by (try exact Hrass; rewrite length_tele_sub; exact HNl).
    assert (Hl2 : List.length (tele_insts (tele_sub (im_nparams Mm) τU) Id Ns) = im_nn Mm)
      by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_im_nparams; lia).
    destruct (Nat.lt_ge_cases j (im_nn Mm)) as [Hk | Hk].
    - rewrite List.nth_error_app1 in HN by lia.
      rewrite List.nth_error_app1 in HT by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_im_nparams; lia).
      rewrite tele_insts_tele_sub in HT.
      rewrite (tele_insts_sb_eq _ _ τU) in HT by (intros x; cbn; apply sentry_sub_id).
      exact (HNs _ _ _ HN HT).
    - rewrite List.nth_error_app2 in HN by lia.
      rewrite List.nth_error_app2 in HT by (rewrite length_tele_insts by exact Hrass; rewrite length_tele_sub, length_im_nparams; lia).
      rewrite HNl in HN; rewrite length_tele_insts, length_tele_sub, length_im_nparams, HNl, Nat.min_id in HT by exact Hrass.
      destruct (j - im_nn Mm) as [| j'] eqn:Hk'; cbn in HN, HT; [| destruct j'; discriminate ].
      injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
      rewrite ind_head_inst by (try exact Hc; try exact HUl; exact HNl).
      rewrite (List.map_ext (fun U => U[Id]) (fun U => U)), List.map_id by (intros; apply exp_sub_id).
      exact HMv.
  Qed.

  (** The uniform parameters' values, as arguments of their telescope. *)
  Lemma U_tele_args : forall a b, RU (decl_env D a) (decl_env D b) -> List.length a = ind_nu D -> List.length b = ind_nu D ->
      per_tele_args (List.rev (ind_uparams D)) nil nil a b.
  Proof. intros * H La Lb; exact (uparams_of_env D HD Hc a b RU HRU La Lb H). Qed.

  (** ** The Arguments Before a Position, Weakened to Their Non-Recursive
      Ones, over [Γ] *)
  Lemma cargs_wk_ext : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> forall gs1 gs2, gs = gs1 ++ gs2 ->
      cargs_ctx p D Mk gs1 ++ im_params D Mk ++ Γ ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk ++ Γ.
  Proof.
    intros k Mk c gs HMk Hcon.
    pose proof (valid_group_cargs_sem p D Hvg Hcv k Mk c gs HMk Hcon) as HΨ.
    pose proof (member_params_ass D Hc _ _ HMk) as HPa.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_nonrec_ctx cargs_pat List.rev List.map List.app].
      destruct (closed_app_sem _ _ HPa (valid_ind_decl_params _ HD _ _ HMk) HΓ) as [HPΓ _].
      destruct (rel_ctx_wf_per_ctx_env HPΓ) as [R HR].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) | intros x Hx; exact Hx |].
      intros ρ ρ' _ x _; cbn [wk_pat]; change (fun x0 : nat => x0) with wk_id; rewrite eval_wk_id; reflexivity.
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as IHw.
      pose proof (cargs_prefix_sem D p Mk gs HΨ (gs1 ++ g :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as HC.
      assert (HCa : all_assumptions (cargs_ctx p D Mk (gs1 ++ g :: nil) ++ im_params D Mk))
        by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HPa ]).
      destruct (closed_app_sem _ _ HCa HC HΓ) as [HCΓ _].
      rewrite <- List.app_assoc in HCΓ.
      rewrite cargs_ctx_snoc, cargs_pat_snoc in *.
      destruct g as [rA A0 | t]; cbn [cargs_ctx_aux List.app wk_pat] in *.
      + rewrite cargs_nonrec_ctx_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A0)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        pose proof (nonrec_kind_at gs1 gs2 rA A0) as Hr; rewrite <- Heq in Hr.
        destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HMk Hcon HA Hr) as (_ & j & HAv).
        assert (HSs : ⊨ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)
          by (apply (valid_ind_decl_nonrec_prefixes _ HD _ _ _ _ _ HMk Hcon); rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
        rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HAv, HSs.
        assert (HSa : all_assumptions (cargs_nonrec_ctx gs1 ++ im_params D Mk))
          by (apply List.Forall_app; split; [ rewrite cargs_nonrec_ctx_rev_tele; apply List.Forall_rev, all_assumptions_cargs_nonrec_tele | exact HPa ]).
        pose proof (closed_app_valid _ _ _ _ _ HSa HSs HΓ HAv) as HAv'.
        rewrite <- List.app_assoc in HAv'.
        exact (rel_wk_under_ctx_q IHw (rel_type_of_abs_kind_sort HAv')).
      + rewrite cargs_nonrec_ctx_snoc_rec.
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HCΓ) IHw).
  Qed.

  (** ** The Fields of a Record View, over [Γ]

      At a record view [Mj], an argument [x] of its type at [σv]: the
      projections of its fields fill the view's constructor's arguments,
      each projection at the record's field type ([valid_exp_under_ctx_proj])
      and the record view equation ([valid_group_views_rview_fields]) turning that
      telescope into the arguments; the projection of a recursive field is
      an argument of the field's shape, at the projections before it. *)
  Lemma rview_fields_gsub : forall Ψ j Mj qr Is fl c gs σv x,
      ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
      gsub Ψ σv (ind_uparams D ++ Γ) ->
      Ψ ⊨ x : apps_exp (a_record qr) (List.map (fun I => I[σv]) Is) -> exp_scoped (List.length Ψ) x ->
      gsub Ψ (sb_of_list σv (projections_of fl x)) (cargs_ctx p D Mj gs ++ ind_uparams D ++ Γ).
  Proof.
    intros * Hj Hh Hcs Hσv Hx Hxs.
    assert (HNss : List.Forall (exp_scoped (List.length Ψ)) (List.map (fun I => I[σv]) Is)).
    { pose proof (gsub_valid Hσv) as [_ _ _ _ _ Hσs].
      apply List.Forall_map; eapply List.Forall_impl; [| exact (decl_closed_rhead_scoped _ Hc _ _ _ _ _ Hj Hh) ].
      intros I HI; eapply exp_scoped_sub; [ exact HI |].
      intros z Hz; apply (proj1 (Hσs z ltac:(rewrite List.length_app; unfold ind_nu in Hz; lia))). }
    destruct (valid_group_records _ _ Hvg _ _ _ _ _ Hj Hh) as [R HR].
    pose proof HR as [HlR HRv HRc HRt].
    pose proof HRv as [_ HPr HS HF HT HFk].
    pose proof (typed_params_ass _ _ _ HRt) as HaR.
    pose proof (record_typed_sort_univ _ _ _ HRt) as HsuR.
    destruct (gsub_sem Hσv) as [HΨ _].
    set (Ns := List.map (fun I => I[σv]) Is) in *.
    assert (HNl : List.length Ns = List.length (record_params R))
      by (unfold Ns; rewrite List.length_map; exact (rview_record_len p D Hvg _ _ _ _ _ _ Hj Hh HR)).
    assert (HNs : forall k N T, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some T ->
               Ψ ⊨ N : T).
    { intros k N T HN HT0; unfold Ns in HN, HT0.
      rewrite <- record_params_insts_sub in HT0 by exact HRc.
      apply nth_error_map_inv in HN as (I0 & HI0 & ->); apply nth_error_map_inv in HT0 as (T0 & HT1 & ->).
      destruct (valid_ind_decl_views _ HD) as [IsS Hvsv].
      pose proof (filed_rview_is p D IsS Hvg Hvsv _ _ _ _ _ _ _ _ _ Hj Hh HlR HI0 HT1) as H.
      exact (rel_exp_under_ctx_gsub Hσv (closed_app_valid _ _ _ _ _ Ua Usem HΓ H)). }
    (** The record view equation, over [Γ]. *)
    pose proof (valid_group_views_rview_fields p D Hvg _ _ _ _ _ _ _ _ Hj Hh HlR Hcs) as HE0.
    pose proof (rel_ext_under_ctx_closed _ Γ _ _ Ua Usem HΓ (all_assumptions_sub _ _ (record_fctx_ass _ _))
                  ltac:(apply cargs_ctx_aux_ass) HE0) as HE.
    pose proof (rel_ext_under_ctx_left _ _ _ HE) as HFn.
    assert (HPf : forall m, m <= List.length (record_fields R) ->
              gsub Ψ (sb_of_list σv (record_pre R m x)) (tele_sub (record_fctx R m) (sb_of_list Id Is) ++ ind_uparams D ++ Γ)).
    { induction m as [| m IH]; intros Hm; [ exact Hσv |].
      destruct (List.nth_error (record_fields R) m) as [[f U] |] eqn:Ef; [| apply List.nth_error_None in Ef; lia ].
      pose proof (IH ltac:(lia)) as Hm'.
      assert (HlP : List.length (record_pre R m x) = m) by (apply length_record_pre; lia).
      assert (HFS : tele_sub (record_fctx R (S m)) (sb_of_list Id Is)
                    = ce_ass (record_field_kind R m) U[sb_qn m (sb_of_list Id Is)] :: tele_sub (record_fctx R m) (sb_of_list Id Is))
        by (rewrite (record_fctx_succ _ _ _ _ Ef); cbn [tele_sub centry_sub]; rewrite length_record_fctx by lia; reflexivity).
      assert (HwS : ⊨ tele_sub (record_fctx R (S m)) (sb_of_list Id Is) ++ ind_uparams D ++ Γ).
      { destruct (record_fctx_split R (S m) Hm) as [X EX].
        pose proof HFn as H0; rewrite EX, tele_sub_app, <- List.app_assoc in H0; exact (rel_ctx_wf_app_r _ _ H0). }
      rewrite HFS in HwS; cbn [List.app] in HwS; destruct (rel_ctx_wf_ass_inv HwS) as (SU & HSU & HU).
      assert (EU : U[sb_qn m (sb_of_list Id Is)][sb_of_list σv (record_pre R m x)] = U[sb_of_list Id (Ns ++ record_pre R m x)]).
      { rewrite exp_sub_sub.
        pose proof (sb_qn_of_list (record_pre R m x) (sb_of_list Id Is) σv) as Hq; rewrite HlP in Hq.
        rewrite (exp_sub_sb_eq _ _ (sb_of_list (sb_of_list σv Ns) (record_pre R m x))).
        - rewrite <- sb_of_list_app; eapply exp_scoped_sub_agree; [ exact (closed_fields _ HRc _ _ _ Ef) |].
          intros z Hz; apply sb_of_list_lt_base; rewrite List.length_app, HNl, HlP; lia.
        - etransitivity; [ exact Hq |]; apply sb_of_list_cong.
          etransitivity; [ apply sb_of_list_compose_gen |]; apply sb_of_list_cong; intros z; reflexivity. }
      pose proof (Mctt.Core.Completeness.Records.Model.valid_exp_under_ctx_proj qr R HlR HaR HsuR HF HS HT HPr HFk Ψ x Ns HΨ Hx HNl HNs HNss Hxs m f U Ef) as Hpr.
      unfold record_pre; rewrite (firstn_succ_nth _ _ _ Ef), List.map_app; fold (record_pre R m x); cbn [List.map fst].
      rewrite sb_of_list_app; cbn [sb_of_list]; rewrite HFS.
      eapply gsub_ass; [ exact Hm' | exact HSU | exact HU | rewrite EU; exact Hpr | cbn; exact Hxs ]. }
    pose proof (HPf _ (le_n _)) as HPn.
    replace (projections_of fl x) with (record_pre R (List.length (record_fields R)) x).
    - eapply gsub_conv_tgt; [ exact HPn | exact (rel_ext_under_ctx_right _ _ _ HE) | exact (rel_ext_under_ctx_eq _ _ _ HE) ].
    - destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ Hj Hh) as [R' HR'].
      rewrite (rview_record_lookup _ _ _ _ _ _ HR') in HlR; injection HlR as <-.
      unfold record_pre, projections_of; rewrite List.firstn_all, (rview_record_names _ _ _ _ _ _ HR'), List.map_map; reflexivity.
  Qed.

  Lemma rview_field_gsub : forall Ψ j Mj qr Is fl c gs fs1 f t fs2 σv x,
      ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
      List.combine fl gs = fs1 ++ (f, ca_rec t) :: fs2 ->
      gsub Ψ σv (ind_uparams D ++ Γ) ->
      Ψ ⊨ x : apps_exp (a_record qr) (List.map (fun I => I[σv]) Is) -> exp_scoped (List.length Ψ) x ->
      gsub Ψ (sb_of_list σv (projections_of (List.map fst fs1) x)) (cargs_ctx p D Mj (List.map snd fs1) ++ ind_uparams D ++ Γ) /\
      Ψ ⊨ a_proj f x : (ptyp_ty p D (im_nn Mj) (cargs_pat (List.map snd fs1)) t)[sb_of_list σv (projections_of (List.map fst fs1) x)].
  Proof.
    intros * Hj Hh Hcs Ec Hσv Hx Hxs.
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ Hj Hh) as (gs' & Hcs' & Hlen).
    rewrite Hcs in Hcs'; injection Hcs' as _ <-.
    destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
    pose proof (rview_fields_gsub _ _ _ _ _ _ _ _ _ _ Hj Hh Hcs Hσv Hx Hxs) as HS.
    set (gs1 := List.map snd fs1) in *; set (gs2 := List.map snd fs2) in *.
    set (Ms1 := projections_of (List.map fst fs1) x) in *.
    set (Ms2 := projections_of (List.map fst fs2) x).
    assert (EMs : projections_of fl x = (Ms1 ++ a_proj f x :: nil) ++ Ms2)
      by (rewrite Efl; unfold Ms1, Ms2, projections_of; rewrite !List.map_app; cbn; rewrite <- List.app_assoc; reflexivity).
    assert (ECtx : cargs_ctx p D Mj gs ++ ind_uparams D ++ Γ
                   = cargs_ctx_aux p D (im_nn Mj) (cargs_pat (gs1 ++ ca_rec t :: nil)) gs2
                     ++ (ce_ass ak_relevant (ptyp_ty p D (im_nn Mj) (cargs_pat gs1) t) :: cargs_ctx p D Mj gs1 ++ ind_uparams D ++ Γ)).
    { rewrite Egs.
      replace (gs1 ++ ca_rec t :: gs2) with ((gs1 ++ ca_rec t :: nil) ++ gs2) by (rewrite <- List.app_assoc; reflexivity).
      rewrite cargs_ctx_app, cargs_ctx_snoc, <- !List.app_assoc; reflexivity. }
    rewrite EMs, ECtx in HS.
    assert (H1 : gsub Ψ (sb_of_list σv (Ms1 ++ a_proj f x :: nil))
                   (ce_ass ak_relevant (ptyp_ty p D (im_nn Mj) (cargs_pat gs1) t) :: cargs_ctx p D Mj gs1 ++ ind_uparams D ++ Γ)).
    { eapply gsub_of_list_prefix; [| exact HS ].
      unfold Ms2, projections_of, gs2; rewrite length_cargs_ctx_aux, !List.length_map; reflexivity. }
    split.
    - change (ce_ass ?κ0 ?T :: ?G) with ((ce_ass κ0 T :: nil) ++ G) in H1.
      exact (gsub_of_list_prefix _ _ Ms1 (a_proj f x :: nil) (ce_ass ak_relevant (ptyp_ty p D (im_nn Mj) (cargs_pat gs1) t) :: nil) _ eq_refl H1).
    - exact (gsub_last_typed _ _ _ _ _ _ _ H1).
  Qed.

  (** ** The Frames of a Leaf Path, Syntactically

      A frame is an argument position [gs1 ++ ca_rec t :: gs2] of a
      constructor [c] of a member [k] ([Mk]): a branch's own, or a field of
      a record view's pseudo-constructor.  Its syntactic side needs no
      environment: the motives' contexts are valid ([HMall]). *)
  Section SynFrame.
    #[local] Set Default Proof Using "All".
    Hypothesis (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ).
    Variables (k : nat) (Mk : imember) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg).
    Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs) (Heq : gs = gs1 ++ ca_rec t :: gs2).
    Let K := List.length (cargs_nonrec gs1).
    Let L := List.length (ptyp_doms t).
    Let Tg := cargs_nonrec_ctx gs1 ++ im_params D Mk ++ Γ.

    Lemma frame_nonrec_le : K <= List.length (cargs_nonrec gs).
    Proof. unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia. Qed.

    Lemma frame_nonrec_ctx : cargs_nonrec_ctx gs1 = nonrec_args_prefix gs (List.length (cargs_nonrec gs1)).
    Proof. rewrite Heq; apply cargs_nonrec_ctx_nonrec_args_prefix. Qed.

    Lemma frame_nonrec_ctx_valid : ⊨ cargs_nonrec_ctx gs1 ++ im_params D Mk.
    Proof. rewrite frame_nonrec_ctx; apply (valid_ind_decl_nonrec_prefixes _ HD k Mk c gs); [ exact HMk | exact Hcon | exact frame_nonrec_le ]. Qed.

    Lemma frame_nonrec_ctx_all_assumptions : all_assumptions (cargs_nonrec_ctx gs1 ++ im_params D Mk).
    Proof.
      apply List.Forall_app; split;
        [ rewrite cargs_nonrec_ctx_rev_tele; apply List.Forall_rev, all_assumptions_cargs_nonrec_tele | exact (member_params_ass D Hc _ _ HMk) ].
    Qed.

    Lemma frame_target_valid : ⊨ Tg.
    Proof.
      destruct (closed_app_sem _ _ frame_nonrec_ctx_all_assumptions frame_nonrec_ctx_valid HΓ) as [H _]; unfold Tg; rewrite <- List.app_assoc in H; exact H.
    Qed.

    (** The kind of the entry [x] of the components' context: a
        non-recursive argument's own, [ak_relevant] at a parameter (a type
        of a universe or of levels, never a proposition). *)
    Definition frame_rf (x : nat) : abs_kind :=
      if x <? K then match List.nth_error (cargs_nonrec_kinds gs) (K - 1 - x) with Some r => r | None => ak_relevant end
      else ak_relevant.

    (** Each entry of the components' context is of the sort its kind
        gives, over [Γ]: a parameter type ([rel_param_typed]) at
        [ak_relevant], a non-recursive argument of a universe, a uniform
        parameter of a universe or of levels, and a proposition at
        [ak_propositional]. *)
    Lemma frame_entry_sort : forall x Δ1 κ T Δ2, cargs_nonrec_ctx gs1 ++ im_params D Mk = Δ1 ++ ce_ass κ T :: Δ2 -> List.length Δ1 = x ->
        (evaluated_kind (frame_rf x) -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i) /\
        (frame_rf x = ak_propositional -> Δ2 ++ Γ ⊨ T : Propₘ).
    Proof.
      intros * E Hx; unfold frame_rf.
      rewrite frame_nonrec_ctx in E; fold K in E.
      destruct (Nat.ltb_spec x K) as [Hlt | Hge].
      - unfold nonrec_args_prefix in E.
        assert (LK : List.length (List.firstn K (cargs_nonrec_tele gs)) = K)
          by (rewrite List.length_firstn, length_cargs_nonrec_tele; pose proof frame_nonrec_le; lia).
        destruct (rev_app_entry_split (List.firstn K (cargs_nonrec_tele gs)) (im_params D Mk) Δ1 Δ2 (K - 1 - x) (ce_ass κ T)
                    ltac:(lia) E ltac:(lia)) as [He ->].
        rewrite List.nth_error_firstn in He; destruct (Nat.ltb_spec (K - 1 - x) K); [| discriminate ].
        destruct (cargs_nonrec_tele_nth _ _ _ _ He) as [HA0 Hr]; rewrite Hr.
        destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HMk Hcon HA0 Hr) as (_ & i & HAi).
        assert (Hj' : K - 1 - x <= List.length (cargs_nonrec gs)) by (pose proof frame_nonrec_le; lia).
        pose proof (valid_ind_decl_nonrec_prefixes _ HD _ _ _ _ _ HMk Hcon Hj') as HSj.
        assert (HSa : all_assumptions (nonrec_args_prefix gs (K - 1 - x) ++ im_params D Mk))
          by (apply List.Forall_app; split;
              [ apply all_assumptions_nonrec_args_prefix
              | exact (member_params_ass D Hc _ _ HMk) ]).
        pose proof (closed_app_valid _ _ _ _ _ HSa HSj HΓ HAi) as HAΓ.
        unfold nonrec_args_prefix in HAΓ; rewrite List.firstn_firstn, Nat.min_l by lia.
        rewrite <- List.app_assoc in HAΓ |- *.
        split; intros Hrr; [ exists i; inversion Hrr; subst; [ left | right ]; exact HAΓ | rewrite Hrr in HAΓ; exact HAΓ ].
      - split; [ intros _ | intros [=] ].
        assert (Lp : List.length (nonrec_args_prefix gs K) = K) by (apply length_nonrec_args_prefix; exact frame_nonrec_le).
        destruct (app_split_prefix _ _ _ _ E ltac:(lia)) as (m1 & -> & Ep).
        destruct (im_params_evaluated D HD k Mk HMk m1 κ T Δ2 Ep) as [i HT].
        exists i.
        pose proof (member_params_ass D Hc _ _ HMk) as Ha; rewrite Ep in Ha.
        apply List.Forall_app in Ha as [_ Ha]; pose proof (List.Forall_inv_tail Ha) as Ha2.
        pose proof frame_nonrec_ctx_valid as HV; rewrite frame_nonrec_ctx, Ep in HV.
        apply rel_ctx_wf_app_r, rel_ctx_wf_app_r, rel_ctx_wf_tail in HV.
        destruct HT as [HT | HT]; [ left | right ]; exact (closed_app_valid _ _ _ _ _ Ha2 HV HΓ HT).
    Qed.

    Lemma frame_doms_valid : forall kd, kd <= L -> ⊨ doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk.
    Proof. intros kd Hk; rewrite frame_nonrec_ctx; exact (valid_ind_decl_dctx _ HD k Mk c gs gs1 t gs2 kd HMk Hcon Heq Hk). Qed.

    Lemma frame_doms_ass : forall kd, all_assumptions (doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk).
    Proof. intros; apply List.Forall_app; split; [ apply List.Forall_rev, all_assumptions_map_ass | exact frame_nonrec_ctx_all_assumptions ]. Qed.

    Lemma frame_doms_len : forall kd, kd <= L -> List.length (doms_ctx (List.firstn kd (ptyp_doms t))) = kd.
    Proof. intros; rewrite doms_ctx_length, List.length_firstn; unfold L in *; lia. Qed.

    (** *** The Syntactic Side of a Frame

        The base context [Ψ0 ++ Γ] the recursive results are typed in, the
        substitution [σ0] of the frame's components into it, the base
        [β0], a weakening past [Ψ0], and the argument [x0]. *)
    #[warnings="-cannot-define-projection"]
    Record sem_frame (Ψ0 : ctx) (σ0 β0 : sub) (x0 : exp) : Prop := mk_sem_frame
      { (** The base context is valid *)
        sem_frame_ctx : ⊨ Ψ0 ++ Γ
        (** The components' substitution *)
      ; sem_frame_sigma : gsub (Ψ0 ++ Γ) σ0 Tg
        (** The base is the weakening past [Ψ0] *)
      ; sem_frame_base : sb_eq β0 (sb_of_wk (wk_shiftn (List.length Ψ0)))
        (** [σ0] sends the uniform parameters to [Us] moved by [β0] *)
      ; sem_frame_uparams : shape_uc D Us (cargs_nonrec_ctx gs1 ++ im_params D Mk) σ0 β0
        (** The argument is of the shape's type *)
      ; sem_frame_arg : Ψ0 ++ Γ ⊨ x0 : ptyp_ty_at p D (List.map (fun U => U[β0]) Us) σ0 t
        (** It is scoped by the base context *)
      ; sem_frame_arg_scoped : exp_scoped (List.length (Ψ0 ++ Γ)) x0
        (** Past the non-recursive arguments before the position and the
            non-uniform parameters, [σ0] is [Us] moved by [β0], then
            [β0] *)
      ; sem_frame_form : forall y, σ0 (y + List.length (cargs_nonrec_ctx gs1 ++ im_nparams Mk))
                                   = sb_of_list β0 (List.map (fun U => U[β0]) Us) y }.

    Section FrameEnd.
      Variables (Ψ0 : ctx) (σ0 β0 : sub) (x0 : exp).
      Hypothesis (Hf : sem_frame Ψ0 σ0 β0 x0).

      (** The components past the first [kd] domains. *)
      Lemma frame_gsub_doms_at : forall kd, kd <= L ->
          gsub (tele_sub (doms_ctx (List.firstn kd (ptyp_doms t))) σ0 ++ Ψ0 ++ Γ) (sb_qn kd σ0)
            (doms_ctx (List.firstn kd (ptyp_doms t)) ++ Tg).
      Proof.
        intros kd Hk.
        assert (HV : ⊨ doms_ctx (List.firstn kd (ptyp_doms t)) ++ Tg).
        { destruct (closed_app_sem _ _ (frame_doms_ass kd) (frame_doms_valid kd Hk) HΓ) as [H _].
          unfold Tg; rewrite <- !List.app_assoc in H; exact H. }
        rewrite <- (frame_doms_len kd Hk) at 2.
        apply gsub_qn; [ exact (sem_frame_sigma _ _ _ _ Hf) | unfold doms_ctx; apply List.Forall_rev, all_assumptions_map_ass | exact HV ].
      Qed.

      (** The shape ends in the member [Mj]. *)
      Variables (Mj : imember).
      Hypotheses (HMj : ind_member D (ptyp_mem t) = Some Mj).
      Let Ps' := List.map (fun P => P[sb_qn L σ0]) (ptyp_ps t).
      Let xL := apps_vars_iter L x0.
      Let τL := sb_of_list (sb_shift_iter L β0) (Ps' ++ xL :: nil).
      Let ΨL := tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ.
      Let ITj := ind_mty p D (ptyp_mem t) (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)).

      Lemma frame_end_params_len : List.length (ptyp_ps t) = im_nn Mj.
      Proof.
        destruct (length_rec_ps D HD k Mk HMk c gs gs1 t gs2 Hcon Heq) as (Mj' & HMj' & H).
        rewrite HMj in HMj'; injection HMj' as <-; exact H.
      Qed.

      Lemma frame_tele_len : List.length (ptyp_tele t) = L.
      Proof. unfold ptyp_tele; apply doms_ctx_length. Qed.

      Lemma frame_doms_tele : ptyp_tele t = doms_ctx (List.firstn L (ptyp_doms t)).
      Proof. unfold ptyp_tele, L; rewrite List.firstn_all; reflexivity. Qed.

      Lemma frame_tele_valid : ⊨ ptyp_tele t ++ Tg.
      Proof.
        pose proof (frame_doms_valid L (le_n _)) as H; rewrite <- frame_doms_tele in H.
        assert (Ha : all_assumptions (ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk)) by (rewrite frame_doms_tele; apply frame_doms_ass).
        destruct (closed_app_sem _ _ Ha H HΓ) as [H' _]; unfold Tg; rewrite <- !List.app_assoc in H'; exact H'.
      Qed.

      Lemma frame_gsub_doms : gsub ΨL (sb_qn L σ0) (ptyp_tele t ++ Tg).
      Proof.
        rewrite <- frame_tele_len; apply gsub_qn; [ exact (sem_frame_sigma _ _ _ _ Hf) | unfold ptyp_tele, doms_ctx; apply List.Forall_rev, all_assumptions_map_ass |].
        exact frame_tele_valid.
      Qed.

      Lemma frame_end_ctx_valid : ⊨ ΨL.
      Proof. exact (gsub_rel_ctx_wf _ _ _ frame_gsub_doms). Qed.

      Lemma frame_end_base_eq : sb_eq (sb_shift_iter L β0) (sb_of_wk (wk_shiftn (List.length (tele_sub (ptyp_tele t) σ0 ++ Ψ0)))).
      Proof.
        rewrite sb_shift_iter_eq, (sem_frame_base _ _ _ _ Hf), <- sb_of_wk_compose; apply sb_of_wk_cong; intros z; cbn.
        rewrite List.length_app, length_tele_sub, frame_tele_len; lia.
      Qed.

      Lemma frame_gsub_end_base : gsub ΨL (sb_shift_iter L β0) Γ.
      Proof.
        eapply gsub_eq; [| symmetry; exact frame_end_base_eq ].
        pose proof frame_end_ctx_valid as H; unfold ΨL in H |- *; rewrite List.app_assoc in H |- *.
        apply gsub_wk; [ apply rel_wk_under_ctx_shiftn; exact H | exact H | exact HΓ ].
      Qed.

      Lemma frame_uparams_doms : forall kd, kd <= L ->
          shape_uc D Us (doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk) (sb_qn kd σ0) (sb_shift_iter kd β0).
      Proof.
        induction kd as [| kd IH]; intros Hk; [ exact (sem_frame_uparams _ _ _ _ Hf) |].
        destruct (nth_error_lt_some' (ptyp_doms t) kd ltac:(unfold L in Hk; lia)) as [Bk HBk].
        rewrite (firstn_S_snoc _ _ _ HBk), doms_ctx_snoc; cbn [sb_qn sb_shift_iter List.app].
        apply shape_uc_pi; [| apply IH; lia ].
        rewrite !List.length_app, length_im_params; unfold im_np; lia.
      Qed.

      Lemma frame_end_params_valid : forall kk P T0, List.nth_error (ptyp_ps t) kk = Some P ->
          List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))) (ptyp_ps t)) kk = Some T0 ->
          ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk ⊨ P : T0.
      Proof.
        intros kk P0 T0 HP0 HT; pose proof (valid_ind_decl_rec_field _ HD k Mk c gs gs1 t gs2 Mj kk P0 T0 HMk Hcon Heq HMj HP0 HT) as H.
        rewrite <- frame_nonrec_ctx in H; exact H.
      Qed.

      Lemma frame_end_nparams_valid : ⊨ tele_sub (im_nparams Mj) τU ++ Γ.
      Proof. exact (rel_ctx_wf_tail (HMall _ _ HMj)). Qed.

      (** The parameters of the end, one by one, at any instance agreeing
          with [Us] moved past the domains on the uniform parameters. *)
      Lemma frame_end_params_each : forall σ', (forall y, y < ind_nu D ->
            sentry_exp ((τU ⨟ sb_shift_iter L β0) y) = sentry_exp (σ' y)) ->
          forall kk N T0, List.nth_error Ps' kk = Some N -> List.nth_error (tele_insts (im_nparams Mj) σ' Ps') kk = Some T0 ->
          ΨL ⊨ N : T0.
      Proof.
        intros σ' Hσ' kk N T0 HN HT.
        unfold Ps' in HN, HT; apply nth_error_map_inv in HN as (P0 & HPk & ->).
        set (σ1 := sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))).
        assert (HT0 : exists T1, List.nth_error (tele_insts (im_nparams Mj) σ1 (ptyp_ps t)) kk = Some T1).
        { assert (Hk : kk < List.length (ptyp_ps t)) by (apply List.nth_error_Some; congruence).
          apply nth_error_lt_some'; rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMj).
          rewrite length_im_nparams, <- frame_end_params_len; lia. }
        destruct HT0 as [T1 HT1].
        pose proof (frame_end_params_valid _ _ _ HPk HT1) as HP1.
        assert (Ha : all_assumptions (ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk)) by (rewrite frame_doms_tele; apply frame_doms_ass).
        assert (Hs : ⊨ ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk) by (rewrite frame_doms_tele; apply frame_doms_valid, le_n).
        pose proof (closed_app_valid _ _ _ _ _ Ha Hs HΓ HP1) as HP2; rewrite <- !List.app_assoc in HP2.
        pose proof (rel_exp_under_ctx_gsub frame_gsub_doms HP2) as HP3.
        replace T0 with T1[sb_qn L σ0]; [ exact HP3 |].
        rewrite <- (tele_insts_sub_mvc (im_nparams Mj) (ind_nu D) σ1 σ' (sb_qn L σ0) (ptyp_ps t)) in HT.
        + apply nth_error_map_inv in HT as (T2 & HT2 & ->); rewrite HT1 in HT2; injection HT2 as ->; reflexivity.
        + exact (decl_closed_nparams_ass D Hc _ _ HMj).
        + exact (decl_nparams_mvc _ _ _ Hdt _ _ HMj).
        + exact (decl_closed_nparams_scoped D Hc _ _ HMj).
        + intros y Hy; unfold σ1; cbn [sb_of_wk sentry_sub wk_shiftn].
          pose proof (frame_uparams_doms L (le_n _) y Hy) as H; rewrite <- frame_doms_tele in H.
          rewrite <- Hσ' by exact Hy.
          etransitivity; [| exact H ]; f_equal; f_equal.
          rewrite !List.length_app, frame_tele_len, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele, length_im_params;
            unfold ptyp_depth, K, im_np; fold L; lia.
      Qed.

      (** The leaf's parameters, moved into the frame, are scoped by its
          context: the shape is closed, and [σ0] is scoped by the base. *)
      Lemma frame_end_params_scoped : List.Forall (exp_scoped (List.length ΨL)) Ps'.
      Proof.
        pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ HMk) _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as Ht.
        pose proof (ptyp_scoped_ps _ _ Ht) as HPs.
        pose proof (gsub_valid (sem_frame_sigma _ _ _ _ Hf)) as [_ _ _ _ _ Hσs].
        unfold Ps'; apply List.Forall_map; eapply List.Forall_impl; [| exact HPs ].
        intros P0 HP0.
        assert (HlΨL : List.length ΨL = L + List.length (Ψ0 ++ Γ))
          by (unfold ΨL; rewrite List.length_app, length_tele_sub, frame_tele_len; reflexivity).
        rewrite HlΨL; apply (exp_scoped_sub _ (L + List.length Tg)).
        - apply (exp_scoped_mono _ (ptyp_depth t + (List.length (cargs_nonrec_ctx gs1) + im_np D Mk))); [| exact HP0 ].
          unfold ptyp_depth, Tg; fold L; rewrite !List.length_app, length_im_params; lia.
        - apply (sb_qn_bound L σ0 (List.length Tg)); intros z Hz; exact (proj1 (Hσs z Hz)).
      Qed.

      Lemma frame_gsub_end_params : gsub ΨL (sb_of_list (sb_shift_iter L β0) Ps') (tele_sub (im_nparams Mj) τU ++ Γ).
      Proof.
        apply gsub_of_list; [ exact frame_gsub_end_base | apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMj) | exact frame_end_nparams_valid
                            | unfold Ps'; rewrite List.length_map, length_tele_sub, length_im_nparams; exact frame_end_params_len
                            | | exact frame_end_params_scoped ].
        intros kk N T0 HN HT; rewrite tele_insts_tele_sub in HT.
        exact (frame_end_params_each _ (fun y _ => eq_refl) kk N T0 HN HT).
      Qed.

      Lemma frame_end_type_valid : exists jI : nat, tele_sub (im_nparams Mj) τU ++ Γ ⊨ ITj : Typeω@jI.
      Proof.
        pose proof (HMall _ _ HMj) as HM'.
        change (elim_mctx p D (ptyp_mem t) Mj Us ++ Γ) with ((tele_sub (im_nparams Mj) τU ++ Γ) ▹{ak_relevant} ITj) in HM'.
        destruct (rel_ctx_wf_ass_inv HM') as (Srt & HSrt & HIT).
        apply (rel_exp_univ_of_sort_relevant _ _ _ (sort_kind_type_sort _ _ HSrt) HIT).
        - intros ρ0 a Ea; exact (ind_mty_relevant _ _ _ _ _ _ _ _ HMj Ea).
        - intros ρ0 a Ea; exact (ind_mty_not_level _ _ _ _ _ _ _ _ HMj Ea).
      Qed.

      Lemma frame_end_arg_typed : ΨL ⊨ xL : ind_mty p D (ptyp_mem t) (List.map (fun U => U[sb_shift_iter L β0]) Us) Ps'.
      Proof.
        pose proof (sem_frame_arg _ _ _ _ Hf) as Hlk.
        rewrite ptyp_ty_at_ctx_pi in Hlk.
        unfold ptyp_depth in Hlk; fold L in Hlk.
        destruct frame_end_type_valid as [jI HIT].
        pose proof (rel_exp_under_ctx_gsub frame_gsub_end_params HIT) as HIT'.
        unfold ITj in HIT'; rewrite ind_head_inst in HIT' by (try exact Hc; try exact HUl; unfold Ps'; rewrite List.length_map; exact frame_end_params_len).
        replace (List.map (fun U => U[sb_shift_iter L β0]) Us) with (List.map (fun U => U[wk_shiftn L]ʷ) (List.map (fun U => U[β0]) Us))
          in HIT' |- *
          by (rewrite List.map_map; apply List.map_ext; intros U; rewrite <- exp_sub_of_wk, exp_sub_sub;
              apply exp_sub_sb_eq; rewrite sb_shift_iter_eq; reflexivity).
        unfold xL; rewrite apps_vars_iter_eq.
        apply (valid_apps_vars L (tele_sub (ptyp_tele t) σ0) (Ψ0 ++ Γ) _ jI x0);
          [ rewrite length_tele_sub; exact frame_tele_len | apply all_assumptions_sub; unfold ptyp_tele, doms_ctx; apply List.Forall_rev, all_assumptions_map_ass
          | exact frame_end_ctx_valid | exact HIT' | exact Hlk ].
      Qed.

      (** The argument past the domains is scoped by the frame's context. *)
      Lemma frame_end_arg_scoped : exp_scoped (List.length ΨL) xL.
      Proof.
        pose proof (sem_frame_arg_scoped _ _ _ _ Hf) as Hx.
        assert (HlΨL : List.length ΨL = L + List.length (Ψ0 ++ Γ))
          by (unfold ΨL; rewrite List.length_app, length_tele_sub, frame_tele_len; reflexivity).
        unfold xL; rewrite apps_vars_iter_eq, HlΨL; apply exp_scoped_apps; split.
        - eapply exp_scoped_wk; [ exact Hx | intros z Hz; cbn; lia ].
        - apply vars_from_scoped; lia.
      Qed.

      Lemma frame_gsub_leaf : gsub ΨL τL (elim_mctx p D (ptyp_mem t) Mj Us ++ Γ).
      Proof.
        destruct frame_end_type_valid as [jI HIT].
        unfold τL; rewrite sb_of_list_app; cbn [sb_of_list].
        change (elim_mctx p D (ptyp_mem t) Mj Us ++ Γ) with ((tele_sub (im_nparams Mj) τU ++ Γ) ▹{ak_relevant} ITj).
        eapply gsub_ass; [ exact frame_gsub_end_params | apply sort_kind_universe | exact HIT | | exact frame_end_arg_scoped ].
        unfold ITj; rewrite ind_head_inst by (try exact Hc; try exact HUl; unfold Ps'; rewrite List.length_map; exact frame_end_params_len).
        exact frame_end_arg_typed.
      Qed.

      (** *** At a Record View

          When the shape ends in a record view, the components past the
          domains, cut to the uniform parameters ([σv]), are [Us] moved
          past the domains; the argument past the domains, [xL], is of the
          view's record type there. *)
      Let σv := ι (wk_shiftn (im_nn Mk + K + L)) ⨟ sb_qn L σ0.

      Lemma frame_rview_uparams_form : sb_eq σv (sb_of_list (sb_shift_iter L β0) (List.map (fun U => U[sb_shift_iter L β0]) Us)).
      Proof.
        pose proof (sem_frame_form _ _ _ _ Hf) as EN.
        assert (LN : List.length (cargs_nonrec_ctx gs1 ++ im_nparams Mk) = im_nn Mk + K)
          by (rewrite List.length_app, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele, length_im_nparams; fold K; lia).
        intros y; unfold σv; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        rewrite sb_qn_ge by lia.
        replace (y + (im_nn Mk + K + L) - L) with (y + List.length (cargs_nonrec_ctx gs1 ++ im_nparams Mk)) by lia.
        rewrite EN.
        destruct (Nat.lt_ge_cases y (ind_nu D)) as [Hy | Hy].
        - rewrite !(sb_of_list_nth _ _ _ a_prop) by (rewrite List.length_map; lia).
          cbn [sentry_wk]; f_equal.
          rewrite !List.length_map.
          rewrite (List.nth_indep (List.map (fun U => U[β0]) Us) _ (a_prop[β0])),
            (List.nth_indep (List.map (fun U => U[sb_shift_iter L β0]) Us) _ (a_prop[sb_shift_iter L β0]))
            by (rewrite List.length_map; lia).
          pose proof (List.map_nth (fun U => U[β0]) Us a_prop (List.length Us - 1 - y)) as E1; cbn beta in E1; rewrite E1.
          pose proof (List.map_nth (fun U => U[sb_shift_iter L β0]) Us a_prop (List.length Us - 1 - y)) as E2;
            cbn beta in E2; rewrite E2.
          rewrite <- exp_sub_of_wk, exp_sub_sub; apply exp_sub_sb_eq; symmetry; apply sb_shift_iter_eq.
        - replace y with (List.length (List.map (fun U => U[β0]) Us) + (y - ind_nu D)) at 1 by (rewrite List.length_map; lia).
          replace y with (List.length (List.map (fun U => U[sb_shift_iter L β0]) Us) + (y - ind_nu D)) at 2
            by (rewrite List.length_map; lia).
          rewrite !sb_of_list_ge.
          rewrite (sb_shift_iter_eq L β0 (y - ind_nu D)); cbn [sb_compose]; rewrite sentry_sub_of_wk; reflexivity.
      Qed.

      Lemma frame_rview_uparams_sub : gsub ΨL σv (ind_uparams D ++ Γ).
      Proof.
        destruct (gsub_props frame_gsub_doms) as [Hv Hk].
        pose proof frame_tele_valid as HT.
        assert (E0 : ptyp_tele t ++ Tg = (ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk) ++ ind_uparams D ++ Γ)
          by (unfold Tg, im_params; rewrite <- !List.app_assoc; reflexivity).
        rewrite E0 in HT, Hv, Hk.
        pose proof (rel_wk_under_ctx_shiftn _ _ HT) as Hw.
        replace (List.length (ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk)) with (im_nn Mk + K + L) in Hw
          by (rewrite !List.length_app, frame_tele_len, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele, length_im_nparams; fold K; lia).
        unfold σv; eapply gsub_comp; [ exact (gsub_wk _ _ _ Hw HT (rel_ctx_wf_app_r _ _ HT)) | exact frame_end_ctx_valid | exact Hv | exact Hk ].
      Qed.

      Lemma frame_rview_arg_typed : forall qr Is fl, im_head Mj = mh_record qr Is fl ->
          ΨL ⊨ xL : apps_exp (a_record qr) (List.map (fun I => I[σv]) Is).
      Proof.
        intros * Hh.
        destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [_ Hnn].
        pose proof frame_end_arg_typed as Hx.
        pose proof frame_end_params_len as H0; rewrite Hnn in H0.
        assert (EP : Ps' = nil) by (unfold Ps'; destruct (ptyp_ps t); [ reflexivity | discriminate ]).
        rewrite EP in Hx.
        rewrite <- (rview_mty _ _ p _ _ _ _ _ _ (List.map (fun U => U[sb_shift_iter L β0]) Us) σv Hdt Hc HMj Hh); [ exact Hx |].
        intros y Hy; rewrite (frame_rview_uparams_form y), !(sb_of_list_lt_base _ _ Id) by (rewrite List.length_map; lia); reflexivity.
      Qed.

      (** The frame of a recursive field [f] of the record view: the
          components are the projections of the fields before it, moved to
          its non-recursive ones, over [σv]; the base is [β0] moved past the
          domains; the argument is the projection. *)
      Lemma frame_rview_field : forall qr Is fl c' gsr fs1 f tf fs2, im_head Mj = mh_record qr Is fl -> im_cons Mj = (c', gsr) :: nil ->
          List.combine fl gsr = fs1 ++ (f, ca_rec tf) :: fs2 ->
          let σ' := ι (wk_pat (cargs_pat (List.map snd fs1))) ⨟ sb_of_list σv (projections_of (List.map fst fs1) xL) in
          gsub ΨL σ' (cargs_nonrec_ctx (List.map snd fs1) ++ im_params D Mj ++ Γ) /\
          shape_uc D Us (cargs_nonrec_ctx (List.map snd fs1) ++ im_params D Mj) σ' (sb_shift_iter L β0) /\
          ΨL ⊨ a_proj f xL : ptyp_ty_at p D (List.map (fun U => U[sb_shift_iter L β0]) Us) σ' tf /\
          sb_eq σ' (sb_of_list (sb_of_list (sb_shift_iter L β0) (List.map (fun U => U[sb_shift_iter L β0]) Us))
                      (projections_of (fields_args fs1) xL)).
      Proof.
        intros * Hh Hcs Ec σ'.
        destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [EG Hnn].
        destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gs' & Hcs' & Hlen).
        rewrite Hcs in Hcs'; injection Hcs' as _ <-.
        destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
        pose proof (ind_con_single _ _ _ Hcs) as Hcon'.
        destruct (rview_field_gsub ΨL _ _ _ _ _ _ _ _ _ _ _ σv xL HMj Hh Hcs Ec frame_rview_uparams_sub (frame_rview_arg_typed _ _ _ Hh)
                    frame_end_arg_scoped) as [Hτ Hxf].
        set (gs1' := List.map snd fs1) in *.
        set (τ := sb_of_list σv (projections_of (List.map fst fs1) xL)) in *.
        assert (Hlg : List.length (cargs_pat gs1') = List.length (projections_of (List.map fst fs1) xL))
          by (unfold gs1', projections_of; rewrite length_cargs_pat, !List.length_map; reflexivity).
        assert (Huc1 : forall y, y < ind_nu D ->
                  sentry_exp (τ (y + (List.length (cargs_pat gs1') + im_nn Mj))) = sentry_exp ((sb_of_list Id Us ⨟ sb_shift_iter L β0) y)).
        { intros y Hy; rewrite Hnn, Nat.add_0_r, Nat.add_comm, Hlg; unfold τ; rewrite sb_of_list_ge, (frame_rview_uparams_form y).
          cbn [sb_compose]; rewrite sb_of_list_lt_compose, !(sb_of_list_lt_base _ _ Id) by (rewrite ?List.length_map; lia); reflexivity. }
        split; [| split; [| split ] ].
        - (** The components' substitution. *)
          assert (Hst : cargs_nonrec_ctx gs1' = nonrec_args_prefix gsr (List.length (cargs_nonrec gs1')))
            by (rewrite Egs; apply cargs_nonrec_ctx_nonrec_args_prefix).
          assert (HK' : List.length (cargs_nonrec gs1') <= List.length (cargs_nonrec gsr))
            by (rewrite Egs, cargs_nonrec_app, List.length_app; lia).
          pose proof (valid_ind_decl_nonrec_prefixes _ HD (ptyp_mem t) Mj c' gsr _ HMj Hcon' HK') as HS; rewrite <- Hst in HS.
          assert (HSa : all_assumptions (cargs_nonrec_ctx gs1' ++ im_params D Mj))
            by (apply List.Forall_app; split;
                [ rewrite cargs_nonrec_ctx_rev_tele; apply List.Forall_rev, all_assumptions_cargs_nonrec_tele | exact (member_params_ass D Hc _ _ HMj) ]).
          destruct (closed_app_sem _ _ HSa HS HΓ) as [HSΓ _]; rewrite <- List.app_assoc in HSΓ.
          rewrite <- EG in Hτ.
          destruct (gsub_props Hτ) as [Hτv Hτl]; destruct (gsub_sem Hτ) as [HΨL HCΓ].
          unfold σ'; eapply gsub_comp; [ exact (gsub_wk _ _ _ (cargs_wk_ext _ _ _ _ HMj Hcon' _ _ Egs) HCΓ HSΓ) | exact HΨL | exact Hτv | exact Hτl ].
        - (** The uniform parameters. *)
          intros y Hy; cbn [doms_ctx List.rev List.map List.app] in *.
          rewrite EG, List.length_app; cbn [sb_compose sb_of_wk sentry_sub].
          replace (y + (List.length (cargs_nonrec_ctx gs1') + List.length (ind_uparams D) - ind_nu D))
            with (pat_nargs (cargs_pat gs1') + y) by (rewrite pat_nargs_cargs_pat; unfold ind_nu; lia).
          unfold σ'; cbn [sb_compose sb_of_wk sentry_sub]; rewrite wk_pat_ge.
          pose proof (Huc1 y Hy) as H1; rewrite Hnn, Nat.add_0_r, Nat.add_comm in H1; exact H1.
        - (** The projection. *)
          rewrite ptyp_ty_eq_at, ptyp_ty_at_sub in Hxf by (try exact Hc; apply length_ind_uvars).
          rewrite (uvars_inst _ _ _ _ _ _ HUl Huc1) in Hxf; exact Hxf.
        - (** Its form. *)
          unfold σ', τ, gs1'.
          pose proof (wk_pat_projections fs1 nil σv xL) as E; rewrite List.app_nil_r in E.
          etransitivity; [ exact E |]; apply sb_of_list_cong.
          etransitivity; [| exact frame_rview_uparams_form ].
          intros z; reflexivity.
      Qed.
    End FrameEnd.
  End SynFrame.

  (** ** The Canonical Uniform Parameters

      The values [u0] of [Us] at an environment [C1] of [Γ]: the canonical
      relations of the group there, [G] its elements. *)
  Section Base.
    Variable (C1 : env) (u0 : list domain).
    Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).

    Lemma u0_len : List.length u0 = ind_nu D.
    Proof. rewrite (eval_exps_length _ _ _ HUC); exact HUl. Qed.

    Lemma u0_env : RU (decl_env D u0) (decl_env D u0).
    Proof.
      destruct (us_vals C1 C1 HC11) as (u1 & u2 & Hu1 & Hu2 & H12).
      pose proof (functional_eval_exps' _ _ _ _ Hu1 HUC) as ->; pose proof (functional_eval_exps' _ _ _ _ Hu2 HUC) as ->.
      exact H12.
    Qed.

    Lemma u0_tele_args : per_tele_args (List.rev (ind_uparams D)) nil nil u0 u0.
    Proof. exact (U_tele_args _ _ u0_env u0_len u0_len). Qed.

    Let nr := canon_nparams_rel D u0.
    Let ar := canon_args_rel D u0.
    Let dr := canon_doms_rel D u0.
    #[local] Abbreviation Hcp := (valid_group_canon p D Hvg u0 u0_tele_args u0_len).
    #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
    #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
    #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
    #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
    #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
    #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
    #[local] Abbreviation Had := (valid_group_adm p D Hvg u0 u0 u0_tele_args u0_len u0_tele_args).
    Let G := grp_rel p D u0 nr ar dr.

    (** The environments related to [C1]: their values of [Us] are related
        to [u0], so admissible beside it. *)
    Lemma us_class : forall B, RΓ B C1 -> exists u, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u /\ RU (decl_env D u) (decl_env D u0).
    Proof.
      intros B HB1; destruct (us_vals B C1 HB1) as (u & u' & Hu & Hu' & H).
      pose proof (functional_eval_exps' _ _ _ _ Hu' HUC) as ->; eauto.
    Qed.

    (** The canonical relation of a propositional non-recursive argument
        relates proofs that read back: its type is a proposition there. *)
    Lemma canon_arg_proof : forall m Mm c gs ns j A pre pre', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) ns ns ->
        List.nth_error (cargs_nonrec gs) j = Some A -> List.nth_error (cargs_nonrec_kinds gs) j = Some ak_propositional ->
        tele_prefix_rel (ar m ns c) j pre pre' -> forall x x', ar m ns c j pre x x' -> proof_readable x /\ proof_readable x'.
    Proof.
      intros * HMm Hcon Hns HA Hr Hpre x x' Hx.
      destruct (sort_value D HD u0 u0_tele_args u0_len) as [a0 Ha0].
      assert (Hj : j <= List.length (cargs_nonrec gs)) by (apply nth_error_lt_length in HA; lia).
      pose proof (ar_tele_args D HD Hc Hsu m Mm HMm c gs u0 u0 a0 ns ns Hcon u0_tele_args u0_len Ha0 Hns j pre pre Hj
                    (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HMm ns c gs Hns Hcon j _ _ Hj Hpre)) as Hg.
      pose proof (params_tele_args D HD Hc Hsu m Mm HMm u0 u0 a0 ns ns u0_tele_args u0_len Ha0 Hns) as Hgp.
      pose proof (valid_ind_decl_nonrec_prefixes _ HD _ _ _ _ _ HMm Hcon Hj) as HS.
      destruct (rel_ctx_wf_per_ctx_env HS) as [RS HRS].
      assert (Lpre : List.length pre = j)
        by (pose proof Hpre as H0; rewrite tele_prefix_rel_iff in H0; destruct H0 as (H0 & _); exact H0).
      assert (HE : RS (env_tele nil (List.rev (nonrec_args_prefix gs j ++ im_params D Mm)) (u0 ++ ns ++ pre))
                      (env_tele nil (List.rev (nonrec_args_prefix gs j ++ im_params D Mm)) (u0 ++ ns ++ pre))).
      { pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        rewrite List.length_rev, length_im_nparams in Ln.
        apply (tele_args_env_rel _ _ _ _ _ _ HRS HS).
        - rewrite !List.length_app, length_nonrec_args_prefix, length_im_params, u0_len, Ln, Lpre by exact Hj; unfold im_np; lia.
        - unfold nonrec_args_prefix; rewrite List.rev_app_distr, List.rev_involutive, List.app_assoc.
          apply per_tele_args_app_intro; [ rewrite List.length_rev, length_im_params, List.length_app, u0_len, Ln; unfold im_np; lia
                                     | exact Hgp | unfold im_params; rewrite env_tele_uparams by exact u0_len; exact Hg ]. }
      destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HMm Hcon HA Hr) as [HAp _]; cbn [abs_kind_sort] in HAp.
      destruct (rel_exp_of_prop_inversion_simple_at HRS HAp _ _ HE) as (a & a' & Ea & Ea' & Hpp).
      unfold ar, canon_args_rel in Hx; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMm Hcon HA) in Hx.
      assert (EE : env_tele nil (List.rev (nonrec_args_prefix gs j ++ im_params D Mm)) (u0 ++ ns ++ pre)
                   = components_env D u0 (List.rev (member_nparams D m) ++ member_con_tele D m c) (ns ++ pre)).
      { pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        rewrite (member_nparams_eq _ _ _ HMm), (member_con_tele_eq _ _ _ _ _ HMm Hcon).
        rewrite (components_env_app_firstn D u0 (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs) ns pre Ln)
          by (rewrite length_cargs_nonrec_tele; lia).
        unfold im_params; rewrite List.app_assoc, env_tele_uparams by exact u0_len.
        unfold nonrec_args_prefix, cargs_nonrec_tele; rewrite List.rev_app_distr, List.rev_involutive, Lpre; reflexivity. }
      rewrite EE in Ea, Ea'.
      exact (Hx 0 per_proof a a' Ea Ea' (per_univ_elem_of_prop 0 _ _ Hpp)).
    Qed.

    (** Conversely, any two proofs that read back are related there. *)
    Lemma canon_arg_proof_intro : forall m Mm c gs ns j A pre pre', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) ns ns ->
        List.nth_error (cargs_nonrec gs) j = Some A -> List.nth_error (cargs_nonrec_kinds gs) j = Some ak_propositional ->
        tele_prefix_rel (ar m ns c) j pre pre' -> forall x x', proof_readable x -> proof_readable x' -> ar m ns c j pre x x'.
    Proof.
      intros * HMm Hcon Hns HA Hr Hpre x x' Hx Hx'.
      destruct (sort_value D HD u0 u0_tele_args u0_len) as [a0 Ha0].
      assert (Hj : j <= List.length (cargs_nonrec gs)) by (apply nth_error_lt_length in HA; lia).
      pose proof (ar_tele_args D HD Hc Hsu m Mm HMm c gs u0 u0 a0 ns ns Hcon u0_tele_args u0_len Ha0 Hns j pre pre Hj
                    (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HMm ns c gs Hns Hcon j _ _ Hj Hpre)) as Hg.
      pose proof (params_tele_args D HD Hc Hsu m Mm HMm u0 u0 a0 ns ns u0_tele_args u0_len Ha0 Hns) as Hgp.
      pose proof (valid_ind_decl_nonrec_prefixes _ HD _ _ _ _ _ HMm Hcon Hj) as HS.
      destruct (rel_ctx_wf_per_ctx_env HS) as [RS HRS].
      assert (Lpre : List.length pre = j)
        by (pose proof Hpre as H0; rewrite tele_prefix_rel_iff in H0; destruct H0 as (H0 & _); exact H0).
      assert (HE : RS (env_tele nil (List.rev (nonrec_args_prefix gs j ++ im_params D Mm)) (u0 ++ ns ++ pre))
                      (env_tele nil (List.rev (nonrec_args_prefix gs j ++ im_params D Mm)) (u0 ++ ns ++ pre))).
      { pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        rewrite List.length_rev, length_im_nparams in Ln.
        apply (tele_args_env_rel _ _ _ _ _ _ HRS HS).
        - rewrite !List.length_app, length_nonrec_args_prefix, length_im_params, u0_len, Ln, Lpre by exact Hj; unfold im_np; lia.
        - unfold nonrec_args_prefix; rewrite List.rev_app_distr, List.rev_involutive, List.app_assoc.
          apply per_tele_args_app_intro; [ rewrite List.length_rev, length_im_params, List.length_app, u0_len, Ln; unfold im_np; lia
                                     | exact Hgp | unfold im_params; rewrite env_tele_uparams by exact u0_len; exact Hg ]. }
      destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HMm Hcon HA Hr) as [HAp _]; cbn [abs_kind_sort] in HAp.
      destruct (rel_exp_of_prop_inversion_simple_at HRS HAp _ _ HE) as (a & a' & Ea & Ea' & Hpp).
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (EE : env_tele nil (List.rev (nonrec_args_prefix gs j ++ im_params D Mm)) (u0 ++ ns ++ pre)
                   = components_env D u0 (List.rev (member_nparams D m) ++ member_con_tele D m c) (ns ++ pre)).
      { pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        rewrite (member_nparams_eq _ _ _ HMm), (member_con_tele_eq _ _ _ _ _ HMm Hcon).
        rewrite (components_env_app_firstn D u0 (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs) ns pre Ln)
          by (rewrite length_cargs_nonrec_tele; lia).
        unfold im_params; rewrite List.app_assoc, env_tele_uparams by exact u0_len.
        unfold nonrec_args_prefix, cargs_nonrec_tele; rewrite List.rev_app_distr, List.rev_involutive, Lpre; reflexivity. }
      rewrite EE in Ea.
      unfold ar, canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMm Hcon HA).
      intros i R b b' Eb Eb' HR.
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (b' = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (Eq : R <~> per_proof) by (eapply per_univ_elem_right_irrel; [ exact HR | exact (per_univ_elem_of_prop i _ _ Hpp) ]).
      apply Eq; split; assumption.
    Qed.

    (** Arguments of a constructor whose non-recursive ones are related
        canonically: a proof that reads back at each propositional
        argument. *)
    Lemma con_args_proofs : forall m Mm c gs ns vs vs', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) ns ns ->
        tele_rel (ar m ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
        List.length vs = List.length gs -> List.length vs' = List.length gs ->
        forall a A v v', List.nth_error gs a = Some (ca_arg ak_propositional A) ->
        List.nth_error vs a = Some v -> List.nth_error vs' a = Some v' -> proof_readable v /\ proof_readable v'.
    Proof.
      intros * HMm Hcon Hns Har Lvs Lvs' * Ha Hv Hv'.
      destruct (List.nth_error_split _ _ Ha) as (gs1 & gs2 & -> & Lg1).
      destruct (List.nth_error_split _ _ Hv) as (vs1 & vs2 & -> & Lv1).
      destruct (List.nth_error_split _ _ Hv') as (vs1' & vs2' & -> & Lv1').
      rewrite !List.length_app in Lvs, Lvs'; cbn [List.length] in Lvs, Lvs'.
      rewrite !nonrec_arg_vals_app in Har by lia; cbn [nonrec_arg_vals] in Har.
      set (j := List.length (cargs_nonrec gs1)).
      assert (Lj : List.length (nonrec_arg_vals gs1 vs1) = j) by (apply length_nonrec_arg_vals; lia).
      assert (Lj' : List.length (nonrec_arg_vals gs1 vs1') = j) by (apply length_nonrec_arg_vals; lia).
      assert (HA : List.nth_error (cargs_nonrec (gs1 ++ ca_arg ak_propositional A :: gs2)) j = Some A)
        by (rewrite cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      pose proof (nonrec_kind_at gs1 gs2 ak_propositional A) as Hr.
      pose proof Har as H0; rewrite tele_rel_iff in H0; destruct H0 as (_ & _ & Hall).
      assert (Hy : List.nth_error (nonrec_arg_vals gs1 vs1 ++ v :: nonrec_arg_vals gs2 vs2) j = Some v)
        by (rewrite List.nth_error_app2, Lj, Nat.sub_diag by lia; reflexivity).
      assert (Hy' : List.nth_error (nonrec_arg_vals gs1 vs1' ++ v' :: nonrec_arg_vals gs2 vs2') j = Some v')
        by (rewrite List.nth_error_app2, Lj', Nat.sub_diag by lia; reflexivity).
      assert (Hjl : j <= List.length (cargs_nonrec (gs1 ++ ca_arg ak_propositional A :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; unfold j; lia).
      exact (canon_arg_proof m Mm c _ ns j A _ _ HMm Hcon Hns HA Hr (tele_prefix_rel_of_full _ _ _ _ j Har Hjl) v v' (Hall _ _ _ Hy Hy')).
    Qed.

    Lemma adm_of_ru : forall w, RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D -> adm_uparams D u0 nr ar dr w.
    Proof.
      intros w H Lw.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      exact (valid_group_adm p D Hvg u0 w u0_tele_args u0_len (U_tele_args _ _ (symmetry H) u0_len Lw)).
    Qed.

    (** The uniform parameters an eliminator carries, of the class of
        [u0]: as the model reads them. *)
    Lemma mrefs_of_ru : forall w, RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D -> mrefs_ok p D w.
    Proof.
      intros w Hw Lw j Mj HMj.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (Hww : RU (decl_env D w) (decl_env D w)) by (etransitivity; [ exact Hw | symmetry; exact Hw ]).
      split.
      - intros Hrv; destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
        + exists (p, j, w); eapply eval_mref_decl; [ exact Hl | exact HMj | exact Hh ].
        + destruct (view_target_decl P p D HP HPD j Mj HMj qc kc Is vm Hh) as (Dq & Mk' & pm & Hq & _ & _ & _).
          destruct (valid_group_views_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMj Hh Hq w w (U_tele_args _ _ Hww Lw Lw) Lw)
            as (cs & _ & Ecs & _ & _).
          exists (qc, kc, cs); eapply eval_mref_view; [ exact Hl | exact HMj | exact Hh | exact Ecs ].
        + exfalso; exact (not_rview_record _ _ _ _ Hrv Hh).
      - (** A record view: its instance at [w]. *)
        intros qr Is fl Hh.
        destruct (valid_group_records _ _ Hvg _ _ _ _ _ HMj Hh) as [R HR].
        destruct (valid_group_views_rview_args_values p D Hvg _ _ _ _ _ _ HMj Hh HR w w (U_tele_args _ _ Hww Lw Lw) Lw)
          as (cs & _ & Ecs & _ & _).
        exists cs; exact Ecs.
    Qed.

    (** The containers' uniform parameters at two uniform parameters of the
        class of [u0] read back alike. *)
    Lemma ups_container_uparams : forall w1 w2, RU (decl_env D w1) (decl_env D u0) -> RU (decl_env D w2) (decl_env D u0) ->
        List.length w1 = ind_nu D -> List.length w2 = ind_nu D ->
        forall j Mj hd k pa pb Dq, ind_member D j = Some Mj ->
          ⟦mref j of p w1 ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pa) -> ⟦mref j of p w2 ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pb) ->
          ind_lookup gc_deps gc_stack hd = Some Dq ->
          per_top_ps (List.rev (ind_uparams Dq)) pa pb.
    Proof.
      intros * H1 H2 L1 L2.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (H12 : RU (decl_env D w1) (decl_env D w2)) by (etransitivity; [ exact H1 | symmetry; exact H2 ]).
      pose proof (U_tele_args _ _ H12 L1 L2) as Hg12.
      intros * HMj Ea Eb Hq.
      inversion Ea as [? ? ? D1 M1 pm1 Hl1 HM1 Hh1 | ? ? ? D1 M1 qc1 k1 Is1 vm1 cs1 Hl1 HM1 Hh1 Ec1]; subst;
        rewrite Hl in Hl1; injection Hl1 as <-; rewrite HMj in HM1; injection HM1 as <-;
        inversion Eb as [? ? ? D2 M2 pm2 Hl2 HM2 Hh2 | ? ? ? D2 M2 qc2 k2 Is2 vm2 cs2 Hl2 HM2 Hh2 Ec2]; subst;
        rewrite Hl in Hl2; injection Hl2 as <-; rewrite HMj in HM2; injection HM2 as <-; try congruence.
      - rewrite Hl in Hq; injection Hq as <-.
        exact (per_tele_args_per_top_ps _ _ _ Hg12 ltac:(rewrite List.length_rev; exact L1)).
      - rewrite Hh1 in Hh2; injection Hh2; intros; subst.
        destruct (valid_group_views_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMj Hh1 Hq w1 w2 Hg12 L1) as (c0 & c0' & E0 & E0' & Hc0).
        pose proof (functional_eval_exps' _ _ _ _ E0 Ec1) as ->; pose proof (functional_eval_exps' _ _ _ _ E0' Ec2) as ->.
        destruct (view_target_decl P p D HP HPD j Mj HMj _ _ _ _ Hh1) as (Dq' & Mk' & pm & Hq' & _ & _ & HIl).
        rewrite Hq in Hq'; injection Hq' as <-.
        exact (per_tele_args_per_top_ps _ _ _ Hc0 ltac:(rewrite List.length_rev, (eval_exps_length _ _ _ Ec1), HIl; reflexivity)).
    Qed.

    (** Two neutrals of a record view's record type, at the instances of two
        sides' uniform parameters of the class of [u0], are related elements
        of the view: the record type's relation is the view's
        ([rview_end_rel_all]), at the canonical bases, moved to the sides'. *)
    Lemma rneut_rel : forall ua ub, RU (decl_env D ua) (decl_env D u0) -> RU (decl_env D ub) (decl_env D u0) ->
        List.length ua = ind_nu D -> List.length ub = ind_nu D ->
        forall j Mj qr Is fl cups1 cups2 e e', ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
        ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ua ↘ cups1 -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ub ↘ cups2 ->
        Dom e ≈ e' ∈ per_bot -> G j ua ub nil nil (⇑ (d_record qr cups1) e) (⇑ (d_record qr cups2) e').
    Proof.
      intros * Ha Hb La Lb * HMj Hh E1 E2 He.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      destruct (valid_group_records _ _ Hvg _ _ _ _ _ HMj Hh) as [R HR].
      assert (Hab : RU (decl_env D ua) (decl_env D ub)) by (etransitivity; [ exact Ha | symmetry; exact Hb ]).
      destruct (valid_group_views_rview_args_values p D Hvg _ _ _ _ _ _ HMj Hh HR ua ub (U_tele_args _ _ Hab La Lb) La) as (c1 & c2 & Ec1 & Ec2 & Hc12).
      pose proof (functional_eval_exps' _ _ _ _ Ec1 E1) as ->; pose proof (functional_eval_exps' _ _ _ _ Ec2 E2) as ->.
      assert (H0a : RU (decl_env D u0) (decl_env D ua)) by (symmetry; exact Ha).
      assert (H0b : RU (decl_env D u0) (decl_env D ub)) by (symmetry; exact Hb).
      destruct (valid_group_views_rview_args_values p D Hvg _ _ _ _ _ _ HMj Hh HR u0 ua (U_tele_args _ _ H0a u0_len La) u0_len) as (c0 & ca & Ec0 & Eca & Hc0a).
      destruct (valid_group_views_rview_args_values p D Hvg _ _ _ _ _ _ HMj Hh HR u0 ub (U_tele_args _ _ H0b u0_len Lb) u0_len) as (c0' & cb & Ec0' & Ecb & Hc0b).
      pose proof (functional_eval_exps' _ _ _ _ Eca E1) as ->; pose proof (functional_eval_exps' _ _ _ _ Ecb E2) as ->.
      pose proof (functional_eval_exps' _ _ _ _ Ec0' Ec0) as ->.
      assert (Lc : List.length cups1 = List.length (record_params R))
        by (rewrite (eval_exps_length _ _ _ E1); exact (rview_record_len p D Hvg _ _ _ _ _ _ HMj Hh HR)).
      destruct (vrr_type_rel qr R cups1 cups2 HR Hc12 Lc) as [i HRR].
      pose proof (rview_end_rel_all P p D HP HPD u0 u0 u0_tele_args u0_len j Mj qr Is fl R c0 c0 HMj Hh (valid_rview_record_lookup _ _ HR)
                    Ec0 Ec0 cups1 cups2 i _ Hc0a Hc0b HRR) as ER.
      pose proof (proj1 (ER _ _) (per_bot_then_per_elem HRR (per_bot_neutral_at (d_record qr cups1) _ _ ltac:(discriminate) ltac:(discriminate) He))) as H00.
      exact (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ ua ub _ _ _ _ Had (adm_of_ru ua Ha La) (adm_of_ru ub Hb Lb) H00).
    Qed.

    (** A closed telescope's environment over the value of the uniform
        parameters' instance at an environment [B], extended by readable
        values of the telescope at any types, against the canonical
        one. *)
    Lemma closed_pre_base : forall Pre RK, all_assumptions (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
        EF Pre ++ ind_uparams D ≈ Pre ++ ind_uparams D ∈ per_ctx_env ↘ RK ->
        forall B u vts zs, RΓ B B -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B ↘ u -> RU (decl_env D u) (decl_env D u0) ->
        per_tele_args (List.rev Pre) (decl_env D u0) (decl_env D u0) zs zs -> List.length zs = List.length Pre ->
        List.map fst vts = zs -> List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
        RK (env_extend_typed (env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ B) u) vts)
           (components_env D u0 (List.rev Pre) zs).
    Proof.
      intros * HKa HK HRK * HB Hu H10 Hg00 Lz0 Hvz Hvr.
      assert (HPa : all_assumptions Pre) by (apply List.Forall_app in HKa as [H _]; exact H).
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      pose proof (eval_exps_length _ _ _ Hu) as Lu1; rewrite HUl in Lu1.
      pose proof (U_tele_args _ _ H10 Lu1 u0_len) as Hg10.
      assert (Lv : List.length vts = List.length Pre) by (rewrite <- (List.length_map fst), Hvz; exact Lz0).
      assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK).
      pose proof (per_tele_args_base _ _ _ HRU HKr (List.Forall_rev HPa) (decl_env D u0) (decl_env D u0)
                    (decl_env D u) (decl_env D u0) zs zs u0_env (symmetry H10) u0_env Hg00) as Hgb.
      (** The closed environments of the values. *)
      assert (H0 : RK (env_tele nil (List.rev (Pre ++ ind_uparams D)) (u ++ zs)) (components_env D u0 (List.rev Pre) zs)).
      { rewrite <- (env_tele_uparams D Pre u0 zs u0_len).
        apply (tele_args_env_rel _ _ _ _ _ _ HRK HK); [ rewrite !List.length_app; unfold ind_nu in Lu1; lia |].
        rewrite List.rev_app_distr; apply per_tele_args_app_intro;
          [ rewrite List.length_rev; exact Lu1 | exact Hg10 | rewrite env_tele_uparams_nil; exact Hgb ]. }
      (** The instance's value holds the same values, which read back. *)
      destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ _].
      destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
      pose proof (uniform_params_sub_eval B B u HB Hu) as Hev.
      assert (HBτ : RUΓ (env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ B) u)
                        (env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ B) u))
        by (eapply (rel_sub_under_ctx_at' (gsub_valid gsub_U) HRΓ HRUΓ); eassumption).
      pose proof (proj1 (per_ctx_env_heads_readable HRUΓ _ _ HBτ)) as HrU.
      apply (env_heads_readable_app_tele _ _ _ Ua) in HrU.
      assert (Lt : List.length (List.rev (ind_uparams D)) = List.length u) by (rewrite List.length_rev; exact (eq_sym Lu1)).
      eapply (per_ctx_env_resp_retagged_left HRK _ _ _ _ _ H0). Unshelve.
      - rewrite env_extend_tagged_typed, <- env_extend_typed_app; unfold env_tele.
        replace (List.length (Pre ++ ind_uparams D)) with (List.length (tele_entries nil (List.rev (Pre ++ ind_uparams D)) (u ++ zs)))
          by (rewrite tele_entries_length, !List.length_app; unfold ind_nu in Lu1; lia).
        apply env_agree_retagged_typed.
        rewrite tele_entries_values, List.map_app, tagged_entries_fst by exact Lt; rewrite Hvz; reflexivity.
      - exact (env_heads_readable_tele_ext Pre (ind_uparams D) _ _ HPa Lv Hvr HrU).
    Qed.

    (** The same at any environment extended by readable values of the
        uniform parameters [w] of the class of [u0] and of the telescope:
        the closed telescope reads the values only. *)
    Lemma closed_pre_typed : forall Pre RK, all_assumptions (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
        EF Pre ++ ind_uparams D ≈ Pre ++ ind_uparams D ∈ per_ctx_env ↘ RK ->
        forall B w vts zs, RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
        per_tele_args (List.rev Pre) (decl_env D u0) (decl_env D u0) zs zs -> List.length zs = List.length Pre ->
        List.map fst vts = w ++ zs -> List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
        RK (env_extend_typed B vts) (components_env D u0 (List.rev Pre) zs).
    Proof.
      intros * HKa HK HRK * H10 Lw Hg00 Lz0 Hvz Hvr.
      assert (HPa : all_assumptions Pre) by (apply List.Forall_app in HKa as [H _]; exact H).
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
      pose proof (U_tele_args _ _ H10 Lw u0_len) as Hg10.
      assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK).
      pose proof (per_tele_args_base _ _ _ HRU HKr (List.Forall_rev HPa) (decl_env D u0) (decl_env D u0)
                    (decl_env D w) (decl_env D u0) zs zs u0_env (symmetry H10) u0_env Hg00) as Hgb.
      assert (Lt : List.length (w ++ zs) = List.length (Pre ++ ind_uparams D))
        by (rewrite !List.length_app; unfold ind_nu in Lw; lia).
      assert (Lt0 : List.length (u0 ++ zs) = List.length (Pre ++ ind_uparams D))
        by (rewrite !List.length_app; pose proof u0_len as L0; unfold ind_nu in L0; lia).
      assert (H0 : RK (env_tele nil (List.rev (Pre ++ ind_uparams D)) (w ++ zs)) (components_env D u0 (List.rev Pre) zs)).
      { rewrite <- (env_tele_uparams D Pre u0 zs u0_len).
        apply (tele_args_env_rel _ _ _ _ _ _ HRK HK); [ exact Lt |].
        rewrite List.rev_app_distr; apply per_tele_args_app_intro;
          [ rewrite List.length_rev; exact Lw | exact Hg10 | rewrite env_tele_uparams_nil; exact Hgb ]. }
      assert (H00 : RK (components_env D u0 (List.rev Pre) zs) (components_env D u0 (List.rev Pre) zs))
        by (etransitivity; [ symmetry; exact H0 | exact H0 ]).
      rewrite <- (env_tele_uparams D Pre u0 zs u0_len) in H0, H00 |- *.
      unfold env_tele in H0, H00 |- *.
      assert (HC' : ⊨ List.rev (List.rev (Pre ++ ind_uparams D)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HK).
      assert (HRC' : EF List.rev (List.rev (Pre ++ ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (Pre ++ ind_uparams D)) ++ ⋅
                       ∈ per_ctx_env ↘ RK)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRK).
      assert (Le0 : List.length (tele_entries nil (List.rev (Pre ++ ind_uparams D)) (u0 ++ zs)) = List.length (List.rev (Pre ++ ind_uparams D)))
        by (rewrite tele_entries_length, List.length_rev; exact Lt0).
      destruct (per_tele_args_of_env_extend_readable _ _ _ _ per_ctx_env_nil_true HC' (List.Forall_rev HKa) HRC' _ _ _ _ Le0 Le0 H00) as [Hr0 _].
      refine (closed_env_base _ RK _ _ vts _ nil nil B nil HKa HK HRK _ _ _ eq_refl Hvr Hr0 H0).
      - rewrite tele_entries_length; exact Lt.
      - rewrite tele_entries_length; exact Lt0.
      - rewrite tele_entries_values; exact Hvz.
    Qed.

    (** ** Instances of a Closed Telescope

        Arguments related at a closed telescope over the canonical uniform
        parameters are related at its instance, over any related
        environments whose uniform parameters are related to the canonical
        ones, and conversely. *)
    Lemma canonical_gen : forall Pre, all_assumptions (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D -> ⊨ tele_sub Pre τU ++ Γ ->
        forall B1 B2 u1 u2, RΓ B1 B2 ->
        ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 ->
        RU (decl_env D u1) (decl_env D u0) -> RU (decl_env D u2) (decl_env D u0) ->
        forall zs zs', per_tele_args (List.rev Pre) (decl_env D u0) (decl_env D u0) zs zs' -> List.length zs = List.length Pre ->
          per_tele_args (List.rev (tele_sub Pre τU)) B1 B2 zs zs'.
    Proof.
      induction Pre as [| e Pre IH]; intros HKa HK HS * HB Hu1 Hu2 H10 H20 zs zs' Hg Hlz.
      - destruct zs; cbn in Hlz; [| discriminate ]; inversion Hg; subst; constructor.
      - assert (He : exists κ A, e = ce_ass κ A) by (inversion HKa as [| ? ? He _]; exact He).
        destruct He as (κX & X & ->).
        assert (HKa' : all_assumptions (Pre ++ ind_uparams D)) by (inversion HKa; assumption).
        assert (HPa : all_assumptions Pre) by (apply List.Forall_app in HKa' as [H _]; exact H).
        pose proof (eval_exps_length _ _ _ Hu1) as Lu1; rewrite HUl in Lu1.
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        destruct (List.exists_last (l := zs) ltac:(intros ->; cbn in Hlz; discriminate)) as (zs0 & x & ->).
        rewrite List.length_app in Hlz; cbn in Hlz.
        assert (Lz0 : List.length zs0 = List.length Pre) by lia; clear Hlz.
        pose proof (per_tele_args_length _ _ _ _ _ Hg) as [Lzz _].
        rewrite List.length_app in Lzz; cbn [List.length] in Lzz.
        destruct (List.exists_last (l := zs') ltac:(intros ->; cbn in Lzz; lia)) as (zs0' & x' & ->).
        rewrite List.length_app in Lzz; cbn in Lzz.
        cbn [List.rev] in Hg.
        assert (Lr : List.length zs0 = List.length (List.rev Pre)) by (rewrite List.length_rev; exact Lz0).
        assert (Lr' : List.length zs0' = List.length (List.rev Pre)) by (rewrite List.length_rev; lia).
        destruct (per_tele_args_app (List.rev Pre) (ce_ass κX X :: nil) _ _ zs0 zs0' (x :: nil) (x' :: nil) Lr Hg Lr') as [Hg0 Hgx].
        inversion Hgx as [| ? ? ? ? ? ? ? ? ? ? R0 HX0 Hx _]; subst.
        cbn [tele_sub centry_sub List.rev List.app] in HS |- *.
        destruct (rel_ctx_wf_ass_inv HS) as (Si & HSi & HXi).
        destruct (rel_type_of_sort_at (sort_kind_type_sort _ _ HSi)) as [j Hj].
        pose proof (rel_ctx_wf_tail HS) as HS'.
        destruct (rel_ctx_wf_ass_inv HK) as (Sc & HSc & HXc).
        pose proof (rel_ctx_wf_tail HK) as HK'.
        pose proof (IH HKa' HK' HS' _ _ _ _ HB Hu1 Hu2 H10 H20 _ _ Hg0 Lz0) as IHz.
        destruct (rel_ctx_wf_per_ctx_env HS') as [RS HRS].
        assert (HE : RS (env_tele B1 (List.rev (tele_sub Pre τU)) zs0) (env_tele B2 (List.rev (tele_sub Pre τU)) zs0'))
          by (eapply tele_args_env_rel_gen; [ exact HRΓ | exact HRS | exact HS' | exact HB | rewrite length_tele_sub; exact Lz0 | exact IHz ]).
        destruct (rel_type_inversion_simple_at HRS (Hj _ _ _ HXi) _ _ HE) as (t1 & t2 & Et1 & Et2 & [R12 HR12]).
        assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
        assert (HEE : RS (env_tele B1 (List.rev (tele_sub Pre τU)) zs0) (env_tele B1 (List.rev (tele_sub Pre τU)) zs0))
          by (etransitivity; [ exact HE | symmetry; exact HE ]).
        destruct (rel_ctx_wf_per_ctx_env HK') as [RK HRK].
        assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK').
        pose proof (per_tele_args_refl_l _ _ _ HRU HKr (List.Forall_rev HPa) (decl_env D u0) (decl_env D u0) zs0 zs0' u0_env Hg0) as Hg00.
        assert (HB11 : RΓ B1 B1) by (etransitivity; [ exact HB | symmetry; exact HB ]).
        pose proof (proj1 (per_tele_args_entries_readable _ _ _ _ _ IHz)) as Hr1.
        pose proof (closed_pre_base Pre RK HKa' HK' HRK B1 u1 _ zs0 HB11 Hu1 H10 Hg00 Lz0 (tele_entries_values _ _ _) Hr1) as HK1.
        destruct (closed_typ_inst Pre (ind_uparams D) Γ X Sc τU RΓ RK RS B1 _ _ _
                    HKa' HK' Ua Usem HΓ HRΓ HRK HRS (sort_kind_type_sort _ _ HSc) HXc (gsub_valid gsub_U) HEE
                    ltac:(rewrite tele_entries_length; exact Lz0)
                    (uniform_params_sub_eval B1 B2 u1 HB Hu1) HK1)
          as (jc & a & c & Ea & Ec & [R1c HR1c]).
        assert (a = t1) as -> by (eapply functional_eval_exp; eassumption).
        destruct HX0 as [c0 c0' Ec0 Ec0' HR0].
        assert (c0 = c) as -> by (eapply functional_eval_exp; eassumption).
        assert (E1 : R12 <~> R1c) by (eapply per_univ_elem_right_irrel; [ exact HR12 | exact HR1c ]).
        assert (E2 : R1c <~> R0) by (eapply per_univ_elem_chain_iff; [ exact HR1c | exact HR0 ]).
        destruct (per_univ_elem_to_nat _ _ _ _ HR12) as [n Hn].
        apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ n R12).
        + rewrite List.length_rev, length_tele_sub; exact Lz0.
        + exact IHz.
        + exact (mk_rel_mod_eval t1 t2 Et1 Et2 Hn).
        + apply E1, E2; exact Hx.
    Qed.

    Lemma canonical_gen_rev : forall Pre, all_assumptions (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D -> ⊨ tele_sub Pre τU ++ Γ ->
        forall B1 B2 u1, RΓ B1 B2 ->
        ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> RU (decl_env D u1) (decl_env D u0) ->
        forall zs zs', per_tele_args (List.rev (tele_sub Pre τU)) B1 B2 zs zs' -> List.length zs = List.length Pre ->
          per_tele_args (List.rev Pre) (decl_env D u0) (decl_env D u0) zs zs'.
    Proof.
      induction Pre as [| e Pre IH]; intros HKa HK HS * HB Hu1 H10 zs zs' Hg Hlz.
      - destruct zs; cbn in Hlz; [| discriminate ]; inversion Hg; subst; constructor.
      - assert (He : exists κ A, e = ce_ass κ A) by (inversion HKa as [| ? ? He _]; exact He).
        destruct He as (κX & X & ->).
        assert (HKa' : all_assumptions (Pre ++ ind_uparams D)) by (inversion HKa; assumption).
        assert (HPa : all_assumptions Pre) by (apply List.Forall_app in HKa' as [H _]; exact H).
        pose proof (eval_exps_length _ _ _ Hu1) as Lu1; rewrite HUl in Lu1.
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        destruct (List.exists_last (l := zs) ltac:(intros ->; cbn in Hlz; discriminate)) as (zs0 & x & ->).
        rewrite List.length_app in Hlz; cbn in Hlz.
        assert (Lz0 : List.length zs0 = List.length Pre) by lia; clear Hlz.
        pose proof (per_tele_args_length _ _ _ _ _ Hg) as [Lzz _].
        rewrite List.length_app in Lzz; cbn [List.length] in Lzz.
        destruct (List.exists_last (l := zs') ltac:(intros ->; cbn in Lzz; lia)) as (zs0' & x' & ->).
        rewrite List.length_app in Lzz; cbn in Lzz.
        cbn [tele_sub centry_sub List.rev List.app] in HS, Hg |- *.
        assert (Lr : List.length zs0 = List.length (List.rev (tele_sub Pre τU))) by (rewrite List.length_rev, length_tele_sub; exact Lz0).
        assert (Lr' : List.length zs0' = List.length (List.rev (tele_sub Pre τU))) by (rewrite List.length_rev, length_tele_sub; lia).
        destruct (per_tele_args_app (List.rev (tele_sub Pre τU)) _ _ _ zs0 zs0' (x :: nil) (x' :: nil) Lr Hg Lr') as [Hg0 Hgx].
        inversion Hgx as [| ? ? ? ? ? ? ? ? ? ? R0 HX0 Hx _]; subst.
        pose proof (rel_ctx_wf_tail HS) as HS'.
        destruct (rel_ctx_wf_ass_inv HK) as (Sc & HSc & HXc).
        pose proof (rel_ctx_wf_tail HK) as HK'.
        pose proof (IH HKa' HK' HS' _ _ _ HB Hu1 H10 _ _ Hg0 Lz0) as IHz.
        destruct (rel_ctx_wf_per_ctx_env HS') as [RS HRS].
        assert (HE : RS (env_tele B1 (List.rev (tele_sub Pre τU)) zs0) (env_tele B2 (List.rev (tele_sub Pre τU)) zs0'))
          by (eapply tele_args_env_rel_gen; [ exact HRΓ | exact HRS | exact HS' | exact HB | rewrite length_tele_sub; exact Lz0 | exact Hg0 ]).
        assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
        assert (HEE : RS (env_tele B1 (List.rev (tele_sub Pre τU)) zs0) (env_tele B1 (List.rev (tele_sub Pre τU)) zs0))
          by (etransitivity; [ exact HE | symmetry; exact HE ]).
        destruct (rel_ctx_wf_per_ctx_env HK') as [RK HRK].
        assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
        assert (HKr : ⊨ List.rev (List.rev Pre) ++ ind_uparams D) by (rewrite List.rev_involutive; exact HK').
        pose proof (per_tele_args_refl_l _ _ _ HRU HKr (List.Forall_rev HPa) (decl_env D u0) (decl_env D u0) zs0 zs0' u0_env IHz) as Hg00.
        assert (HB11 : RΓ B1 B1) by (etransitivity; [ exact HB | symmetry; exact HB ]).
        pose proof (proj1 (per_tele_args_entries_readable _ _ _ _ _ Hg0)) as Hr1.
        pose proof (closed_pre_base Pre RK HKa' HK' HRK B1 u1 _ zs0 HB11 Hu1 H10 Hg00 Lz0 (tele_entries_values _ _ _) Hr1) as HK1.
        destruct (closed_typ_inst Pre (ind_uparams D) Γ X Sc τU RΓ RK RS B1 _ _ _
                    HKa' HK' Ua Usem HΓ HRΓ HRK HRS (sort_kind_type_sort _ _ HSc) HXc (gsub_valid gsub_U) HEE
                    ltac:(rewrite tele_entries_length; exact Lz0)
                    (uniform_params_sub_eval B1 B2 u1 HB Hu1) HK1)
          as (jc & a & c & Ea & Ec & [R1c HR1c]).
        destruct HX0 as [a0 a0' Ea0 Ea0' HR0].
        assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
        (** The closed entry at the two canonical prefixes. *)
        assert (HKK : RK (components_env D u0 (List.rev Pre) zs0) (components_env D u0 (List.rev Pre) zs0')).
        { rewrite <- !(env_tele_uparams D Pre u0 _ u0_len).
          apply (tele_args_env_rel _ _ _ _ _ _ HRK HK'); [ rewrite !List.length_app; pose proof u0_len as L0; unfold ind_nu in L0; lia |].
          rewrite List.rev_app_distr; apply per_tele_args_app_intro;
            [ rewrite List.length_rev; exact u0_len | exact u0_tele_args | rewrite env_tele_uparams_nil; exact IHz ]. }
        destruct (rel_type_of_sort_at (sort_kind_type_sort _ _ HSc)) as [jc' Hjc].
        destruct (rel_type_inversion_simple_at HRK (Hjc _ _ _ HXc) _ _ HKK) as (c1 & c1' & Ec1 & Ec1' & [Rc HRc]).
        assert (c1 = c) as -> by (eapply functional_eval_exp; eassumption).
        assert (E1 : R0 <~> R1c) by (eapply per_univ_elem_right_irrel; [ exact HR0 | exact HR1c ]).
        assert (E2 : R1c <~> Rc) by (eapply per_univ_elem_chain_iff; [ exact HR1c | exact HRc ]).
        destruct (per_univ_elem_to_nat _ _ _ _ HRc) as [n Hn].
        apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ n Rc).
        + rewrite List.length_rev; exact Lz0.
        + exact IHz.
        + exact (mk_rel_mod_eval c c1' Ec1 Ec1' Hn).
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

      Lemma mctx_split : elim_mctx p D k Mk Us ++ Γ = (tele_sub (im_nparams Mk) τU ++ Γ) ▹{ak_relevant} IT.
      Proof. reflexivity. Qed.

      Lemma base_member_HNt : ⊨ tele_sub (im_nparams Mk) τU ++ Γ.
      Proof. exact (rel_ctx_wf_tail HMm). Qed.

      Lemma base_member_Pa : all_assumptions (im_nparams Mk ++ ind_uparams D).
      Proof. exact (member_params_ass D Hc _ _ HMk). Qed.

      Lemma base_member_Ps : ⊨ im_nparams Mk ++ ind_uparams D.
      Proof. exact (valid_ind_decl_params _ HD _ _ HMk). Qed.

      Lemma base_member_T_len : List.length T = im_nn Mk.
      Proof. unfold T; rewrite List.length_rev; reflexivity. Qed.

      (** Canonically related non-uniform parameters are related at their
          closed telescope at [u0], and conversely. *)
      Lemma nparams_closed_of_canon : forall ns ns', tele_rel (nr k) T ns ns' ->
          per_tele_args (List.rev (im_nparams Mk)) (decl_env D u0) (decl_env D u0) ns ns'.
      Proof.
        intros * Hns.
        destruct (sort_value D HD u0 u0_tele_args u0_len) as [a0 Ha0].
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        pose proof (nr_tele_args D HD Hc Hsu k Mk HMk u0 u0 a0 u0_tele_args u0_len Ha0 (im_nn Mk) ns ns' (le_n _)
                      ltac:(apply tele_rel_pre in Hns; rewrite base_member_T_len in Hns; exact Hns)) as H.
        rewrite List.firstn_all2 in H by (rewrite List.length_rev; reflexivity); exact H.
      Qed.

      Lemma canon_of_nparams_closed : forall ns ns', List.length ns = im_nn Mk ->
          per_tele_args (List.rev (im_nparams Mk)) (decl_env D u0) (decl_env D u0) ns ns' -> tele_rel (nr k) T ns ns'.
      Proof.
        intros * Ln Hg0.
        refine (tele_rel_of_per_tele_args T (nr k) (decl_env D u0) _ (decl_env D u0) ns ns' Hg0 ltac:(rewrite base_member_T_len; exact Ln)).
        intros j κ A pre HA.
        unfold nr, canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ _ HMk HA), (member_nparams_eq _ _ _ HMk); reflexivity.
      Qed.

      Lemma canonical_nparams : forall B1 B2 u1 u2, RΓ B1 B2 ->
          ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B2 ↘ u2 ->
          RU (decl_env D u1) (decl_env D u0) -> RU (decl_env D u2) (decl_env D u0) ->
          forall ns ns', tele_rel (nr k) T ns ns' ->
          per_tele_args (List.rev (tele_sub (im_nparams Mk) τU)) B1 B2 ns ns'.
      Proof.
        intros * HB Hu1 Hu2 H10 H20 * Hns.
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _).
        exact (canonical_gen (im_nparams Mk) base_member_Pa base_member_Ps base_member_HNt B1 B2 u1 u2 HB Hu1 Hu2 H10 H20 ns ns'
                 (nparams_closed_of_canon _ _ Hns) ltac:(rewrite base_member_T_len in Ln; rewrite length_im_nparams; exact Ln)).
      Qed.

      Lemma canonical_nparams_rev : forall B1 B2 u1, RΓ B1 B2 ->
          ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> RU (decl_env D u1) (decl_env D u0) ->
          forall ns ns', List.length ns = im_nn Mk ->
          per_tele_args (List.rev (tele_sub (im_nparams Mk) τU)) B1 B2 ns ns' -> tele_rel (nr k) T ns ns'.
      Proof.
        intros * HB Hu1 H10 * Ln Hg0.
        apply canon_of_nparams_closed; [ exact Ln |].
        exact (canonical_gen_rev (im_nparams Mk) base_member_Pa base_member_Ps base_member_HNt B1 B2 u1 HB Hu1 H10 ns ns' Hg0
                 ltac:(rewrite length_im_nparams; exact Ln)).
      Qed.

      (** The relation of the member's type at an environment of the class
          of [C1] and canonically related non-uniform parameters: the
          group's at [k], at the canonical bases. *)
      Lemma mctx_head_rel : forall B1 B2 u1, RΓ B1 B2 ->
          ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ B1 ↘ u1 -> RU (decl_env D u1) (decl_env D u0) ->
          forall RS, EF tele_sub (im_nparams Mk) τU ++ Γ ≈ tele_sub (im_nparams Mk) τU ++ Γ ∈ per_ctx_env ↘ RS ->
          forall ns ns' vts1 vts2, tele_rel (nr k) T ns ns' -> List.map fst vts1 = ns -> List.map fst vts2 = ns' ->
          RS (env_extend_typed B1 vts1) (env_extend_typed B1 vts1) ->
          forall t1 t2 (i : universe_index) R, ⟦ IT ⟧ env_extend_typed B1 vts1 ↘ t1 ->
          ⟦ IT ⟧ env_extend_typed B2 vts2 ↘ t2 ->
          DF t1 ≈ t2 ∈ per_univ_elem i ↘ R -> (R <~> G k u0 u0 ns ns').
      Proof.
        intros * HB Hu1 H10 RS HRS * Hns Hv1 Hv2 HEE * Et1 Et2 HR.
        destruct (sort_value D HD u0 u0_tele_args u0_len) as [a0 Ha0].
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        pose proof (eval_exps_length _ _ _ Hu1) as Lu1; rewrite HUl in Lu1.
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & Ln' & _).
        rewrite base_member_T_len in Ln, Ln'.
        destruct (rel_ctx_wf_per_ctx_env base_member_Ps) as [RK HRK].
        assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
        destruct (mty_vars_valid p D Hvg Hcv k Mk HMk) as [jx HX].
        (** The closed side. *)
        pose proof (params_tele_args D HD Hc Hsu k Mk HMk u0 u0 a0 ns ns' u0_tele_args u0_len Ha0 Hns) as Hgc.
        assert (HKc : RK (components_env D u0 T ns) (components_env D u0 T ns')).
        { unfold T; rewrite <- !(env_tele_uparams D (im_nparams Mk) u0 _ u0_len).
          apply (tele_args_env_rel _ _ _ _ _ _ HRK base_member_Ps); [| exact Hgc ].
          rewrite !List.length_app, length_im_nparams; pose proof u0_len as L0; unfold ind_nu in L0; lia. }
        destruct (rel_exp_of_typ_inversion_simple_at HRK HX _ _ HKc) as (c1 & c2 & Ec1 & Ec2 & [Rc HRc]).
        assert (Ev : forall zs, List.length zs = im_nn Mk -> ⟦ vars_from 0 (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u0 T zs ↘ zs).
        { intros zs Lz; unfold components_env, env_tele.
          pose proof (eval_vars_from_args (tele_entries (decl_env D u0) T zs) (decl_env D u0) nil) as H.
          rewrite List.app_nil_r, tele_entries_values, tele_entries_length in H; cbn [List.length] in H.
          rewrite Lz in H; exact H. }
        pose proof (member_type_rel P p D HP HPD k Mk u0 u0 (im_nparams Mk) RK ns ns' (im_nn Mk) 0 (vars_from 0 (im_nn Mk))
                      ns ns' c1 c2 jx Rc HMk u0_len u0_tele_args base_member_Ps HRK ltac:(rewrite length_im_nparams; exact Ln)
                      ltac:(rewrite length_im_nparams; exact Ln') ltac:(cbn; lia) HKc (length_vars_from _ _) (Ev _ Ln) (Ev _ Ln')
                      Ec1 Ec2 HRc) as ERc.
        (** The left side, against the closed one. *)
        assert (Hg00 : per_tele_args (List.rev (im_nparams Mk)) (decl_env D u0) (decl_env D u0) ns ns)
          by exact (nparams_closed_of_canon _ _ (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk _ _ Hns)).
        assert (HB11 : RΓ B1 B1) by (etransitivity; [ exact HB | symmetry; exact HB ]).
        assert (Hta : all_assumptions (List.rev (tele_sub (im_nparams Mk) τU)))
          by (apply List.Forall_rev, all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMk)).
        assert (HNr : ⊨ List.rev (List.rev (tele_sub (im_nparams Mk) τU)) ++ Γ) by (rewrite List.rev_involutive; exact base_member_HNt).
        assert (HRSr : EF List.rev (List.rev (tele_sub (im_nparams Mk) τU)) ++ Γ ≈ List.rev (List.rev (tele_sub (im_nparams Mk) τU)) ++ Γ
                         ∈ per_ctx_env ↘ RS) by (rewrite List.rev_involutive; exact HRS).
        assert (Lt : List.length vts1 = List.length (List.rev (tele_sub (im_nparams Mk) τU)))
          by (rewrite <- (List.length_map fst), Hv1, List.length_rev, length_tele_sub; exact Ln).
        destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HNr Hta HRSr _ _ _ _ Lt Lt HEE) as [Hr1 _].
        pose proof (closed_pre_base (im_nparams Mk) RK base_member_Pa base_member_Ps HRK B1 u1 _ ns HB11 Hu1 H10 Hg00
                      ltac:(rewrite length_im_nparams; exact Ln) Hv1 Hr1) as HK1.
        destruct (closed_typ_inst (im_nparams Mk) (ind_uparams D) Γ _ Typeω@jx τU RΓ RK RS B1 _ _ _
                    base_member_Pa base_member_Ps Ua Usem HΓ HRΓ HRK HRS ltac:(constructor) HX
                    (gsub_valid gsub_U) HEE ltac:(rewrite Lt, List.length_rev, length_tele_sub; reflexivity)
                    (uniform_params_sub_eval B1 B2 u1 HB Hu1) HK1)
          as (jc & a & c & Ea & Ec & [R1c HR1c]).
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
      Lemma canonical_mctx : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
          forall RM, EF elim_mctx p D k Mk Us ++ Γ ≈ elim_mctx p D k Mk Us ++ Γ ∈ per_ctx_env ↘ RM ->
          forall ns ns' u u' m m', tele_rel (nr k) T ns ns' -> G k u u' ns ns' m m' ->
            RM (env_tele B1 (List.rev (elim_mctx p D k Mk Us)) (ns ++ m :: nil))
               (env_tele B2 (List.rev (elim_mctx p D k Mk Us)) (ns' ++ m' :: nil)).
      Proof.
        intros * HB1 HB2 RM HRM * Hns Hm.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        assert (HB : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
        destruct (us_class B1 HB1) as (u1 & Hu1 & H10); destruct (us_class B2 HB2) as (u2 & Hu2 & H20).
        pose proof Hns as H0; rewrite tele_rel_iff in H0; destruct H0 as (Ln & _ & _); rewrite base_member_T_len in Ln.
        pose proof (canonical_nparams B1 B2 u1 u2 HB Hu1 Hu2 H10 H20 ns ns' Hns) as Hg.
        assert (LNt : List.length (tele_sub (im_nparams Mk) τU) = im_nn Mk) by (rewrite length_tele_sub; reflexivity).
        pose proof HMm as HM'; rewrite mctx_split in HM'.
        destruct (rel_ctx_wf_ass_inv HM') as (Sj & HSj & HIT0).
        destruct (rel_exp_univ_of_sort_relevant _ _ _ (sort_kind_type_sort _ _ HSj) HIT0 (fun ρ0 a Ea => ind_mty_relevant _ _ _ _ _ _ _ _ HMk Ea)
                (fun ρ0 a Ea => ind_mty_not_level _ _ _ _ _ _ _ _ HMk Ea))
          as [j HIT].
        destruct (rel_ctx_wf_per_ctx_env base_member_HNt) as [RN HRN].
        assert (HPN : PER RN) by (eapply per_env_PER; exact HRN).
        assert (HE : RN (env_tele B1 (List.rev (tele_sub (im_nparams Mk) τU)) ns) (env_tele B2 (List.rev (tele_sub (im_nparams Mk) τU)) ns'))
          by (eapply tele_args_env_rel_gen; [ exact HRΓ | exact HRN | exact base_member_HNt | exact HB | lia | exact Hg ]).
        assert (HEE : RN (env_tele B1 (List.rev (tele_sub (im_nparams Mk) τU)) ns) (env_tele B1 (List.rev (tele_sub (im_nparams Mk) τU)) ns))
          by (etransitivity; [ exact HE | symmetry; exact HE ]).
        destruct (rel_exp_of_typ_inversion_simple_at HRN HIT _ _ HE) as (t1 & t2 & Et1 & Et2 & [R12 HR12]).
        pose proof (mctx_head_rel B1 B2 u1 HB Hu1 H10 RN HRN ns ns' _ _ Hns (tele_entries_values _ _ _) (tele_entries_values _ _ _)
                      HEE t1 t2 j R12 Et1 Et2 HR12) as ER.
        eapply tele_args_env_rel_gen; [ exact HRΓ | exact HRM | exact HMm | exact HB | rewrite List.length_app, length_elim_mctx; cbn; lia |].
        unfold elim_mctx; cbn [List.rev].
        destruct (per_univ_elem_to_nat _ _ _ _ HR12) as [n Hn].
        apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ n R12);
          [ rewrite List.length_rev, length_tele_sub; exact Ln | exact Hg | exact (mk_rel_mod_eval _ _ Et1 Et2 Hn) |].
        apply ER.
        exact (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k u u' u0 u0 ns ns' m m' Had Had Had Hm).
      Qed.
    End Member.

    #[local] Abbreviation tsym := (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).
    #[local] Abbreviation ttrans := (nparams_rel_trans p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).
    #[local] Abbreviation trefl_l := (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).
    #[local] Abbreviation trefl_r := (nparams_rel_refl_r p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).
    #[local] Abbreviation isym := (proj1 (ind_rel_sym_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (admissible_index_at D u0 nr))).
    #[local] Abbreviation itrans := (proj1 (ind_rel_trans_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (admissible_index_at D u0 nr))).
    #[local] Abbreviation ind_rel_idx_u0 := (ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (admissible_index_at D u0 nr)).
    #[local] Abbreviation ins := (ind_rel_ns p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (admissible_index_at D u0 nr)).

    (** *** The Types of the Members at the Class of [u0]

        A member's type at uniform parameters [w] of the class of [u0],
        at indices related to others: related to its type at [u0], at the
        group's relation from [u0] to [w].  At a declared member it is the
        group's own type; at a view, the container's member's, whose
        relation is the group's at the view ([view_end_rel_all]). *)
    Lemma member_type_from_u0 : forall w j Mj hd0 k0 p0 hd k pw bs bs',
        RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
        ind_member D j = Some Mj -> im_is_rview Mj = false ->
        ⟦mref j of p u0 ⟧ gc_deps ⍮ gc_stack ↘ (hd0, k0, p0) -> ⟦mref j of p w ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pw) ->
        tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs' ->
        exists (i : universe_index) R, DF d_ind hd0 k0 (p0 ++ bs) ≈ d_ind hd k (pw ++ bs') ∈ per_univ_elem i ↘ R /\
          (R <~> G j u0 w bs bs').
    Proof.
      intros * Hw Lw HMj Hrv E0 Ew Hbs.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      pose proof (U_tele_args _ _ (symmetry Hw) u0_len Lw) as Hg0w.
      destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; [| | exfalso; exact (not_rview_record _ _ _ _ Hrv Hh) ].
      - pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMj Hh E0) as Er0; injection Er0 as -> -> ->.
        pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HMj Hh Ew) as Erw; injection Erw as -> -> ->.
        destruct (valid_group_relate p D Hvg j Mj pm u0 w bs bs' HMj Hh Hg0w u0_len Hbs) as [i Hi].
        exists i, (G j u0 w bs bs'); split; [ exact Hi | reflexivity ].
      - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMj Hh E0) as (c0 & Er0 & Ec0); injection Er0 as -> -> ->.
        destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMj Hh Ew) as (cw & Erw & Ecw); injection Erw as -> -> ->.
        destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & HMk' & Hkd & HIl & _ & Hvm & _ & _).
        pose proof (Hcv _ _ _ _ _ _ _ HMj Hh Hq) as HgQ.
        assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
        { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
          unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate | discriminate ]. }
        destruct Hhd as [pm Hhd].
        destruct (valid_group_views_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMj Hh Hq u0 w Hg0w u0_len)
          as (c1 & c1' & E1 & E1' & Hc01).
        pose proof (functional_eval_exps' _ _ _ _ E1 Ec0) as ->; pose proof (functional_eval_exps' _ _ _ _ E1' Ecw) as ->.
        assert (Hlc : List.length c0 = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ Ec0); exact HIl).
        pose proof (view_agreement_canonical_all P p D HP HPD u0 u0 u0_tele_args u0_len j _ _ _ _ _ _ _ _ HMj Hh Hq Ec0 Ec0) as Hvc.
        destruct (agree_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvc _ _ HMk') as (v & Mv & Hvmb).
        assert (v = j) as -> by (pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
        assert (Mv = Mj) as -> by (pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HMj in HMv; congruence).
        pose proof (nr_from p D u0 u0 _ _ _ qc Dq c0 c0 _ _ _ vm Hvc kc Mk' j Mj bs bs' HMk' Hvmb Hbs) as Hbs'.
        destruct (valid_group_relate qc Dq HgQ kc Mk' pm c0 cw bs bs' HMk' Hhd Hc01 Hlc Hbs') as [i W].
        exists i; eexists; split; [ exact W |].
        pose proof (valid_group_valid _ _ HgQ) as HDq; pose proof (valid_group_closed _ _ HgQ) as HcQ.
        exact (view_end_rel_all P p D HP HPD u0 w Hg0w u0_len j Mj qc kc Is vm Dq c0 cw HMj Hh Hq Ec0 Ecw c0 cw bs bs' i _
                 (uparams_refl_l Dq HDq HcQ _ _ Hc01)
                 (uparams_refl_l Dq HDq HcQ _ _ (uparams_sym Dq HDq HcQ _ _ Hc01 Hlc)) W).
    Qed.

    (** The member's type at [u0] is defined. *)
    Lemma member_mref_u0 : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false ->
        exists hd0 k0 p0, ⟦mref j of p u0 ⟧ gc_deps ⍮ gc_stack ↘ (hd0, k0, p0).
    Proof.
      intros * HMj Hrv.
      destruct (proj1 (mrefs_of_ru u0 u0_env u0_len j Mj HMj) Hrv) as [[[hd0 k0] p0] E0].
      exists hd0, k0, p0; exact E0.
    Qed.

    (** Two elements of a member at admissible bases, the left one at its
        indices moved to related ones and at the class of [u0]: an element
        at the bases [u0] and [w]. *)
    Lemma member_element_at : forall w j Mj u u' bs bs' bs2 v v', RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
        ind_member D j = Some Mj -> adm_uparams D u0 nr ar dr u -> adm_uparams D u0 nr ar dr u' ->
        G j u u' bs bs' v v' -> tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs2 -> G j u0 w bs2 bs2 v v.
    Proof.
      intros * Hw Lw HMj Hu Hu' Hv Hbs.
      pose proof (itrans _ _ _ _ _ _ _ Hv _ _ _ _ (isym _ _ _ _ _ _ _ Hv)) as Hvv.
      pose proof (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI j u u u0 w bs bs v v Had Had (adm_of_ru w Hw Lw) Hvv)
        as Hvv'.
      exact (ind_rel_idx_u0 _ _ _ _ _ _ _ _ _ _ HMj Hvv' Hbs Hbs).
    Qed.

    (** The left one of two elements of a member at admissible bases reads
        back at the member's type at [w], at indices related to its own. *)
    Lemma member_elements_readable : forall w j Mj hd k pw u u' bs bs' bs2 v v',
        RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
        ind_member D j = Some Mj -> im_is_rview Mj = false ->
        adm_uparams D u0 nr ar dr u -> adm_uparams D u0 nr ar dr u' ->
        ⟦mref j of p w ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pw) -> G j u u' bs bs' v v' ->
        tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs2 ->
        entry_readable (de_term v (entry_type_value (d_ind hd k (pw ++ bs2)))).
    Proof.
      intros * Hw Lw HMj Hrv Hu Hu' Ew Hv Hbs.
      destruct (member_mref_u0 j Mj HMj Hrv) as (hd0 & k0 & p0 & E0).
      pose proof (trefl_r _ _ HMj _ _ Hbs) as Hbs2.
      destruct (member_type_from_u0 w j Mj hd0 k0 p0 hd k pw bs2 bs2 Hw Lw HMj Hrv E0 Ew Hbs2) as (i & R & HR & ER).
      pose proof (member_element_at w j Mj u u' bs bs' bs2 v v' Hw Lw HMj Hu Hu' Hv Hbs) as Hvv.
      exact (proj2 (entry_readable_of_elem HR (proj2 (ER _ _) Hvv))).
    Qed.

    (** The left one of two elements of a record view at admissible bases
        reads back at the record type at its instance at [w]. *)
    Lemma rview_elements_readable : forall w j Mj qr Is fl cw u u' v v',
        RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
        ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
        adm_uparams D u0 nr ar dr u -> adm_uparams D u0 nr ar dr u' ->
        ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D w ↘ cw -> G j u u' nil nil v v' ->
        entry_readable (de_term v (entry_type_value (d_record qr cw))).
    Proof.
      intros * Hw Lw HMj Hh Hu Hu' Ecw Hv.
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      pose proof (U_tele_args _ _ (symmetry Hw) u0_len Lw) as Hg0w.
      destruct (valid_group_records _ _ Hvg _ _ _ _ _ HMj Hh) as [R HR].
      destruct (valid_group_views_rview_args_values p D Hvg _ _ _ _ _ _ HMj Hh HR u0 w Hg0w u0_len)
        as (c0 & cw' & Ec0 & Ecw' & Hc0w).
      pose proof (functional_eval_exps' _ _ _ _ Ecw' Ecw) as ->.
      assert (Hlc : List.length c0 = List.length (record_params R)) by (rewrite (eval_exps_length _ _ _ Ec0); exact (rview_record_len p D Hvg _ _ _ _ _ _ HMj Hh HR)).
      destruct (vrr_type_rel qr R c0 cw HR Hc0w Hlc) as [i W].
      assert (Hww : RU (decl_env D w) (decl_env D w)) by (etransitivity; [ exact Hw | symmetry; exact Hw ]).
      destruct (valid_group_views_rview_args_values p D Hvg _ _ _ _ _ _ HMj Hh HR u0 u0 u0_tele_args u0_len)
        as (c1 & c1' & Ec1 & Ec1' & Hc00).
      pose proof (functional_eval_exps' _ _ _ _ Ec1 Ec0) as ->; pose proof (functional_eval_exps' _ _ _ _ Ec1' Ec0) as ->.
      destruct (valid_group_views_rview_args_values p D Hvg _ _ _ _ _ _ HMj Hh HR w w (U_tele_args _ _ Hww Lw Lw) Lw)
        as (c2 & c2' & Ec2 & Ec2' & Hcww).
      pose proof (functional_eval_exps' _ _ _ _ Ec2 Ecw) as ->; pose proof (functional_eval_exps' _ _ _ _ Ec2' Ecw) as ->.
      assert (Hnil : tele_rel (nr j) (List.rev (im_nparams Mj)) nil nil)
        by (rewrite (member_closed_rview_nn _ _ (decl_closed_members _ Hc _ _ HMj) _ _ _ Hh); split; [ reflexivity | exact I ]).
      pose proof (member_element_at w j Mj u u' nil nil nil v v' Hw Lw HMj Hu Hu' Hv Hnil) as Hvv.
      pose proof (rview_end_rel_all P p D HP HPD u0 w Hg0w u0_len j Mj qr Is fl R c0 cw HMj Hh (valid_rview_record_lookup _ _ HR)
                    Ec0 Ecw c0 cw i _ Hc00 Hcww W)
        as ER.
      exact (proj2 (entry_readable_of_elem W (proj2 (ER _ _) Hvv))).
    Qed.

    (** A member's types at two uniform parameters of the class of [u0],
        at related indices, read back alike. *)
    Lemma member_types_alike : forall w1 w2 j Mj hd k pa pb bs bs',
        RU (decl_env D w1) (decl_env D u0) -> RU (decl_env D w2) (decl_env D u0) ->
        List.length w1 = ind_nu D -> List.length w2 = ind_nu D ->
        ind_member D j = Some Mj -> im_is_rview Mj = false ->
        ⟦mref j of p w1 ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pa) -> ⟦mref j of p w2 ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pb) ->
        tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs' ->
        Dom d_ind hd k (pa ++ bs) ≈ d_ind hd k (pb ++ bs') ∈ per_top_typ.
    Proof.
      intros * H1 H2 L1 L2 HMj Hrv Ea Eb Hbs.
      destruct (member_mref_u0 j Mj HMj Hrv) as (hd0 & k0 & p0 & E0).
      pose proof (trefl_l _ _ HMj _ _ Hbs) as Hbb.
      destruct (member_type_from_u0 w1 j Mj hd0 k0 p0 hd k pa bs bs H1 L1 HMj Hrv E0 Ea Hbb) as (i1 & R1 & HR1 & _).
      destruct (member_type_from_u0 w2 j Mj hd0 k0 p0 hd k pb bs bs' H2 L2 HMj Hrv E0 Eb Hbs) as (i2 & R2 & HR2 & _).
      destruct (per_univ_elem_sym _ _ _ _ HR1) as [HR1' _].
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR1' HR2) as (R3 & HR3 & _).
      exact (per_univ_then_per_top_typ HR3).
    Qed.

    Lemma ups_ok : forall w1 w2, RU (decl_env D w1) (decl_env D u0) -> RU (decl_env D w2) (decl_env D u0) ->
        List.length w1 = ind_nu D -> List.length w2 = ind_nu D ->
        elim_ups_ok p D u0 (canon_nparams_rel D u0) (canon_args_rel D u0) (canon_doms_rel D u0) w1 w2.
    Proof.
      intros * H1 H2 L1 L2.
      constructor; [ exact L1 | exact L2 | exact (adm_of_ru w1 H1 L1) | exact (adm_of_ru w2 H2 L2)
                   | exact (mrefs_of_ru w1 H1 L1) | exact (mrefs_of_ru w2 H2 L2)
                   | exact (ups_container_uparams w1 w2 H1 H2 L1 L2) | | | | | ].
      - intros * HMj Hrv Hu Hu' Ea Hv Hbs; exact (member_elements_readable w1 _ _ _ _ _ _ _ _ _ _ _ _ H1 L1 HMj Hrv Hu Hu' Ea Hv Hbs).
      - intros * HMj Hrv Hu Hu' Eb Hv Hbs.
        exact (member_elements_readable w2 _ _ _ _ _ _ _ _ _ _ _ _ H2 L2 HMj Hrv Hu' Hu Eb (isym _ _ _ _ _ _ _ Hv) Hbs).
      - intros * HMj Hh Hu Hu' Ec Hv; exact (rview_elements_readable w1 _ _ _ _ _ _ _ _ _ _ H1 L1 HMj Hh Hu Hu' Ec Hv).
      - intros * HMj Hh Hu Hu' Ec Hv.
        exact (rview_elements_readable w2 _ _ _ _ _ _ _ _ _ _ H2 L2 HMj Hh Hu' Hu Ec (isym _ _ _ _ _ _ _ Hv)).
      - intros * HMj Hrv Ea Eb Hbs; exact (member_types_alike w1 w2 _ _ _ _ _ _ _ _ H1 H2 L1 L2 HMj Hrv Ea Eb Hbs).
    Qed.

    (** The type of a scrutinee of the member [m] at [C1] and an
        environment related to it: its relation is the group's at [m], at
        the canonical bases, the values of the non-uniform parameters
        related canonically. *)
    Lemma scrut_rel : forall m Mm, ind_member D m = Some Mm -> ⊨ elim_mctx p D m Mm Us ++ Γ ->
        forall Ns, List.length Ns = im_nn Mm -> gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) τU ++ Γ) ->
        forall C2', RΓ C1 C2' -> forall ns ns', ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ ns -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ C2' ↘ ns' ->
        forall t t' (i : universe_index) R, ⟦ ind_mty p D m Us Ns ⟧ C1 ↘ t -> ⟦ ind_mty p D m Us Ns ⟧ C2' ↘ t' ->
        DF t ≈ t' ∈ per_univ_elem i ↘ R ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) ns ns' /\ (R <~> G m u0 u0 ns ns').
    Proof.
      intros * HMm HMa * HNl HgN * HC2 * Ens Ens' * Et Et' HR.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HC22 : RΓ C2' C2') by (etransitivity; [ symmetry; exact HC2 | exact HC2 ]).
      pose proof HMa as HM'; rewrite (mctx_split m Mm) in HM'.
      destruct (rel_ctx_wf_ass_inv HM') as (SI & HSI & HIT0).
      destruct (rel_exp_univ_of_sort_relevant _ _ _ (sort_kind_type_sort _ _ HSI) HIT0 (fun ρ0 a Ea => ind_mty_relevant _ _ _ _ _ _ _ _ HMm Ea)
                (fun ρ0 a Ea => ind_mty_not_level _ _ _ _ _ _ _ _ HMm Ea))
        as [jI HIT].
      pose proof (rel_ctx_wf_tail HMa) as HNt.
      destruct (rel_ctx_wf_per_ctx_env HNt) as [RS HRS].
      assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
      assert (Hta : all_assumptions (tele_sub (im_nparams Mm) τU))
        by (apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMm)).
      (** The instance's values: the terms', the entries being relevant. *)
      destruct (instance_values_of_sub _ _ _ _ _ Hta HRΓ HRS (nparams_sub_evaluated m Mm HMm) (gsub_valid HgN)
                  ltac:(rewrite length_tele_sub; exact HNl) C1 C2' HC2) as [n1 n2 En1 En2 HE Eτ1 Eτ2].
      pose proof (functional_eval_exps' _ _ _ _ En1 Ens) as ->; pose proof (functional_eval_exps' _ _ _ _ En2 Ens') as ->.
      assert (Ln : List.length ns = im_nn Mm) by (rewrite (eval_exps_length _ _ _ Ens); exact HNl).
      assert (Ln' : List.length ns' = im_nn Mm) by (rewrite (eval_exps_length _ _ _ Ens'); exact HNl).
      assert (LT : List.length (List.rev (tele_sub (im_nparams Mm) τU)) = im_nn Mm)
        by (rewrite List.length_rev, length_tele_sub; reflexivity).
      rewrite !env_extend_tagged_typed in HE.
      set (vts1 := tagged_entries Γ (List.rev (tele_sub (im_nparams Mm) τU)) (ctx_retag Γ C1) ns) in *.
      set (vts2 := tagged_entries Γ (List.rev (tele_sub (im_nparams Mm) τU)) (ctx_retag Γ C2') ns') in *.
      assert (Hv1 : List.map fst vts1 = ns) by (apply tagged_entries_fst; rewrite LT; symmetry; exact Ln).
      assert (Hv2 : List.map fst vts2 = ns') by (apply tagged_entries_fst; rewrite LT; symmetry; exact Ln').
      assert (Lv1 : List.length vts1 = im_nn Mm) by (rewrite <- (List.length_map fst), Hv1; exact Ln).
      assert (Lv2 : List.length vts2 = im_nn Mm) by (rewrite <- (List.length_map fst), Hv2; exact Ln').
      assert (HE11 : RS (env_extend_typed (ctx_retag Γ C1) vts1) (env_extend_typed (ctx_retag Γ C1) vts1))
        by (etransitivity; [ exact HE | symmetry; exact HE ]).
      assert (HB : RΓ (ctx_retag Γ C1) (ctx_retag Γ C2')) by exact (per_ctx_env_retag HRΓ _ _ HC2).
      destruct (us_class (ctx_retag Γ C1) (per_ctx_env_retag_left HRΓ _ _ HC11)) as (u1 & Hu1 & H10).
      assert (HNr : ⊨ List.rev (List.rev (tele_sub (im_nparams Mm) τU)) ++ Γ) by (rewrite List.rev_involutive; exact HNt).
      assert (HRSr : EF List.rev (List.rev (tele_sub (im_nparams Mm) τU)) ++ Γ ≈ List.rev (List.rev (tele_sub (im_nparams Mm) τU)) ++ Γ
                       ∈ per_ctx_env ↘ RS) by (rewrite List.rev_involutive; exact HRS).
      destruct (per_tele_args_of_env_extend _ _ _ _ HRΓ HNr (List.Forall_rev Hta) HRSr _ _ _ _ ltac:(rewrite LT; exact Lv1) ltac:(rewrite LT; exact Lv2) HE)
        as [_ Hg].
      rewrite Hv1, Hv2 in Hg.
      pose proof (canonical_nparams_rev m Mm HMm HMa _ _ u1 HB Hu1 H10 ns ns' Ln Hg) as Hns.
      destruct (rel_exp_of_typ_inversion_simple_at HRS HIT _ _ HE) as (b1 & b2 & Eb1 & Eb2 & [R12 HR12]).
      pose proof (mctx_head_rel m Mm HMm HMa _ _ u1 HB Hu1 H10 RS HRS ns ns' vts1 vts2 Hns Hv1 Hv2 HE11 b1 b2 _ R12 Eb1 Eb2 HR12) as HG.
      destruct (typ_inst_link _ _ _ _ _ _ _ _ _ (rel_type_of_typ HIT) HRΓ (gsub_valid HgN) HC22 Eτ2) as (a & b & Ea & Eb & [R2 HR2]).
      rewrite ind_head_inst in Ea by (try exact Hc; try exact HUl; exact HNl).
      rewrite (List.map_ext (fun U => U[Id]) (fun U => U)), List.map_id in Ea by (intros; apply exp_sub_id).
      assert (a = t') as -> by (eapply functional_eval_exp; eassumption).
      rewrite env_extend_tagged_typed in Eb.
      assert (b = b2) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR HR2) as (R'' & HR'' & ER).
      assert (E2 : R'' <~> R12) by (eapply per_univ_elem_left_irrel; [ exact HR'' | exact HR12 ]).
      split; [ exact Hns |].
      etransitivity; [ exact ER | etransitivity; [ exact E2 | exact HG ] ].
    Qed.

    (** ** A Constructor's Arguments, Canonically

        Arguments related canonically at the bases [u0], after the stored
        non-uniform parameters [X] and [X'] of the two constructors, are
        related at the closed telescope of their types there. *)
    Section ConCanon.
      Variable (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
      Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
      Let HΨ := valid_group_cargs_sem p D Hvg Hcv k Mk c gs HMk Hcon.
      Let T := List.rev (im_nparams Mk).

      Lemma cargs_tele_args : forall X X' vs vs',
          tele_rel (nr k) T X X' ->
          tele_rel (ar k X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
          con_args_rel p D (admissible_index_at D u0 nr) nr ar dr k u0 u0 X X' T gs vs vs' ->
          forall n, n <= List.length gs ->
          per_tele_args (List.rev (cargs_ctx p D Mk (List.firstn n gs))) (components_env D u0 T X) (components_env D u0 T X')
            (List.firstn n vs) (List.firstn n vs').
      Proof.
        intros * Hab Har Hia.
        unfold T; rewrite <- !(env_tele_uparams D (im_nparams Mk) u0 _ u0_len).
        apply (CargsRel.cargs_tele_args p D Hvg Hcv u0 u0_tele_args u0_len k Mk c gs HMk Hcon); [| exact Hab | exact Har | exact Hia ].
        intros gs1 t gs2 _; split; [ exact (view_end_rel_all P p D HP HPD u0 u0 u0_tele_args u0_len _)
                                    | exact (rview_end_rel_all P p D HP HPD u0 u0 u0_tele_args u0_len _) ].
      Qed.

      (** The arguments, at the closed telescope. *)
      Lemma closed_args_tele_args : forall X X' vs vs',
          tele_rel (nr k) T X X' ->
          tele_rel (ar k X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
          con_args_rel p D (admissible_index_at D u0 nr) nr ar dr k u0 u0 X X' T gs vs vs' ->
          forall n, n <= List.length gs ->
          per_tele_args (List.rev (cargs_ctx p D Mk (List.firstn n gs) ++ im_nparams Mk)) (decl_env D u0) (decl_env D u0)
            (X ++ List.firstn n vs) (X' ++ List.firstn n vs').
      Proof.
        intros * HX Har Hia n Hn.
        pose proof (cargs_tele_args X X' vs vs' HX Har Hia n Hn) as Hc1.
        pose proof HX as HX0; rewrite tele_rel_iff in HX0; destruct HX0 as (LX & LX' & _).
        unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
        rewrite List.rev_app_distr; apply per_tele_args_app_intro;
          [ rewrite List.length_rev, length_im_nparams; exact LX | exact (nparams_closed_of_canon k Mk HMk _ _ HX) |].
        exact Hc1.
      Qed.

      (** A constructor's element related to itself, its arguments replaced
          at propositional ones by other proofs that read back and its
          stored uniform parameters by others: related to it. *)
      Lemma con_up_to_proofs : im_is_rview Mk = false ->
          forall hd k' cs cs' X vs vs', im_ref p k Mk = (hd, k') -> List.length cs = im_unu D Mk ->
          G k u0 u0 X X (d_con hd k' c (cs ++ X ++ vs)) (d_con hd k' c (cs ++ X ++ vs)) ->
          List.length cs' = List.length cs -> List.length vs' = List.length vs ->
          (forall j v v', List.nth_error vs j = Some v -> List.nth_error vs' j = Some v' -> v = v' \/
             (proof_readable v' /\ con_arg_kind Mk c j = ak_propositional)) ->
          G k u0 u0 X X (d_con hd k' c (cs ++ X ++ vs)) (d_con hd k' c (cs' ++ X ++ vs')).
      Proof.
        intros Hrv * Href Lcs Hm Lcs' Lvs Hmix.
        rewrite List.app_assoc in Hm.
        assert (Lb : List.length (cs ++ X) = (im_unu D Mk + im_nn Mk)%nat).
        { pose proof (ins _ _ _ _ _ _ _ _ HMk Hm) as H0; rewrite tele_rel_iff in H0; destruct H0 as (H0 & _).
          rewrite List.length_rev, length_im_nparams in H0; rewrite List.length_app, Lcs, H0; reflexivity. }
        destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ (cs ++ X) vs _ Hm HMk Hrv Lb)
          as (gs0 & bs' & vs0 & Ez & _ & HXX & Hcon0 & Lbs' & _ & _ & Har & Hia).
        rewrite Hcon in Hcon0; injection Hcon0 as <-.
        injection Ez as Ez; destruct (app_split_eq _ _ _ _ Ez ltac:(lia)) as [<- <-].
        rewrite List.skipn_app, List.skipn_all2, Lcs, Nat.sub_diag in Har, Hia by lia; cbn [List.skipn List.app] in Har, Hia.
        destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
        pose proof HXX as H0; rewrite tele_rel_iff in H0; destruct H0 as (LX & _).
        unfold T in LX; rewrite List.length_rev, length_im_nparams in LX.
        (** The arguments at the closed telescope of the constructor. *)
        pose proof (closed_args_tele_args X X vs vs HXX Har Hia (List.length gs) (le_n _)) as Hcg.
        rewrite List.firstn_all, List.firstn_all2 in Hcg by lia.
        set (ts := List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)).
        assert (Ets : ts = List.rev (ind_uparams D) ++ List.rev (cargs_ctx p D Mk gs ++ im_nparams Mk))
          by (unfold ts, im_params; rewrite List.app_assoc, List.rev_app_distr; reflexivity).
        assert (Hgx : per_tele_args ts nil nil (u0 ++ X ++ vs) (u0 ++ X ++ vs)).
        { rewrite Ets; apply per_tele_args_app_intro; [ rewrite List.length_rev; exact u0_len | exact u0_tele_args | exact Hcg ]. }
        pose proof (valid_group_cargs_sem p D Hvg Hcv k Mk c gs HMk Hcon) as HΨ0.
        assert (Hta : all_assumptions ts)
          by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMk) ]).
        assert (HCr : ⊨ List.rev ts ++ ⋅) by (unfold ts; rewrite List.rev_involutive, List.app_nil_r; exact HΨ0).
        assert (Lts : List.length ts = (ind_nu D + im_nn Mk + List.length gs)%nat)
          by (unfold ts; rewrite List.length_rev, List.length_app, length_cargs_ctx, length_im_params; unfold im_np; lia).
        (** The replaced arguments, related to the original ones. *)
        assert (Hgy : per_tele_args ts nil nil (u0 ++ X ++ vs) (u0 ++ X ++ vs')).
        { apply (per_tele_args_replace_proofs _ _ _ per_ctx_env_nil_true HCr Hta nil nil _ _ I Hgx);
            [ rewrite !List.length_app; lia |].
          intros j x y Hx Hy.
          destruct (Nat.lt_ge_cases j (ind_nu D + im_nn Mk)) as [Hj | Hj].
          - left; rewrite List.app_assoc in Hx, Hy.
            rewrite List.nth_error_app1 in Hx, Hy by (rewrite List.length_app, u0_len; lia); congruence.
          - rewrite List.app_assoc in Hx, Hy.
            rewrite List.nth_error_app2 in Hx, Hy by (rewrite List.length_app, u0_len; lia).
            rewrite List.length_app, u0_len, LX in Hx, Hy.
            destruct (Hmix _ _ _ Hx Hy) as [-> | (Hry & Hr)]; [ left; reflexivity | right; split; [ exact Hry |] ].
            intros ts1 κ A ts2 a Eq Lt1 Ea.
            pose proof (nth_error_lt_length _ _ _ Hx) as Hjx.
            assert (Lf : List.length (List.firstn j (u0 ++ X ++ vs)) = List.length ts1)
              by (rewrite List.length_firstn, !List.length_app, u0_len, LX; lia).
            assert (Hpre : per_tele_args ts1 nil nil (List.firstn j (u0 ++ X ++ vs)) (List.firstn j (u0 ++ X ++ vs))).
            { pose proof Hgx as Hgx0; rewrite Eq, <- (List.firstn_skipn j (u0 ++ X ++ vs)) in Hgx0.
              exact (proj1 (per_tele_args_app _ _ _ _ _ _ _ _ Lf Hgx0 Lf)). }
            assert (HC1 : ⊨ List.rev ts1).
            { pose proof HCr as H; rewrite Eq, List.rev_app_distr, List.app_nil_r in H; cbn [List.rev] in H.
              rewrite <- List.app_assoc in H; cbn [List.app] in H.
              exact (rel_ctx_wf_tail (rel_ctx_wf_app_r _ _ H)). }
            destruct (rel_ctx_wf_per_ctx_env HC1) as [R1 HR1].
            assert (Hz : R1 (env_tele nil ts1 (List.firstn j (u0 ++ X ++ vs))) (env_tele nil ts1 (List.firstn j (u0 ++ X ++ vs)))).
            { rewrite <- (List.rev_involutive ts1).
              apply (tele_args_env_rel _ _ _ _ _ _ HR1 HC1); [ rewrite List.length_rev; first [ exact Lf | symmetry; exact Lf ] |].
              rewrite List.rev_involutive; exact Hpre. }
            rewrite (con_tele_dom_kind P p D HP HPD k Mk c gs HMk Hcon ts1 κ A ts2 R1 _ a Eq HR1 Hz Ea).
            destruct (Nat.ltb_spec (List.length ts1) (im_np D Mk)) as [Hlt | _]; [ unfold im_np in Hlt; lia |].
            replace (List.length ts1 - im_np D Mk) with (j - (ind_nu D + im_nn Mk)) by (unfold im_np; lia); exact Hr. }
        (** The constructor's values at both. *)
        assert (Hcv0 : forall ys, List.length ys = List.length vs -> exists w, con_value p D k Mk c (u0 ++ X ++ ys) w).
        { intros ys Lys.
          destruct (im_head Mk) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
          - exists (d_con p k c (u0 ++ X ++ ys)); apply (con_value_decl _ _ _ _ _ pm); exact Hh.
          - destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mk' & Hq & _).
            destruct (valid_group_views_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMk Hh Hq u0 u0 u0_tele_args u0_len)
              as (cups & _ & Ecups & _ & _).
            eexists; apply (con_value_view _ _ _ _ _ qc kc Is vm _ cups Hh); [ rewrite List.length_app, u0_len; lia |].
            rewrite List.firstn_app, u0_len, Nat.sub_diag, <- u0_len, List.firstn_all; cbn [List.firstn]; rewrite List.app_nil_r; exact Ecups.
          - exfalso; exact (not_rview_record _ _ _ _ Hrv Hh). }
        destruct (Hcv0 vs eq_refl) as [w Hw]; destruct (Hcv0 vs' Lvs) as [w' Hw'].
        pose proof (con_at_args P p D HP HPD k Mk c gs HMk Hcon _ _ w w' Hgy
                      ltac:(rewrite !List.length_app, u0_len, LX, Lv, length_cargs_ctx, length_im_params; unfold im_np; lia) Hw Hw') as Hh.
        (** At the member's type: the group's relation. *)
        destruct (mty_vars_valid_at p D Hvg Hcv k Mk (cargs_ctx p D Mk gs) HMk HΨ0) as [jt Hjt].
        rewrite length_cargs_ctx in Hjt.
        set (Z := cargs_ctx p D Mk gs ++ im_nparams Mk).
        assert (HZ : ⊨ Z ++ ind_uparams D) by (unfold Z, im_params in *; rewrite <- List.app_assoc; exact HΨ0).
        destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
        assert (EZ : forall zs, env_tele nil ts (u0 ++ zs) = components_env D u0 (List.rev Z) zs)
          by (intros zs; unfold ts, Z, im_params; rewrite List.app_assoc; exact (env_tele_uparams D _ u0 zs u0_len)).
        assert (HE : RZ (components_env D u0 (List.rev Z) (X ++ vs)) (components_env D u0 (List.rev Z) (X ++ vs'))).
        { rewrite <- !EZ; unfold ts; rewrite <- (List.rev_involutive (List.rev (cargs_ctx p D Mk gs ++ im_params D Mk))).
          rewrite List.rev_involutive.
          replace (cargs_ctx p D Mk gs ++ im_params D Mk) with (Z ++ ind_uparams D) by (unfold Z, im_params; rewrite <- List.app_assoc; reflexivity).
          apply (tele_args_env_rel _ _ _ _ _ _ HRZ HZ); [ rewrite !List.length_app; unfold Z; rewrite List.length_app, length_cargs_ctx, length_im_nparams;
                                                      pose proof u0_len; unfold ind_nu in *; lia |].
          replace (List.rev (Z ++ ind_uparams D)) with ts by (unfold ts, Z, im_params; rewrite <- List.app_assoc; reflexivity).
          exact Hgy. }
        assert (HjtZ : Z ++ ind_uparams D ⊨ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk))
                         : Typeω@jt) by (unfold Z, im_params in *; rewrite <- List.app_assoc; exact Hjt).
        destruct (rel_exp_of_typ_inversion_simple_at HRZ HjtZ _ _ HE) as (a & a' & Ea & Ea' & [R HR]).
        assert (Ev : forall ys, List.length ys = List.length gs ->
                       ⟦ vars_from (List.length gs) (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u0 (List.rev Z) (X ++ ys) ↘ X).
        { intros ys Lys; unfold Z; rewrite List.rev_app_distr.
          pose proof (eval_nvars_components D u0 (List.rev (im_nparams Mk)) (List.rev (cargs_ctx p D Mk gs)) X ys
                        ltac:(rewrite List.length_rev, length_im_nparams; exact LX)) as H; rewrite Lys, LX in H; exact H. }
        pose proof (member_type_rel P p D HP HPD k Mk u0 u0 Z RZ (X ++ vs) (X ++ vs') (im_nn Mk) (List.length gs)
                      (vars_from (List.length gs) (im_nn Mk)) X X a a' jt R HMk u0_len u0_tele_args HZ HRZ
                      ltac:(unfold Z; rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia)
                      ltac:(unfold Z; rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia)
                      ltac:(rewrite List.length_app; lia) HE (length_vars_from _ _) (Ev vs ltac:(lia)) (Ev vs' ltac:(lia)) Ea Ea' HR) as ER.
        rewrite <- !EZ in Ea, Ea'.
        pose proof (proj2 (per_head_iff Ea Ea' HR _ _) Hh) as Hww; apply ER in Hww.
        (** The values, at the stored uniform parameters. *)
        assert (Lz : List.length (u0 ++ X ++ vs) = (im_np D Mk + List.length gs)%nat)
          by (rewrite !List.length_app, u0_len, LX, Lv; unfold im_np; lia).
        assert (Lz' : List.length (u0 ++ X ++ vs') = (im_np D Mk + List.length gs)%nat)
          by (rewrite !List.length_app, u0_len, LX, Lvs, Lv; unfold im_np; lia).
        destruct (con_value_full p D k Mk c gs (u0 ++ X ++ vs) w Hrv Lz Hw) as (c1 & Lc1 & ->).
        destruct (con_value_full p D k Mk c gs (u0 ++ X ++ vs') w' Hrv Lz' Hw') as (c2 & Lc2 & ->).
        rewrite Href in Hww; cbn [fst snd] in Hww.
        rewrite !(List.skipn_app (ind_nu D) u0) in Hww; rewrite <- u0_len, !List.skipn_all, Nat.sub_diag in Hww.
        cbn [List.skipn List.app] in Hww.
        exact (ind_rel_con_prefix_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c1 cs (X ++ vs) Mk HMk Lc1 ltac:(lia)
                 (ind_rel_con_prefix_r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c2 cs' (X ++ vs') Mk HMk Lc2 ltac:(lia) Hww)).
      Qed.
    End ConCanon.

    (** ** The Motives

        The motives of the blocks [Bks], each in its member's context, and
        their family [Rel] between [C1] and an environment [C2] related to
        it: the head relation of the motive at the two extended
        environments, the motive's context's telescope giving the types
        of the indices and the element. *)
    Section Motives.
      Variable (C2 : env).
      Hypothesis (HC12 : RΓ C1 C2).
      Variable (Bks : list eblock) (iA : nat).
      Hypothesis (HBks : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks j = Some b).
      Hypothesis (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ).
      Hypothesis (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
                    elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@iA).
      (** The telescope of the motive's context of the member [j]. *)
      Let mctx_tele j := match ind_member D j with Some Mj => List.rev (elim_mctx p D j Mj Us) | None => nil end.
      Let Rel := fun j ns m ns' m' =>
        per_head (List.nth j (blocks_motives Bks) a_prop) (List.nth j (blocks_motives Bks) a_prop)
          (env_tele C1 (mctx_tele j) (ns ++ m :: nil)) (env_tele C2 (mctx_tele j) (ns' ++ m' :: nil)).

      Lemma mctx_tele_at : forall j Mj, ind_member D j = Some Mj -> mctx_tele j = List.rev (elim_mctx p D j Mj Us).
      Proof. intros * HMj; unfold mctx_tele; rewrite HMj; reflexivity. Qed.

      Lemma mctx_at : forall j Mj, ind_member D j = Some Mj -> forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
          forall RM, EF elim_mctx p D j Mj Us ++ Γ ≈ elim_mctx p D j Mj Us ++ Γ ∈ per_ctx_env ↘ RM ->
          forall u u' ns ns' m m', G j u u' ns ns' m m' ->
            RM (env_tele B1 (List.rev (elim_mctx p D j Mj Us)) (ns ++ m :: nil))
               (env_tele B2 (List.rev (elim_mctx p D j Mj Us)) (ns' ++ m' :: nil)).
      Proof.
        intros * HMj * HB1 HB2 RM HRM * Hm.
        exact (canonical_mctx j Mj HMj (HMall _ _ HMj) B1 B2 HB1 HB2 RM HRM ns ns' u u' m m' (ins _ _ _ _ _ _ _ _ HMj Hm) Hm).
      Qed.

      (** As many indices and elements as the motive's context has
          entries. *)
      Lemma mctx_len : forall j Mj, ind_member D j = Some Mj -> forall u u' ns ns' m m', G j u u' ns ns' m m' ->
          List.length (ns ++ m :: nil) = List.length (List.rev (elim_mctx p D j Mj Us)) /\
          List.length (ns' ++ m' :: nil) = List.length (List.rev (elim_mctx p D j Mj Us)).
      Proof.
        intros * HMj * Hm.
        pose proof (ins _ _ _ _ _ _ _ _ HMj Hm) as H; rewrite tele_rel_iff in H; destruct H as (H & H' & _).
        rewrite List.length_rev, length_im_nparams in H, H'.
        rewrite List.length_rev, length_elim_mctx, !List.length_app; cbn [List.length]; lia.
      Qed.

      (** The motive's context at its telescope's entries, reversed back. *)
      Lemma mctx_rev_sem : forall j Mj, ind_member D j = Some Mj ->
          forall RM, EF elim_mctx p D j Mj Us ++ Γ ≈ elim_mctx p D j Mj Us ++ Γ ∈ per_ctx_env ↘ RM ->
          ⊨ List.rev (List.rev (elim_mctx p D j Mj Us)) ++ Γ /\
          EF List.rev (List.rev (elim_mctx p D j Mj Us)) ++ Γ ≈ List.rev (List.rev (elim_mctx p D j Mj Us)) ++ Γ ∈ per_ctx_env ↘ RM /\
          all_assumptions (List.rev (elim_mctx p D j Mj Us)).
      Proof.
        intros * HMj RM HRM; rewrite !List.rev_involutive.
        split; [ exact (HMall _ _ HMj) | split; [ exact HRM | exact (List.Forall_rev (elim_mctx_ass p D j Mj Us Hc HMj)) ] ].
      Qed.

      (** The canonical entries of related elements read back. *)
      Lemma mctx_readable : forall j Mj, ind_member D j = Some Mj -> forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
          forall u u' ns ns' m m', G j u u' ns ns' m m' ->
          List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) (tele_entries B1 (List.rev (elim_mctx p D j Mj Us)) (ns ++ m :: nil)) /\
          List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) (tele_entries B2 (List.rev (elim_mctx p D j Mj Us)) (ns' ++ m' :: nil)).
      Proof.
        intros * HMj * HB1 HB2 * Hm.
        destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
        destruct (mctx_rev_sem j Mj HMj RM HRM) as (HMr & HRMr & Hta).
        destruct (mctx_len j Mj HMj _ _ _ _ _ _ Hm) as [L L'].
        exact (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ ltac:(rewrite tele_entries_length; exact L)
                 ltac:(rewrite tele_entries_length; exact L') (mctx_at j Mj HMj B1 B2 HB1 HB2 RM HRM _ _ _ _ _ _ Hm)).
      Qed.

      (** Related elements at any entry types they read back at. *)
      Lemma mctx_at_typed : forall j Mj, ind_member D j = Some Mj -> forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
          forall RM, EF elim_mctx p D j Mj Us ++ Γ ≈ elim_mctx p D j Mj Us ++ Γ ∈ per_ctx_env ↘ RM ->
          forall u u' ns ns' m m', G j u u' ns ns' m m' ->
          forall vts vts', List.map fst vts = ns ++ m :: nil -> List.map fst vts' = ns' ++ m' :: nil ->
          List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
          List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts' ->
          RM (env_extend_typed B1 vts) (env_extend_typed B2 vts').
      Proof.
        intros * HMj * HB1 HB2 RM HRM * Hm * Hv Hv' Hr Hr'.
        destruct (mctx_rev_sem j Mj HMj RM HRM) as (HMr & HRMr & Hta).
        destruct (mctx_len j Mj HMj _ _ _ _ _ _ Hm) as [L L'].
        pose proof (mctx_at j Mj HMj B1 B2 HB1 HB2 RM HRM _ _ _ _ _ _ Hm) as E; unfold env_tele in E.
        destruct (per_tele_args_of_env_extend _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ ltac:(rewrite tele_entries_length; exact L)
                    ltac:(rewrite tele_entries_length; exact L') E) as [HB Hg].
        rewrite !tele_entries_values, <- Hv, <- Hv' in Hg.
        apply (tele_args_env_rel_typed _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ HB); [| | exact Hg | exact Hr | exact Hr' ].
        - rewrite <- (List.length_map fst), Hv; exact L.
        - rewrite <- (List.length_map fst), Hv'; exact L'.
      Qed.

      (** Related elements read back at some types, on each side. *)
      Lemma mctx_idx_readable : forall j Mj u u' ns ns' m m', ind_member D j = Some Mj -> G j u u' ns ns' m m' ->
          (exists ts, List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts) /\
          (exists ts', List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts').
      Proof.
        intros * HMj Hm.
        destruct (mctx_readable j Mj HMj C1 C1 HC11 HC11 _ _ _ _ _ _ Hm) as [Hr Hr'].
        apply (Forall2_of_Forall_pairs (fun v t => entry_readable (de_term v t))) in Hr, Hr'.
        rewrite tele_entries_values in Hr, Hr'.
        split; eexists; eassumption.
      Qed.

      (** The family at related elements does not depend on their
          indices, nor on their bases. *)
      Lemma rel_move : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> forall u u' ns ns' m m' ns1 ns1',
          G j u u' ns ns' m m' ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns1 -> tele_rel (nr j) (List.rev (im_nparams Mj)) ns' ns1' ->
          (Rel j ns m ns' m' <~> Rel j ns1 m ns1' m').
      Proof.
        intros * HMj Hrv * Hm H1 H1'.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        destruct (HBks j Mj HMj Hrv) as [b Hb].
        assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
        pose proof (ins _ _ _ _ _ _ _ _ HMj Hm) as Hn.
        pose proof (isym _ _ _ _ _ _ _ Hm) as Hms.
        pose proof (trefl_r _ _ HMj _ _ Hn) as Hn'n'.
        pose proof (ind_rel_idx_u0 _ _ _ _ _ _ _ _ _ _ HMj Hms Hn'n' H1) as Hm2.
        pose proof (ind_rel_idx_u0 _ _ _ _ _ _ _ _ _ _ HMj Hm H1 H1') as Hm3.
        destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
        unfold Rel; rewrite (blocks_motives_nth _ _ _ Hb), (mctx_tele_at _ _ HMj).
        apply (per_head_of_typ_resp HRM (HAv _ _ _ HMj Hb)).
        apply rel_chain_cons; [ exact (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm) |].
        apply rel_chain_cons; [ exact (mctx_at j Mj HMj C2 C1 HC21 HC11 RM HRM _ _ _ _ _ _ Hm2) |].
        apply rel_chain_of_pair; exact (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm3).
      Qed.

      Lemma ind_rel_refl_l : forall j u u' ns ns' m m', G j u u' ns ns' m m' -> G j u u ns ns m m.
      Proof. intros * Hm; exact (itrans _ _ _ _ _ _ _ Hm _ _ _ _ (isym _ _ _ _ _ _ _ Hm)). Qed.

      Lemma ind_rel_refl_r : forall j u u' ns ns' m m', G j u u' ns ns' m m' -> G j u' u' ns' ns' m' m'.
      Proof. intros * Hm; exact (itrans _ _ _ _ _ _ _ (isym _ _ _ _ _ _ _ Hm) _ _ _ _ Hm). Qed.

      (** The motive of the member [j] at [C1], at an element related to
          another, is a type of a universe: not [LevelSort], not a type of
          levels. *)
      Lemma motive_mid_not_level_sort : forall j Mj b A0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
          elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ A0 : Typeω@iA ->
          forall u u' ns ns' m m' ts a, G j u u' ns ns' m m' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
          ⟦ eb_motive b ⟧ env_extend_typed C1 (List.combine (ns ++ m :: nil) ts) ↘ a ->
          not_level_sort a /\ domain_kind a <> ak_level.
      Proof.
        intros * HMj Hb HA * Hm Ht Ea.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
        destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
        pose proof (ind_rel_refl_l _ _ _ _ _ _ _ Hm) as Hmm.
        destruct (mctx_readable j Mj HMj C1 C2 HC11 HC21 _ _ _ _ _ _ Hm) as [Hc1 _].
        pose proof (Forall_combine_of_Forall2 _ _ _ Ht) as Hr.
        pose proof (combine_fst_eq _ _ (List.Forall2_length Ht)) as Hv.
        pose proof (mctx_at_typed j Mj HMj C1 C1 HC11 HC11 RM HRM _ _ _ _ _ _ Hmm _ _ Hv (tele_entries_values _ _ _) Hr Hc1) as HE1.
        pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
        destruct (rel_exp_of_typ_not_level_sort HAl _ HRM _ _ HE1) as (a1 & Ea1 & Hn).
        destruct (rel_exp_of_typ_relevant_at HRM HAl _ _ HE1) as (a2 & Ea2 & Hk).
        assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
        assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
        split; [ exact Hn | rewrite Hk; discriminate ].
      Qed.

      (** The motive of the member [j] at [C1] and a motive equal to it at
          [C2], at related elements: related at the family. *)
      Lemma motive_mid : forall j Mj b A0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
          elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ A0 : Typeω@iA ->
          forall u u' ns ns' m m' ts ts', G j u u' ns ns' m m' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts' ->
          exists a a', ⟦ eb_motive b ⟧ env_extend_typed C1 (List.combine (ns ++ m :: nil) ts) ↘ a /\
            ⟦ A0 ⟧ env_extend_typed C2 (List.combine (ns' ++ m' :: nil) ts') ↘ a' /\
            DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns m ns' m'.
      Proof.
        intros * HMj Hb HA * Hm Ht Ht'.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
        assert (HC22 : RΓ C2 C2) by (etransitivity; [ exact HC21 | exact HC12 ]).
        destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
        pose proof (ind_rel_refl_l _ _ _ _ _ _ _ Hm) as Hmm.
        pose proof (ind_rel_refl_r _ _ _ _ _ _ _ Hm) as Hmm'.
        destruct (mctx_readable j Mj HMj C1 C2 HC11 HC21 _ _ _ _ _ _ Hm) as [Hc1 Hc2].
        pose proof (Forall_combine_of_Forall2 _ _ _ Ht) as Hr; pose proof (Forall_combine_of_Forall2 _ _ _ Ht') as Hr'.
        pose proof (combine_fst_eq _ _ (List.Forall2_length Ht)) as Hv; pose proof (combine_fst_eq _ _ (List.Forall2_length Ht')) as Hv'.
        pose proof (mctx_at_typed j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm _ _ Hv Hv' Hr Hr') as HE.
        pose proof (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm) as HEc.
        pose proof (mctx_at_typed j Mj HMj C1 C1 HC11 HC11 RM HRM _ _ _ _ _ _ Hmm _ _ Hv (tele_entries_values _ _ _) Hr Hc1) as HE1.
        pose proof (mctx_at_typed j Mj HMj C2 C2 HC21 HC21 RM HRM _ _ _ _ _ _ Hmm' _ _ (tele_entries_values _ _ _) Hv' Hc2 Hr') as HE2.
        pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
        destruct (rel_exp_of_typ_inversion_simple_at HRM HA _ _ HE) as (a & a' & Ea & Ea' & _).
        destruct (rel_exp_of_typ_inversion_simple_at HRM HAl _ _ HEc) as (b1 & c1 & Eb1 & Ec1 & Hbc).
        destruct (rel_exp_of_typ_inversion_simple_at HRM HAl _ _ HE1) as (a0 & b0 & Ea0 & Eb0 & Hab).
        destruct (rel_exp_of_typ_inversion_simple_at HRM HA _ _ HE2) as (c0 & d & Ec0 & Ed & Hcd).
        assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
        assert (b0 = b1) as -> by (eapply functional_eval_exp; eassumption).
        assert (c0 = c1) as -> by (eapply functional_eval_exp; eassumption).
        assert (d = a') as -> by (eapply functional_eval_exp; eassumption).
        exists a, a'; split; [ exact Ea | split; [ exact Ea' |] ].
        unfold Rel; rewrite (blocks_motives_nth _ _ _ Hb), (mctx_tele_at _ _ HMj).
        eapply univ_connect; [ exact Hab | exact (per_univ_elem_at_head Eb1 Ec1 Hbc) | symmetry; exact Hcd ].
      Qed.

      (** The motive moved by a semantic substitution [σ0] from [Γ'] at
          [ρ0] is a type of a universe there: not [LevelSort], not a type
          of levels, as its value is related to the motive's at the value
          [ρ0σ0] of [σ0], which is in the motive's universe. *)
      Lemma motive_out_not_level_sort : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
          forall Γ' RΓ' σ0 ρ0 ρ0σ0 A0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ ->
          RΓ' ρ0 ρ0 -> ⟦ σ0 : Γ ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
          elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ A0 : Typeω@iA ->
          forall u u' ns ns' m m' ts a, G j u u' ns ns' m m' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
          ⟦ A0[sb_qn (S (im_nn Mj)) σ0] ⟧ env_extend_typed ρ0 (List.combine (ns ++ m :: nil) ts) ↘ a ->
          not_level_sort a /\ domain_kind a <> ak_level.
      Proof.
        intros * HMj Hb * HRΓ' Hσ0 Hρ0 Hev0 HρC HA0 * Hm Ht Ea.
        pose proof (HMall _ _ HMj) as HM.
        destruct (rel_ctx_wf_per_ctx_env HM) as [RM HRM].
        destruct (mctx_rev_sem j Mj HMj RM HRM) as (HMr & HRMr & Hta).
        pose proof (ind_rel_refl_l _ _ _ _ _ _ _ Hm) as Hmm.
        pose proof (Forall_combine_of_Forall2 _ _ _ Ht) as Hr.
        pose proof (combine_fst_eq _ _ (List.Forall2_length Ht)) as Hv.
        pose proof (mctx_at_typed j Mj HMj ρ0σ0 ρ0σ0 HρC HρC RM HRM _ _ _ _ _ _ Hmm _ _ Hv Hv Hr Hr) as El.
        destruct (mctx_len j Mj HMj _ _ _ _ _ _ Hm) as [Ll _].
        assert (Lv : List.length (List.combine (ns ++ m :: nil) ts) = List.length (List.rev (elim_mctx p D j Mj Us)))
          by (rewrite <- (List.length_map fst), Hv; exact Ll).
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        pose proof (proj2 (per_tele_args_of_env_extend _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ Lv Lv El)) as Hg.
        destruct (outer_universe_type_link (elim_mctx p D j Mj Us) Γ Γ' RΓ' σ0 ρ0 ρ0σ0 A0 A0 iA (elim_mctx_ass p D j Mj Us Hc HMj) HM
                    (rel_exp_under_ctx_refl_right HA0) HRΓ' Hσ0 Hρ0 Hev0 _ Hg ltac:(rewrite List.length_rev in Lv; exact Lv) Hr)
          as (a0 & b0 & Ea0 & Eb0 & [Rab Hab0]).
        rewrite length_elim_mctx in Ea0.
        assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
        (** The motive at the inner environment is a type of a universe. *)
        destruct (rel_exp_of_typ_not_level_sort (rel_exp_under_ctx_refl_right HA0) _ HRM _ _ El) as (b1 & Eb1 & Hnb).
        destruct (rel_exp_of_typ_relevant_at HRM (rel_exp_under_ctx_refl_right HA0) _ _ El) as (b2 & Eb2 & Hkb).
        assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption).
        assert (b2 = b0) as -> by (eapply functional_eval_exp; eassumption).
        split; [ exact (proj2 (per_univ_elem_not_level_sort_iff _ _ _ _ Hab0) Hnb) |].
        rewrite (per_univ_elem_kind _ _ _ _ Hab0), Hkb; discriminate.
      Qed.

      (** The motive moved by a semantic substitution [σ0] from [Γ'] at
          [ρ0], against a motive equal to it at the value [ρ0σ0] of [σ0],
          of the class of [C1]. *)
      Lemma motive_out : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
          forall Γ' RΓ' σ0 ρ0 ρ0σ0 A0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ ->
          RΓ' ρ0 ρ0 -> ⟦ σ0 : Γ ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
          elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ A0 : Typeω@iA ->
          forall u u' ns ns' m m' ts ts', G j u u' ns ns' m m' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts' ->
            exists a a', ⟦ A0[sb_qn (S (im_nn Mj)) σ0] ⟧ env_extend_typed ρ0 (List.combine (ns ++ m :: nil) ts) ↘ a /\
              ⟦ A0 ⟧ env_extend_typed ρ0σ0 (List.combine (ns' ++ m' :: nil) ts') ↘ a' /\
              DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns m ns' m'.
      Proof.
        intros * HMj Hb * HRΓ' Hσ0 Hρ0 Hev0 HρC HA0 * Hm Ht Ht'.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
        pose proof (HMall _ _ HMj) as HM.
        destruct (rel_ctx_wf_per_ctx_env HM) as [RM HRM].
        destruct (mctx_rev_sem j Mj HMj RM HRM) as (HMr & HRMr & Hta).
        pose proof (ind_rel_refl_l _ _ _ _ _ _ _ Hm) as Hmm.
        pose proof (ind_rel_refl_r _ _ _ _ _ _ _ Hm) as Hmm'.
        pose proof (HAv _ _ _ HMj Hb) as HAl.
        destruct (mctx_readable j Mj HMj C1 C2 HC11 HC21 _ _ _ _ _ _ Hm) as [Hc1 Hc2].
        pose proof (Forall_combine_of_Forall2 _ _ _ Ht) as Hr; pose proof (Forall_combine_of_Forall2 _ _ _ Ht') as Hr'.
        pose proof (combine_fst_eq _ _ (List.Forall2_length Ht)) as Hv; pose proof (combine_fst_eq _ _ (List.Forall2_length Ht')) as Hv'.
        pose proof (mctx_at_typed j Mj HMj ρ0σ0 ρ0σ0 HρC HρC RM HRM _ _ _ _ _ _ Hmm _ _ Hv Hv Hr Hr) as El.
        destruct (mctx_len j Mj HMj _ _ _ _ _ _ Hm) as [Ll _].
        assert (Lv : List.length (List.combine (ns ++ m :: nil) ts) = List.length (List.rev (elim_mctx p D j Mj Us)))
          by (rewrite <- (List.length_map fst), Hv; exact Ll).
        pose proof (proj2 (per_tele_args_of_env_extend _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ Lv Lv El)) as Hg.
        destruct (outer_universe_type_link (elim_mctx p D j Mj Us) Γ Γ' RΓ' σ0 ρ0 ρ0σ0 A0 A0 iA (elim_mctx_ass p D j Mj Us Hc HMj) HM
                    (rel_exp_under_ctx_refl_right HA0) HRΓ' Hσ0 Hρ0 Hev0 _ Hg ltac:(rewrite List.length_rev in Lv; exact Lv) Hr)
          as (a & b0 & Ea & Eb0 & Hab0).
        rewrite length_elim_mctx in Ea.
        pose proof (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm) as Ebc.
        destruct (rel_exp_of_typ_inversion_simple_at HRM HAl _ _ Ebc) as (b1 & c0 & Eb & Ec & Hbc).
        pose proof (mctx_at_typed j Mj HMj C1 ρ0σ0 HC11 HρC RM HRM _ _ _ _ _ _ Hmm _ _ (tele_entries_values _ _ _) Hv Hc1 Hr) as E1.
        destruct (rel_exp_of_typ_inversion_simple_at HRM HA0 _ _ E1) as (b' & b0' & Eb' & Eb0' & Hbb0).
        assert (b' = b1) as -> by (eapply functional_eval_exp; eassumption).
        assert (b0' = b0) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (mctx_at_typed j Mj HMj C2 ρ0σ0 HC21 HρC RM HRM _ _ _ _ _ _ Hmm' _ _ (tele_entries_values _ _ _) Hv' Hc2 Hr') as E2.
        destruct (rel_exp_of_typ_inversion_simple_at HRM HA0 _ _ E2) as (c' & d & Ec' & Ed & Hcd).
        assert (c' = c0) as -> by (eapply functional_eval_exp; eassumption).
        exists a, d; split; [ exact Ea | split; [ exact Ed |] ].
        unfold Rel; rewrite (blocks_motives_nth _ _ _ Hb), (mctx_tele_at _ _ HMj).
        eapply univ_connect; [ etransitivity; [ exact Hab0 | symmetry; exact Hbb0 ] | exact (per_univ_elem_at_head Eb Ec Hbc) |].
        symmetry; exact Hcd.
      Qed.

      (** The family along related elements. *)
      Lemma rel_resp : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false ->
          forall u1 u2 u3 u4 u5 u6 ns1 m1 ns2 m2 ns3 m3 ns4 m4,
          G j u1 u2 ns1 ns2 m1 m2 -> G j u3 u4 ns2 ns3 m2 m3 -> G j u5 u6 ns3 ns4 m3 m4 ->
          (Rel j ns1 m1 ns2 m2 <~> Rel j ns3 m3 ns4 m4).
      Proof.
        intros * HMj Hrv * M12 M23 M34.
        assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
        destruct (HBks j Mj HMj Hrv) as [b Hb].
        destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
        unfold Rel; rewrite (blocks_motives_nth _ _ _ Hb), (mctx_tele_at _ _ HMj).
        apply (per_head_of_typ_resp HRM (HAv _ _ _ HMj Hb)).
        apply rel_chain_cons; [ exact (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ M12) |].
        apply rel_chain_cons; [ exact (mctx_at j Mj HMj C2 C1 HC21 HC11 RM HRM _ _ _ _ _ _ M23) |].
        apply rel_chain_of_pair; exact (mctx_at j Mj HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ M34).
      Qed.

      Lemma rel_per : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> forall u u' ns ns' m m',
          G j u u' ns ns' m m' -> PER (Rel j ns m ns' m').
      Proof.
        intros * HMj Hrv * Hm.
        destruct (HBks j Mj HMj Hrv) as [b Hb].
        destruct (mctx_idx_readable j Mj _ _ _ _ _ _ HMj Hm) as [(ts & Ht) (ts' & Ht')].
        destruct (motive_mid j Mj b (eb_motive b) HMj Hb (HAv _ _ _ HMj Hb) _ _ _ _ _ _ _ _ Hm Ht Ht') as (a & a' & _ & _ & H).
        eapply per_elem_PER; exact H.
      Qed.

      (** Recursive results related at any bases are related at [u0]: the
          end's parameters at [u0] are related to the ones at the bases
          ([admissible_index_at]), and the family does not depend on them. *)
      Lemma rec_rebase_all : forall kr u u',
        (forall pre pre' Ts t v v' rs rs', rec_result_rel D dr Rel kr u u' pre pre' Ts t v v' rs rs' ->
           rec_arg_rel p D (admissible_index_at D u0 nr) nr ar dr kr u u' pre pre' Ts t v v' ->
           rec_result_rel D dr Rel kr u0 u0 pre pre' Ts t v v' rs rs') /\
        (forall pre pre' Ts t v c v' c' rs rs', rec_result_app_rel D dr Rel kr u u' pre pre' Ts t v c v' c' rs rs' ->
           rec_arg_app_rel p D (admissible_index_at D u0 nr) nr ar dr kr u u' pre pre' Ts t v c v' c' ->
           rec_result_app_rel D dr Rel kr u0 u0 pre pre' Ts t v c v' c' rs rs') /\
        (forall pre pre' Ts gs vs vs' ihs ihs', rec_results_rel D dr Rel kr u u' pre pre' Ts gs vs vs' ihs ihs' ->
           con_args_rel p D (admissible_index_at D u0 nr) nr ar dr kr u u' pre pre' Ts gs vs vs' ->
           rec_results_rel D dr Rel kr u0 u0 pre pre' Ts gs vs vs' ihs ihs').
      Proof.
        apply (rec_result_rel_mut_ind_all _ D dr Rel
                 (fun kr u u' pre pre' Ts t v v' rs rs' _ => rec_arg_rel p D (admissible_index_at D u0 nr) nr ar dr kr u u' pre pre' Ts t v v' ->
                    rec_result_rel D dr Rel kr u0 u0 pre pre' Ts t v v' rs rs')
                 (fun kr u u' pre pre' Ts t v c v' c' rs rs' _ => rec_arg_app_rel p D (admissible_index_at D u0 nr) nr ar dr kr u u' pre pre' Ts t v c v' c' ->
                    rec_result_app_rel D dr Rel kr u0 u0 pre pre' Ts t v c v' c' rs rs')
                 (fun kr u u' pre pre' Ts gs vs vs' ihs ihs' _ => con_args_rel p D (admissible_index_at D u0 nr) nr ar dr kr u u' pre pre' Ts gs vs vs' ->
                    rec_results_rel D dr Rel kr u0 u0 pre pre' Ts gs vs vs' ihs ihs')).
        - (** At a member with a block: the motive at [u0]'s indices. *)
          intros kr u u' pre pre' Ts j Mj Ps bs bs' v v' ih ih' HMj Hrv Ebs Ebs' Hrr Ha.
          destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha) as (bs0 & bs0' & Eb0 & Eb0' & [o Eo Ho] & [o' Eo' Ho'] & Hir).
          pose proof (functional_eval_exps' _ _ _ _ Eb0 Ebs) as ->; pose proof (functional_eval_exps' _ _ _ _ Eb0' Ebs') as ->.
          unfold nparams_tele_rel in Ho, Ho'; rewrite HMj in Ho, Ho'.
          eapply rec_result_self; [ exact HMj | exact Hrv | exact Eo | exact Eo' |].
          exact (proj1 (rel_move j Mj HMj Hrv _ _ _ _ _ _ _ _ Hir (tsym _ _ HMj _ _ Ho) (tsym _ _ HMj _ _ Ho') ih ih') Hrr).
        - (** At a record view: its fields'. *)
          intros kr u u' pre pre' Ts j Mj qr Is fl c gs Ps v v' ws ws' rs rs' HMj Hh Hcs Ew Ew' Hr IH Ha.
          destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha) as (bs0 & bs0' & _ & _ & _ & _ & Hir).
          inversion Hir; subst;
            match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end;
            try (exfalso; match goal with H2 : im_is_rview Mj = false |- _ => exact (not_rview_record _ _ _ _ H2 Hh) end).
          match goal with H2 : im_head Mj = _, H3 : im_cons Mj = _ |- _ =>
            rewrite Hh in H2; injection H2 as <- <- <-; rewrite Hcs in H3; injection H3 as <- <- end.
          match goal with E1 : eval_projs _ _ fl v _, E2 : eval_projs _ _ fl v' _ |- _ =>
            pose proof (functional_eval_projs _ _ _ _ E1 Ew) as ->; pose proof (functional_eval_projs _ _ _ _ E2 Ew') as -> end.
          eapply rec_result_rview; [ exact HMj | exact Hh | exact Hcs | exact Ew | exact Ew' | apply IH; eassumption ].
        - (** At a domain: at related arguments. *)
          intros kr u u' pre pre' Ts B t v v' rs rs' Hr IH Hfr Hfr' Ha.
          inversion Ha; subst.
          constructor; [ intros c0 c0' Hc0; apply (IH c0 c0' Hc0); eauto | exact Hfr | exact Hfr' ].
        - intros kr u u' pre pre' Ts t v c v' c' rs rs' fc fc' rcs rcs' Ef Ef' F1 F2 Hr IH Ha.
          inversion Ha; subst.
          match goal with Er : _ |- _ => pose proof (functional_eval_app _ _ _ _ Er Ef) as -> end.
          match goal with Er : _ |- _ => pose proof (functional_eval_app _ _ _ _ Er Ef') as -> end.
          econstructor; [ exact Ef | exact Ef' | exact F1 | exact F2 | apply IH; assumption ].
        - intros; constructor.
        - intros * Hr IH Ha; inversion Ha; subst; constructor; apply IH; assumption.
        - intros * L1 L2 Hr IH1 Hrs IH2 Ha; inversion Ha; subst.
          constructor; [ exact L1 | exact L2 | apply IH1; assumption | apply IH2; assumption ].
      Qed.

      Lemma rec_results_rebase : forall kr u u' pre pre' Ts gs vs vs' ihs ihs',
          con_args_rel p D (admissible_index_at D u0 nr) nr ar dr kr u u' pre pre' Ts gs vs vs' ->
          rec_results_rel D dr Rel kr u u' pre pre' Ts gs vs vs' ihs ihs' ->
          rec_results_rel D dr Rel kr u0 u0 pre pre' Ts gs vs vs' ihs ihs'.
      Proof. intros * Ha Hr; exact (proj2 (proj2 (rec_rebase_all kr u u')) _ _ _ _ _ _ _ _ Hr Ha). Qed.

      (** ** The Frames of a Leaf Path

          A frame is an argument position [gs1 ++ ca_rec t :: gs2] of a
          constructor [c] of a member [k] ([Mk]): a branch's own, or a field
          of a record view's pseudo-constructor.  A leaf path walks the
          domains of the shape [t] in its frame and, at a record view, moves
          on to the frame of one of the view's fields. *)
      Section Frame.
        #[local] Set Default Proof Using "All".
        Variables (k : nat) (Mk : imember) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg).
        Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs) (Heq : gs = gs1 ++ ca_rec t :: gs2).
        Let T := List.rev (im_nparams Mk).
        Let K := List.length (cargs_nonrec gs1).
        Let L := List.length (ptyp_doms t).
        Let Tg := cargs_nonrec_ctx gs1 ++ im_params D Mk ++ Γ.
        (** The syntactic side of the frame ([SynFrame]), at this frame. *)
        #[local] Abbreviation frame_nonrec_le := (frame_nonrec_le HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation frame_nonrec_ctx := (frame_nonrec_ctx HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation frame_nonrec_ctx_valid := (frame_nonrec_ctx_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation frame_nonrec_ctx_all_assumptions := (frame_nonrec_ctx_all_assumptions HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation frame_target_valid := (frame_target_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation frame_doms_valid := (frame_doms_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation frame_doms_ass := (frame_doms_ass HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation frame_doms_len := (frame_doms_len HMall k Mk c gs gs1 t gs2 HMk Hcon Heq).
        #[local] Abbreviation sem_frame := (sem_frame Mk gs1 t).
        (** The telescope of the components before the [kd]-th domain. *)
        Let Tk kd := T ++ cargs_nonrec_tele gs1 ++ List.firstn kd (shape_doms_tele t).
        (** The closed context of the components and the first [kd] domains. *)
        Let Kk kd := doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk.

        (** A closed environment of a telescope [Pre] after the member's
            parameters, at [u0]. *)
        Lemma frame_components_closed : forall Pre zs,
            env_tele nil (List.rev (Pre ++ im_params D Mk)) (u0 ++ zs) = components_env D u0 (List.rev (Pre ++ im_nparams Mk)) zs.
        Proof. intros; unfold im_params; rewrite List.app_assoc; exact (env_tele_uparams D _ u0 zs u0_len). Qed.

        (** The telescope of the components and the first [kd] domains. *)
        Lemma frame_tele_rev : forall kd,
            List.rev (doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk) = Tk kd.
        Proof.
          intros; unfold Tk, T, doms_ctx, shape_doms_tele.
          rewrite !List.rev_app_distr, rev_nonrec_args_context, List.rev_involutive, List.firstn_map, <- !List.app_assoc; reflexivity.
        Qed.

        (** The closed environment of the components at [u0]. *)
        Lemma frame_closed_env : forall kd pre, env_tele nil (List.rev (Kk kd)) (u0 ++ pre) = components_env D u0 (Tk kd) pre.
        Proof.
          intros; unfold Kk; rewrite List.app_assoc, frame_components_closed, <- List.app_assoc, frame_tele_rev; reflexivity.
        Qed.

        (** Past all the domains, the telescope of all the components. *)
        Lemma frame_tele_all : Tk L = T ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t.
        Proof. unfold Tk; rewrite List.firstn_all2; [ reflexivity | unfold shape_doms_tele, L; rewrite List.length_map; lia ]. Qed.

        (** The canonical arguments of the closed telescope of the domains. *)
        Lemma frame_canon_tele_args : forall kd ms ms' ws ws' ys ys', kd <= L ->
            tele_rel (nr k) T ms ms' -> tele_prefix_rel (ar k ms c) K ws ws' ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ms ws t) kd ys ys' ->
            per_tele_args (List.rev (Kk kd)) nil nil (u0 ++ ms ++ ws ++ ys) (u0 ++ ms' ++ ws' ++ ys').
        Proof.
          intros * Hk Hm Hw Hy.
          destruct (sort_value D HD u0 u0_tele_args u0_len) as [a0 Ha0].
          pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Lms & Lms' & _).
          unfold T in Lms, Lms'; rewrite List.length_rev, length_im_nparams in Lms, Lms'.
          pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Lws & Lws' & _).
          pose proof (params_tele_args D HD Hc Hsu k Mk HMk u0 u0 a0 ms ms' u0_tele_args u0_len Ha0 Hm) as Hpg.
          pose proof (ar_tele_args D HD Hc Hsu k Mk HMk c gs u0 u0 a0 ms ms' Hcon u0_tele_args u0_len Ha0 Hm K ws ws' frame_nonrec_le Hw) as Hgv.
          pose proof (dom_tele_args D HD Hc Hsu k Mk HMk c gs gs1 t gs2 u0 u0 a0 ms ms' ws ws' Hcon Heq u0_tele_args u0_len Ha0 Hm Hw kd ys ys' Hk Hy)
            as Hgd.
          pose proof frame_nonrec_le as HK0.
          unfold Kk; rewrite frame_nonrec_ctx, List.rev_app_distr.
          replace (u0 ++ ms ++ ws ++ ys) with ((u0 ++ ms ++ ws) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
          replace (u0 ++ ms' ++ ws' ++ ys') with ((u0 ++ ms' ++ ws') ++ ys') by (rewrite <- !List.app_assoc; reflexivity).
          apply per_tele_args_app_intro;
            [ rewrite List.length_rev, !List.length_app, length_im_params, u0_len; unfold nonrec_args_prefix;
              rewrite List.length_rev, List.length_firstn, length_cargs_nonrec_tele; unfold K, im_np in *; lia | |].
          - rewrite List.rev_app_distr.
            replace (u0 ++ ms ++ ws) with ((u0 ++ ms) ++ ws) by (rewrite <- !List.app_assoc; reflexivity).
            replace (u0 ++ ms' ++ ws') with ((u0 ++ ms') ++ ws') by (rewrite <- !List.app_assoc; reflexivity).
            apply per_tele_args_app_intro; [ rewrite List.length_app, List.length_rev, length_im_params, u0_len; unfold im_np; lia
                                       | exact Hpg |].
            unfold im_params; rewrite (env_tele_uparams D (im_nparams Mk) u0 ms u0_len), (env_tele_uparams D (im_nparams Mk) u0 ms' u0_len).
            unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgv.
          - rewrite !frame_components_closed.
            unfold doms_ctx; rewrite List.rev_involutive, <- List.firstn_map; exact Hgd.
        Qed.

        (** The canonical environments of related canonical arguments are
            related. *)
        Lemma frame_canon_rel : forall kd ms ms' ws ws' ys ys', kd <= L ->
            tele_rel (nr k) T ms ms' -> tele_prefix_rel (ar k ms c) K ws ws' ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ms ws t) kd ys ys' ->
            forall RK, EF Kk kd ≈ Kk kd ∈ per_ctx_env ↘ RK ->
            RK (components_env D u0 (Tk kd) (ms ++ ws ++ ys)) (components_env D u0 (Tk kd) (ms' ++ ws' ++ ys')).
        Proof.
          intros * Hk Hm Hw Hy RK HRK.
          pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Lms & _ & _).
          unfold T in Lms; rewrite List.length_rev, length_im_nparams in Lms.
          pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Lws & _ & _).
          pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Lys & _ & _).
          rewrite <- !frame_closed_env.
          apply (tele_args_env_rel _ _ _ _ _ _ HRK (frame_doms_valid kd Hk)); [| exact (frame_canon_tele_args kd _ _ _ _ _ _ Hk Hm Hw Hy) ].
          unfold Kk; rewrite !List.length_app, frame_doms_len, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele, length_im_params, u0_len
            by exact Hk; fold K; unfold im_np; lia.
        Qed.

        (** The canonical arguments, as values of the telescope of the
            components at [u0]. *)
        Lemma frame_canon_pre : forall kd X nvs ys, kd <= L -> tele_rel (nr k) T X X -> tele_prefix_rel (ar k X c) K nvs nvs ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) X nvs t) kd ys ys ->
            per_tele_args (List.rev (doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk)) (decl_env D u0) (decl_env D u0)
              (X ++ nvs ++ ys) (X ++ nvs ++ ys).
        Proof.
          intros * Hk HX Hnv Hys.
          pose proof (frame_canon_tele_args kd X X nvs nvs ys ys Hk HX Hnv Hys) as Hg.
          replace (Kk kd) with ((doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk) ++ ind_uparams D) in Hg
            by (unfold Kk, im_params; rewrite <- !List.app_assoc; reflexivity).
          rewrite List.rev_app_distr in Hg.
          destruct (per_tele_args_app _ _ _ _ u0 u0 _ _ ltac:(rewrite List.length_rev; exact u0_len) Hg ltac:(rewrite List.length_rev; exact u0_len))
            as [_ Hg1].
          exact Hg1.
        Qed.

        (** A side's environment of the closed telescope, against the
            canonical one. *)
        Lemma frame_closed_link : forall kd Bσ wts w X nvs yts, kd <= L -> RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
            List.map fst wts = w ++ X ++ nvs -> List.length yts = kd ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) wts ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts ->
            tele_rel (nr k) T X X -> tele_prefix_rel (ar k X c) K nvs nvs ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) X nvs t) kd (List.map fst yts) (List.map fst yts) ->
            forall RK, EF Kk kd ≈ Kk kd ∈ per_ctx_env ↘ RK ->
              RK (env_extend_typed (env_extend_typed Bσ wts) yts) (components_env D u0 (Tk kd) (X ++ nvs ++ List.map fst yts)).
        Proof.
          intros * Hk Hw Lw Hwv Lys Hrw Hry HX Hnv Hys RK HRK.
          set (Pre := doms_ctx (List.firstn kd (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk).
          assert (HPe : Pre ++ ind_uparams D = Kk kd) by (unfold Pre, Kk, im_params; rewrite <- !List.app_assoc; reflexivity).
          pose proof HX as H0; rewrite tele_rel_iff in H0; destruct H0 as (LX & _ & _).
          unfold T in LX; rewrite List.length_rev, length_im_nparams in LX.
          pose proof Hnv as H0; rewrite tele_prefix_rel_iff in H0; destruct H0 as (Lnvs & _ & _).
          assert (LPre : List.length (X ++ nvs ++ List.map fst yts) = List.length Pre)
            by (unfold Pre; rewrite !List.length_app, List.length_map, frame_doms_len, length_im_nparams, cargs_nonrec_ctx_rev_tele,
                  List.length_rev, length_cargs_nonrec_tele by exact Hk; fold K; lia).
          rewrite <- HPe in HRK.
          rewrite <- env_extend_typed_app, <- (frame_tele_rev kd).
          refine (closed_pre_typed Pre RK _ _ HRK Bσ w (wts ++ yts) _ Hw Lw (frame_canon_pre kd X nvs _ Hk HX Hnv Hys) LPre _ _).
          - rewrite HPe; apply frame_doms_ass.
          - rewrite HPe; apply frame_doms_valid, Hk.
          - rewrite List.map_app, Hwv, <- !List.app_assoc; reflexivity.
          - apply List.Forall_app; split; assumption.
        Qed.

        (** The domains' arguments at a side's value of the components. *)
        Lemma frame_side_dom_tele_args : forall kd Bσ wts w X nvs ys, kd <= L -> RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
            List.map fst wts = w ++ X ++ nvs -> List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) wts ->
            tele_rel (nr k) T X X -> tele_prefix_rel (ar k X c) K nvs nvs ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) X nvs t) kd ys ys ->
            per_tele_args (List.rev (doms_ctx (List.firstn kd (ptyp_doms t)))) (env_extend_typed Bσ wts) (env_extend_typed Bσ wts) ys ys.
        Proof.
          intros * Hk Hw Lw Hwv Hrw HX Hnvs Hys.
          destruct (sort_value D HD u0 u0_tele_args u0_len) as [a0 Ha0].
          pose proof (dom_tele_args D HD Hc Hsu k Mk HMk c gs gs1 t gs2 u0 u0 a0 X X nvs nvs Hcon Heq u0_tele_args u0_len Ha0 HX Hnvs kd ys ys Hk Hys)
            as Hgd.
          rewrite <- frame_nonrec_ctx in Hgd.
          destruct (rel_ctx_wf_per_ctx_env frame_nonrec_ctx_valid) as [RK0 HRK0].
          assert (HPK : PER RK0) by (eapply per_env_PER; exact HRK0).
          assert (Hc0 : RK0 (env_extend_typed Bσ wts) (components_env D u0 (List.rev (cargs_nonrec_ctx gs1 ++ im_nparams Mk)) (X ++ nvs))).
          { pose proof (frame_closed_link 0 Bσ wts w X nvs nil ltac:(lia) Hw Lw Hwv eq_refl Hrw (List.Forall_nil _) HX Hnvs
                          (tele_prefix_rel_nil _) RK0 HRK0) as H.
            rewrite <- (frame_tele_rev 0) in H; change (List.map fst (@nil (domain * entry_type))) with (@nil domain) in H.
            rewrite List.app_nil_r in H; exact H. }
          assert (Hcc : RK0 (components_env D u0 (List.rev (cargs_nonrec_ctx gs1 ++ im_nparams Mk)) (X ++ nvs))
                            (components_env D u0 (List.rev (cargs_nonrec_ctx gs1 ++ im_nparams Mk)) (X ++ nvs)))
            by (etransitivity; [ symmetry; exact Hc0 | exact Hc0 ]).
          rewrite List.firstn_map in Hgd; unfold doms_ctx; rewrite List.rev_involutive.
          eapply (per_tele_args_base _ _ _ HRK0); [ exact (frame_doms_valid kd Hk) | apply all_assumptions_map_ass
                                              | exact Hcc | symmetry; exact Hc0 | symmetry; exact Hc0 | exact Hgd ].
        Qed.

        (** The canonical arguments and the side's, one prefix along. *)
        Lemma frame_side_refl : forall ns X nv nvs kd ys0 ys, kd <= L ->
            tele_rel (nr k) T ns X -> tele_prefix_rel (ar k ns c) K nv nvs ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns nv t) kd ys0 ys ->
            tele_rel (nr k) T X X /\ tele_prefix_rel (ar k X c) K nvs nvs /\
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) X nvs t) kd ys ys.
        Proof.
          intros * Hk HX Hnv Hys.
          split; [ exact (trefl_r _ _ HMk _ _ HX) | split ].
          - exact (args_prefix_rel_refl_r p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns X c gs K nv nvs HX Hcon frame_nonrec_le Hnv).
          - exact (doms_rel_refl_inst p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns X c gs gs1 t gs2 nv nvs kd ys0 ys
                     HX Hcon Heq Hnv Hk Hys).
        Qed.

        (** The values at an environment [E] of the base: [E] over [B],
            [σ0]'s value over [B] at the uniform parameters [w], the
            non-uniform ones [X] and the non-recursive arguments [nv]
            before the position, and [x0]'s value [v]. *)
        #[warnings="-cannot-define-projection"]
        Record sem_frame_vals (Ψ0 : ctx) (σ0 : sub) (x0 : exp) (RΨ : relation env)
            (E B : env) (zts : list (domain * entry_type)) (w X nv : list domain) (v : domain) : Prop := mk_sem_frame_vals
          { (** [E] is related to itself *)
            frame_vals_env : RΨ E E
            (** It extends [B] by one typed value per entry of [Ψ0] *)
          ; frame_vals_split : E = env_extend_typed B zts
            (** As many as [Ψ0] has entries *)
          ; frame_vals_split_len : List.length zts = List.length Ψ0
            (** [B] is of the class of [C1] *)
          ; frame_vals_base : RΓ B C1
            (** The components' value, over a base of its own: the
                components' values, read back at their types, are read off
                it, the base not *)
          ; frame_vals_sigma : exists Bσ wts, ⟦ σ0 : Tg ⟧s E ↘ env_extend_typed Bσ wts /\ List.map fst wts = w ++ X ++ nv /\
              List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) wts
            (** The argument's value *)
          ; frame_vals_arg : ⟦ x0 ⟧ E ↘ v
            (** The uniform parameters are of the class of [u0] *)
          ; frame_vals_uparams : RU (decl_env D w) (decl_env D u0)
            (** One per uniform parameter *)
          ; frame_vals_uparams_len : List.length w = ind_nu D
            (** One per non-uniform parameter *)
          ; frame_vals_nparams_len : List.length X = im_nn Mk
            (** One per non-recursive argument before *)
          ; frame_vals_args_len : List.length nv = K }.

        Section Base.
          Variables (Ψ0 : ctx) (σ0 β0 : sub) (x0 : exp).
          Hypothesis (Hf : sem_frame Ψ0 σ0 β0 x0).
          Variable (RΨ : relation env).
          Hypothesis (HRΨ : EF Ψ0 ++ Γ ≈ Ψ0 ++ Γ ∈ per_ctx_env ↘ RΨ).

          (** The domain of the [kd]-th step at a side: its value, against
              its canonical value, relevant. *)
          Lemma frame_dom_value : forall kd Bk, List.nth_error (ptyp_doms t) kd = Some Bk ->
              forall E B zts w X nv v yts, sem_frame_vals Ψ0 σ0 x0 RΨ E B zts w X nv v -> List.length yts = kd ->
              List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts ->
              tele_rel (nr k) T X X -> tele_prefix_rel (ar k X c) K nv nv ->
              tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) X nv t) kd (List.map fst yts) (List.map fst yts) ->
              exists a b (i : nat), ⟦ Bk[sb_qn kd σ0] ⟧ env_extend_typed E yts ↘ a /\
                ⟦ Bk ⟧ components_env D u0 (Tk kd) (X ++ nv ++ List.map fst yts) ↘ b /\ Dom a ≈ b ∈ per_univ i /\
                domain_kind a = ak_relevant.
          Proof.
            intros * HBk * Hv Lys Hry HX Hnvs Hys.
            destruct Hf as [_ Hsig _ _ _ _ _]; destruct Hv as [HE _ _ _ (Bσ & wts & Hσe & Hwv & Hrw) _ HwU Lw LX Lnv].
            assert (Hk : kd < L) by (unfold L; apply List.nth_error_Some; congruence).
            set (Δ := doms_ctx (List.firstn kd (ptyp_doms t))).
            assert (LΔ : List.length Δ = kd) by (apply frame_doms_len; lia).
            destruct (valid_ind_decl_dom _ HD k Mk c gs gs1 t gs2 kd Bk HMk Hcon Heq HBk) as (_ & i0 & HBv).
            rewrite <- frame_nonrec_ctx in HBv; fold Δ in HBv.
            pose proof (frame_doms_valid kd ltac:(lia)) as HKk; fold Δ in HKk.
            pose proof (frame_doms_ass kd) as HKka; fold Δ in HKka.
            assert (HΔa : all_assumptions Δ) by (unfold Δ, doms_ctx; apply List.Forall_rev, all_assumptions_map_ass).
            destruct (closed_app_sem _ _ HKka HKk HΓ) as [HKkΓ _].
            rewrite <- !List.app_assoc in HKkΓ.
            pose proof (closed_app_valid _ _ _ _ _ HKka HKk HΓ HBv) as HBvΓ; rewrite <- !List.app_assoc in HBvΓ.
            pose proof (frame_side_dom_tele_args kd Bσ wts w X nv _ ltac:(lia) HwU Lw Hwv Hrw HX Hnvs Hys) as Hgy; fold Δ in Hgy.
            destruct (outer_universe_type_link Δ Tg (Ψ0 ++ Γ) RΨ σ0 _ _ Bk Bk i0 HΔa HKkΓ HBvΓ HRΨ (gsub_valid Hsig) HE Hσe yts Hgy
                        ltac:(rewrite LΔ; exact Lys) Hry) as (a & b' & Ea & Eb' & Hab).
            rewrite LΔ in Ea.
            destruct (rel_ctx_wf_per_ctx_env HKk) as [RK HRK].
            pose proof (frame_closed_link kd Bσ wts w X nv yts ltac:(lia) HwU Lw Hwv Lys Hrw Hry HX Hnvs Hys RK HRK) as HEK.
            destruct (rel_exp_of_typ_inversion_simple_at HRK HBv _ _ HEK) as (b1 & b & Eb1 & Eb & Hbb).
            assert (b1 = b') as -> by (eapply functional_eval_exp; eassumption).
            (** The domain is of a universe, so relevant on the closed side, and
                so at [a]. *)
            destruct (rel_exp_of_typ_relevant_at HRK HBv _ _ HEK) as (b2 & Eb2 & Hr2).
            assert (b2 = b') as -> by (eapply functional_eval_exp; eassumption).
            destruct Hab as [Rab HRab]; pose proof (per_univ_elem_kind _ _ _ _ HRab) as Hr.
            exists a, b, i0; split; [ exact Ea | split; [ exact Eb | split; [ etransitivity; [ exists Rab; exact HRab | exact Hbb ] | congruence ] ] ].
          Qed.

          (** The domain of the [kd]-th step at a side, against its
              canonical value. *)
          Lemma frame_dom_link : forall kd Bk, List.nth_error (ptyp_doms t) kd = Some Bk ->
              forall E B zts w X nv v yts a ns cv ys0, sem_frame_vals Ψ0 σ0 x0 RΨ E B zts w X nv v -> List.length yts = kd ->
              List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts ->
              tele_rel (nr k) T ns X -> tele_prefix_rel (ar k ns c) K cv nv ->
              tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns cv t) kd ys0 (List.map fst yts) ->
              ⟦ Bk[sb_qn kd σ0] ⟧ env_extend_typed E yts ↘ a ->
              exists b (i : nat), ⟦ Bk ⟧ components_env D u0 (Tk kd) (ns ++ cv ++ ys0) ↘ b /\ Dom a ≈ b ∈ per_univ i /\
                domain_kind a = ak_relevant.
          Proof.
            intros * HBk * Hv Lys Hry HX Hnvs Hys Ea.
            assert (Hk : kd < L) by (unfold L; apply List.nth_error_Some; congruence).
            destruct (frame_side_refl ns X cv nv kd ys0 _ ltac:(lia) HX Hnvs Hys) as (HXd & Hnvd & Hysd).
            destruct (frame_dom_value kd Bk HBk E B zts w X nv v yts Hv Lys Hry HXd Hnvd Hysd) as (a' & b & i & Ea' & Eb & Hab & Hr).
            assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
            (** The canonical value, at the canonical arguments. *)
            destruct (valid_ind_decl_dom _ HD k Mk c gs gs1 t gs2 kd Bk HMk Hcon Heq HBk) as (_ & i0 & HBv).
            rewrite <- frame_nonrec_ctx in HBv.
            destruct (rel_ctx_wf_per_ctx_env (frame_doms_valid kd ltac:(lia))) as [RK HRK].
            pose proof (frame_canon_rel kd _ _ _ _ _ _ ltac:(lia) HX Hnvs Hys RK HRK) as Q.
            destruct (rel_exp_of_typ_inversion_simple_at HRK HBv _ _ Q) as (c0 & b' & Ec0 & Eb' & Hcb).
            assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
            exists c0, i; split; [ exact Ec0 | split; [| exact Hr ] ].
            eapply per_univ_trans'; [ exact Hab | apply per_univ_sym'; exact Hcb ].
          Qed.

          (** *** The End of the Frame's Shape

              The shape ends in the member [Mj] with a block [bj]. *)
          Variables (Mj : imember).
          Hypotheses (HMj : ind_member D (ptyp_mem t) = Some Mj).
          Let Ps' := List.map (fun P => P[sb_qn L σ0]) (ptyp_ps t).
          Let xL := apps_vars_iter L x0.
          Let τL := sb_of_list (sb_shift_iter L β0) (Ps' ++ xL :: nil).
          Let ΨL := tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ.
          Let ITj := ind_mty p D (ptyp_mem t) (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)).

          #[local] Abbreviation frame_end_params_len := (frame_end_params_len HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
          #[local] Abbreviation frame_tele_len :=
            (frame_tele_len HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj : List.length (ptyp_tele t) = L).
          #[local] Abbreviation frame_doms_tele :=
            (frame_doms_tele HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj : ptyp_tele t = doms_ctx (List.firstn L (ptyp_doms t))).
          #[local] Abbreviation frame_tele_valid := (frame_tele_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
          #[local] Abbreviation frame_end_ctx_valid := (frame_end_ctx_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
          #[local] Abbreviation frame_end_base_eq := (frame_end_base_eq HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
          #[local] Abbreviation frame_end_params_valid := (frame_end_params_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
          #[local] Abbreviation frame_gsub_leaf := (frame_gsub_leaf HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).

          (** A side's environment of the base extended by the domains'
              values [ys], of the context [ΨL]. *)
          Lemma frame_end_env : forall ns nv0 ys0 E B zts w X nv v yts,
              sem_frame_vals Ψ0 σ0 x0 RΨ E B zts w X nv v -> List.length yts = L ->
              List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts ->
              tele_rel (nr k) T ns X -> tele_prefix_rel (ar k ns c) K nv0 nv ->
              tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns nv0 t) L ys0 (List.map fst yts) ->
              forall RSL, EF ΨL ≈ ΨL ∈ per_ctx_env ↘ RSL -> RSL (env_extend_typed E yts) (env_extend_typed E yts).
          Proof.
            intros * Hv Lys Hry HX Hnv Hys RSL HRSL.
            pose proof Hv as [HE _ _ _ (Bσ & wts & Hσe & Hwv & Hrw) _ HwU Lw LX Lnvs].
            destruct (frame_side_refl ns X nv0 nv L ys0 _ (le_n _) HX Hnv Hys) as (HXd & Hnvd & Hysd).
            pose proof (frame_side_dom_tele_args L Bσ wts w X nv _ (le_n _) HwU Lw Hwv Hrw HXd Hnvd Hysd) as Hgy; rewrite <- frame_doms_tele in Hgy.
            assert (HΔa : all_assumptions (ptyp_tele t)) by (unfold ptyp_tele, doms_ctx; apply List.Forall_rev, all_assumptions_map_ass).
            exact (tele_stage_rel (ptyp_tele t) Tg (Ψ0 ++ Γ) σ0 RΨ E _ HΔa frame_tele_valid HRΨ (gsub_valid (sem_frame_sigma _ _ _ _ _ _ _ Hf)) HE Hσe yts Hgy
                     ltac:(rewrite frame_tele_len; exact Lys) Hry RSL HRSL).
          Qed.

          (** The base past the domains, at a side's environment extended by
              their values: the side's base, retagged at [Γ]. *)
          Lemma frame_end_base_eval : forall E B zts w X nv v yts,
              sem_frame_vals Ψ0 σ0 x0 RΨ E B zts w X nv v -> List.length yts = L ->
              ⟦ sb_shift_iter L β0 : Γ ⟧s env_extend_typed E yts ↘ ctx_retag Γ B.
          Proof.
            intros * Hv Lys.
            pose proof Hv as [_ HEB Lzs _ _ _ _ _ _ _].
            assert (HEys : env_extend_typed E yts = env_extend_typed B (zts ++ yts)) by (rewrite HEB, env_extend_typed_app; reflexivity).
            apply (eval_sub_sb_eq (symmetry frame_end_base_eq)).
            rewrite HEys.
            replace (List.length (tele_sub (ptyp_tele t) σ0 ++ Ψ0)) with (List.length (zts ++ yts))
              by (rewrite !List.length_app, length_tele_sub, frame_tele_len, Lzs, Lys; lia).
            pose proof (@eval_sub_of_wk gc_deps gc_stack Γ (wk_shiftn (List.length (zts ++ yts))) (env_extend_typed B (zts ++ yts))
                          (wk_mono_shiftn _)) as H.
            rewrite eval_wk_shiftn_extend_typed in H; exact H.
          Qed.

          (** At a member with a block [bj]. *)
          Variable (bj : eblock).
          Hypotheses (Hrvj : im_is_rview Mj = false) (Hbj : List.nth_error Bks (ptyp_mem t) = Some bj).

          (** The motive at the end of the shape at a side, after all the
              domains, against its value at the side's parameters of the
              end ([Xq]), related to the canonical ones [bs]. *)
          Lemma frame_leaf_link : forall ns nv0 ys0 bs E B zts w X nv v yts f a, leaf_term x0 -> leaf_apps_relevant x0 E ->
              sem_frame_vals Ψ0 σ0 x0 RΨ E B zts w X nv v -> List.length yts = L ->
              List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts ->
              tele_rel (nr k) T ns X -> tele_prefix_rel (ar k ns c) K nv0 nv ->
              tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns nv0 t) L ys0 (List.map fst yts) ->
              ⟦ ptyp_ps t ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u0 (T ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv0 ++ ys0)
                ↘ bs ->
              $*| v & List.map fst yts | gc_deps ⍮ gc_stack ↘ f -> apps_relevant v (List.map fst yts) ->
              ⟦ (eb_motive bj)[τL] ⟧ env_extend_typed E yts ↘ a ->
              exists Xq b, tele_rel (nr (ptyp_mem t)) (List.rev (im_nparams Mj)) bs Xq /\
                ⟦ eb_motive bj ⟧ env_extend_tagged Γ (List.rev (elim_mctx p D (ptyp_mem t) Mj Us)) (ctx_retag Γ B) (Xq ++ f :: nil) ↘ b /\
                Dom a ≈ b ∈ per_univ iA /\
                List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt)))
                  (tagged_entries Γ (List.rev (elim_mctx p D (ptyp_mem t) Mj Us)) (ctx_retag Γ B) (Xq ++ f :: nil)).
          Proof.
            intros * Hlt Hxr Hv Lys Hry HX Hnv Hys Ebs Ef Hrel Ea.
            pose proof Hv as [HE HEB Lzs _ (Bσ & wts & Hσe & Hwv & Hrw) Hxv HwU Lw LX Lnvs].
            set (ys := List.map fst yts) in *.
            assert (Lnv0 : List.length nv0 = K) by (pose proof Hnv as H0; rewrite tele_prefix_rel_iff in H0; destruct H0 as (H0 & _); exact H0).
            assert (Lys0 : List.length ys0 = L) by (pose proof Hys as H0; rewrite tele_prefix_rel_iff in H0; destruct H0 as (H0 & _); exact H0).
            assert (LXn : List.length ns = im_nn Mk)
              by (pose proof HX as H0; rewrite tele_rel_iff in H0; destruct H0 as (H0 & _); unfold T in H0;
                  rewrite List.length_rev, length_im_nparams in H0; exact H0).
            destruct (frame_side_refl ns X nv0 nv L ys0 ys (le_n _) HX Hnv Hys) as (HXd & Hnvd & Hysd).
            assert (Hns : tele_rel (nr k) T ns ns) by exact (trefl_l _ _ HMk _ _ HX).
            assert (Hnv0 : tele_prefix_rel (ar k ns c) K nv0 nv0)
              by exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs Hns Hcon K _ _ frame_nonrec_le Hnv).
            assert (Hys0 : tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns nv0 t) L ys0 ys0)
              by exact (doms_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs gs1 t gs2 nv0 Hns Hcon Heq Hnv0
                          L _ _ (le_n _) Hys).
            set (ρσ := env_extend_typed Bσ wts) in *.
            pose proof (frame_side_dom_tele_args L Bσ wts w X nv ys (le_n _) HwU Lw Hwv Hrw HXd Hnvd Hysd) as Hgy; rewrite <- frame_doms_tele in Hgy.
            assert (HΔa : all_assumptions (ptyp_tele t)) by (unfold ptyp_tele, doms_ctx; apply List.Forall_rev, all_assumptions_map_ass).
            destruct (rel_ctx_wf_per_ctx_env frame_end_ctx_valid) as [RSL HRSL].
            pose proof (tele_stage_rel (ptyp_tele t) Tg (Ψ0 ++ Γ) σ0 RΨ E ρσ HΔa frame_tele_valid HRΨ (gsub_valid (sem_frame_sigma _ _ _ _ _ _ _ Hf)) HE Hσe yts Hgy
                          ltac:(rewrite frame_tele_len; exact Lys) Hry RSL HRSL) as HEL.
            (** The closed telescope of the end. *)
            set (KL := ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk).
            assert (HKa : all_assumptions KL) by (unfold KL; rewrite frame_doms_tele; apply frame_doms_ass).
            assert (HKs : ⊨ KL) by (unfold KL; rewrite frame_doms_tele; apply frame_doms_valid, le_n).
            destruct (rel_ctx_wf_per_ctx_env HKs) as [RK HRK].
            assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
            assert (HRK' : EF Kk L ≈ Kk L ∈ per_ctx_env ↘ RK) by (unfold KL in HRK; rewrite frame_doms_tele in HRK; exact HRK).
            set (can0 := components_env D u0 (T ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv0 ++ ys0)).
            set (Es := env_extend_typed ρσ yts).
            assert (Hc0s : RK can0 (components_env D u0 (T ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (X ++ nv ++ ys))).
            { unfold can0; rewrite <- frame_tele_all; exact (frame_canon_rel L _ _ _ _ _ _ (le_n _) HX Hnv Hys RK HRK'). }
            assert (Hc00 : RK can0 can0) by (etransitivity; [ exact Hc0s | symmetry; exact Hc0s ]).
            assert (HEs : RK Es (components_env D u0 (T ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (X ++ nv ++ ys))).
            { unfold Es, ρσ; rewrite <- frame_tele_all.
              exact (frame_closed_link L Bσ wts w X nv yts (le_n _) HwU Lw Hwv Lys Hrw Hry HXd Hnvd Hysd RK HRK'). }
            assert (HEs0 : RK Es can0) by (etransitivity; [ exact HEs | symmetry; exact Hc0s ]).
            destruct (closed_app_sem _ _ HKa HKs HΓ) as [HKΓ HresK].
            (** The canonical parameters. *)
            assert (Hgall : per_tele_args (List.rev (ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)) nil nil
                              (u0 ++ ns ++ nv0 ++ ys0) (u0 ++ ns ++ nv0 ++ ys0)).
            { rewrite <- frame_nonrec_ctx, frame_doms_tele; exact (frame_canon_tele_args L _ _ _ _ _ _ (le_n _) Hns Hnv0 Hys0). }
            destruct (rec_closure D HD Hc k Mk HMk c gs gs1 t gs2 Mj Hcon Heq HMj u0 u0 ns ns nv0 nv0 ys0 ys0
                        u0_len LXn Lnv0 Lys0 u0_len LXn Lnv0 Lys0 Hgall)
              as (bs' & _ & Ebs' & _ & _ & Hil).
            pose proof (functional_eval_exps' _ _ _ _ Ebs' Ebs) as ->.
            (** The parameters of the end, against the canonical ones. *)
            assert (Hcomp : forall kk P0 T1, List.nth_error (ptyp_ps t) kk = Some P0 ->
                       List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))) (ptyp_ps t)) kk
                         = Some T1 ->
                       exists m1 b, ⟦ P0[sb_qn L σ0] ⟧ env_extend_typed E yts ↘ m1 /\ ⟦ P0 ⟧ can0 ↘ b /\ per_head T1 T1 can0 can0 b m1).
            { intros * HP0 HT1.
              pose proof (frame_end_params_valid _ _ _ HP0 HT1) as HPv; fold KL in HPv.
              pose proof (closed_app_valid _ _ _ _ _ HKa HKs HΓ HPv) as HPvΓ.
              assert (HPvΓ' : ptyp_tele t ++ Tg ⊨ P0 : T1) by (unfold KL in HPvΓ; unfold Tg; rewrite <- !List.app_assoc in HPvΓ; exact HPvΓ).
              (** A non-uniform parameter's type is not [LevelSort]
                  ([rec_closure]). *)
              pose proof (proj2 (proj2 (Hil _ _ _ HP0 HT1))) as HTn; rewrite <- frame_nonrec_ctx in HTn.
              destruct (presup_rel_exp_under_ctx HPv HTn) as [iT HT].
              (** A non-uniform parameter is relevant: at the canonical
                  environment, so at [Es], related to it. *)
              assert (HrT : rel_typ_evaluated T1 Es).
              { destruct (proj1 (proj2 (Hil _ _ _ HP0 HT1))) as (tc & Etc & Hrc).
                destruct (rel_type_inversion_simple_at HRK HT _ _ HEs0) as (te & tc' & Ete & Etc' & [Rt HRt]).
                assert (tc' = tc) as -> by (eapply functional_eval_exp; eassumption).
                pose proof (per_univ_elem_kind _ _ _ _ HRt) as Hrr.
                exists te; split; [ exact Ete | rewrite Hrr, Hrc; constructor ]. }
              destruct (outer_exp_link (ptyp_tele t) Tg (Ψ0 ++ Γ) RΨ σ0 E ρσ T1 P0 P0 HΔa frame_tele_valid HPvΓ' HRΨ (gsub_valid (sem_frame_sigma _ _ _ _ _ _ _ Hf))
                          HE Hσe yts Hgy ltac:(rewrite frame_tele_len; exact Lys) Hry HrT) as (RΔ & F & m1 & n & HRΔ & HF & Em1 & En & Hmn).
              rewrite frame_tele_len in Em1.
              destruct (rel_ctx_wf_per_ctx_env HKΓ) as [RKΓ HRKΓ].
              assert (HRKΓ' : EF ptyp_tele t ++ Tg ≈ ptyp_tele t ++ Tg ∈ per_ctx_env ↘ RKΓ)
                by (unfold Tg; unfold KL in HRKΓ; rewrite <- !List.app_assoc in HRKΓ; exact HRKΓ).
              assert (EΔ : RΔ <~> RKΓ) by (eapply per_ctx_env_right_irrel; [ exact HRΔ | exact HRKΓ' ]).
              assert (HF' : RK F Es) by (apply (HresK _ _ HRK HRKΓ), EΔ; exact HF).
              destruct (rel_exp_under_ctx_simple_at_evaluated HRK HPv _ _ HEs0 HrT) as (n' & b & En' & Eb & Hnb).
              assert (n' = n) as -> by (eapply functional_eval_exp; eassumption).
              assert (C1' : per_head T1 T1 F Es <~> per_head T1 T1 can0 can0).
              { apply (per_head_of_type_resp HRK HT).
                apply rel_chain_cons; [ exact HF' |]. apply rel_chain_cons; [ exact HEs0 |]. apply rel_chain_of_pair; exact Hc00. }
              assert (C2' : per_head T1 T1 Es can0 <~> per_head T1 T1 can0 can0).
              { apply (per_head_of_type_resp HRK HT).
                apply rel_chain_cons; [ exact HEs0 |]. apply rel_chain_cons; [ exact Hc00 |]. apply rel_chain_of_pair; exact Hc00. }
              exists m1, b; split; [ exact Em1 | split; [ exact Eb |] ].
              apply (per_head_sym _ _ _ _ _ _ HRK HT Hc00).
              exact (per_head_trans _ _ _ _ _ _ HRK HT Hc00 _ _ _ (proj1 (C1' _ _) Hmn) (proj1 (C2' _ _) Hnb)). }
            (** Their values. *)
            pose proof frame_end_params_len as HPl.
            assert (HTex : forall kk, kk < im_nn Mj ->
                       exists T1, List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))) (ptyp_ps t)) kk
                                    = Some T1).
            { intros kk Hkk; apply nth_error_lt_some'.
              rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMj); rewrite length_im_nparams; lia. }
            destruct (eval_exps_each Ps' (env_extend_typed E yts)) as [Xq HXq].
            { intros kk M HM0; unfold Ps' in HM0; rewrite List.nth_error_map in HM0.
              destruct (List.nth_error (ptyp_ps t) kk) as [P0 |] eqn:HP0; cbn in HM0; [ injection HM0 as <- | discriminate ].
              assert (Hkk : kk < im_nn Mj) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
              destruct (HTex _ Hkk) as [T1 HT1].
              destruct (Hcomp _ _ _ HP0 HT1) as (m1 & _ & Em1 & _); eauto. }
            assert (Htf : tele_rel (nr (ptyp_mem t)) (List.rev (im_nparams Mj)) bs Xq).
            { rewrite tele_rel_iff; rewrite List.length_rev, length_im_nparams.
              rewrite (eval_exps_length _ _ _ Ebs), (eval_exps_length _ _ _ HXq); unfold Ps'; rewrite List.length_map.
              split; [ exact HPl | split; [ exact HPl |] ].
              intros jj y y' Hy Hy'.
              assert (Hjj : jj < im_nn Mj) by (rewrite <- HPl, <- (eval_exps_length _ _ _ Ebs); apply List.nth_error_Some; congruence).
              destruct (nth_error_lt_some' (ptyp_ps t) jj ltac:(lia)) as [P0 HP0].
              destruct (HTex _ Hjj) as [T1 HT1].
              destruct (Hcomp _ _ _ HP0 HT1) as (m1 & b & Em1 & Eb & Hbm).
              destruct (eval_exps_nth _ _ _ _ _ Ebs HP0) as (b0 & Hb0 & Eb0).
              destruct (eval_exps_nth _ _ _ _ _ HXq ltac:(unfold Ps'; rewrite List.nth_error_map, HP0; reflexivity)) as (m2 & Hm2 & Em2).
              assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
              assert (m2 = m1) as -> by (eapply functional_eval_exp; eassumption).
              rewrite Hy in Hb0; injection Hb0 as ->; rewrite Hy' in Hm2; injection Hm2 as ->.
              apply (proj1 (Hil _ _ _ HP0 HT1)); exact Hbm. }
            (** The value of the end's substitution. *)
            pose proof (frame_end_base_eval _ _ _ _ _ _ _ _ Hv Lys) as Hβe.
            assert (Ex : ⟦ xL ⟧ env_extend_typed E yts ↘ f).
            { exact (frame_arg_end_eval x0 L E yts v f Hlt Lys Hxr Hxv Ef Hrel). }
            (** The end's substitution: its terms' values, the motive
                context's entries being relevant. *)
            destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
            destruct (sb_of_list_values_of_sub (elim_mctx p D (ptyp_mem t) Mj Us) Γ ΨL (sb_shift_iter L β0) (Ps' ++ xL :: nil)
                        RSL RM (env_extend_typed E yts) (ctx_retag Γ B) (elim_mctx_ass p D _ Mj Us Hc HMj) HRSL HRM
                        (mctx_evaluated _ _ HMj (HMall _ _ HMj)) (gsub_valid frame_gsub_leaf)
                        ltac:(rewrite List.length_app, length_elim_mctx; unfold Ps'; rewrite List.length_map, HPl; cbn; lia)
                        HEL Hβe) as (ms & Ems & Hτe & HMe).
            assert (Ems' : ⟦ Ps' ++ xL :: nil ⟧* gc_deps ⍮ gc_stack ⍮ env_extend_typed E yts ↘ Xq ++ f :: nil)
              by (apply eval_exps_app; [ exact HXq | econstructor; [ exact Ex | constructor ] ]).
            pose proof (functional_eval_exps' _ _ _ _ Ems Ems') as ->.
            destruct (typ_inst_link _ _ _ _ _ _ _ _ _ (rel_type_of_typ (HAv _ _ _ HMj Hbj)) HRSL (gsub_valid frame_gsub_leaf) HEL Hτe) as (a' & b & Ea' & Eb & Hab).
            assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
            (** The motive's environment reads back. *)
            destruct (mctx_rev_sem _ _ HMj RM HRM) as (HMr & HRMr & Hta).
            assert (LXf : List.length (List.rev (elim_mctx p D (ptyp_mem t) Mj Us)) = List.length (Xq ++ f :: nil)).
            { pose proof Htf as H0; rewrite tele_rel_iff in H0; destruct H0 as (_ & H0 & _).
              rewrite List.length_rev, length_im_nparams in H0.
              rewrite List.length_rev, length_elim_mctx, List.length_app; cbn [List.length]; lia. }
            rewrite env_extend_tagged_typed in HMe.
            assert (Lt : List.length (tagged_entries Γ (List.rev (elim_mctx p D (ptyp_mem t) Mj Us)) (ctx_retag Γ B) (Xq ++ f :: nil))
                         = List.length (List.rev (elim_mctx p D (ptyp_mem t) Mj Us)))
              by (rewrite tagged_entries_length by exact LXf; symmetry; exact LXf).
            destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ Lt Lt HMe) as [Hrd _].
            exists Xq, b; split; [ exact Htf | split; [ exact Eb | split; [ exact Hab | exact Hrd ] ] ].
          Qed.
        End Base.

        (** At the end, at two sides related to the canonical arguments:
            the type of the result is the family at the end. *)
        Lemma frame_leaf_char : forall Mj bj, ind_member D (ptyp_mem t) = Some Mj -> im_is_rview Mj = false ->
            List.nth_error Bks (ptyp_mem t) = Some bj ->
            forall Ψ1 σ1 β1 x1 RΨ1 Ψ2 σ2 β2 x2 RΨ2, sem_frame Ψ1 σ1 β1 x1 -> EF Ψ1 ++ Γ ≈ Ψ1 ++ Γ ∈ per_ctx_env ↘ RΨ1 ->
            sem_frame Ψ2 σ2 β2 x2 -> EF Ψ2 ++ Γ ≈ Ψ2 ++ Γ ∈ per_ctx_env ↘ RΨ2 ->
            forall ns cv E1 B1 zts1 w1 X1 nv1 v1 E2 B2 zts2 w2 X2 nv2 v2 yts1 yts2 f1 f2 bs bs' a1 a2 (i : nat) R,
            leaf_term x1 -> leaf_term x2 -> leaf_apps_relevant x1 E1 -> leaf_apps_relevant x2 E2 ->
            sem_frame_vals Ψ1 σ1 x1 RΨ1 E1 B1 zts1 w1 X1 nv1 v1 -> sem_frame_vals Ψ2 σ2 x2 RΨ2 E2 B2 zts2 w2 X2 nv2 v2 ->
            List.length yts1 = L -> List.length yts2 = L ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts1 ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts2 ->
            tele_rel (nr k) T ns X1 -> tele_rel (nr k) T ns X2 -> tele_prefix_rel (ar k ns c) K cv nv1 -> tele_prefix_rel (ar k ns c) K cv nv2 ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns cv t) L (List.map fst yts1) (List.map fst yts2) ->
            $*| v1 & List.map fst yts1 | gc_deps ⍮ gc_stack ↘ f1 -> $*| v2 & List.map fst yts2 | gc_deps ⍮ gc_stack ↘ f2 ->
            apps_relevant v1 (List.map fst yts1) -> apps_relevant v2 (List.map fst yts2) ->
            ⟦ ptyp_ps t ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u0 (T ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                                                (ns ++ cv ++ List.map fst yts1) ↘ bs ->
            G (ptyp_mem t) u0 u0 bs bs' f1 f2 ->
            ⟦ (eb_motive bj)[sb_of_list (sb_shift_iter L β1) (List.map (fun P => P[sb_qn L σ1]) (ptyp_ps t) ++ apps_vars_iter L x1 :: nil)] ⟧
              env_extend_typed E1 yts1 ↘ a1 ->
            ⟦ (eb_motive bj)[sb_of_list (sb_shift_iter L β2) (List.map (fun P => P[sb_qn L σ2]) (ptyp_ps t) ++ apps_vars_iter L x2 :: nil)] ⟧
              env_extend_typed E2 yts2 ↘ a2 ->
            DF a1 ≈ a2 ∈ per_univ_elem i ↘ R -> (R <~> Rel (ptyp_mem t) bs f1 bs' f2).
        Proof.
          intros Mj bj HMj Hrvj Hbj * Hf1 HRΨ1 Hf2 HRΨ2 * Hlt1 Hlt2 Hxr1 Hxr2 Hv1 Hv2 Lys1 Lys2 Hry1 Hry2 HX1 HX2 Hcv1 Hcv2 Hys Ef1 Ef2
                 Hrel1 Hrel2 Ebs Hrr Ea1 Ea2 HR.
          pose proof (ins _ _ _ _ _ _ _ _ HMj Hrr) as Hbb'.
          pose proof (isym _ _ _ _ _ _ _ Hrr) as Hrs.
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
          assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
          assert (Hns : tele_rel (nr k) T ns ns) by exact (trefl_l _ _ HMk _ _ HX1).
          assert (Hcvv : tele_prefix_rel (ar k ns c) K cv cv)
            by exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs Hns Hcon K _ _ frame_nonrec_le Hcv1).
          assert (Hys11 : tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns cv t) L (List.map fst yts1) (List.map fst yts1))
            by exact (doms_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs gs1 t gs2 cv Hns Hcon Heq Hcvv
                        L _ _ (le_n _) Hys).
          destruct (frame_leaf_link _ _ _ _ Hf1 _ HRΨ1 Mj HMj bj Hrvj Hbj ns cv _ bs _ _ _ _ _ _ _ yts1 f1 a1 Hlt1 Hxr1 Hv1 Lys1 Hry1 HX1 Hcv1
                      Hys11 Ebs Ef1 Hrel1 Ea1) as (Xq1 & A1 & Htf1 & EA1 & Ha1 & Hrd1).
          destruct (frame_leaf_link _ _ _ _ Hf2 _ HRΨ2 Mj HMj bj Hrvj Hbj ns cv _ bs _ _ _ _ _ _ _ yts2 f2 a2 Hlt2 Hxr2 Hv2 Lys2 Hry2 HX2 Hcv2
                      Hys Ebs Ef2 Hrel2 Ea2) as (Xq2 & A2 & Htf2 & EA2 & Ha2 & Hrd2).
          pose proof (frame_vals_base _ _ _ _ _ _ _ _ _ _ _ Hv1) as HB1; pose proof (frame_vals_base _ _ _ _ _ _ _ _ _ _ _ Hv2) as HB2.
          pose proof (per_ctx_env_retag_left HRΓ _ _ HB1) as HB1r; pose proof (per_ctx_env_retag_left HRΓ _ _ HB2) as HB2r.
          rewrite env_extend_tagged_typed in EA1, EA2.
          destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMj)) as [RM HRM].
          pose proof (HAv _ _ _ HMj Hbj) as HAj.
          pose proof (ttrans _ _ HMj _ _ _ (tsym _ _ HMj _ _ Hbb') Htf2) as Htf2'.
          pose proof (ind_rel_idx_u0 _ _ _ _ _ _ _ _ _ _ HMj Hrr Htf1 Htf2') as H12.
          pose proof (ind_rel_idx_u0 _ _ _ _ _ _ _ _ _ _ HMj Hrs Htf2' (trefl_l _ _ HMj _ _ Htf1)) as H21.
          destruct (mctx_len _ _ HMj _ _ _ _ _ _ H12) as [LX1 LX2].
          pose proof (tagged_entries_fst _ Γ (ctx_retag Γ B1) _ (eq_sym LX1)) as Hv1'.
          pose proof (tagged_entries_fst _ Γ (ctx_retag Γ B2) _ (eq_sym LX2)) as Hv2'.
          destruct (mctx_readable _ _ HMj C1 C2 HC11 HC21 _ _ _ _ _ _ Hrr) as [Hrc1 _].
          pose proof (mctx_at_typed _ _ HMj _ _ HB1r HB2r RM HRM _ _ _ _ _ _ H12 _ _ Hv1' Hv2' Hrd1 Hrd2) as L1.
          pose proof (mctx_at_typed _ _ HMj _ _ HB2r HC11 RM HRM _ _ _ _ _ _ H21 _ _ Hv2' (tele_entries_values _ _ _) Hrd2 Hrc1) as L2.
          pose proof (mctx_at _ _ HMj C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hrr) as L3.
          destruct (rel_exp_of_typ_inversion_simple_at HRM HAj _ _ L1) as (A1' & A2' & EA1' & EA2' & HA12).
          assert (A1' = A1) as -> by (eapply functional_eval_exp; eassumption).
          assert (A2' = A2) as -> by (eapply functional_eval_exp; eassumption).
          assert (Ha1A2 : Dom a1 ≈ A2 ∈ per_univ iA) by (eapply per_univ_trans'; [ exact Ha1 | exact HA12 ]).
          destruct Ha1A2 as [R' HR']; destruct HA12 as [R12 HR12].
          assert (Q1 : R <~> R') by (eapply per_univ_elem_right_irrel; eassumption).
          assert (Q2 : R' <~> R12) by (eapply per_univ_elem_left_irrel; [ exact HR' | exact HR12 ]).
          pose proof (per_head_iff EA1 EA2 HR12) as Q3.
          assert (Ch : rel_chain RM (env_extend_typed (ctx_retag Γ B1) (tagged_entries Γ (List.rev (elim_mctx p D (ptyp_mem t) Mj Us))
                                                                       (ctx_retag Γ B1) (Xq1 ++ f1 :: nil))
                                     :: env_extend_typed (ctx_retag Γ B2) (tagged_entries Γ (List.rev (elim_mctx p D (ptyp_mem t) Mj Us))
                                                                            (ctx_retag Γ B2) (Xq2 ++ f2 :: nil))
                                     :: env_tele C1 (List.rev (elim_mctx p D (ptyp_mem t) Mj Us)) (bs ++ f1 :: nil)
                                     :: env_tele C2 (List.rev (elim_mctx p D (ptyp_mem t) Mj Us)) (bs' ++ f2 :: nil) :: nil)).
          { apply rel_chain_cons; [ exact L1 |]. apply rel_chain_cons; [ exact L2 |]. apply rel_chain_of_pair; exact L3. }
          pose proof (per_head_of_typ_resp HRM HAj _ _ _ _ Ch) as Q4.
          unfold Rel; rewrite (blocks_motives_nth _ _ _ Hbj), (mctx_tele_at _ _ HMj).
          etransitivity; [ exact Q1 | etransitivity; [ exact Q2 | etransitivity; [ exact Q3 | exact Q4 ] ] ].
        Qed.

        (** The domain of the [kd]-th step, at two sides related to the
            canonical arguments [ns], [nv1] and [ys1]: the canonical
            family. *)
        (** A domain of the shape at a side related to canonical arguments
            is a relevant type, as a shape's domain, a type of a universe,
            is. *)
        Lemma frame_dom_relevant : forall kd Bk, List.nth_error (ptyp_doms t) kd = Some Bk ->
            forall Ψ1 σ1 β1 x1 RΨ1, sem_frame Ψ1 σ1 β1 x1 -> EF Ψ1 ++ Γ ≈ Ψ1 ++ Γ ∈ per_ctx_env ↘ RΨ1 ->
            forall ns E1 B1 zts1 w1 X1 nv0 nv1 v1 ys0 yts1 a1,
            sem_frame_vals Ψ1 σ1 x1 RΨ1 E1 B1 zts1 w1 X1 nv1 v1 -> List.length yts1 = kd ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts1 ->
            tele_rel (nr k) T ns X1 -> tele_prefix_rel (ar k ns c) K nv0 nv1 ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns nv0 t) kd ys0 (List.map fst yts1) ->
            ⟦ Bk[sb_qn kd σ1] ⟧ env_extend_typed E1 yts1 ↘ a1 -> domain_kind a1 = ak_relevant.
        Proof.
          intros * HBk * Hf1 HRΨ1 * Hv1 Lys1 Hry1 HX1 Hnv01 Hys01 Ea1.
          assert (Hk : kd < L) by (unfold L; apply List.nth_error_Some; congruence).
          destruct (frame_side_refl ns X1 nv0 nv1 kd ys0 _ ltac:(lia) HX1 Hnv01 Hys01) as (HX1d & Hnv1d & Hys1d).
          destruct (frame_dom_link _ _ _ _ Hf1 _ HRΨ1 kd Bk HBk _ _ _ _ _ _ _ yts1 a1 _ _ _ Hv1 Lys1 Hry1 HX1d Hnv1d Hys1d Ea1)
            as (b1 & i1 & Eb1 & Hab1 & Hr1).
          exact Hr1.
        Qed.

        Lemma frame_dom_char : forall kd Bk, List.nth_error (ptyp_doms t) kd = Some Bk ->
            forall Ψ1 σ1 β1 x1 RΨ1 Ψ2 σ2 β2 x2 RΨ2, sem_frame Ψ1 σ1 β1 x1 -> EF Ψ1 ++ Γ ≈ Ψ1 ++ Γ ∈ per_ctx_env ↘ RΨ1 ->
            sem_frame Ψ2 σ2 β2 x2 -> EF Ψ2 ++ Γ ≈ Ψ2 ++ Γ ∈ per_ctx_env ↘ RΨ2 ->
            forall ns cv E1 B1 zts1 w1 X1 nv1 v1 E2 B2 zts2 w2 X2 nv2 v2 yts1 yts2 a1 a2 (i : nat) R,
            sem_frame_vals Ψ1 σ1 x1 RΨ1 E1 B1 zts1 w1 X1 nv1 v1 -> sem_frame_vals Ψ2 σ2 x2 RΨ2 E2 B2 zts2 w2 X2 nv2 v2 ->
            List.length yts1 = kd -> List.length yts2 = kd ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts1 ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts2 ->
            tele_rel (nr k) T ns X1 -> tele_rel (nr k) T ns X2 ->
            tele_prefix_rel (ar k ns c) K cv nv1 -> tele_prefix_rel (ar k ns c) K cv nv2 ->
            tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns cv t) kd (List.map fst yts1) (List.map fst yts2) ->
            ⟦ Bk[sb_qn kd σ1] ⟧ env_extend_typed E1 yts1 ↘ a1 -> ⟦ Bk[sb_qn kd σ2] ⟧ env_extend_typed E2 yts2 ↘ a2 ->
            DF a1 ≈ a2 ∈ per_univ_elem i ↘ R ->
            (R <~> dr k (ns ++ cv ++ List.map fst yts1) (Tk kd) Bk).
        Proof.
          intros * HBk * Hf1 HRΨ1 Hf2 HRΨ2 * Hv1 Hv2 Lys1 Lys2 Hry1 Hry2 HX1 HX2 Hcv1 Hcv2 Hys Ea1 Ea2 HR.
          assert (Hk : kd < L) by (unfold L; apply List.nth_error_Some; congruence).
          assert (Hns : tele_rel (nr k) T ns ns) by exact (trefl_l _ _ HMk _ _ HX1).
          assert (Hcvv : tele_prefix_rel (ar k ns c) K cv cv)
            by exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs Hns Hcon K _ _ frame_nonrec_le Hcv1).
          assert (Hys11 : tele_prefix_rel (shape_doms_rel (dr k) T (cargs_nonrec_tele gs1) ns cv t) kd (List.map fst yts1) (List.map fst yts1))
            by exact (doms_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs gs1 t gs2 cv Hns Hcon Heq Hcvv
                        kd _ _ ltac:(lia) Hys).
          destruct (frame_side_refl ns X1 cv nv1 kd _ _ ltac:(lia) HX1 Hcv1 Hys11) as (HX1d & Hnv1d & Hys1d).
          destruct (frame_side_refl ns X2 cv nv2 kd _ _ ltac:(lia) HX2 Hcv2 Hys) as (HX2d & Hnv2d & Hys2d).
          destruct (frame_dom_link _ _ _ _ Hf1 _ HRΨ1 kd Bk HBk _ _ _ _ _ _ _ yts1 a1 _ _ _ Hv1 Lys1 Hry1 HX1d Hnv1d Hys1d Ea1) as (b1 & i1 & Eb1 & Hab1 & _).
          destruct (frame_dom_link _ _ _ _ Hf2 _ HRΨ2 kd Bk HBk _ _ _ _ _ _ _ yts2 a2 _ _ _ Hv2 Lys2 Hry2 HX2d Hnv2d Hys2d Ea2) as (b2 & i2 & Eb2 & Hab2 & _).
          (** The canonical value. *)
          destruct (valid_ind_decl_dom _ HD k Mk c gs gs1 t gs2 kd Bk HMk Hcon Heq HBk) as (_ & i0 & HBv).
          rewrite <- frame_nonrec_ctx in HBv.
          pose proof (frame_doms_valid kd ltac:(lia)) as HKk.
          destruct (rel_ctx_wf_per_ctx_env HKk) as [RK HRK].
          pose proof (frame_canon_rel kd _ _ _ _ _ _ ltac:(lia) HX1 Hcv1 Hys11 RK HRK) as Q1.
          pose proof (frame_canon_rel kd _ _ _ _ _ _ ltac:(lia) HX2 Hcv2 Hys RK HRK) as Q2.
          destruct (rel_exp_of_typ_inversion_simple_at HRK HBv _ _ Q1) as (c0 & b1' & Ec0 & Eb1' & Hcb1).
          destruct (rel_exp_of_typ_inversion_simple_at HRK HBv _ _ Q2) as (c0' & b2' & Ec0' & Eb2' & Hcb2).
          assert (b1' = b1) as -> by (eapply functional_eval_exp; eassumption).
          assert (b2' = b2) as -> by (eapply functional_eval_exp; eassumption).
          assert (c0' = c0) as -> by (eapply functional_eval_exp; eassumption).
          assert (Ha1c : Dom a1 ≈ c0 ∈ per_univ i1) by (eapply per_univ_trans'; [ exact Hab1 | apply per_univ_sym'; exact Hcb1 ]).
          assert (Hca2 : Dom c0 ≈ a2 ∈ per_univ i0) by (eapply per_univ_trans'; [ exact Hcb2 | apply per_univ_sym'; exact Hab2 ]).
          assert (Hcc : Dom c0 ≈ c0 ∈ per_univ i0) by (eapply per_univ_trans'; [ exact Hcb1 | apply per_univ_sym'; exact Hcb1 ]).
          destruct Ha1c as [R1 HR1]; destruct Hcc as [Rc HRc].
          assert (ER1 : R <~> R1) by (eapply per_univ_elem_right_irrel; eassumption).
          assert (ER2 : R1 <~> Rc) by (eapply per_univ_elem_left_irrel; eassumption).
          pose proof (per_head_iff Ec0 Ec0 HRc) as ER3.
          unfold dr, canon_doms_rel.
          etransitivity; [ exact ER1 | etransitivity; [ exact ER2 | exact ER3 ] ].
        Qed.

      End Frame.

      (** *** From a Record View to Its Field

          The end of a frame's shape is a record view [Mj]: the projection
          of a recursive field [f] of the view, at the frame's values, is in
          the frame of the field, at the values of the projections. *)
      Lemma record_view_step_frame : forall k Mk c gs gs1 t gs2, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
          gs = gs1 ++ ca_rec t :: gs2 ->
          forall Ψ0 σ0 β0 x0, sem_frame Mk gs1 t Ψ0 σ0 β0 x0 ->
          forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
          forall qr Is fl c' gsr fs1 f tf fs2, im_head Mj = mh_record qr Is fl -> im_cons Mj = (c', gsr) :: nil ->
          List.combine fl gsr = fs1 ++ (f, ca_rec tf) :: fs2 ->
          let L := List.length (ptyp_doms t) in
          let xL := apps_vars_iter L x0 in
          sem_frame Mj (List.map snd fs1) tf (tele_sub (ptyp_tele t) σ0 ++ Ψ0)
            (ι (wk_pat (cargs_pat (List.map snd fs1)))
               ⨟ sb_of_list (ι (wk_shiftn (im_nn Mk + List.length (cargs_nonrec gs1) + L)) ⨟ sb_qn L σ0)
                   (projections_of (List.map fst fs1) xL))
            (sb_shift_iter L β0) (a_proj f xL).
      Proof.
        intros * HMk Hcon Heq * Hf * HMj * Hh Hcs Ec L xL.
        destruct (frame_rview_field HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj _ _ _ _ _ _ _ _ _ Hh Hcs Ec)
          as (Hg & Huc & Hx & Hform).
        destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [_ Hnn].
        assert (EΨ : (tele_sub (ptyp_tele t) σ0 ++ Ψ0) ++ Γ = tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ)
          by (rewrite <- List.app_assoc; reflexivity).
        constructor; rewrite ?EΨ.
        - exact (frame_end_ctx_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
        - exact Hg.
        - exact (frame_end_base_eq HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
        - exact Huc.
        - exact Hx.
        - cbn [exp_scoped]; exact (frame_end_arg_scoped HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj).
        - intros y; rewrite (Hform (y + _)).
          assert (Enp : im_nparams Mj = nil) by (unfold im_nn in Hnn; destruct (im_nparams Mj); [ reflexivity | discriminate ]).
          replace (List.length (cargs_nonrec_ctx (List.map snd fs1) ++ im_nparams Mj)) with (List.length (projections_of (fields_args fs1) xL)).
          + rewrite Nat.add_comm; apply sb_of_list_ge.
          + rewrite Enp, List.app_nil_r; unfold projections_of; rewrite List.length_map.
            clear; induction fs1 as [| [? []] fs1 IH]; cbn [List.map snd fields_args cargs_nonrec_ctx];
              rewrite ?List.length_app; cbn [List.length]; lia.
      Qed.

      Lemma record_view_step_vals : forall k Mk c gs gs1 t gs2, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
          gs = gs1 ++ ca_rec t :: gs2 ->
          forall Ψ0 σ0 β0 x0, sem_frame Mk gs1 t Ψ0 σ0 β0 x0 -> forall RΨ, EF Ψ0 ++ Γ ≈ Ψ0 ++ Γ ∈ per_ctx_env ↘ RΨ ->
          forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
          forall qr Is fl c' gsr fs1 f tf fs2, im_head Mj = mh_record qr Is fl -> im_cons Mj = (c', gsr) :: nil ->
          List.combine fl gsr = fs1 ++ (f, ca_rec tf) :: fs2 ->
          let L := List.length (ptyp_doms t) in
          let xL := apps_vars_iter L x0 in
          forall ns nv0 ys0 E B zts w X nv v yts f1 ws cv,
          sem_frame_vals Mk gs1 Ψ0 σ0 x0 RΨ E B zts w X nv v -> List.length yts = L ->
          List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts ->
          tele_rel (nr k) (List.rev (im_nparams Mk)) ns X -> tele_prefix_rel (ar k ns c) (List.length (cargs_nonrec gs1)) nv0 nv ->
          tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns nv0 t) L ys0 (List.map fst yts) ->
          ⟦ xL ⟧ env_extend_typed E yts ↘ f1 -> ⟦projs fl of f1 ⟧ gc_deps ⍮ gc_stack ↘ ws ->
          tele_prefix_rel (ar (ptyp_mem t) nil rview_con) (List.length (cargs_nonrec (List.map snd fs1)))
            cv (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws)) ->
          forall RΨ', EF (tele_sub (ptyp_tele t) σ0 ++ Ψ0) ++ Γ ≈ (tele_sub (ptyp_tele t) σ0 ++ Ψ0) ++ Γ ∈ per_ctx_env ↘ RΨ' ->
          exists w' nv', sem_frame_vals Mj (List.map snd fs1) (tele_sub (ptyp_tele t) σ0 ++ Ψ0)
            (ι (wk_pat (cargs_pat (List.map snd fs1)))
               ⨟ sb_of_list (ι (wk_shiftn (im_nn Mk + List.length (cargs_nonrec gs1) + L)) ⨟ sb_qn L σ0)
                   (projections_of (List.map fst fs1) xL))
            (a_proj f xL) RΨ' (env_extend_typed E yts) B (zts ++ yts) w' nil nv' (List.nth (List.length fs1) ws d_True) /\
            tele_prefix_rel (ar (ptyp_mem t) nil rview_con) (List.length (cargs_nonrec (List.map snd fs1))) cv nv'.
      Proof.
        intros * HMk Hcon Heq * Hf * HRΨ * HMj * Hh Hcs Ec L xL * Hv Lys Hry HX Hnv Hys Ex Ews Hnvf RΨ' HRΨ'.
        destruct (frame_rview_field HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj _ _ _ _ _ _ _ _ _ Hh Hcs Ec)
          as (Hg' & _ & _ & Hform).
        destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [_ Hnn].
        destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gs' & Hcs' & Hlen).
        rewrite Hcs in Hcs'; injection Hcs' as Ec' <-; subst c'.
        destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
        pose proof Hv as [HE HEB Lzs HB _ Hxv HwU Lw LX Lnv].
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        assert (EΨ : (tele_sub (ptyp_tele t) σ0 ++ Ψ0) ++ Γ = tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ)
          by (rewrite <- List.app_assoc; reflexivity).
        pose proof HRΨ' as HRSL; rewrite EΨ in HRSL.
        pose proof (frame_end_env k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf RΨ HRΨ Mj HMj ns nv0 ys0 E B zts w X nv v yts Hv Lys Hry
                      HX Hnv Hys _ HRSL) as HE'.
        assert (HEys : env_extend_typed E yts = env_extend_typed B (zts ++ yts)) by (rewrite HEB, env_extend_typed_app; reflexivity).
        (** The base. *)
        pose proof (frame_end_base_eval k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf RΨ HRΨ Mj HMj E B zts w X nv v yts Hv Lys)
          as Hβe.
        (** The uniform parameters past the domains. *)
        pose proof (per_ctx_env_retag_left HRΓ _ _ HB) as HBr.
        destruct (us_class (ctx_retag Γ B) HBr) as (u & Hu & Huu0).
        destruct (gsub_props gsub_U) as [HvU HlU].
        destruct (gsub_props (frame_gsub_end_base HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj)) as [HβL _].
        destruct (vals_sub_link Us HUl HvU HlU _ _ (sb_shift_iter L β0) (env_extend_typed E yts) (ctx_retag Γ B) u HRSL HβL HE' Hβe Hu)
          as (w' & Hw' & Hw'u).
        (** The fields' projections. *)
        rewrite Efl in Ews.
        pose proof (eval_projections_fields fs1 _ _ _ _ _ Ex Ews) as Hnv'.
        destruct (eval_projs_at (List.map fst fs1) f _ _ _ Ews) as (w0 & Hw0 & Hp0).
        rewrite List.length_map in Hw0.
        assert (Lws : List.length ws = List.length (List.map fst fs1 ++ f :: List.map fst fs2)) by exact (eval_projs_length _ _ _ Ews).
        rewrite List.length_app, !List.length_map in Lws; cbn [List.length] in Lws.
        (** The components' value: over [B], the uniform parameters' values
            and the non-recursive fields', a propositional field's the
            proof. *)
        assert (Enp : im_nparams Mj = nil) by (unfold im_nn in Hnn; destruct (im_nparams Mj); [ reflexivity | discriminate ]).
        pose proof (ind_con_single _ _ _ Hcs) as Hcon'.
        set (K' := List.length (cargs_nonrec (List.map snd fs1))) in *.
        assert (Lfa : List.length (fields_args fs1) = K')
          by (unfold K'; clear; induction fs1 as [| [? []] fs1 IH]; cbn [List.map snd fields_args cargs_nonrec List.length]; lia).
        assert (Lnvf : List.length (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws)) = K')
          by (apply length_nonrec_arg_vals; rewrite List.length_firstn, List.length_map; lia).
        set (ts := cargs_nonrec_tele (List.map snd fs1)).
        assert (Lts : List.length ts = K') by (unfold ts; rewrite length_cargs_nonrec_tele; reflexivity).
        assert (ETg : cargs_nonrec_ctx (List.map snd fs1) ++ im_params D Mj ++ Γ = (List.rev ts ++ ind_uparams D) ++ Γ)
          by (unfold ts, im_params; rewrite cargs_nonrec_ctx_rev_tele, Enp, List.app_nil_l, List.app_assoc; reflexivity).
        assert (Hnth : forall j, j < K' -> List.nth_error (cargs_nonrec gsr) j = List.nth_error (cargs_nonrec (List.map snd fs1)) j)
          by (intros j Hj; rewrite Egs, cargs_nonrec_app, List.nth_error_app1 by exact Hj; reflexivity).
        assert (Hpref : forall j, j < K' -> nonrec_args_prefix gsr j = List.rev (List.firstn j ts)).
        { intros j Hj; unfold nonrec_args_prefix, ts; rewrite Egs, cargs_nonrec_tele_app, List.firstn_app.
          rewrite length_cargs_nonrec_tele; replace (j - List.length (cargs_nonrec (List.map snd fs1))) with 0 by (unfold K' in Hj; lia).
          rewrite List.app_nil_r; reflexivity. }
        (** Each non-recursive field, of its kind, over the fields before it. *)
        assert (Hent : forall x Δ1 κ T Δ2, x < K' -> List.rev ts ++ ind_uparams D = Δ1 ++ ce_ass κ T :: Δ2 -> List.length Δ1 = x ->
                  exists r, List.nth_error (cargs_nonrec_kinds gsr) (K' - 1 - x) = Some r /\
                    exists i : nat, Δ2 ++ Γ ⊨ T : abs_kind_sort r Typeω@i).
        { intros x Δ1 κ T Δ2 Hx Heq0 HΔ1.
          destruct (rev_app_entry_split ts (ind_uparams D) Δ1 Δ2 (K' - 1 - x) (ce_ass κ T) ltac:(lia) Heq0 ltac:(lia)) as [He ->].
          unfold ts in He; destruct (cargs_nonrec_tele_nth _ _ _ _ He) as [HA0 _].
          rewrite <- (Hnth (K' - 1 - x) ltac:(lia)) in HA0.
          destruct (nonrec_kind_nth _ _ _ HA0) as [r Hr].
          exists r; split; [ exact Hr |].
          destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HMj Hcon' HA0 Hr) as (_ & i & HAi).
          exists i.
          assert (Hj' : K' - 1 - x <= List.length (cargs_nonrec gsr))
            by (rewrite Egs, cargs_nonrec_app, List.length_app; unfold K' in *; lia).
          pose proof (valid_ind_decl_nonrec_prefixes _ HD _ _ _ _ _ HMj Hcon' Hj') as HSj.
          assert (HSa : all_assumptions (nonrec_args_prefix gsr (K' - 1 - x) ++ im_params D Mj))
            by (apply List.Forall_app; split;
                [ apply all_assumptions_nonrec_args_prefix
                | exact (member_params_ass D Hc _ _ HMj) ]).
          pose proof (closed_app_valid _ _ _ _ _ HSa HSj HΓ HAi) as HAΓ.
          rewrite (Hpref (K' - 1 - x) ltac:(lia)) in HAΓ; unfold im_params in HAΓ; rewrite Enp in HAΓ; exact HAΓ. }
        assert (Hrf : forall x, x < K' -> exists r, List.nth_error (cargs_nonrec_kinds gsr) (K' - 1 - x) = Some r).
        { intros x Hx.
          destruct (nth_error_lt_some' (cargs_nonrec (List.map snd fs1)) (K' - 1 - x) ltac:(unfold K' in *; lia)) as [A0 HA0].
          rewrite <- (Hnth (K' - 1 - x) ltac:(lia)) in HA0; exact (nonrec_kind_nth _ _ _ HA0). }
        assert (HaT : all_assumptions (List.rev ts ++ ind_uparams D))
          by (apply List.Forall_app; split; [ unfold ts; apply List.Forall_rev, all_assumptions_cargs_nonrec_tele | exact Ua ]).
        (** The value of the substitution, at the semantic substitution. *)
        destruct (rel_sub_under_ctx_simple (gsub_valid Hg')) as (R1 & HR1 & RT & HRT & Hs).
        assert (E1 : RΨ' <~> R1) by (eapply per_ctx_env_right_irrel; [ exact HRSL | exact HR1 ]).
        destruct (Hs _ _ (proj1 (E1 _ _) HE')) as (e1 & e1' & Ee1 & _ & He1).
        assert (HPT : PER RT) by (eapply per_env_PER; exact HRT).
        assert (He11 : RT e1 e1) by (etransitivity; [ exact He1 | symmetry; exact He1 ]).
        rewrite ETg in HRT, Ee1.
        pose proof (eval_sub_sb_eq Hform Ee1) as Ee1f; rewrite <- List.app_assoc in Ee1f.
        set (rf := fun x => match List.nth_error (cargs_nonrec_kinds gsr) (K' - 1 - x) with Some r => r | None => ak_relevant end).
        assert (Hnprop : forall x, x < List.length ts -> evaluated_kind (rf x) ->
                           ~ entry_propositional gc_deps gc_stack (List.rev ts ++ ind_uparams D ++ Γ) e1 x).
        { intros x Hx Hr; rewrite List.app_assoc.
          refine (evaluated_entry_not_propositional (List.rev ts ++ ind_uparams D) Γ RT x HaT
                    ltac:(rewrite List.length_app, List.length_rev; lia) _ HRT e1 e1 He11).
          intros Δ1 κ T Δ2 Heq0 HΔ1; destruct (Hent x Δ1 κ T Δ2 ltac:(lia) Heq0 HΔ1) as (r & Hr' & i & HT).
          unfold rf in Hr; rewrite Hr' in Hr; exists i; destruct Hr; [ left | right ]; exact HT. }
        assert (Hprop : forall x, x < List.length ts -> rf x = ak_propositional ->
                          entry_propositional gc_deps gc_stack (List.rev ts ++ ind_uparams D ++ Γ) e1 x).
        { intros x Hx Hr; rewrite List.app_assoc.
          refine (prop_entry_propositional (List.rev ts ++ ind_uparams D) Γ RT x HaT
                    ltac:(rewrite List.length_app, List.length_rev; lia) _ HRT e1 e1 He11).
          intros Δ1 κ T Δ2 Heq0 HΔ1; destruct (Hent x Δ1 κ T Δ2 ltac:(lia) Heq0 HΔ1) as (r & Hr' & i & HT).
          unfold rf in Hr; rewrite Hr' in Hr; subst r; exact HT. }
        destruct (eval_sb_of_list_sorted_split (projections_of (fields_args fs1) xL) ts
                    (sb_of_list (sb_shift_iter L β0) (List.map (fun U => U[sb_shift_iter L β0]) Us)) (ind_uparams D ++ Γ)
                    (env_extend_typed E yts) e1 rf ltac:(unfold projections_of; rewrite List.length_map; lia) Ee1f Hnprop Hprop)
          as (ms & Lms & Hms & Hagr).
        unfold projections_of in Lms; rewrite List.length_map, Lfa in Lms.
        (** The stored values of the fields: the projections at a relevant
            field, a kept proof at a propositional one, which read back. *)
        assert (Hnil : tele_rel (nr (ptyp_mem t)) (List.rev (im_nparams Mj)) nil nil) by (rewrite Enp; split; [ reflexivity | exact I ]).
        pose proof (frame_end_arg_scoped HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj) as HxLs.
        assert (Hmsrel : tele_prefix_rel (ar (ptyp_mem t) nil rview_con) K' cv ms).
        { pose proof Hnvf as H0; rewrite tele_prefix_rel_iff in H0; destruct H0 as (Lcv & _ & Hall).
          rewrite tele_prefix_rel_iff; split; [ exact Lcv | split; [ exact Lms |] ].
          intros j y y' Hy Hy'.
          assert (Hj : j < K') by (rewrite <- Lms; apply List.nth_error_Some; congruence).
          destruct (nth_error_lt_some' (projections_of (fields_args fs1) xL) j ltac:(unfold projections_of; rewrite List.length_map; lia))
            as [M HM].
          destruct (Hms j M y' HM Hy') as [HmR HmP].
          unfold projections_of in HmR, HmP; rewrite List.length_map, Lfa in HmR, HmP.
          destruct (nth_error_lt_some' (cargs_nonrec (List.map snd fs1)) j ltac:(unfold K' in *; lia)) as [A0 HA0].
          rewrite <- (Hnth j Hj) in HA0.
          destruct (nonrec_kind_nth _ _ _ HA0) as [r Hr].
          assert (Erf : rf (K' - 1 - j) = r) by (unfold rf; replace (K' - 1 - (K' - 1 - j)) with j by lia; rewrite Hr; reflexivity).
          destruct (evaluated_kind_or_propositional r) as [Hre | ->].
          - destruct (eval_exps_nth _ _ _ _ _ Hnv' HM) as (y0 & Hy0 & Ey0).
            pose proof (functional_eval_exp _ _ _ _ (HmR ltac:(rewrite Erf; exact Hre)) Ey0) as ->.
            exact (Hall _ _ _ Hy Hy0).
          - pose proof (HmP Erf) as ->.
            destruct (nth_error_lt_some' (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws)) j ltac:(lia))
              as [y1 Hy1].
            assert (HMs : exp_free_bound M <= List.length (tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ)).
            { apply exp_scoped_free_bound.
              unfold projections_of in HM; apply List.nth_error_In, List.in_map_iff in HM as (g & <- & _); cbn [exp_scoped]; exact HxLs. }
            pose proof (proj1 (per_ctx_env_kept_proof_readable _ _ _ M HRSL HMs _ _ HE')) as Hrm.
            pose proof (canon_arg_proof (ptyp_mem t) Mj rview_con gsr nil j A0 _ _ HMj Hcon' Hnil HA0 Hr
                          (tele_prefix_rel_of_pre _ _ _ _ j Hnvf ltac:(lia)) y y1 (Hall _ _ _ Hy Hy1)) as [Hry0 _].
            exact (canon_arg_proof_intro (ptyp_mem t) Mj rview_con gsr nil j A0 _ _ HMj Hcon' Hnil HA0 Hr
                     (tele_prefix_rel_of_pre _ _ _ _ j Hnvf ltac:(lia)) y _ Hry0 Hrm). }
        (** Past the fields, the value of the uniform parameters' instance. *)
        assert (Lpj : List.length ts = List.length (projections_of (fields_args fs1) xL))
          by (unfold projections_of; rewrite List.length_map; lia).
        pose proof (eval_sb_of_list_tail _ _ _ _ _ _ Lpj Ee1f) as Htail.
        destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ _].
        destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
        assert (HgV : gsub (tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ)
                        (sb_of_list (sb_shift_iter L β0) (List.map (fun U => U[sb_shift_iter L β0]) Us)) (ind_uparams D ++ Γ))
          by (eapply gsub_eq; [ exact (frame_rview_uparams_sub HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj)
                              | exact (frame_rview_uparams_form HMall k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj) ]).
        destruct (sb_of_list_values_of_sub (ind_uparams D) Γ _ (sb_shift_iter L β0) (List.map (fun U => U[sb_shift_iter L β0]) Us)
                    RΨ' RUΓ (env_extend_typed E yts) (ctx_retag Γ B) Ua HRSL HRUΓ
                    (closed_evaluated_over _ _ Ua Usem HΓ (valid_ind_decl_uparams_evaluated _ HD))
                    (gsub_valid HgV) ltac:(rewrite List.length_map; exact HUl) HE' Hβe) as (w'' & Ew'' & Hin & _).
        pose proof (functional_eval_exps' _ _ _ _ Ew'' Hw') as ->.
        pose proof (functional_eval_sub _ _ _ _ _ Htail Hin) as Hag.
        set (Eu := env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ B) w').
        set (Eσ := env_extend_tagged (ind_uparams D ++ Γ) ts Eu ms).
        assert (HagE : env_agree_upto (List.length ((List.rev ts ++ ind_uparams D) ++ Γ)) e1 Eσ).
        { rewrite <- List.app_assoc, List.length_app, List.length_rev.
          intros x Hx; rewrite Hagr.
          exact (env_extend_tagged_agree ts (ind_uparams D ++ Γ) _ _ ms ltac:(lia) Hag x Hx). }
        assert (Hsig : ⟦ ι (wk_pat (cargs_pat (List.map snd fs1)))
                           ⨟ sb_of_list (ι (wk_shiftn (im_nn Mk + List.length (cargs_nonrec gs1) + L)) ⨟ sb_qn L σ0)
                               (projections_of (List.map fst fs1) xL)
                         : cargs_nonrec_ctx (List.map snd fs1) ++ im_params D Mj ++ Γ ⟧s env_extend_typed E yts ↘ Eσ).
        { rewrite ETg; exact (eval_sub_resp_agree _ _ _ _ _ Ee1 HagE). }
        (** The value as a typed extension, its entries reading back. *)
        set (wts := tagged_entries Γ (List.rev (ind_uparams D)) (ctx_retag Γ B) w' ++ tagged_entries (ind_uparams D ++ Γ) ts Eu ms).
        assert (EEσ : Eσ = env_extend_typed (ctx_retag Γ B) wts).
        { unfold Eσ, wts; rewrite env_extend_tagged_typed, env_extend_typed_app; unfold Eu; rewrite env_extend_tagged_typed; reflexivity. }
        assert (Lw' : List.length w' = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw'), List.length_map; exact HUl).
        assert (Hwv : List.map fst wts = w' ++ nil ++ ms).
        { unfold wts; rewrite List.map_app, !tagged_entries_fst; [ reflexivity | lia | rewrite List.length_rev; exact (eq_sym Lw') ]. }
        assert (HEσ : RT Eσ Eσ) by exact (per_ctx_env_resp_agree HRT _ _ _ _ HagE HagE He11).
        assert (Hstr : cargs_nonrec_ctx (List.map snd fs1) = nonrec_args_prefix gsr K') by (rewrite Egs; apply cargs_nonrec_ctx_nonrec_args_prefix).
        assert (HTv : ⊨ (List.rev ts ++ ind_uparams D) ++ Γ).
        { rewrite <- ETg, Hstr.
          assert (HKr : K' <= List.length (cargs_nonrec gsr)) by (rewrite Egs, cargs_nonrec_app, List.length_app; unfold K'; lia).
          assert (HSa : all_assumptions (nonrec_args_prefix gsr K' ++ im_params D Mj))
            by (apply List.Forall_app; split;
                [ apply all_assumptions_nonrec_args_prefix
                | exact (member_params_ass D Hc _ _ HMj) ]).
          destruct (closed_app_sem _ _ HSa (valid_ind_decl_nonrec_prefixes _ HD _ _ _ _ _ HMj Hcon' HKr) HΓ) as [H _].
          rewrite <- !List.app_assoc in H; exact H. }
        assert (HTr : ⊨ List.rev (List.rev (List.rev ts ++ ind_uparams D)) ++ Γ) by (rewrite List.rev_involutive; exact HTv).
        assert (HRTr : EF List.rev (List.rev (List.rev ts ++ ind_uparams D)) ++ Γ ≈ List.rev (List.rev (List.rev ts ++ ind_uparams D)) ++ Γ
                         ∈ per_ctx_env ↘ RT) by (rewrite List.rev_involutive; exact HRT).
        assert (Lwts : List.length wts = List.length (List.rev (List.rev ts ++ ind_uparams D))).
        { rewrite <- (List.length_map fst), Hwv, List.length_rev, !List.length_app, List.length_rev, Lms, Lw', Lts; cbn [List.length].
          unfold ind_nu; lia. }
        rewrite EEσ in HEσ.
        destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HTr (List.Forall_rev HaT) HRTr _ _ _ _ Lwts Lwts HEσ) as [Hrw _].
        exists w', ms; split; [| exact Hmsrel ].
        constructor.
        - exact HE'.
        - exact HEys.
        - rewrite !List.length_app, length_tele_sub, Lzs, Lys; unfold ptyp_tele; rewrite doms_ctx_length; lia.
        - exact HB.
        - exists (ctx_retag Γ B), wts; rewrite <- EEσ; split; [ exact Hsig | split; [ exact Hwv | exact Hrw ] ].
        - rewrite (List.nth_error_nth _ _ _ Hw0); econstructor; [ exact Ex | exact Hp0 ].
        - assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
          etransitivity; [ exact Hw'u | exact Huu0 ].
        - exact Lw'.
        - exact (eq_sym Hnn).
        - exact Lms.
      Qed.

      (** *** Along a Leaf Path

          Two arguments of the shape [t] of a frame, past [kd] of its
          domains at related values, with related recursive results: the
          result at the leaf path [idx] is related at the type of the
          recursive result along that path.  By strong induction on the
          member [n] bounding the record view the shape ends in (its fields'
          shapes end in record views before it, [rview_order_ok]), and on
          the domains left. *)
      Lemma leaf_walk_sem : forall n k Mk c gs gs1 t gs2, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
          gs = gs1 ++ ca_rec t :: gs2 ->
          forall Mj, ind_member D (ptyp_mem t) = Some Mj -> (im_is_rview Mj = true -> ptyp_mem t < n) ->
          forall Ψ0 σ0 β0 x0, sem_frame Mk gs1 t Ψ0 σ0 β0 x0 -> leaf_term x0 -> forall RΨ, EF Ψ0 ++ Γ ≈ Ψ0 ++ Γ ∈ per_ctx_env ↘ RΨ ->
          forall ns cv E1 B1 zts1 w1 X1 nv1 v1 E2 B2 zts2 w2 X2 nv2 v2,
          sem_frame_vals Mk gs1 Ψ0 σ0 x0 RΨ E1 B1 zts1 w1 X1 nv1 v1 -> sem_frame_vals Mk gs1 Ψ0 σ0 x0 RΨ E2 B2 zts2 w2 X2 nv2 v2 ->
          leaf_apps_relevant x0 E1 -> leaf_apps_relevant x0 E2 ->
          tele_rel (nr k) (List.rev (im_nparams Mk)) ns X1 -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns X2 ->
          tele_prefix_rel (ar k ns c) (List.length (cargs_nonrec gs1)) cv nv1 ->
          tele_prefix_rel (ar k ns c) (List.length (cargs_nonrec gs1)) cv nv2 ->
          forall pre2 kd yts1 yts2 f1 f2 rs1 rs2, kd <= List.length (ptyp_doms t) -> List.length yts1 = kd -> List.length yts2 = kd ->
          List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts1 ->
          List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) yts2 ->
          tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns cv t) kd
            (List.map fst yts1) (List.map fst yts2) ->
          $*| v1 & List.map fst yts1 | gc_deps ⍮ gc_stack ↘ f1 -> $*| v2 & List.map fst yts2 | gc_deps ⍮ gc_stack ↘ f2 ->
          apps_relevant v1 (List.map fst yts1) -> apps_relevant v2 (List.map fst yts2) ->
          rec_arg_rel p D (admissible_index_at D u0 nr) nr ar dr k u0 u0 (ns ++ cv ++ List.map fst yts1) (pre2 ++ List.map fst yts2)
            (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kd (shape_doms_tele t)) (ptyp_skip kd t) f1 f2 ->
          rec_result_rel D dr Rel k u0 u0 (ns ++ cv ++ List.map fst yts1) (pre2 ++ List.map fst yts2)
            (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kd (shape_doms_tele t)) (ptyp_skip kd t) f1 f2 rs1 rs2 ->
          List.length rs1 = List.length (shape_leaves (rview_leaves D) 0 (ptyp_skip kd t)) ->
          List.length rs2 = List.length (shape_leaves (rview_leaves D) 0 (ptyp_skip kd t)) ->
          forall idx l, List.nth_error (shape_leaves (rview_leaves D) (im_nn Mk + List.length (cargs_nonrec gs1) + kd) (ptyp_skip kd t)) idx
                          = Some l ->
          forall a1 a2 (i : nat) R,
          ⟦ leaf_ihty ak_relevant (blocks_motives Bks) (sb_shift_iter kd β0) (sb_qn kd σ0) (apps_vars_iter kd x0) l ⟧
            env_extend_typed E1 yts1 ↘ a1 ->
          ⟦ leaf_ihty ak_relevant (blocks_motives Bks) (sb_shift_iter kd β0) (sb_qn kd σ0) (apps_vars_iter kd x0) l ⟧
            env_extend_typed E2 yts2 ↘ a2 ->
          DF a1 ≈ a2 ∈ per_univ_elem i ↘ R -> R (List.nth idx rs1 d_True) (List.nth idx rs2 d_True).
      Proof.
        induction n as [n IHn] using Wf_nat.lt_wf_ind.
        intros k Mk c gs gs1 t gs2 HMk Hcon Heq Mj HMj Hrk Ψ0 σ0 β0 x0 Hf Hlt RΨ HRΨ ns cv E1 B1 zts1 w1 X1 nv1 v1 E2 B2 zts2 w2 X2 nv2 v2
          Hv1 Hv2 Hxr1 Hxr2 HX1 HX2 Hcv1 Hcv2 pre2 kd.
        set (L := List.length (ptyp_doms t)).
        set (K := List.length (cargs_nonrec gs1)).
        remember (L - kd) as m eqn:Hm; revert kd Hm.
        induction m as [| m IHm];
          intros kd Hm yts1 yts2 f1 f2 rs1 rs2 Hk Lys1 Lys2 Hry1 Hry2 Hys Ef1 Ef2 Hrel1 Hrel2 Hsh Hih Lr1 Lr2 idx l Hleaf a1 a2 i R
                 Ea1 Ea2 HR.
        - (** At the end of the shape. *)
          assert (kd = L) as -> by lia.
          pose proof (ptyp_skip_end t) as HsL; fold L in HsL; rewrite HsL in Hsh, Hih, Hleaf, Lr1, Lr2.
          cbn [shape_leaves] in Hleaf.
          destruct (im_is_rview Mj) eqn:Hrv.
          + (** A record view: on to the frame of the field the path
                projects. *)
            specialize (Hrk eq_refl).
            destruct (im_head Mj) as [pm | qc k' Is0 vm | qr Is fl] eqn:Hh; unfold im_is_rview in Hrv; rewrite Hh in Hrv;
              try discriminate.
            destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gsr & Hcs & Hlen).
            pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_record_struct _ _ _ Hdt))) as Hco.
            rewrite (Hco _ _ _ _ _ _ _ HMj Hh Hcs) in Hleaf.
            apply nth_error_map_inv in Hleaf as (l0 & Hl0 & ->).
            destruct (fields_leaves_nth _ _ _ _ _ Hl0) as (fs1 & f & tf & fs2 & idx1 & l1 & Ec & -> & -> & Hl1).
            cbn [List.app] in Hl1.
            rewrite !leaf_ihty_wk in Ea1, Ea2; cbn [leaf_ihty List.app] in Ea1, Ea2.
            destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
            pose proof (ind_con_single _ _ _ Hcs) as Hcon'.
            destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [_ Hnn].
            assert (Enp : im_nparams Mj = nil) by (unfold im_nn in Hnn; destruct (im_nparams Mj); [ reflexivity | discriminate ]).
            destruct (length_rec_ps D HD _ _ HMj _ _ _ _ _ Hcon' Egs) as (Mt & HMt & _).
            (** The semantic side: the projections, related as the
                pseudo-constructor's arguments, and the field's results. *)
            destruct (rec_result_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hih) as (ws & ws' & Ews & Ews' & Hrs).
            destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (b1 & b2 & _ & _ & _ & _ & Hir).
            destruct (ind_rel_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hir) as (vs & vs' & Evs & Evs' & Har & Hca).
            pose proof (functional_eval_projs _ _ _ _ Evs Ews) as ->; pose proof (functional_eval_projs _ _ _ _ Evs' Ews') as ->.
            destruct (rec_results_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrs (List.map snd fs1) tf (List.map snd fs2) Egs)
              as (vf & vf' & rsf & rsf' & ih1 & ih1' & ih2 & ih2' & Hvf & Hvf' & -> & -> & Lih1 & Lih1' & Lrf & Lrf' & Hrf).
            destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca (List.map snd fs1) tf (List.map snd fs2) Egs)
              as (x & x' & Hx & Hx' & Haf).
            rewrite Hvf in Hx; injection Hx as <-; rewrite Hvf' in Hx'; injection Hx' as <-.
            destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as [Lvs Lvs'].
            rewrite List.length_map in Hvf, Hvf', Hrf, Haf.
            (** The field's frame and the values in it. *)
            pose proof (record_view_step_frame k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf Mj HMj _ _ _ _ _ _ _ _ _
                          Hh Hcs Ec) as Hf'; cbv zeta in Hf'.
            pose proof Hv1 as [_ _ _ _ _ Hxv1 _ _ _ _]; pose proof Hv2 as [_ _ _ _ _ Hxv2 _ _ _ _].
            pose proof (frame_arg_end_eval x0 L E1 yts1 v1 f1 Hlt Lys1 Hxr1 Hxv1 Ef1 Hrel1) as Ex1.
            pose proof (frame_arg_end_eval x0 L E2 yts2 v2 f2 Hlt Lys2 Hxr2 Hxv2 Ef2 Hrel2) as Ex2.
            pose proof (leaf_apps_relevant_apps_vars yts1 x0 E1 v1 f1 Hlt Hxr1 Hxv1 Ef1 Hrel1) as HxL1; rewrite Lys1 in HxL1.
            pose proof (leaf_apps_relevant_apps_vars yts2 x0 E2 v2 f2 Hlt Hxr2 Hxv2 Ef2 Hrel2) as HxL2; rewrite Lys2 in HxL2.
            destruct (rel_ctx_wf_per_ctx_env (sem_frame_ctx _ _ _ _ _ _ _ Hf')) as [RΨ' HRΨ'].
            assert (Hns : tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns) by exact (trefl_l _ _ HMk _ _ HX1).
            assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
            assert (Hcvv : tele_prefix_rel (ar k ns c) K cv cv)
              by exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs Hns Hcon _ _ _ HK Hcv1).
            assert (Hys11 : tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns cv t) L
                              (List.map fst yts1) (List.map fst yts1))
              by exact (doms_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs gs1 t gs2 cv Hns Hcon Heq Hcvv
                          L _ _ (le_n _) Hys).
            (** The non-recursive fields before the field. *)
            assert (Hnvf : tele_prefix_rel (ar (ptyp_mem t) nil rview_con) (List.length (cargs_nonrec (List.map snd fs1)))
                             (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws))
                             (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws'))).
            { replace (List.length fs1) with (List.length (List.map snd fs1)) by apply List.length_map.
              rewrite Egs in Har, Lvs, Lvs'.
              rewrite <- !(nonrec_arg_vals_firstn _ (ca_rec tf :: List.map snd fs2)) by assumption.
              apply tele_prefix_rel_of_full with (T := cargs_nonrec (List.map snd fs1 ++ ca_rec tf :: List.map snd fs2)); [ exact Har |].
              rewrite cargs_nonrec_app, List.length_app; lia. }
            assert (Hnil : tele_rel (nr (ptyp_mem t)) (List.rev (im_nparams Mj)) nil nil) by (rewrite Enp; split; [ reflexivity | exact I ]).
            assert (Hnvf1 : tele_prefix_rel (ar (ptyp_mem t) nil rview_con) (List.length (cargs_nonrec (List.map snd fs1)))
                              (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws))
                              (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws)))
              by exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (ptyp_mem t) Mj HMj nil rview_con gsr Hnil Hcon'
                          (List.length (cargs_nonrec (List.map snd fs1))) _ _
                          ltac:(rewrite Egs, cargs_nonrec_app, List.length_app; lia) Hnvf).
            (** The fields' frames: their stored values, related to the
                projections. *)
            destruct (record_view_step_vals k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf RΨ HRΨ Mj HMj _ _ _ _ _ _ _ _ _ Hh Hcs Ec
                        ns cv (List.map fst yts1) E1 B1 zts1 w1 X1 nv1 v1 yts1 f1 ws _ Hv1 Lys1 Hry1 HX1 Hcv1 Hys11 Ex1 Ews Hnvf1
                        RΨ' HRΨ') as (w1' & nv1' & Hv1' & Hc1').
            destruct (record_view_step_vals k Mk c gs gs1 t gs2 HMk Hcon Heq Ψ0 σ0 β0 x0 Hf RΨ HRΨ Mj HMj _ _ _ _ _ _ _ _ _ Hh Hcs Ec
                        ns cv (List.map fst yts1) E2 B2 zts2 w2 X2 nv2 v2 yts2 f2 ws' _ Hv2 Lys2 Hry2 HX2 Hcv2 Hys Ex2 Ews' Hnvf
                        RΨ' HRΨ') as (w2' & nv2' & Hv2' & Hc2').
            rewrite (List.nth_error_nth _ _ d_True Hvf) in Hv1'; rewrite (List.nth_error_nth _ _ d_True Hvf') in Hv2'.
            (** The rank drops: the field's shape ends before the view. *)
            assert (Hrk' : im_is_rview Mt = true -> ptyp_mem tf < ptyp_mem t)
              by (intros HrT; exact (rview_struct_order _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Egs HMt HrT)).
            assert (Hl1' : List.nth_error (shape_leaves (rview_leaves D) (im_nn Mj + List.length (cargs_nonrec (List.map snd fs1)) + 0)
                                             (ptyp_skip 0 tf)) idx1 = Some l1).
            { replace (im_nn Mj + List.length (cargs_nonrec (List.map snd fs1)) + 0) with (List.length (fields_args fs1)); [ exact Hl1 |].
              rewrite Hnn; clear; induction fs1 as [| [? []] fs1 IH]; cbn [List.map snd fields_args cargs_nonrec]; cbn [List.length]; lia. }
            (** The type along the path, in the field's frame. *)
            assert (Eσ : sb_eq (sb_of_list (ι (wk_shiftn (im_nn Mk + K + L)) ⨟ sb_qn L σ0) (projections_of (fields_args fs1) (apps_vars_iter L x0)))
                           (ι (wk_pat (cargs_pat (List.map snd fs1)))
                              ⨟ sb_of_list (ι (wk_shiftn (im_nn Mk + K + L)) ⨟ sb_qn L σ0)
                                  (projections_of (List.map fst fs1) (apps_vars_iter L x0)))).
            { pose proof (wk_pat_projections fs1 nil (ι (wk_shiftn (im_nn Mk + K + L)) ⨟ sb_qn L σ0) (apps_vars_iter L x0)) as E.
              rewrite List.app_nil_r in E; symmetry; etransitivity; [ exact E |]; apply sb_of_list_cong; intros z; reflexivity. }
            rewrite (leaf_ihty_sb_eq ak_relevant l1 _ _ (sb_shift_iter L β0) _ _ _ (reflexivity _) Eσ) in Ea1, Ea2.
            pose proof (IHn (ptyp_mem t) Hrk (ptyp_mem t) Mj rview_con gsr (List.map snd fs1) tf (List.map snd fs2) HMj Hcon' Egs Mt HMt Hrk'
                          _ _ _ _ Hf' (leaf_term_proj _ _ (leaf_term_apps_vars _ _ Hlt)) RΨ' HRΨ' nil _ _ _ _ _ nil _ _ _ _ _ _ nil _ _
                          Hv1' Hv2' HxL1 HxL2 Hnil Hnil Hc1' Hc2' _ 0 nil nil _ _ rsf rsf'
                          (Nat.le_0_l _) eq_refl eq_refl (List.Forall_nil _) (List.Forall_nil _)
                          ltac:(apply tele_prefix_rel_nil) ltac:(apply eval_apps_nil) ltac:(apply eval_apps_nil)
                          ltac:(intros ? ? Hj; cbn in Hj; lia) ltac:(intros ? ? Hj; cbn in Hj; lia)
                          ltac:(rewrite Enp; cbn [List.rev List.firstn List.map List.app]; rewrite !List.app_nil_r; exact Haf)
                          ltac:(rewrite Enp; cbn [List.rev List.firstn List.map List.app]; rewrite !List.app_nil_r; exact Hrf)
                          Lrf Lrf' idx1 l1 Hl1' a1 a2 i R ltac:(exact Ea1) ltac:(exact Ea2) HR) as Hres.
            assert (Hi1 : idx1 < List.length rsf)
              by (rewrite Lrf, (length_shape_leaves _ _ 0 (List.length (fields_args fs1))); apply List.nth_error_Some; congruence).
            rewrite (List.app_nth2 ih1), (List.app_nth2 ih1') by lia; rewrite Lih1, Lih1', Nat.add_comm, Nat.add_sub.
            rewrite (List.app_nth1 rsf), (List.app_nth1 rsf') by lia; exact Hres.
          + rewrite (rview_leaves_not_rview _ _ _ HMj Hrv) in Hleaf.
            destruct idx as [| idx]; [| destruct idx; discriminate ]; cbn in Hleaf; injection Hleaf as <-.
            cbn [leaf_ihty] in Ea1, Ea2.
            destruct (HBks _ _ HMj Hrv) as [bj Hbj].
            rewrite (blocks_motives_nth _ _ _ Hbj) in Ea1, Ea2.
            destruct (rec_result_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hrv Hih) as (bs & bs' & ih & ih' & -> & -> & Ebs & Ebs' & Hrr).
            destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (b1 & b2 & Eb1 & Eb2 & _ & _ & Hir).
            pose proof (functional_eval_exps' _ _ _ _ Eb1 Ebs) as ->.
            pose proof (functional_eval_exps' _ _ _ _ Eb2 Ebs') as ->.
            rewrite List.firstn_all2 in Ebs by (unfold shape_doms_tele, L; rewrite List.length_map; lia).
            exact (proj2 (frame_leaf_char k Mk c gs gs1 t gs2 HMk Hcon Heq Mj bj HMj Hrv Hbj Ψ0 σ0 β0 x0 RΨ Ψ0 σ0 β0 x0 RΨ Hf HRΨ Hf HRΨ
                            ns cv E1 B1 zts1 w1 X1 nv1 v1 E2 B2 zts2 w2 X2 nv2 v2 yts1 yts2 f1 f2 bs bs' a1 a2 i R Hlt Hlt Hxr1 Hxr2
                            Hv1 Hv2 Lys1 Lys2
                            Hry1 Hry2 HX1 HX2 Hcv1 Hcv2 Hys Ef1 Ef2 Hrel1 Hrel2 Ebs Hir Ea1 Ea2 HR _ _) Hrr).
        - (** At a domain. *)
          assert (Hk' : kd < L) by lia.
          destruct (ptyp_skip_lt kd t Hk') as (Bk & HBk & Hs).
          rewrite Hs in Hsh, Hih, Hleaf, Lr1, Lr2.
          cbn [shape_leaves] in Hleaf, Lr1, Lr2.
          apply nth_error_map_inv in Hleaf as (l' & Hl' & ->).
          rewrite List.length_map, (length_shape_leaves _ _ 1 0) in Lr1, Lr2.
          cbn [leaf_ihty] in Ea1, Ea2.
          inversion Ea1; subst a1; inversion Ea2; subst a2.
          match goal with H : ⟦ Bk[sb_qn kd σ0] ⟧ env_extend_typed E1 yts1 ↘ _ |- _ => rename H into Eb1 end.
          match goal with H : ⟦ Bk[sb_qn kd σ0] ⟧ env_extend_typed E2 yts2 ↘ _ |- _ => rename H into Eb2 end.
          basic_invert_per_univ_elem HR.
          match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
          match goal with H : _ <~> pi_elements _ _ _ _ |- _ => rename H into HRE end.
          pose proof (frame_dom_char k Mk c gs gs1 t gs2 HMk Hcon Heq kd Bk HBk Ψ0 σ0 β0 x0 RΨ Ψ0 σ0 β0 x0 RΨ Hf HRΨ Hf HRΨ
                        ns cv E1 B1 zts1 w1 X1 nv1 v1 E2 B2 zts2 w2 X2 nv2 v2 yts1 yts2 _ _ i in_rel Hv1 Hv2 Lys1 Lys2 Hry1 Hry2
                        HX1 HX2 Hcv1 Hcv2 Hys Eb1 Eb2 equiv_a_a') as Edr.
          assert (Hi1 : idx < List.length rs1)
            by (rewrite Lr1, (length_shape_leaves _ _ 0 (S (im_nn Mk + K + kd))); apply List.nth_error_Some; congruence).
          assert (Hi2 : idx < List.length rs2) by lia.
          destruct (nth_error_lt_some' rs1 idx Hi1) as [r1 Hr1]; destruct (nth_error_lt_some' rs2 idx Hi2) as [r2 Hr2].
          rewrite (List.nth_error_nth _ _ _ Hr1), (List.nth_error_nth _ _ _ Hr2).
          (** The results take relevant arguments, as the domain is. *)
          pose proof Hih as Hih0; apply rec_result_pi_relevant in Hih0 as [Fr1 Fr2].
          assert (Hns : tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns) by exact (trefl_l _ _ HMk _ _ HX1).
          assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
          assert (Hcvv : tele_prefix_rel (ar k ns c) K cv cv)
            by exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs Hns Hcon _ _ _ HK Hcv1).
          assert (Hys11 : tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns cv t) kd
                            (List.map fst yts1) (List.map fst yts1))
            by exact (doms_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk ns c gs gs1 t gs2 cv Hns Hcon Heq Hcvv
                        kd _ _ ltac:(lia) Hys).
          pose proof (frame_dom_relevant k Mk c gs gs1 t gs2 HMk Hcon Heq kd Bk HBk Ψ0 σ0 β0 x0 RΨ Hf HRΨ
                        ns E1 B1 zts1 w1 X1 cv nv1 v1 _ yts1 _ Hv1 Lys1 Hry1 HX1 Hcv1 Hys11 Eb1) as Hrb1.
          pose proof (frame_dom_relevant k Mk c gs gs1 t gs2 HMk Hcon Heq kd Bk HBk Ψ0 σ0 β0 x0 RΨ Hf HRΨ
                        ns E2 B2 zts2 w2 X2 cv nv2 v2 _ yts2 _ Hv2 Lys2 Hry2 HX2 Hcv2 Hys Eb2) as Hrb2.
          apply HRE; constructor;
            [ rewrite Hrb1; exact (proj1 (List.Forall_forall _ _) Fr1 _ (List.nth_error_In _ _ Hr1))
            | rewrite Hrb2; exact (proj1 (List.Forall_forall _ _) Fr2 _ (List.nth_error_In _ _ Hr2)) |].
          intros c0 c0' Hin.
          pose proof (proj1 (Edr c0 c0') Hin) as Hcc.
          destruct (rec_result_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hih c0 c0' Hcc) as (fc & fc' & rcs & rcs' & Efc & Efc' & HF1 & HF2 & Hih').
          destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c0 c0' Hcc) as (g0 & g0' & Ec & Ec' & Hsh').
          destruct (entry_readable_of_elem equiv_a_a' Hin) as [Hrc0 Hrc0'].
          assert (g0 = fc) as -> by (eapply functional_eval_app; eassumption).
          assert (g0' = fc') as -> by (eapply functional_eval_app; eassumption).
          pose proof Hsh as Hsh0; apply rec_arg_pi_kind in Hsh0 as [Hf1r Hf2r].
          destruct (Hcod c0 c0' Hin) as [a1' a2' Ea1' Ea2' HR'].
          destruct (Forall2_nth_error _ _ _ _ _ HF1 Hr1) as (q1 & Hq1 & Eq1).
          destruct (Forall2_nth_error _ _ _ _ _ HF2 Hr2) as (q2 & Hq2 & Eq2).
          econstructor; [ exact Eq1 | exact Eq2 |].
          rewrite <- (List.nth_error_nth _ _ d_True Hq1), <- (List.nth_error_nth _ _ d_True Hq2).
          pose proof (List.Forall2_length HF1) as LF1; pose proof (List.Forall2_length HF2) as LF2.
          match type of Hrc0 with entry_readable (de_term _ ?t) => set (t1 := t) in * end.
          match type of Hrc0' with entry_readable (de_term _ ?t) => set (t2 := t) in * end.
          set (yts1' := yts1 ++ (c0, t1) :: nil); set (yts2' := yts2 ++ (c0', t2) :: nil).
          assert (Hm1 : List.map fst yts1' = List.map fst yts1 ++ c0 :: nil) by (unfold yts1'; rewrite List.map_app; reflexivity).
          assert (Hm2 : List.map fst yts2' = List.map fst yts2 ++ c0' :: nil) by (unfold yts2'; rewrite List.map_app; reflexivity).
          assert (Hys' : tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns cv t) (S kd)
                           (List.map fst yts1') (List.map fst yts2')).
          { rewrite Hm1, Hm2; apply tele_prefix_rel_snoc; [ exact Hys |].
            unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HBk); exact Hcc. }
          assert (Ef1' : $*| v1 & List.map fst yts1' | gc_deps ⍮ gc_stack ↘ fc)
            by (rewrite Hm1; apply eval_apps_app; exists f1; split; [ exact Ef1 | econstructor; [ exact Efc | constructor ] ]).
          assert (Ef2' : $*| v2 & List.map fst yts2' | gc_deps ⍮ gc_stack ↘ fc')
            by (rewrite Hm2; apply eval_apps_app; exists f2; split; [ exact Ef2 | econstructor; [ exact Efc' | constructor ] ]).
          assert (HBs : List.nth_error (shape_doms_tele t) kd = Some (ce_ass ak_relevant Bk))
            by (unfold shape_doms_tele; rewrite List.nth_error_map, HBk; reflexivity).
          rewrite <- !List.app_assoc in Hsh', Hih'; cbn [List.app] in Hsh', Hih'.
          assert (Hl'' : List.nth_error (shape_leaves (rview_leaves D) (im_nn Mk + K + S kd) (ptyp_skip (S kd) t)) idx = Some l')
            by (replace (im_nn Mk + K + S kd) with (S (im_nn Mk + K + kd)) by lia; exact Hl').
          exact (IHm (S kd) ltac:(lia) yts1' yts2' fc fc' rcs rcs' ltac:(lia)
                   ltac:(unfold yts1'; rewrite List.length_app, Lys1; cbn; lia) ltac:(unfold yts2'; rewrite List.length_app, Lys2; cbn; lia)
                   ltac:(unfold yts1'; apply List.Forall_app; split; [ exact Hry1 | constructor; [ exact Hrc0 | constructor ] ])
                   ltac:(unfold yts2'; apply List.Forall_app; split; [ exact Hry2 | constructor; [ exact Hrc0' | constructor ] ])
                   Hys' Ef1' Ef2'
                   ltac:(rewrite Hm1; exact (apps_relevant_snoc _ _ _ _ Hrel1 Ef1 Hf1r))
                   ltac:(rewrite Hm2; exact (apps_relevant_snoc _ _ _ _ Hrel2 Ef2 Hf2r))
                   ltac:(rewrite Hm1, Hm2, (firstn_S_snoc _ _ _ HBs); rewrite ?List.app_assoc in *; exact Hsh')
                   ltac:(rewrite Hm1, Hm2, (firstn_S_snoc _ _ _ HBs); rewrite ?List.app_assoc in *; exact Hih')
                   ltac:(rewrite <- LF1; exact Lr1) ltac:(rewrite <- LF2; exact Lr2)
                   idx l' Hl'' a1' a2' i _
                   ltac:(unfold yts1'; rewrite env_extend_typed_app; exact Ea1')
                   ltac:(unfold yts2'; rewrite env_extend_typed_app; exact Ea2') HR').
      Qed.

      (** ** The Branches' Contexts

          The branch of a constructor [c] of the member [k], with arguments
          [gs]: its context, the non-uniform parameters, the arguments and
          the recursive results, each at the motive of the member its
          argument's shape ends in. *)
      Section Branch.
        Variable (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
        Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
        Hypothesis (HB : ⊨ elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ).
        (** A branch is of a member with a block, not of a record view. *)
        Hypothesis (HrvK : im_is_rview Mk = false).
        Let HΨ := valid_group_cargs_sem p D Hvg Hcv k Mk c gs HMk Hcon.
        Let As := blocks_motives Bks.
        Let T := List.rev (im_nparams Mk).

        (** The branch's context: the recursive results over the instance
            of the arguments and the non-uniform parameters. *)
        Lemma branch_context_split : elim_bctx ak_relevant p D Mk gs As Us ++ Γ
                           = ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs ++ con_inst_ctx Γ p D Mk Us gs.
        Proof. unfold elim_bctx, con_inst_ctx; rewrite <- !List.app_assoc; reflexivity. Qed.

        (** The recursive results of the arguments [gs1] before the others,
            over the instance of the arguments and the non-uniform
            parameters, form a valid context. *)
        Lemma branch_context_recursive_results_prefix_valid : forall gs1 gs2, gs = gs1 ++ gs2 ->
            ⊨ ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs1 ++ con_inst_ctx Γ p D Mk Us gs.
        Proof.
          intros * Heq; pose proof HB as H; fold As in H; rewrite branch_context_split in H.
          replace (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs)
            with (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) (cargs_pat gs1 ++ nil) (0 + cargs_nrec D gs1) gs2
                  ++ ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs1) in H
            by (rewrite <- ihs_ctx_aux_app, <- Heq; reflexivity).
          rewrite <- List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H).
        Qed.

        (** The recursive results of a recursive argument, one per leaf path
            of its shape: after those of the arguments before it ([E0]), the
            entry of the leaf path [n] over the entries of the paths before
            it. *)
        Lemma branch_context_recursive_results_at_recursive_argument : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
            ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 (gs1 ++ ca_rec t :: nil)
            = leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) (cargs_nrec D gs1)
                (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t)
              ++ ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs1.
        Proof.
          intros * Heq; rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app Nat.add]; reflexivity.
        Qed.

        Lemma leaves_ctx_firstn_S : forall nn na pat j ls n l, List.nth_error ls n = Some l ->
            leaves_ctx ak_relevant nn As Us na pat j (List.firstn (S n) ls)
            = ce_ass ak_relevant (leaf_ihty ak_relevant As (sb_of_wk (wk_shiftn ((j + n) + na + nn))) (ihs_sub nn Us na pat (j + n))
                        (a_var ((j + n) + na - 1 - List.length pat)) l)
              :: leaves_ctx ak_relevant nn As Us na pat j (List.firstn n ls).
        Proof.
          intros * Hn.
          assert (Hn' : List.nth_error (List.firstn (S n) ls) n = Some l)
            by (rewrite List.nth_error_firstn; destruct (Nat.ltb_spec n (S n)); [ exact Hn | lia ]).
          rewrite (leaves_ctx_split _ _ _ _ _ _ _ _ _ _ Hn').
          assert (Hlen : List.length (List.firstn (S n) ls) = S n)
            by (rewrite List.length_firstn; apply nth_error_lt_length in Hn; lia).
          rewrite List.skipn_all2 by lia; cbn [leaves_ctx List.app].
          rewrite List.firstn_firstn, Nat.min_l by lia; reflexivity.
        Qed.

        Lemma leaf_pre_sem : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
            forall n l, List.nth_error (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t) n = Some l ->
            ⊨ leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) (cargs_nrec D gs1)
                (List.firstn (S n) (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t))
              ++ ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs1 ++ con_inst_ctx Γ p D Mk Us gs.
        Proof.
          intros * Heq n l Hn.
          pose proof (branch_context_recursive_results_prefix_valid (gs1 ++ ca_rec t :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as H.
          rewrite (branch_context_recursive_results_at_recursive_argument _ _ _ Heq) in H.
          set (ls := shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t) in *.
          rewrite <- (List.firstn_skipn (S n) ls) in H.
          assert (Hsk : forall j0 ls1 ls2, leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) j0 (ls1 ++ ls2)
                          = leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) (j0 + List.length ls1) ls2
                            ++ leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) j0 ls1).
          { intros j0 ls1; revert j0; induction ls1 as [| l1 ls1 IH]; intros j0 ls2; cbn [leaves_ctx List.app List.length];
              [ rewrite Nat.add_0_r, List.app_nil_r; reflexivity |].
            rewrite IH, <- List.app_assoc; replace (S j0 + List.length ls1) with (j0 + S (List.length ls1)) by lia; reflexivity. }
          rewrite Hsk, <- !List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H).
        Qed.

        (** *** The Frame of a Recursive Argument

            A recursive argument [x] of shape [t] in the branch's context,
            after the recursive results [Er]: its frame, with the components
            [σ] moved into the context and the base [β] past it. *)
        Section Entry.
          #[local] Set Default Proof Using "All".
          Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
          Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
          Variable (Er : ctx).
          Hypothesis (HCtx : ⊨ Er ++ con_inst_ctx Γ p D Mk Us gs).
          Let pat := cargs_pat gs1.
          Let K := List.length (cargs_nonrec gs1).
          Let Ctx := Er ++ con_inst_ctx Γ p D Mk Us gs.
          Let jr := List.length Er.
          Let na := List.length gs.
          Let σ := ihs_sub (im_nn Mk) Us na pat jr.
          Let m := jr + na + im_nn Mk.
          Let β := sb_of_wk (wk_shiftn m).
          Let idx := jr + na - 1 - List.length pat.
          Let Tg := cargs_nonrec_ctx gs1 ++ im_params D Mk ++ Γ.
          Let Ψ0 := Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU.

          Lemma branch_entry_LE : List.length Er = jr.
          Proof. reflexivity. Qed.

          Lemma branch_entry_Lpat : List.length pat = List.length gs1.
          Proof. apply length_cargs_pat. Qed.

          Lemma branch_entry_Lna : na = List.length gs1 + S (List.length gs2).
          Proof. unfold na; rewrite Heq, List.length_app; cbn; lia. Qed.

          Lemma branch_entry_ctx_split : Ctx = Ψ0 ++ Γ.
          Proof. unfold Ctx, Ψ0; rewrite con_inst_ctx_eq, List.app_assoc; reflexivity. Qed.

          Lemma branch_entry_LΨ0 : List.length Ψ0 = m.
          Proof.
            unfold Ψ0, m; rewrite List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams; unfold na; lia.
          Qed.

          (** The components' substitution. *)
          Lemma gsub_sigma : gsub Ctx σ Tg.
          Proof.
            assert (Hp1 : ⊨ cargs_ctx p D Mk gs1 ++ im_params D Mk) by exact (cargs_prefix_sem D p Mk gs HΨ gs1 _ Heq).
            assert (Hp1a : all_assumptions (cargs_ctx p D Mk gs1 ++ im_params D Mk))
              by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMk) ]).
            destruct (closed_app_sem _ _ Hp1a Hp1 HΓ) as [HΨ1Γ _].
            pose proof (gsub_wk _ _ _ (cargs_wk_ext k Mk c gs HMk Hcon gs1 _ Heq) ltac:(rewrite <- List.app_assoc in HΨ1Γ; exact HΨ1Γ)
                          (frame_target_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq)) as G0.
            assert (Hτ2 : gsub (con_inst_ctx Γ p D Mk Us gs1) (sb_qn (List.length pat + im_nn Mk) (sb_of_list Id Us))
                            (cargs_ctx p D Mk gs1 ++ im_params D Mk ++ Γ)).
            { rewrite con_inst_ctx_eq.
              replace (List.length pat + im_nn Mk) with (List.length (cargs_ctx p D Mk gs1 ++ im_nparams Mk))
                by (rewrite List.length_app, length_cargs_ctx, length_im_nparams, branch_entry_Lpat; lia).
              replace (cargs_ctx p D Mk gs1 ++ im_params D Mk ++ Γ) with ((cargs_ctx p D Mk gs1 ++ im_nparams Mk) ++ ind_uparams D ++ Γ)
                by (unfold im_params; rewrite <- !List.app_assoc; reflexivity).
              apply gsub_qn; [ exact gsub_U | apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_nparams_ass D Hc _ _ HMk) ] |].
              unfold im_params in HΨ1Γ; repeat rewrite <- List.app_assoc in HΨ1Γ; repeat rewrite <- List.app_assoc; exact HΨ1Γ. }
            destruct (gsub_props Hτ2) as [Hτ2v Hτ2l].
            pose proof (gsub_comp _ _ _ _ _ G0 (gsub_rel_ctx_wf _ _ _ Hτ2) Hτ2v Hτ2l) as G1.
            assert (Hw3 : Ctx ⊨ʷ (wk_shiftn (na - List.length pat + jr)) : con_inst_ctx Γ p D Mk Us gs1).
            { pose proof HCtx as H0; fold Ctx in H0; unfold Ctx in H0 |- *.
              rewrite Heq in H0 |- *; rewrite con_inst_ctx_split in H0 |- *; rewrite List.app_assoc in H0 |- *.
              match goal with |- ?C ++ _ ⊨ʷ _ : _ => replace (na - List.length pat + jr) with (List.length C) end.
              - apply rel_wk_under_ctx_shiftn; exact H0.
              - rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux, branch_entry_LE, branch_entry_Lna, branch_entry_Lpat; cbn; lia. }
            exact (gsub_comp _ _ _ _ _ G1 HCtx (rel_sub_of_wk Hw3) (sub_link_wk Hw3)).
          Qed.

          (** The environments of the branch's context there. *)
          Lemma branch_entry_Lm : forall (X fa : list domain) (v : domain) (aft ihp : list domain), List.length X = im_nn Mk ->
              List.length fa = List.length gs1 -> List.length aft = List.length gs2 -> List.length ihp = jr ->
              List.length (X ++ fa ++ v :: aft ++ ihp) = m.
          Proof. intros; unfold m; rewrite branch_entry_Lna; rewrite !List.length_app; cbn; rewrite List.length_app; lia. Qed.

          Lemma side_w : forall RS, EF Ctx ≈ Ctx ∈ per_ctx_env ↘ RS -> forall B vtsE, RΓ B C1 -> List.length vtsE = m ->
              RS (env_extend_typed B vtsE) (env_extend_typed B vtsE) ->
              exists w, ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_extend_typed B vtsE ↘ w /\
                RU (decl_env D w) (decl_env D u0) /\ List.length w = ind_nu D.
          Proof.
            intros RS HRS * HBC Lv HE.
            assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
            pose proof HRS as HRS'; rewrite branch_entry_ctx_split in HRS'.
            pose proof HCtx as HC'; fold Ctx in HC'; rewrite branch_entry_ctx_split in HC'.
            destruct (us_wk_vals _ _ _ HRS' HC' HE) as (w & uB & Hw & HuB & Hwu).
            rewrite branch_entry_LΨ0 in Hw, HuB.
            rewrite <- Lv, eval_wk_shiftn_extend_typed in HuB.
            destruct (us_class B HBC) as (uB' & HuB' & HuB0).
            pose proof (functional_eval_exps' _ _ _ _ HuB HuB') as <-.
            exists w; split; [ exact Hw | split; [ etransitivity; eassumption |] ].
            rewrite (eval_exps_length _ _ _ Hw), List.length_map; exact HUl.
          Qed.

          (** Past the non-recursive arguments before the position and the
              non-uniform parameters, [σ] is [Us] moved past the branch's
              context, then the weakening past it. *)
          Lemma branch_entry_form : forall y, σ (y + List.length (cargs_nonrec_ctx gs1 ++ im_nparams Mk))
                                   = sb_of_list β (List.map (fun U => U[β]) Us) y.
          Proof.
            intros y.
            replace (y + List.length (cargs_nonrec_ctx gs1 ++ im_nparams Mk)) with (pat_nargs pat + (im_nn Mk + y))
              by (rewrite List.length_app, length_im_nparams; unfold pat; rewrite pat_nargs_cargs_pat; lia).
            unfold σ, ihs_sub; cbn [sb_compose sb_of_wk sentry_sub].
            rewrite wk_pat_ge, sb_qn_ge by lia.
            replace (List.length pat + (im_nn Mk + y) - (List.length pat + im_nn Mk)) with y by lia.
            rewrite sentry_sub_of_wk, sentry_wk_wk.
            destruct (Nat.lt_ge_cases y (ind_nu D)) as [Hy | Hy].
            - rewrite !(sb_of_list_nth _ _ _ a_prop) by (rewrite ?List.length_map; lia); cbn [sentry_wk]; f_equal.
              rewrite List.length_map.
              rewrite (List.nth_indep (List.map (fun U => U[β]) Us) _ (a_prop[β])) by (rewrite List.length_map; lia).
              pose proof (List.map_nth (fun U => U[β]) Us a_prop (List.length Us - 1 - y)) as E1; cbn beta in E1; rewrite E1.
              unfold β; rewrite exp_sub_of_wk; apply exp_wk_wk_eq; intros z; cbn; unfold m; rewrite branch_entry_Lna, branch_entry_Lpat; lia.
            - replace y with (List.length Us + (y - ind_nu D)) at 1 by lia.
              replace y with (List.length (List.map (fun U => U[β]) Us) + (y - ind_nu D)) at 2 by (rewrite List.length_map; lia).
              rewrite !sb_of_list_ge; unfold β; cbn [sb_id sentry_wk sb_of_wk wk_compose wk_shiftn]; f_equal;
                unfold m; rewrite branch_entry_Lna, branch_entry_Lpat; lia.
          Qed.

          (** The components' value: the uniform parameters' values [w],
              which the canonical ones relate, the non-uniform parameters
              [X] and the non-recursive arguments before, related to
              themselves canonically, so holding the proofs of the
              target. *)
          Lemma sigma_side : forall RS, EF Ctx ≈ Ctx ∈ per_ctx_env ↘ RS -> forall B vtsE X fa v aft ihp w,
              List.map fst vtsE = X ++ fa ++ v :: aft ++ ihp ->
              List.length X = im_nn Mk -> List.length fa = List.length gs1 ->
              List.length aft = List.length gs2 -> List.length ihp = jr ->
              RS (env_extend_typed B vtsE) (env_extend_typed B vtsE) ->
              ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_extend_typed B vtsE ↘ w ->
              exists Bσ wts, ⟦ σ : Tg ⟧s env_extend_typed B vtsE ↘ env_extend_typed Bσ wts /\
                List.map fst wts = w ++ X ++ nonrec_arg_vals gs1 fa /\
                List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) wts.
          Proof.
            intros RS HRS * Hv LX Lfa Laft Lihp HE Hw.
            set (E := env_extend_typed B vtsE) in *.
            (** The semantic substitution's value. *)
            destruct (rel_sub_under_ctx_simple (gsub_valid gsub_sigma)) as (R1 & HR1 & RT & HRT & Hs).
            assert (E1 : RS <~> R1) by (eapply per_ctx_env_right_irrel; [ exact HRS | exact HR1 ]).
            destruct (Hs _ _ (proj1 (E1 _ _) HE)) as (e1 & e1' & Ee1 & _ & He1).
            assert (HPT : PER RT) by (eapply per_env_PER; exact HRT).
            assert (He11 : RT e1 e1) by (etransitivity; [ exact He1 | symmetry; exact He1 ]).
            set (K0 := cargs_nonrec_ctx gs1 ++ im_params D Mk).
            set (n := List.length K0).
            set (tl := w ++ X ++ nonrec_arg_vals gs1 fa).
            assert (Lw : List.length w = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw), List.length_map; exact HUl).
            assert (Lnv : List.length (nonrec_arg_vals gs1 fa) = K) by (apply length_nonrec_arg_vals; exact Lfa).
            assert (Ln : n = K + im_nn Mk + ind_nu D)
              by (unfold n, K0; rewrite List.length_app, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele, length_im_params;
                  unfold im_np, K; lia).
            assert (Ltl : List.length tl = n) by (unfold tl; rewrite !List.length_app, Lw, LX, Lnv; lia).
            assert (LTg : List.length Tg = n + List.length Γ) by (unfold Tg, n, K0; rewrite !List.length_app; lia).
            pose proof (frame_nonrec_ctx_all_assumptions HMall k Mk c gs gs1 t gs2 HMk Hcon Heq) as HK0a.
            assert (HRT' : EF K0 ++ Γ ≈ K0 ++ Γ ∈ per_ctx_env ↘ RT) by (unfold K0; rewrite <- List.app_assoc; exact HRT).
            (** The entries' propositionality is decided by their relevance. *)
            assert (Hdec : forall x, x < n -> evaluated_kind (frame_rf gs gs1 x) -> ~ entry_propositional gc_deps gc_stack Tg e1 x).
            { intros x Hx Hr; unfold Tg; rewrite List.app_assoc.
              refine (evaluated_entry_not_propositional K0 Γ RT x HK0a Hx _ HRT' e1 e1 He11).
              intros Δ1 κ0 T0 Δ2 E0 HΔ1.
              exact (proj1 (frame_entry_sort HMall k Mk c gs gs1 t gs2 HMk Hcon Heq x Δ1 κ0 T0 Δ2 E0 HΔ1) Hr). }
            assert (Hpr : forall x, x < n -> frame_rf gs gs1 x = ak_propositional -> entry_propositional gc_deps gc_stack Tg e1 x).
            { intros x Hx Hr; unfold Tg; rewrite List.app_assoc.
              refine (prop_entry_propositional K0 Γ RT x HK0a Hx _ HRT' e1 e1 He11).
              intros Δ1 κ0 T0 Δ2 E0 HΔ1.
              exact (proj2 (frame_entry_sort HMall k Mk c gs gs1 t gs2 HMk Hcon Heq x Δ1 κ0 T0 Δ2 E0 HΔ1) Hr). }
            (** The branch environment past the arguments after the
                position, and the arguments' entries. *)
            assert (Hs0 : na - List.length pat + jr = List.length (v :: aft ++ ihp))
              by (rewrite branch_entry_Lna, branch_entry_Lpat; cbn; rewrite List.length_app, Laft, Lihp; lia).
            destruct (List.map_eq_app _ _ _ _ Hv) as (vX & vr1 & -> & HvX & Hvr1).
            destruct (List.map_eq_app _ _ _ _ Hvr1) as (vfa & vr & -> & Hvfa & Hvr).
            assert (Lvfa : List.length vfa = List.length gs1) by (rewrite <- (List.length_map fst), Hvfa; exact Lfa).
            assert (Lvr : List.length vr = List.length (v :: aft ++ ihp)) by (rewrite <- (List.length_map fst), Hvr; reflexivity).
            assert (Ewk : ⟪wk_shiftn (na - List.length pat + jr)⟫ E = env_extend_typed (env_extend_typed B vX) vfa).
            { unfold E; rewrite Hs0, <- Lvr, List.app_assoc, env_extend_typed_app, eval_wk_shiftn_extend_typed, env_extend_typed_app;
                reflexivity. }
            assert (HK : pat_nargs pat = K)
              by (unfold pat, K; rewrite pat_nargs_cargs_pat, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele; reflexivity).
            assert (Hent : forall x, x < n -> exists t0, env_entry e1 x = de_term (List.nth (n - 1 - x) tl d_prop) t0).
            { intros x Hx.
              destruct (Ee1 x ltac:(lia)) as [HPx HN].
              destruct (Nat.lt_ge_cases x (K + im_nn Mk)) as [Hxl | Hxg].
              - assert (Hσx : σ x = se_var (wk_shiftn (na - List.length pat + jr) (wk_pat pat x))).
                { unfold σ, ihs_sub; cbn [sb_compose sb_of_wk sentry_sub].
                  rewrite sb_qn_lt by (apply wk_pat_bound; lia); cbn [sentry_sub sb_of_wk]; reflexivity. }
                assert (Hy : env_entry e1 x = retag_entry (ctx_entry_tag Tg x e1) (ctx_entry_unit Tg x)
                                               (env_entry E (wk_shiftn (na - List.length pat + jr) (wk_pat pat x)))).
                { destruct (evaluated_kind_or_propositional (frame_rf gs gs1 x)) as [Erf | Erf].
                  - pose proof (HN (Hdec x Hx Erf)) as H0; rewrite Hσx in H0; exact H0.
                  - pose proof (HPx (Hpr x Hx Erf)) as H0; rewrite Hσx in H0; exact H0. }
                rewrite <- (eval_wk_entry _ _ (wk_mono_shiftn _)), Ewk, <- (eval_wk_entry _ _ (wk_mono_pat pat)) in Hy.
                unfold pat in Hy; rewrite (eval_wk_pat_args gs1 _ vfa Lvfa), <- env_extend_typed_app in Hy.
                assert (Lxs : List.length (vX ++ nonrec_typed gs1 vfa) = K + im_nn Mk)
                  by (rewrite <- (List.length_map fst), List.map_app, nonrec_typed_values, HvX, Hvfa, List.length_app, LX, Lnv; lia).
                destruct (env_entry_extend_typed_lt B (vX ++ nonrec_typed gs1 vfa) x ltac:(lia)) as (v' & t' & Hn' & He').
                rewrite He' in Hy; cbn [retag_entry] in Hy.
                exists (ctx_entry_tag Tg x e1); rewrite Hy; f_equal.
                assert (Hfst : List.map fst (vX ++ nonrec_typed gs1 vfa) = X ++ nonrec_arg_vals gs1 fa)
                  by (rewrite List.map_app, nonrec_typed_values, HvX, Hvfa; reflexivity).
                pose proof (List.map_nth_error fst _ _ Hn') as Hn''; rewrite Hfst in Hn''; cbn [fst] in Hn''.
                unfold tl; rewrite List.app_nth2 by lia; rewrite Lw.
                replace (n - 1 - x - ind_nu D) with (List.length (vX ++ nonrec_typed gs1 vfa) - 1 - x) by lia.
                symmetry; apply List.nth_error_nth; exact Hn''.
              - set (y := x - (K + im_nn Mk)).
                assert (Exy : x = y + List.length (cargs_nonrec_ctx gs1 ++ im_nparams Mk))
                  by (rewrite List.length_app, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele, length_im_nparams; unfold y, K in *; lia).
                assert (Hyl : y < ind_nu D) by (unfold y; lia).
                pose proof (branch_entry_form y) as Hσx; rewrite <- Exy in Hσx.
                rewrite (sb_of_list_nth _ _ _ a_prop) in Hσx by (rewrite List.length_map, HUl; exact Hyl).
                assert (Erf : frame_rf gs gs1 x = ak_relevant) by (unfold frame_rf; replace (x <? List.length (cargs_nonrec gs1)) with false
                                                by (symmetry; apply Nat.ltb_ge; unfold K in Hxg; lia); reflexivity).
                pose proof (HN (Hdec x Hx ltac:(rewrite Erf; constructor))) as H0; rewrite Hσx in H0; cbn [eval_sentry] in H0.
                destruct H0 as (mm & Hm & Emm).
                rewrite List.length_map, HUl in Emm.
                destruct (nth_error_lt_some' Us (ind_nu D - 1 - y) ltac:(rewrite HUl; lia)) as [U HU].
                destruct (eval_exps_nth _ _ _ _ _ Hw ltac:(rewrite List.nth_error_map, HU; reflexivity)) as (u & Hu & Eu).
                assert (Emm' : ⟦ U[β] ⟧ E ↘ mm).
                { replace (U[β]) with (List.nth (ind_nu D - 1 - y) (List.map (fun U => U[β]) Us) a_prop); [ exact Emm |].
                  rewrite (List.nth_error_nth _ _ a_prop (eq_trans (List.nth_error_map _ _ _) (f_equal _ HU))); reflexivity. }
                unfold β in Emm'; rewrite exp_sub_of_wk in Emm'.
                pose proof (functional_eval_exp _ _ _ _ Emm' Eu) as ->.
                exists (ctx_entry_tag Tg x e1); rewrite Hm; f_equal.
                unfold tl; rewrite List.app_nth1 by lia.
                replace (n - 1 - x) with (ind_nu D - 1 - y) by (unfold y; lia).
                symmetry; apply List.nth_error_nth; exact Hu. }
            (** The value as a typed extension of its tail. *)
            destruct (env_typed_prefix n e1 ltac:(intros x Hx; destruct (Hent x Hx) as [t0 Ht0]; eauto)) as (vts & Lvts & Hag).
            assert (Hvts : List.map fst vts = tl).
            { apply (List.nth_ext _ _ d_prop d_prop); [ rewrite List.length_map; lia |].
              intros i Hi; rewrite List.length_map in Hi.
              destruct (Hent (n - 1 - i) ltac:(lia)) as [t0 Ht0].
              destruct (env_entry_extend_typed_lt (List.skipn n e1) vts (n - 1 - i) ltac:(lia)) as (v' & t' & Hn' & He').
              rewrite <- Hag, Ht0 in He'; injection He' as Hv' _.
              replace (List.length vts - 1 - (n - 1 - i)) with i in Hn' by lia.
              replace (n - 1 - (n - 1 - i)) with i in Hv' by lia.
              rewrite (List.nth_error_nth _ _ d_prop (eq_trans (List.nth_error_map fst _ _) (f_equal _ Hn'))); exact (eq_sym Hv'). }
            assert (HagT : env_agree_upto (List.length Tg) e1 (env_extend_typed (List.skipn n e1) vts)) by (intros x _; exact (Hag x)).
            exists (List.skipn n e1), vts; split; [ exact (eval_sub_resp_agree _ _ _ _ _ Ee1 HagT) | split; [ exact Hvts |] ].
            (** Its entries read back, the value being related to itself. *)
            pose proof (per_ctx_env_resp_agree HRT _ _ _ _ HagT HagT He11) as HEσ.
            assert (HKr : ⊨ List.rev (List.rev K0) ++ Γ)
              by (rewrite List.rev_involutive; unfold K0; rewrite <- List.app_assoc; exact (frame_target_valid HMall k Mk c gs gs1 t gs2 HMk Hcon Heq)).
            assert (HRTr : EF List.rev (List.rev K0) ++ Γ ≈ List.rev (List.rev K0) ++ Γ ∈ per_ctx_env ↘ RT)
              by (rewrite List.rev_involutive; exact HRT').
            assert (Lv : List.length vts = List.length (List.rev K0)) by (rewrite List.length_rev; exact Lvts).
            exact (proj1 (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HKr (List.Forall_rev HK0a) HRTr _ _ _ _ Lv Lv HEσ)).
          Qed.

          (** The recursive argument, in the branch's context. *)
          Lemma branch_entry_lookup : Ctx ∋ #idx : ptyp_ty_at p D (List.map (fun U => U[β]) Us) σ t.
          Proof.
            unfold Ctx; rewrite Heq; rewrite con_inst_ctx_split, List.app_assoc.
            rewrite <- !List.app_assoc; cbn [List.app]; rewrite List.app_assoc.
            set (Lc := tele_sub (cargs_ctx_aux p D (im_nn Mk) (true :: cargs_pat gs1) gs2)
                        (sb_qn (S (List.length gs1)) (sb_qn (im_nn Mk) (sb_of_list Id Us)))).
            assert (HL : List.length Lc = List.length gs2) by (unfold Lc; rewrite length_tele_sub, length_cargs_ctx_aux; reflexivity).
            replace idx with (0 + List.length (Er ++ Lc)) by (rewrite List.length_app, HL, branch_entry_LE; unfold idx; rewrite branch_entry_Lna, branch_entry_Lpat; lia).
            match goal with |- _ ∋ # _ : ?T0 =>
              replace T0 with ((ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t)
                                [sb_qn (List.length gs1) (sb_qn (im_nn Mk) (sb_of_list Id Us))][wk_shift]ʷ[wk_shiftn (List.length (Er ++ Lc))]ʷ)
            end.
            { apply ctx_lookup_app_r; constructor. }
            rewrite ptyp_ty_eq_at, ptyp_ty_at_sub by (try exact Hc; apply length_ind_uvars).
            rewrite <- !exp_sub_of_wk, !ptyp_ty_at_sub by (try exact Hc; rewrite List.length_map, length_ind_uvars; reflexivity).
            rewrite !List.map_map.
            rewrite ptyp_ty_at_sub by (try exact Hc; rewrite List.length_map, length_ind_uvars; reflexivity).
            rewrite !List.map_map.
            rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ σ); [ f_equal |].
            - unfold ind_uvars.
              rewrite (List.map_ext _ (fun M => M[sb_qn (List.length gs1 + im_nn Mk) (sb_of_list Id Us)][sb_of_wk (wk_shiftn (S (List.length (Er ++ Lc))))]))
                by (intros; rewrite !exp_sub_sub; apply exp_sub_sb_eq; intros z; cbn [sb_compose];
                    rewrite <- !sentry_sub_sub, (sb_qn_add _ _ _ z), !sentry_sub_of_wk, sentry_wk_wk; apply sentry_wk_wk_eq; intros w; cbn; lia).
              rewrite <- (List.map_map (fun M => M[sb_qn (List.length gs1 + im_nn Mk) (sb_of_list Id Us)])
                            (fun M => M[sb_of_wk (wk_shiftn (S (List.length (Er ++ Lc))))])).
              rewrite length_cargs_pat, <- HUl, vars_from_sb_qn, List.map_map.
              apply List.map_ext; intros U; unfold β; rewrite !exp_sub_of_wk, !exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn.
              rewrite List.length_app, HL, branch_entry_LE; unfold m; rewrite branch_entry_Lna; lia.
            - unfold σ, ihs_sub; intros y; cbn [sb_compose].
              rewrite !sentry_sub_sub; apply sentry_sub_sb_eq; intros z; cbn [sb_compose].
              unfold pat; rewrite <- (sb_qn_add _ _ _ z), length_cargs_pat.
              apply sentry_sub_sb_eq; intros w; cbn.
              rewrite List.length_app, HL, branch_entry_LE; f_equal; pose proof branch_entry_Lna as Hna0; pose proof branch_entry_Lpat as Hp0; unfold na, pat in *; lia.
          Qed.

          Lemma branch_entry_uc : shape_uc D Us (cargs_nonrec_ctx gs1 ++ im_params D Mk) σ β.
          Proof.
            intros x Hx.
            replace (x + (List.length (cargs_nonrec_ctx gs1 ++ im_params D Mk) - ind_nu D)) with (pat_nargs pat + (im_nn Mk + x))
              by (rewrite List.length_app, length_im_params; unfold pat; rewrite pat_nargs_cargs_pat; unfold im_np; lia).
            unfold σ, ihs_sub, β; cbn [sb_compose sb_of_wk sentry_sub].
            rewrite wk_pat_ge, sb_qn_ge by lia.
            replace (List.length pat + (im_nn Mk + x) - (List.length pat + im_nn Mk)) with x by lia.
            rewrite !sentry_sub_of_wk, sentry_wk_wk; f_equal; apply sentry_wk_wk_eq; intros z; cbn; unfold m; rewrite branch_entry_Lna, branch_entry_Lpat; lia.
          Qed.

          (** The frame of the argument. *)
          Lemma branch_entry_frame : sem_frame Mk gs1 t Ψ0 σ β (a_var idx).
          Proof.
            constructor; rewrite <- ?branch_entry_ctx_split.
            - exact HCtx.
            - exact gsub_sigma.
            - rewrite branch_entry_LΨ0; reflexivity.
            - exact branch_entry_uc.
            - exact (valid_exp_under_ctx_vlookup branch_entry_lookup HCtx).
            - cbn [exp_scoped]; rewrite branch_entry_ctx_split, List.length_app, branch_entry_LΨ0.
              unfold idx, m; rewrite branch_entry_Lna, branch_entry_Lpat; lia.
            - exact branch_entry_form.
          Qed.

          (** Its values at a side. *)
          Lemma branch_entry_vals : forall RS, EF Ctx ≈ Ctx ∈ per_ctx_env ↘ RS -> forall B vtsE X fa v aft ihp w, RΓ B C1 ->
              List.map fst vtsE = X ++ fa ++ v :: aft ++ ihp ->
              List.length X = im_nn Mk -> List.length fa = List.length gs1 ->
              List.length aft = List.length gs2 -> List.length ihp = jr ->
              RS (env_extend_typed B vtsE) (env_extend_typed B vtsE) ->
              ⟦ List.map (fun U => U[wk_shiftn m]ʷ) Us ⟧* gc_deps ⍮ gc_stack ⍮ env_extend_typed B vtsE ↘ w ->
              RU (decl_env D w) (decl_env D u0) -> List.length w = ind_nu D ->
              sem_frame_vals Mk gs1 Ψ0 σ (a_var idx) RS (env_extend_typed B vtsE) B vtsE w X (nonrec_arg_vals gs1 fa) v.
          Proof.
            intros * HRS * HBC Hv LX Lfa Laft Lihp HE Hw HwU Lw.
            pose proof (branch_entry_Lm X fa v aft ihp LX Lfa Laft Lihp) as Lall.
            assert (Lv : List.length vtsE = m) by (rewrite <- (List.length_map fst), Hv; exact Lall).
            constructor.
            - exact HE.
            - reflexivity.
            - rewrite Lv, branch_entry_LΨ0; reflexivity.
            - exact HBC.
            - exact (sigma_side _ HRS _ _ _ _ _ _ _ _ Hv LX Lfa Laft Lihp HE Hw).
            - replace idx with (List.length vtsE - 1 - (List.length X + List.length fa))
                by (rewrite Lv; unfold idx, m; rewrite branch_entry_Lna, branch_entry_Lpat; lia).
              pose proof (eval_var_extend_typed B vtsE (List.length vtsE - 1 - (List.length X + List.length fa))
                            ltac:(rewrite Lv, <- Lall, !List.length_app; cbn; rewrite List.length_app; lia)) as H0.
              replace (List.length vtsE - 1 - (List.length vtsE - 1 - (List.length X + List.length fa)))
                with (List.length X + List.length fa) in H0
                by (rewrite Lv, <- Lall, !List.length_app; cbn; rewrite List.length_app; lia).
              rewrite Hv, nth_mid in H0; exact H0.
            - exact HwU.
            - exact Lw.
            - exact LX.
            - apply length_nonrec_arg_vals; exact Lfa.
          Qed.
        End Entry.

        (** *** The Recursive Results

            Arguments of two constructors related at the canonical relations
            of their stored non-uniform parameters [X] and [X'], with related
            recursive results: related at the recursive results' telescope
            of the branch's context, one leaf path at a time
            ([leaf_walk_sem]). *)
        Lemma canonical_ihs : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
            forall X X' vs vs' ihs ihs',
            tele_rel (nr k) T X X' ->
            tele_rel (ar k X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
            con_args_rel p D (admissible_index_at D u0 nr) nr ar dr k u0 u0 X X' T gs vs vs' ->
            rec_results_rel D dr Rel k u0 u0 X X' T gs vs vs' ihs ihs' ->
            per_tele_args (List.rev (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)) B1 B2 (X ++ vs) (X' ++ vs') ->
            forall kk, kk <= List.length gs ->
            per_tele_args (List.rev (ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 (List.firstn kk gs)))
              (env_tele B1 (List.rev (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)) (X ++ vs))
              (env_tele B2 (List.rev (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)) (X' ++ vs'))
              (List.firstn (cargs_nrec D (List.firstn kk gs)) ihs) (List.firstn (cargs_nrec D (List.firstn kk gs)) ihs').
        Proof.
          intros B1 B2 HB1 HB2 * HX Har Hia Hir Hci.
          set (TB := List.rev (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)) in *.
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
          assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
          destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
          destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
          pose proof HX as HX0; rewrite tele_rel_iff in HX0; destruct HX0 as (LX & LX' & _).
          unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
          pose proof (trefl_l _ _ HMk _ _ HX) as HXX.
          induction kk as [| kk IH]; intros Hk; [ cbn; constructor |].
          destruct (nth_error_lt_some' gs kk ltac:(lia)) as [g Hg].
          assert (Heq0 : gs = List.firstn kk gs ++ g :: List.skipn (S kk) gs)
            by (rewrite <- (skipn_nth_cons' _ _ _ Hg), List.firstn_skipn; reflexivity).
          assert (Lk : List.length (List.firstn kk gs) = kk) by (rewrite List.length_firstn; lia).
          pose proof (IH ltac:(lia)) as IHk.
          rewrite (firstn_S_snoc _ _ _ Hg).
          set (gs1 := List.firstn kk gs) in *.
          destruct g as [B0 | t].
          - rewrite cargs_nrec_snoc; cbv beta iota; rewrite Nat.add_0_r.
            rewrite ihs_ctx_aux_app; cbn [ihs_ctx_aux List.app]; exact IHk.
          - set (gs2 := List.skipn (S kk) gs) in *.
            rewrite (branch_context_recursive_results_at_recursive_argument gs1 t gs2 Heq0), cargs_nrec_snoc; cbv beta iota.
            set (ls := shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t) in *.
            set (jr := cargs_nrec D gs1) in *.
            destruct (rec_results_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir gs1 t gs2 Heq0)
              as (v & v' & rs & rs' & ih1 & ih1' & ih2 & ih2' & Hv & Hv' & Eih & Eih' & Lih1 & Lih1' & Lrs & Lrs' & Hrih).
            destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq0) as (x & x' & Hx & Hx' & Hrr).
            rewrite Hv in Hx; injection Hx as <-; rewrite Hv' in Hx'; injection Hx' as <-.
            assert (Ef1 : List.firstn jr ihs = ih1) by (rewrite Eih; apply firstn_app_exact; exact Lih1).
            assert (Ef1' : List.firstn jr ihs' = ih1') by (rewrite Eih'; apply firstn_app_exact; exact Lih1').
            rewrite Ef1, Ef1' in IHk.
            assert (Ef2 : List.firstn (jr + List.length (shape_leaves (rview_leaves D) 0 t)) ihs = ih1 ++ rs).
            { rewrite Eih, List.app_assoc; apply firstn_app_exact; rewrite List.length_app; lia. }
            assert (Ef2' : List.firstn (jr + List.length (shape_leaves (rview_leaves D) 0 t)) ihs' = ih1' ++ rs').
            { rewrite Eih', List.app_assoc; apply firstn_app_exact; rewrite List.length_app; lia. }
            rewrite Ef2, Ef2'.
            set (E0 := ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs1) in *.
            assert (LE : List.length E0 = jr) by apply length_ihs_ctx_aux.
            assert (Lls : List.length ls = List.length (shape_leaves (rview_leaves D) 0 t)) by apply length_shape_leaves.
            rewrite List.rev_app_distr; apply per_tele_args_app_intro; [ rewrite List.length_rev; lia | exact IHk |].
            (** The leaf paths of the argument, one at a time. *)
            rewrite Lk in Hv, Hv', Hrr, Hrih.
            assert (Hsplit : forall (Y ws : list domain) w (ihq : list domain), List.nth_error ws kk = Some w -> List.length ws = List.length gs ->
                       (Y ++ ws) ++ ihq = Y ++ List.firstn kk ws ++ w :: List.skipn (S kk) ws ++ ihq).
            { intros * Hw Lw.
              pose proof (List.firstn_skipn kk ws) as Hfs; rewrite (skipn_nth_cons' _ _ _ Hw) in Hfs.
              rewrite <- Hfs at 1; rewrite <- !List.app_assoc; reflexivity. }
            assert (Lf : forall ws : list domain, List.length ws = List.length gs -> List.length (List.firstn kk ws) = List.length gs1)
              by (intros; rewrite List.length_firstn; lia).
            assert (Ls : forall ws : list domain, List.length ws = List.length gs -> List.length (List.skipn (S kk) ws) = List.length gs2)
              by (intros; unfold gs2; rewrite !List.length_skipn; lia).
            set (K := List.length (cargs_nonrec gs1)).
            assert (Hnv : forall ws, List.length ws = List.length gs -> List.firstn K (nonrec_arg_vals gs ws) = nonrec_arg_vals gs1 (List.firstn kk ws)).
            { intros ws Lw; rewrite Heq0 in Lw |- *; rewrite <- Lk; exact (nonrec_arg_vals_firstn _ _ _ Lw). }
            assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq0, cargs_nonrec_app, List.length_app; lia).
            assert (Hpk : tele_prefix_rel (ar k X c) K (nonrec_arg_vals gs1 (List.firstn kk vs)) (nonrec_arg_vals gs1 (List.firstn kk vs'))).
            { rewrite <- (Hnv vs Lv), <- (Hnv vs' Lv'); apply tele_prefix_rel_of_full with (T := cargs_nonrec gs); [ exact Har | exact HKl ]. }
            assert (Hlsn : forall n, n <= List.length ls ->
                       per_tele_args (List.rev (leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) jr (List.firstn n ls)))
                         (env_tele (env_tele B1 TB (X ++ vs)) (List.rev E0) ih1) (env_tele (env_tele B2 TB (X' ++ vs')) (List.rev E0) ih1')
                         (List.firstn n rs) (List.firstn n rs')).
            { intros n; induction n as [| n IHn]; intros Hn; [ cbn; constructor |].
              destruct (nth_error_lt_some' ls n ltac:(lia)) as [l Hl0].
              rewrite (leaves_ctx_firstn_S _ _ _ _ _ _ _ Hl0); cbn [List.rev].
              assert (Hn1 : n < List.length rs) by lia.
              destruct (nth_error_lt_some' rs n Hn1) as [r1 Hr1]; destruct (nth_error_lt_some' rs' n ltac:(lia)) as [r2 Hr2].
              rewrite (firstn_S_snoc _ _ _ Hr1), (firstn_S_snoc _ _ _ Hr2).
              pose proof (IHn ltac:(lia)) as IHn'.
              (** The context of the leaf's entry. *)
              set (Er := leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) jr (List.firstn n ls) ++ E0).
              pose proof (leaf_pre_sem gs1 t gs2 Heq0 n l Hl0) as HCtx2.
              rewrite (leaves_ctx_firstn_S _ _ _ _ _ _ _ Hl0) in HCtx2; cbn [List.app] in HCtx2.
              rewrite List.app_assoc in HCtx2; fold Er in HCtx2.
              destruct (rel_ctx_wf_ass_inv HCtx2) as (ST & HST & HT0).
              destruct (rel_type_of_sort_at (sort_kind_type_sort _ _ HST)) as [jT HjT]; pose proof (HjT _ _ _ HT0) as HT.
              assert (HCtx : ⊨ Er ++ con_inst_ctx Γ p D Mk Us gs) by exact (rel_ctx_wf_tail HCtx2).
              assert (LEr : List.length Er = jr + n)
                by (unfold Er; rewrite List.length_app, length_leaves_ctx, List.length_firstn, LE; lia).
              destruct (rel_ctx_wf_per_ctx_env HCtx) as [RS HRS].
              assert (HΔeq : Er ++ con_inst_ctx Γ p D Mk Us gs = (Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) ++ Γ)
                by (rewrite con_inst_ctx_eq, List.app_assoc; reflexivity).
              set (ihp := ih1 ++ List.firstn n rs); set (ihp' := ih1' ++ List.firstn n rs').
              assert (Lihp : List.length ihp = jr + n) by (unfold ihp; rewrite List.length_app, List.length_firstn; lia).
              assert (Lihp' : List.length ihp' = jr + n) by (unfold ihp'; rewrite List.length_app, List.length_firstn; lia).
              assert (LXv : List.length (X ++ vs) = List.length TB)
                by (unfold TB; rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_im_nparams; lia).
              assert (LXv' : List.length (X' ++ vs') = List.length TB)
                by (unfold TB; rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_im_nparams; lia).
              assert (HEp : RS (env_tele B1 (List.rev (Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)) ((X ++ vs) ++ ihp))
                               (env_tele B2 (List.rev (Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)) ((X' ++ vs') ++ ihp'))).
              { pose proof HRS as HRS'; rewrite HΔeq in HRS'; pose proof HCtx as HCtx'; rewrite HΔeq in HCtx'.
                eapply (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS' HCtx' HB12);
                  [ rewrite !List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams, LEr; lia |].
                rewrite List.rev_app_distr; apply per_tele_args_app_intro;
                  [ rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_im_nparams; lia | exact Hci |].
                unfold Er; rewrite List.rev_app_distr; unfold ihp, ihp'.
                apply per_tele_args_app_intro; [ rewrite List.length_rev; lia | exact IHk | exact IHn' ]. }
              destruct (rel_type_inversion_simple_at HRS HT _ _ HEp) as (ty & ty' & Et & Et' & [R HR]).
              destruct (per_univ_elem_to_nat _ _ _ _ HR) as [i0 Hi0].
              pose proof Et as EtF; pose proof Et' as EtF'.
              unfold Er in Et, Et'; rewrite !List.rev_app_distr in Et, Et'.
              rewrite (env_tele_app B1 TB _ (X ++ vs) ihp LXv) in Et; rewrite (env_tele_app B2 TB _ (X' ++ vs') ihp' LXv') in Et'.
              unfold ihp in Et; unfold ihp' in Et'.
              rewrite env_tele_app in Et by (rewrite List.length_rev; lia); rewrite env_tele_app in Et' by (rewrite List.length_rev; lia).
              apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ i0 R); [ rewrite List.length_rev, length_leaves_ctx, !List.length_firstn; lia | exact IHn'
                                                           | exact (mk_rel_mod_eval _ _ Et Et' Hi0) |].
              (** The sides, in the frame of the argument. *)
              rewrite (Hsplit X vs v ihp Hv Lv) in EtF, HEp.
              rewrite (Hsplit X' vs' v' ihp' Hv' Lv') in EtF', HEp.
              assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
              set (vtsE1 := tele_entries B1 (List.rev (Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU))
                              (X ++ List.firstn kk vs ++ v :: List.skipn (S kk) vs ++ ihp)) in *.
              set (vtsE2 := tele_entries B2 (List.rev (Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU))
                              (X' ++ List.firstn kk vs' ++ v' :: List.skipn (S kk) vs' ++ ihp')) in *.
              assert (HE1 : RS (env_extend_typed B1 vtsE1) (env_extend_typed B1 vtsE1))
                by (etransitivity; [ exact HEp | symmetry; exact HEp ]).
              assert (HE2 : RS (env_extend_typed B2 vtsE2) (env_extend_typed B2 vtsE2))
                by (etransitivity; [ symmetry; exact HEp | exact HEp ]).
              rewrite <- LEr in Lihp, Lihp'.
              assert (Lm1 : List.length vtsE1 = List.length Er + List.length gs + im_nn Mk)
                by (unfold vtsE1; rewrite tele_entries_length, <- (Hsplit X vs v ihp Hv Lv), !List.length_app; lia).
              assert (Lm2 : List.length vtsE2 = List.length Er + List.length gs + im_nn Mk)
                by (unfold vtsE2; rewrite tele_entries_length, <- (Hsplit X' vs' v' ihp' Hv' Lv'), !List.length_app; lia).
              destruct (side_w gs1 t gs2 Heq0 Er HCtx RS HRS B1 vtsE1 HB1 Lm1 HE1) as (w1 & Hw1 & HwU1 & Lw1).
              destruct (side_w gs1 t gs2 Heq0 Er HCtx RS HRS B2 vtsE2 HB2 Lm2 HE2) as (w2 & Hw2 & HwU2 & Lw2).
              (** The stored parameters and the arguments before, related to
                  themselves on each side. *)
              pose proof (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk X c gs HXX Hcon K _ _ HKl Hpk) as Hpk1.
              pose proof (trefl_r _ _ HMk _ _ HX) as HXX'.
              pose proof (args_prefix_rel_refl_r p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk X X' c gs K _ _ HX Hcon HKl Hpk)
                as Hpk2.
              pose proof (branch_entry_vals gs1 t gs2 Heq0 Er HCtx RS HRS B1 vtsE1 X (List.firstn kk vs) v (List.skipn (S kk) vs) ihp w1 HB1
                            (tele_entries_values _ _ _) LX (Lf _ Lv) (Ls _ Lv) Lihp HE1 Hw1 HwU1 Lw1) as Hv1.
              pose proof (branch_entry_vals gs1 t gs2 Heq0 Er HCtx RS HRS B2 vtsE2 X' (List.firstn kk vs') v' (List.skipn (S kk) vs') ihp' w2 HB2
                            (tele_entries_values _ _ _) LX' (Lf _ Lv') (Ls _ Lv') Lihp' HE2 Hw2 HwU2 Lw2) as Hv2.
              pose proof (branch_entry_frame gs1 t gs2 Heq0 Er HCtx) as Hf.
              destruct (length_rec_ps D HD k Mk HMk c gs gs1 t gs2 Hcon Heq0) as (Mj & HMj & _).
              assert (HRS0 : EF (Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) ++ Γ
                               ≈ (Er ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU) ++ Γ ∈ per_ctx_env ↘ RS)
                by (rewrite <- HΔeq; exact HRS).
              assert (Hl1 : List.nth_error (shape_leaves (rview_leaves D) (im_nn Mk + K + 0) (ptyp_skip 0 t)) n = Some l).
              { replace (im_nn Mk + K + 0) with (pat_nargs (cargs_pat gs1) + im_nn Mk); [ exact Hl0 |].
                rewrite pat_nargs_cargs_pat, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele; fold K; lia. }
              rewrite <- (List.nth_error_nth _ _ d_True Hr1), <- (List.nth_error_nth _ _ d_True Hr2).
              exact (leaf_walk_sem (S (ptyp_mem t)) k Mk c gs gs1 t gs2 HMk Hcon Heq0 Mj HMj (fun _ => Nat.lt_succ_diag_r _) _ _ _ _ Hf (leaf_term_var _) RS HRS0
                       X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv1 Hv2 I I HXX HX Hpk1 Hpk _ 0 nil nil v v' rs rs' (Nat.le_0_l _) eq_refl eq_refl
                       (List.Forall_nil _) (List.Forall_nil _)
                       ltac:(apply tele_prefix_rel_nil) ltac:(apply eval_apps_nil) ltac:(apply eval_apps_nil)
                       ltac:(intros ? ? Hj; cbn in Hj; lia) ltac:(intros ? ? Hj; cbn in Hj; lia)
                       ltac:(cbn [List.map List.firstn]; rewrite !List.app_nil_r; exact Hrr)
                       ltac:(cbn [List.map List.firstn]; rewrite !List.app_nil_r; exact Hrih)
                       ltac:(rewrite Lrs; reflexivity) ltac:(rewrite Lrs'; reflexivity) n l Hl1 ty ty' i0 R
                       ltac:(rewrite LEr; exact EtF) ltac:(rewrite LEr; exact EtF') Hi0). }
            replace rs with (List.firstn (List.length ls) rs) by (apply List.firstn_all2; lia).
            replace rs' with (List.firstn (List.length ls) rs') by (apply List.firstn_all2; lia).
            replace (leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) jr ls)
              with (leaves_ctx ak_relevant (im_nn Mk) As Us (List.length gs) (cargs_pat gs1) jr (List.firstn (List.length ls) ls))
              by (rewrite List.firstn_all; reflexivity).
            apply Hlsn; reflexivity.
        Qed.

        (** The environments of the branch's context at such arguments and
            recursive results. *)
        Lemma canonical_bctx : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
            forall X X' vs vs' ihs ihs',
            tele_rel (nr k) T X X' ->
            tele_rel (ar k X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
            con_args_rel p D (admissible_index_at D u0 nr) nr ar dr k u0 u0 X X' T gs vs vs' ->
            rec_results_rel D dr Rel k u0 u0 X X' T gs vs vs' ihs ihs' ->
            forall RB, EF elim_bctx ak_relevant p D Mk gs As Us ++ Γ ≈ elim_bctx ak_relevant p D Mk gs As Us ++ Γ ∈ per_ctx_env ↘ RB ->
            RB (env_tele B1 (List.rev (elim_bctx ak_relevant p D Mk gs As Us)) (X ++ vs ++ ihs))
               (env_tele B2 (List.rev (elim_bctx ak_relevant p D Mk gs As Us)) (X' ++ vs' ++ ihs')).
        Proof.
          intros B1 B2 HB1 HB2 * HX Har Hia Hir RB HRB.
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
          assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
          destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
          destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
          assert (Eb : elim_bctx ak_relevant p D Mk gs As Us
                       = ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs
                         ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) τU)
            by (apply (List.app_inv_tail Γ); rewrite branch_context_split, con_inst_ctx_eq, List.app_assoc; reflexivity).
          pose proof HX as HX0; rewrite tele_rel_iff in HX0; destruct HX0 as (LX & LX' & _).
          unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
          destruct (us_class B1 HB1) as (u1 & Hu1 & H10); destruct (us_class B2 HB2) as (u2 & Hu2 & H20).
          pose proof (closed_args_tele_args k Mk c gs HMk Hcon X X' vs vs' HX Har Hia (List.length gs) (le_n _)) as Hcg.
          rewrite List.firstn_all, !List.firstn_all2 in Hcg by lia.
          assert (HKa : all_assumptions ((cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D))
            by (rewrite <- List.app_assoc; fold (im_params D Mk); apply List.Forall_app; split;
                [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc k Mk HMk) ]).
          assert (HK : ⊨ (cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D)
            by (rewrite <- List.app_assoc; fold (im_params D Mk); exact HΨ).
          pose proof (branch_context_recursive_results_prefix_valid nil gs eq_refl) as HC0; cbn [ihs_ctx_aux List.app] in HC0; rewrite con_inst_ctx_eq in HC0.
          pose proof (canonical_gen _ HKa HK HC0 B1 B2 u1 u2 HB12 Hu1 Hu2 H10 H20 _ _ Hcg
                        ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia)) as Hci.
          pose proof (canonical_ihs B1 B2 HB1 HB2 _ _ _ _ _ _ HX Har Hia Hir Hci (List.length gs) (le_n _)) as Hih.
          rewrite List.firstn_all, !List.firstn_all2 in Hih by lia.
          rewrite branch_context_split, con_inst_ctx_eq, List.app_assoc in HRB.
          pose proof HB as HB'; fold As in HB'; rewrite branch_context_split, con_inst_ctx_eq, List.app_assoc in HB'.
          rewrite Eb, (List.app_assoc X), (List.app_assoc X').
          eapply (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRB HB' HB12);
            [ rewrite !List.length_app, length_ihs_ctx_aux, length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams; lia |].
          rewrite List.rev_app_distr; apply per_tele_args_app_intro;
            [ rewrite List.length_rev, length_tele_sub, !List.length_app, length_cargs_ctx, length_im_nparams; lia | exact Hci | exact Hih ].
        Qed.

        (** *** The Branch's Type

            The branch's type is the motive at the substitution [τb] of the
            branch's context into the member's: the non-uniform parameters,
            and the constructor as the group reads it at them and the
            arguments. *)
        Let nb := (im_nn Mk + List.length gs + cargs_nrec D gs)%nat.
        Let Nb := vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk).
        Let Ab := vars_from (cargs_nrec D gs) (List.length gs).
        Let Ub := List.map (fun U => U[wk_shiftn nb]ʷ) Us.
        Let τb := sb_of_list (sb_of_wk (wk_shiftn nb))
                    (Nb ++ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Ub ++ Nb ++ Ab) :: nil).

        Lemma branch_type_eq : forall A0, elim_branch_type p D k Mk c gs A0 Us = A0[τb].
        Proof. reflexivity. Qed.

        Lemma branch_type_HB : ⊨ elim_bctx ak_relevant p D Mk gs As Us ++ Γ.
        Proof. exact HB. Qed.

        Lemma branch_type_wk : elim_bctx ak_relevant p D Mk gs As Us ++ Γ ⊨ʷ (wk_shiftn nb) : Γ.
        Proof.
          replace nb with (List.length (elim_bctx ak_relevant p D Mk gs As Us)) by (rewrite length_elim_bctx; unfold nb; lia).
          apply rel_wk_under_ctx_shiftn; exact branch_type_HB.
        Qed.

        Lemma branch_type_us : forall j U T0, List.nth_error Ub j = Some U ->
            List.nth_error (tele_insts (ind_uparams D) Id Ub) j = Some T0 -> elim_bctx ak_relevant p D Mk gs As Us ++ Γ ⊨ U : T0.
        Proof.
          intros j U' T' HU HT; unfold Ub in *.
          rewrite <- tele_insts_closed_wk in HT by (first [ exact Ua | exact (decl_uparams_closed D Hc) ]).
          apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T0 & HT & ->).
          exact (rel_exp_under_ctx_wk branch_type_wk (HUs _ _ _ HU HT)).
        Qed.

        Lemma branch_type_vars : forall τ, (forall y, y < ind_nu D -> sentry_exp (τ y) = (sentry_exp (τU y))[wk_shiftn nb]ʷ) ->
            forall j N T0, List.nth_error Nb j = Some N ->
              List.nth_error (tele_insts (im_nparams Mk) τ Nb) j = Some T0 ->
              elim_bctx ak_relevant p D Mk gs As Us ++ Γ ⊨ N : T0.
        Proof.
          set (IHs := ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs).
          set (Cs := tele_sub (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) τU)).
          set (Ns := tele_sub (im_nparams Mk) τU).
          assert (HBeq : elim_bctx ak_relevant p D Mk gs As Us ++ Γ = (IHs ++ Cs) ++ Ns ++ Γ) by (unfold elim_bctx; rewrite <- !List.app_assoc; reflexivity).
          assert (HlI : List.length IHs = cargs_nrec D gs) by (unfold IHs; apply length_ihs_ctx_aux).
          assert (HlC : List.length Cs = List.length gs) by (unfold Cs; rewrite length_tele_sub, length_cargs_ctx; reflexivity).
          intros τ Hτ j N T0 HN HT.
          unfold Nb in HN, HT.
          replace (vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk))
            with (vars_from (List.length (IHs ++ Cs)) (List.length (im_nparams Mk))) in HN, HT
            by (rewrite List.length_app, HlI, HlC, length_im_nparams; reflexivity).
          destruct (vars_tele_lookup (IHs ++ Cs) (im_nparams Mk) τU τ Γ (ind_nu D)
                      (decl_closed_nparams_ass D Hc _ _ HMk) (decl_nparams_mvc _ _ _ Hdt _ _ HMk) (decl_closed_nparams_scoped D Hc _ _ HMk)
                      ltac:(intros y Hy; rewrite Hτ by exact Hy; rewrite List.length_app, HlI, HlC, length_im_nparams; unfold nb;
                            f_equal; f_equal; lia)
                      _ _ _ HN HT) as (x & -> & Hx).
          rewrite HBeq; apply valid_exp_under_ctx_vlookup; [ exact Hx | rewrite <- HBeq; exact branch_type_HB ].
        Qed.

        (** The uniform parameters, the non-uniform ones and the arguments
            the branch's type reads are scoped by the branch's context. *)
        Lemma branch_type_terms_scoped : List.Forall (exp_scoped (List.length (elim_bctx ak_relevant p D Mk gs As Us ++ Γ))) (Ub ++ Nb ++ Ab).
        Proof.
          assert (Lb : List.length (elim_bctx ak_relevant p D Mk gs As Us ++ Γ) = nb + List.length Γ)
            by (rewrite List.length_app, length_elim_bctx; unfold nb; lia).
          rewrite Lb; apply List.Forall_app; split; [| apply List.Forall_app; split ].
          - unfold Ub; apply List.Forall_map; eapply List.Forall_impl; [| exact HUss ].
            intros U HU; apply (exp_scoped_wk _ _ _ _ HU); intros z Hz; cbn; lia.
          - unfold Nb; apply vars_from_scoped; unfold nb; lia.
          - unfold Ab; apply vars_from_scoped; unfold nb; lia.
        Qed.

        (** The constructor of the branch's type, in the branch's context. *)
        Lemma branch_type_con_valid : elim_bctx ak_relevant p D Mk gs As Us ++ Γ
            ⊨ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Ub ++ Nb ++ Ab) : ind_mty p D k Ub Nb.
        Proof.
          pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
          set (IHs := ihs_ctx_aux ak_relevant (rview_leaves D) (im_nn Mk) As Us (List.length gs) nil 0 gs).
          set (Cs := tele_sub (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) τU)).
          set (Ns := tele_sub (im_nparams Mk) τU).
          assert (HBeq : elim_bctx ak_relevant p D Mk gs As Us ++ Γ = (IHs ++ Cs) ++ Ns ++ Γ) by (unfold elim_bctx; rewrite <- !List.app_assoc; reflexivity).
          assert (HlI : List.length IHs = cargs_nrec D gs) by (unfold IHs; apply length_ihs_ctx_aux).
          apply (con_apps_ref_valid P p D HP HPD _ k Mk c gs Ub Nb Ab branch_type_HB HMk HrvK Hcon).
          + unfold Ub; rewrite List.length_map; exact HUl.
          + exact branch_type_us.
          + unfold Nb; apply length_vars_from.
          + apply (branch_type_vars (sb_of_list Id Ub)).
            intros y Hy; unfold Ub; rewrite sb_of_list_map by lia; reflexivity.
          + unfold Ab; apply length_vars_from.
          + intros j N T0 HN HT.
            unfold Ab in HN, HT.
            replace (vars_from (cargs_nrec D gs) (List.length gs)) with (vars_from (List.length IHs) (List.length (cargs_ctx p D Mk gs))) in HN, HT
              by (rewrite HlI, length_cargs_ctx; reflexivity).
            destruct (vars_tele_lookup IHs (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) τU) (sb_of_list Id (Ub ++ Nb)) (Ns ++ Γ) (im_np D Mk)
                        (cargs_ctx_aux_ass _ _ _ _ _) (cargs_ctx_mvc _ _ _ _ _ _ _ _ Hdt Hc HMk Hin)
                        (decl_closed_cargs_scoped D Hc _ _ _ _ _ HMk Hin)) with (k := j) (N := N) (T := T0)
              as (x & -> & Hx).
            * intros y Hy; rewrite length_cargs_ctx, HlI.
              destruct (Nat.lt_ge_cases y (im_nn Mk)) as [Hy1 | Hy1].
              -- unfold Nb; rewrite sb_of_list_app, sb_of_list_vars by lia; rewrite sb_qn_lt by exact Hy1; cbn; f_equal; lia.
              -- replace y with (List.length Nb + (y - im_nn Mk)) at 1 by (unfold Nb; rewrite length_vars_from; lia).
                 rewrite sb_of_list_app, sb_of_list_ge; unfold Ub; rewrite sb_of_list_map by (rewrite HUl; unfold im_np in *; lia).
                 rewrite sb_qn_ge by exact Hy1; rewrite <- sentry_exp_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold nb; lia.
            * exact HN.
            * exact HT.
            * rewrite HBeq, <- List.app_assoc; apply valid_exp_under_ctx_vlookup; [ exact Hx | rewrite List.app_assoc, <- HBeq; exact branch_type_HB ].
          + exact branch_type_terms_scoped.
        Qed.

        Lemma gsub_branch_type : gsub (elim_bctx ak_relevant p D Mk gs As Us ++ Γ) τb (elim_mctx p D k Mk Us ++ Γ).
        Proof.
          set (Ns := tele_sub (im_nparams Mk) τU).
          assert (HlN : List.length Ns = im_nn Mk) by (unfold Ns; rewrite length_tele_sub, length_im_nparams; reflexivity).
          pose proof (gsub_wk _ _ _ branch_type_wk branch_type_HB HΓ) as Hg0.
          apply gsub_of_list; [ exact Hg0 | apply elim_mctx_ass; [ exact Hc | exact HMk ] | exact (HMall _ _ HMk)
                              | unfold Nb; rewrite List.length_app, length_vars_from, length_elim_mctx; cbn; lia | |].
          2:{ pose proof branch_type_terms_scoped as Hs; apply List.Forall_app in Hs as [HsU Hs]; apply List.Forall_app in Hs as [HsN HsA].
              apply List.Forall_app; split; [ exact HsN | constructor; [| constructor ] ].
              apply exp_scoped_apps; split; [ cbn; exact I |].
              apply List.Forall_app; split; [ exact (im_pre_scoped D k Mk Ub _ Hc HMk ltac:(unfold Ub; rewrite List.length_map; exact HUl) HsU) |].
              apply List.Forall_app; split; assumption. }
          intros j N T0 HN HT.
          unfold elim_mctx in HT.
          change (ce_ass ?κ0 ?H0 :: ?R) with ((ce_ass κ0 H0 :: nil) ++ R) in HT.
          assert (Hrass : all_assumptions Ns) by (apply all_assumptions_sub, (decl_closed_nparams_ass D Hc _ _ HMk)).
          rewrite tele_insts_app in HT by (try exact Hrass; unfold Nb; rewrite length_vars_from; symmetry; exact HlN).
          fold τU Ns in HT.
          assert (Hl2 : List.length (tele_insts Ns (sb_of_wk (wk_shiftn nb)) Nb) = im_nn Mk)
            by (rewrite length_tele_insts by exact Hrass; unfold Nb; rewrite HlN, length_vars_from; lia).
          destruct (Nat.lt_ge_cases j (im_nn Mk)) as [Hk | Hk].
          - rewrite List.nth_error_app1 in HN by (unfold Nb; rewrite length_vars_from; lia); rewrite List.nth_error_app1 in HT by lia.
            unfold Ns in HT; rewrite tele_insts_tele_sub in HT.
            apply (branch_type_vars _ ltac:(intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; reflexivity) j); assumption.
          - rewrite List.nth_error_app2 in HN, HT by (rewrite ?Hl2; unfold Nb; rewrite ?length_vars_from; lia).
            unfold Nb in HN; rewrite length_vars_from in HN; rewrite Hl2 in HT.
            destruct (j - im_nn Mk) as [| j'] eqn:Hk'; cbn in HN, HT; [| destruct j'; discriminate ].
            injection HN as <-; unfold tele_insts in HT; cbn in HT; injection HT as <-.
            rewrite ind_head_inst by (try exact Hc; try exact HUl; unfold Nb; apply length_vars_from).
            rewrite (List.map_ext (fun U => U[sb_of_wk (wk_shiftn nb)]) (fun U => U[wk_shiftn nb]ʷ)) by (intros; apply exp_sub_of_wk);
              fold Ub.
            exact branch_type_con_valid.
        Qed.

        (** The branch's type is relevant at related environments of the
            branch's context: the motive is of a universe. *)
        Lemma branch_type_relevant_at : forall b, List.nth_error Bks k = Some b ->
            forall RB, EF elim_bctx ak_relevant p D Mk gs As Us ++ Γ ≈ elim_bctx ak_relevant p D Mk gs As Us ++ Γ ∈ per_ctx_env ↘ RB ->
            forall ρ ρ', RB ρ ρ' -> rel_typ_kind (elim_branch_type p D k Mk c gs (eb_motive b) Us) ρ ak_relevant.
        Proof.
          intros b Hb RB HRB ρ ρ' Hρ.
          pose proof (rel_exp_under_ctx_gsub gsub_branch_type (HAv _ _ _ HMk Hb)) as HTb.
          exact (rel_exp_of_typ_relevant_at HRB HTb _ _ Hρ).
        Qed.

        (** Nor is it [LevelSort]. *)
        Lemma branch_type_not_level_sort : forall b, List.nth_error Bks k = Some b ->
            rel_type_not_level_sort (elim_bctx ak_relevant p D Mk gs As Us ++ Γ) (elim_branch_type p D k Mk c gs (eb_motive b) Us).
        Proof.
          intros b Hb.
          exact (rel_exp_of_typ_not_level_sort (rel_exp_under_ctx_gsub gsub_branch_type (HAv _ _ _ HMk Hb))).
        Qed.

        Lemma eval_branch_type_args : forall B vX vvs vih, List.length vX = im_nn Mk -> List.length vvs = List.length gs ->
            List.length vih = cargs_nrec D gs ->
            ⟦ Nb ++ Ab ⟧* gc_deps ⍮ gc_stack ⍮ env_extend_typed B (vX ++ vvs ++ vih) ↘ List.map fst vX ++ List.map fst vvs.
        Proof.
          intros * LX Lvs Lih.
          apply eval_exps_app.
          - pose proof (eval_vars_from_args vX B (vvs ++ vih)) as H.
            rewrite List.length_app, LX, Lvs, Lih in H; unfold Nb; rewrite Nat.add_comm; exact H.
          - pose proof (eval_vars_from_args vvs (env_extend_typed B vX) vih) as H.
            rewrite Lvs, Lih, <- env_extend_typed_app in H; exact H.
        Qed.

        Lemma eval_branch_type : forall B vX vvs vih l RB,
            EF elim_bctx ak_relevant p D Mk gs As Us ++ Γ ≈ elim_bctx ak_relevant p D Mk gs As Us ++ Γ ∈ per_ctx_env ↘ RB ->
            RB (env_extend_typed B (vX ++ vvs ++ vih)) (env_extend_typed B (vX ++ vvs ++ vih)) ->
            List.length vX = im_nn Mk -> List.length vvs = List.length gs -> List.length vih = cargs_nrec D gs ->
            ⟦ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Ub ++ Nb ++ Ab) ⟧
              env_extend_typed B (vX ++ vvs ++ vih) ↘ l ->
            ⟦ τb : elim_mctx p D k Mk Us ++ Γ ⟧s env_extend_typed B (vX ++ vvs ++ vih)
              ↘ env_extend_tagged Γ (List.rev (elim_mctx p D k Mk Us)) (ctx_retag Γ B) (List.map fst vX ++ l :: nil).
        Proof.
          intros * HRB HE LX Lvs Lih El.
          assert (Lall : List.length (vX ++ vvs ++ vih) = nb) by (rewrite !List.length_app; unfold nb; lia).
          (** The base: past the branch's context, [B] retagged. *)
          assert (Hβ : ⟦ sb_of_wk (wk_shiftn nb) : Γ ⟧s env_extend_typed B (vX ++ vvs ++ vih) ↘ ctx_retag Γ B).
          { pose proof (@eval_sub_of_wk gc_deps gc_stack Γ (wk_shiftn nb) (env_extend_typed B (vX ++ vvs ++ vih)) (wk_mono_shiftn _)) as H.
            replace (⟪wk_shiftn nb⟫ (env_extend_typed B (vX ++ vvs ++ vih))) with B in H
              by (rewrite <- Lall; symmetry; apply eval_wk_shiftn_extend_typed).
            exact H. }
          (** The terms' values, the motive's context being relevant. *)
          destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMk)) as [RM HRM].
          assert (Lτ : List.length (Nb ++ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Ub ++ Nb ++ Ab) :: nil)
                       = List.length (elim_mctx p D k Mk Us))
            by (rewrite List.length_app, length_elim_mctx; unfold Nb; rewrite length_vars_from; cbn [List.length]; lia).
          destruct (sb_of_list_values_of_sub (elim_mctx p D k Mk Us) Γ _ (sb_of_wk (wk_shiftn nb)) _ RB RM _ (ctx_retag Γ B)
                      (elim_mctx_ass p D k Mk Us Hc HMk) HRB HRM (mctx_evaluated k Mk HMk (HMall _ _ HMk))
                      (gsub_valid gsub_branch_type) Lτ HE Hβ) as (ms & Ems & Hτ & _).
          assert (Ems' : ⟦ Nb ++ apps (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (im_pre Mk Ub ++ Nb ++ Ab) :: nil ⟧*
                           gc_deps ⍮ gc_stack ⍮ env_extend_typed B (vX ++ vvs ++ vih) ↘ List.map fst vX ++ l :: nil).
          { pose proof (eval_branch_type_args B vX vvs vih LX Lvs Lih) as H.
            apply eval_exps_app_inv in H as (xs & ys & Exy & Exs & Eys).
            assert (Lxs : List.length xs = List.length (List.map fst vX))
              by (rewrite (eval_exps_length _ _ _ Exs), List.length_map; unfold Nb; rewrite length_vars_from; lia).
            destruct (app_split_eq _ _ _ _ (eq_sym Exy) Lxs) as [-> ->].
            apply eval_exps_app; [ exact Exs | econstructor; [ exact El | constructor ] ]. }
          pose proof (functional_eval_exps' _ _ _ _ Ems Ems') as ->; exact Hτ.
        Qed.

        (** The fields the branch's constructor term gives at an environment
            of the branch's context: the non-uniform parameters, and the
            arguments, a kept proof read back at each propositional one. *)
        Lemma branch_con_fields : forall B vX vvs vih RB,
            EF elim_bctx ak_relevant p D Mk gs As Us ++ Γ ≈ elim_bctx ak_relevant p D Mk gs As Us ++ Γ ∈ per_ctx_env ↘ RB ->
            RB (env_extend_typed B (vX ++ vvs ++ vih)) (env_extend_typed B (vX ++ vvs ++ vih)) ->
            List.length vX = im_nn Mk -> List.length vvs = List.length gs -> List.length vih = cargs_nrec D gs ->
            exists vsp, List.length vsp = List.length gs /\
              eval_field_vals gc_deps gc_stack (List.skipn (ind_nu D) (con_kinds D Mk gs)) (Nb ++ Ab)
                (env_extend_typed B (vX ++ vvs ++ vih)) (List.map fst vX ++ vsp) /\
              (forall j v v', List.nth_error (List.map fst vvs) j = Some v -> List.nth_error vsp j = Some v' ->
                 v = v' \/ (proof_readable v' /\ con_arg_kind Mk c j = ak_propositional)).
        Proof.
          intros * HRB HE LX Lvs Lih.
          set (E := env_extend_typed B (vX ++ vvs ++ vih)) in *.
          set (rs := List.skipn (ind_nu D) (con_kinds D Mk gs)).
          pose proof (eval_branch_type_args B vX vvs vih LX Lvs Lih) as Hargs; fold E in Hargs.
          assert (LNA : List.length (Nb ++ Ab) = (im_nn Mk + List.length gs)%nat)
            by (unfold Nb, Ab; rewrite List.length_app, !length_vars_from; lia).
          assert (Hsr : forall j, j < im_nn Mk + List.length gs -> List.nth j rs ak_relevant = con_entry_kind D Mk c (ind_nu D + j)).
          { intros j Hj; unfold rs; rewrite List.nth_skipn, <- hd_skipn; apply (con_kinds_hd D Mk c gs Hcon); unfold im_np; lia. }
          destruct (Mctt.Core.Completeness.Records.Model.eval_field_vals_each (Nb ++ Ab) rs E) as [zs Hzs].
          { intros j M HM _; destruct (eval_exps_nth _ _ _ _ _ Hargs HM) as (m0 & _ & Em0); eauto. }
          pose proof (Mctt.Core.Completeness.Records.Model.eval_field_vals_length _ _ _ _ Hzs) as Lzs; rewrite LNA in Lzs.
          (** Each field: the value of its variable, or a kept proof of it. *)
          assert (Hfld : forall j M z, List.nth_error (Nb ++ Ab) j = Some M -> List.nth_error zs j = Some z ->
                    (evaluated_kind (con_entry_kind D Mk c (ind_nu D + j)) -> List.nth_error (List.map fst vX ++ List.map fst vvs) j = Some z) /\
                    (con_entry_kind D Mk c (ind_nu D + j) = ak_propositional -> proof_readable z)).
          { intros j M z HM Hz.
            pose proof (nth_error_lt_length _ _ _ HM) as Hj; rewrite LNA in Hj.
            destruct (Mctt.Core.Completeness.Records.Model.eval_field_vals_nth _ _ _ _ Hzs j M HM) as (z0 & Hz0 & Hr0 & Hp0).
            rewrite Hz in Hz0; injection Hz0 as <-.
            rewrite (Hsr j Hj) in Hr0, Hp0.
            split.
            - intros Hr; destruct (eval_exps_nth _ _ _ _ _ Hargs HM) as (m0 & Hm0 & Em0).
              pose proof (functional_eval_exp _ _ _ _ (Hr0 Hr) Em0) as ->; exact Hm0.
            - intros Hp; rewrite (Hp0 Hp).
              assert (HMs : exp_free_bound M <= List.length (elim_bctx ak_relevant p D Mk gs As Us ++ Γ)).
              { apply exp_scoped_free_bound.
                pose proof branch_type_terms_scoped as Hs; apply List.Forall_app in Hs as [_ Hs].
                exact (proj1 (List.Forall_forall _ _) Hs M (List.nth_error_In _ _ HM)). }
              exact (proj1 (per_ctx_env_kept_proof_readable _ _ _ M HRB HMs _ _ HE)). }
          exists (List.skipn (im_nn Mk) zs); split; [ rewrite List.length_skipn; lia | split ].
          - replace (List.map fst vX ++ List.skipn (im_nn Mk) zs) with zs; [ exact Hzs |].
            rewrite <- (List.firstn_skipn (im_nn Mk) zs) at 1; f_equal.
            apply (List.nth_ext _ _ d_prop d_prop); [ rewrite List.length_firstn, List.length_map; lia |].
            intros i Hi; rewrite List.length_firstn in Hi.
            destruct (nth_error_lt_some' zs i ltac:(lia)) as [z Hz].
            destruct (nth_error_lt_some' (Nb ++ Ab) i ltac:(lia)) as [M HM].
            assert (Er : evaluated_kind (con_entry_kind D Mk c (ind_nu D + i)))
              by (unfold con_entry_kind, im_np; destruct (Nat.ltb_spec (ind_nu D + i) (im_nn Mk + ind_nu D));
                  [ apply tele_param_kind_evaluated | lia ]).
            pose proof (proj1 (Hfld i M z HM Hz) Er) as Hn.
            rewrite List.nth_error_app1 in Hn by (rewrite List.length_map; lia).
            assert (Hzf : List.nth_error (List.firstn (im_nn Mk) zs) i = Some z)
              by (rewrite List.nth_error_firstn; destruct (Nat.ltb_spec i (im_nn Mk)); [ exact Hz | lia ]).
            rewrite (List.nth_error_nth _ _ d_prop Hzf), (List.nth_error_nth _ _ d_prop Hn); reflexivity.
          - intros j v v' Hv Hv'.
            rewrite List.nth_error_skipn in Hv'.
            pose proof (nth_error_lt_length _ _ _ Hv) as Hjl; rewrite List.length_map in Hjl.
            destruct (nth_error_lt_some' (Nb ++ Ab) (im_nn Mk + j) ltac:(lia)) as [M HM].
            destruct (Hfld _ M v' HM Hv') as [Hrel Hprf].
            unfold con_entry_kind, im_np in Hrel, Hprf.
            destruct (Nat.ltb_spec (ind_nu D + (im_nn Mk + j)) (im_nn Mk + ind_nu D)) as [Hlt | _]; [ lia |].
            replace (ind_nu D + (im_nn Mk + j) - (im_nn Mk + ind_nu D)) with j in Hrel, Hprf by lia.
            destruct (evaluated_kind_or_propositional (con_arg_kind Mk c j)) as [Er | Er].
            + left; pose proof (Hrel Er) as Hn.
              rewrite List.nth_error_app2 in Hn by (rewrite List.length_map; lia).
              rewrite List.length_map, LX in Hn; replace (im_nn Mk + j - im_nn Mk) with j in Hn by lia; congruence.
            + right; split; [ exact (Hprf Er) | exact Er ].
        Qed.

        (** The branch type's head relation is the motive's family at the
            constructor. *)
        Lemma branch_type_rel : forall b, List.nth_error Bks k = Some b -> forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
            forall u u' hd k' bs bs' vs vs' ihs ihs' vts1 vts2,
            G k u u' (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs')
              (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
            rec_results_rel D dr Rel k u u' (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs') T gs vs vs' ihs ihs' ->
            List.map fst vts1 = List.skipn (im_unu D Mk) bs ++ vs ++ ihs ->
            List.map fst vts2 = List.skipn (im_unu D Mk) bs' ++ vs' ++ ihs' ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts1 ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts2 ->
            (per_head (elim_branch_type p D k Mk c gs (eb_motive b) Us) (elim_branch_type p D k Mk c gs (eb_motive b) Us)
               (env_extend_typed B1 vts1) (env_extend_typed B2 vts2)
             <~> Rel k (List.skipn (im_unu D Mk) bs) (d_con hd k' c (bs ++ vs))
                   (List.skipn (im_unu D Mk) bs') (d_con hd k' c (bs' ++ vs'))).
        Proof.
          intros b Hb B1 B2 HB1 HB2 * Hm Hir Hv1 Hv2 Hr1 Hr2.
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
          assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
          destruct (rec_results_rel_vs_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lv Lv'].
          destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
          destruct (ind_rel_con_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMk HrvK Hcon Lv Lv') as [Lbs Lbs'].
          set (X := List.skipn (im_unu D Mk) bs) in *; set (X' := List.skipn (im_unu D Mk) bs') in *.
          set (Y := List.firstn (im_unu D Mk) bs); set (Y' := List.firstn (im_unu D Mk) bs').
          assert (HbY : bs = Y ++ X) by (symmetry; apply List.firstn_skipn).
          assert (HbY' : bs' = Y' ++ X') by (symmetry; apply List.firstn_skipn).
          assert (LY : List.length Y = im_unu D Mk) by (unfold Y; rewrite List.length_firstn; lia).
          assert (LY' : List.length Y' = im_unu D Mk) by (unfold Y'; rewrite List.length_firstn; lia).
          assert (LX : List.length X = im_nn Mk) by (unfold X; rewrite List.length_skipn; lia).
          assert (LX' : List.length X' = im_nn Mk) by (unfold X'; rewrite List.length_skipn; lia).
          (** The element at the canonical bases, and its components. *)
          pose proof (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ u0 u0 _ _ _ _ Had Had Had Hm) as Hm0.
          destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMk HrvK Lbs)
            as (gs0 & bs1 & vs1 & Ez & Href & HX & Hcon0 & Lbs1 & _ & _ & Har & Hia).
          rewrite Hcon in Hcon0; injection Hcon0 as <-.
          injection Ez as Ez.
          destruct (app_split_eq _ _ _ _ Ez ltac:(congruence)) as [<- <-].
          pose proof (rec_results_rebase _ _ _ _ _ _ _ _ _ _ _ Hia Hir) as Hir0.
          destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 HMk HrvK Lbs)
            as (gs0 & bs2 & vs2 & Ez0 & _ & _ & Hcon0 & Lbs2 & _ & _ & Har0 & Hia0).
          rewrite Hcon in Hcon0; injection Hcon0 as <-.
          injection Ez0 as Ez0.
          destruct (app_split_eq _ _ _ _ Ez0 ltac:(congruence)) as [<- <-].
          (** The branch's context at the two extensions. *)
          destruct (rel_ctx_wf_per_ctx_env HB) as [RB HRB].
          assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
          pose proof (canonical_bctx B1 B2 HB1 HB2 X X' vs vs' ihs ihs' HX Har0 Hia0 Hir0 RB HRB) as HEc.
          set (TB := List.rev (elim_bctx ak_relevant p D Mk gs As Us)) in *.
          assert (HBr : ⊨ List.rev TB ++ Γ) by (unfold TB; rewrite List.rev_involutive; exact HB).
          assert (HRBr : EF List.rev TB ++ Γ ≈ List.rev TB ++ Γ ∈ per_ctx_env ↘ RB) by (unfold TB; rewrite List.rev_involutive; exact HRB).
          assert (HtaB : all_assumptions TB) by (apply List.Forall_rev; exact (elim_bctx_ass ak_relevant p D k Mk gs As Us Hc HMk)).
          assert (LTB : List.length TB = nb) by (unfold TB; rewrite List.length_rev, length_elim_bctx; unfold nb; lia).
          assert (Lw1 : List.length (X ++ vs ++ ihs) = List.length TB) by (rewrite !List.length_app, LTB; unfold nb; lia).
          assert (Lw2 : List.length (X' ++ vs' ++ ihs') = List.length TB) by (rewrite !List.length_app, LTB; unfold nb; lia).
          unfold env_tele in HEc.
          destruct (per_tele_args_of_env_extend _ _ _ _ HRΓ HBr HtaB HRBr _ _ _ _ ltac:(rewrite tele_entries_length; exact Lw1)
                      ltac:(rewrite tele_entries_length; exact Lw2) HEc) as [HB12 Hg].
          rewrite !tele_entries_values, <- Hv1, <- Hv2 in Hg.
          assert (Lv1 : List.length vts1 = List.length TB) by (rewrite <- (List.length_map fst), Hv1; exact Lw1).
          assert (Lv2 : List.length vts2 = List.length TB) by (rewrite <- (List.length_map fst), Hv2; exact Lw2).
          pose proof (tele_args_env_rel_typed _ _ _ _ HRΓ HBr HtaB HRBr _ _ _ _ HB12 Lv1 Lv2 Hg Hr1 Hr2) as HE.
          (** Each side's values, split. *)
          destruct (List.map_eq_app _ _ _ _ Hv1) as (vX1 & vr1 & -> & HvX1 & Hvr1).
          destruct (List.map_eq_app _ _ _ _ Hvr1) as (vvs1 & vih1 & -> & Hvvs1 & Hvih1).
          destruct (List.map_eq_app _ _ _ _ Hv2) as (vX2 & vr2 & -> & HvX2 & Hvr2).
          destruct (List.map_eq_app _ _ _ _ Hvr2) as (vvs2 & vih2 & -> & Hvvs2 & Hvih2).
          assert (LX1 : List.length vX1 = im_nn Mk) by (rewrite <- (List.length_map fst), HvX1; exact LX).
          assert (LX2 : List.length vX2 = im_nn Mk) by (rewrite <- (List.length_map fst), HvX2; exact LX').
          assert (Lvs1 : List.length vvs1 = List.length gs) by (rewrite <- (List.length_map fst), Hvvs1; exact Lv).
          assert (Lvs2 : List.length vvs2 = List.length gs) by (rewrite <- (List.length_map fst), Hvvs2; exact Lv').
          assert (Lih1 : List.length vih1 = cargs_nrec D gs) by (rewrite <- (List.length_map fst), Hvih1; exact Li).
          assert (Lih2 : List.length vih2 = cargs_nrec D gs) by (rewrite <- (List.length_map fst), Hvih2; exact Li').
          assert (HE11 : RB (env_extend_typed B1 (vX1 ++ vvs1 ++ vih1)) (env_extend_typed B1 (vX1 ++ vvs1 ++ vih1)))
            by (etransitivity; [ exact HE | symmetry; exact HE ]).
          assert (HE22 : RB (env_extend_typed B2 (vX2 ++ vvs2 ++ vih2)) (env_extend_typed B2 (vX2 ++ vvs2 ++ vih2)))
            by (etransitivity; [ symmetry; exact HE | exact HE ]).
          (** The constructor term's values and the type's substitution. *)
          destruct (rel_exp_under_ctx_simple_at_mty _ _ _ _ _ _ _ _ _ _ HMk HRB branch_type_con_valid _ _ HE) as (l1 & l2 & El1 & El2 & _).
          assert (HUb : List.length Ub = ind_nu D) by (unfold Ub; rewrite List.length_map; exact HUl).
          assert (LNA : List.length (Nb ++ Ab) = (im_nn Mk + List.length gs)%nat)
            by (unfold Nb, Ab; rewrite List.length_app, !length_vars_from; lia).
          destruct (branch_con_fields B1 vX1 vvs1 vih1 RB HRB HE11 LX1 Lvs1 Lih1) as (vsp & Lvsp & Ezs & Hmix).
          destruct (con_ref_apps_value P p D HP HPD k Mk c gs _ Ub (Nb ++ Ab) _ l1 HMk HrvK Hcon HUb Ezs LNA El1) as (cs1 & Lcs1 & El1v).
          rewrite Href in El1v; cbn [fst snd] in El1v.
          pose proof (eval_branch_type B1 vX1 vvs1 vih1 l1 RB HRB HE11 LX1 Lvs1 Lih1 El1) as Hev1.
          pose proof (eval_branch_type B2 vX2 vvs2 vih2 l2 RB HRB HE22 LX2 Lvs2 Lih2 El2) as Hev2.
          rewrite HvX1 in Hev1, El1v; rewrite HvX2 in Hev2.
          (** The element of the term, against the constructor's. *)
          pose proof (ind_rel_refl_l _ _ _ _ _ _ _ Hm0) as Hm00.
          rewrite HbY, <- List.app_assoc in Hm00.
          assert (Hll : G k u0 u0 X X (d_con hd k' c (Y ++ X ++ vs)) (d_con hd k' c (cs1 ++ X ++ vsp))).
          { apply (con_up_to_proofs k Mk c gs HMk Hcon HrvK hd k' Y cs1 X vs vsp Href LY Hm00 ltac:(lia) ltac:(lia)).
            intros j v v' Hv Hv'; rewrite <- Hvvs1 in Hv; exact (Hmix j v v' Hv Hv'). }
          subst l1.
          (** The chains. *)
          pose proof (HAv _ _ _ HMk Hb) as HAk.
          destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMk)) as [RM HRM].
          assert (HPM : PER RM) by (eapply per_env_PER; exact HRM).
          pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HAk HRB (gsub_valid gsub_branch_type) HE Hev1 Hev2) as ER1.
          pose proof (rel_sub_under_ctx_at' (gsub_valid gsub_branch_type) HRB HRM _ _ _ _ HE Hev1 Hev2) as L1.
          pose proof (L1 : RM _ _) as L1'.
          rewrite !env_extend_tagged_typed in L1.
          (** The term's environment of the motive, against the canonical one. *)
          destruct (mctx_rev_sem _ _ HMk RM HRM) as (HMr & HRMr & Hta).
          destruct (mctx_len _ _ HMk _ _ _ _ _ _ Hll) as [LXl _].
          assert (L11 : RM (env_extend_typed (ctx_retag Γ B1) (tagged_entries Γ (List.rev (elim_mctx p D k Mk Us)) (ctx_retag Γ B1)
                                                                 (X ++ d_con hd k' c (cs1 ++ X ++ vsp) :: nil)))
                           (env_extend_typed (ctx_retag Γ B1) (tagged_entries Γ (List.rev (elim_mctx p D k Mk Us)) (ctx_retag Γ B1)
                                                                 (X ++ d_con hd k' c (cs1 ++ X ++ vsp) :: nil))))
            by (etransitivity; [ exact L1 | symmetry; exact L1 ]).
          assert (Lq : List.length (List.rev (elim_mctx p D k Mk Us)) = List.length (X ++ d_con hd k' c (cs1 ++ X ++ vsp) :: nil))
            by (rewrite List.length_app in LXl |- *; cbn [List.length] in LXl |- *; lia).
          assert (Lt : List.length (tagged_entries Γ (List.rev (elim_mctx p D k Mk Us)) (ctx_retag Γ B1) (X ++ d_con hd k' c (cs1 ++ X ++ vsp) :: nil))
                       = List.length (List.rev (elim_mctx p D k Mk Us)))
            by (rewrite tagged_entries_length by exact Lq; symmetry; exact Lq).
          destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ Lt Lt L11) as [Hrd _].
          pose proof (isym _ _ _ _ _ _ _ Hll) as Hll'.
          destruct (mctx_readable _ _ HMk C1 C1 HC11 HC11 _ _ _ _ _ _ Hm00) as [Hrc _].
          pose proof (mctx_at_typed _ _ HMk _ _ (per_ctx_env_retag_left HRΓ _ _ HB1) HC11 RM HRM _ _ _ _ _ _ Hll' _ _
                        (tagged_entries_fst _ Γ (ctx_retag Γ B1) (X ++ d_con hd k' c (cs1 ++ X ++ vsp) :: nil) Lq)
                        (tele_entries_values _ _ _) Hrd Hrc) as Lc.
          pose proof (mctx_at _ _ HMk C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hm0) as L3.
          rewrite HbY, <- List.app_assoc in L3.
          assert (Ch : rel_chain RM (env_extend_tagged Γ (List.rev (elim_mctx p D k Mk Us)) (ctx_retag Γ B1)
                                       (X ++ d_con hd k' c (cs1 ++ X ++ vsp) :: nil)
                                     :: env_extend_tagged Γ (List.rev (elim_mctx p D k Mk Us)) (ctx_retag Γ B2)
                                          (X' ++ l2 :: nil)
                                     :: env_tele C1 (List.rev (elim_mctx p D k Mk Us)) (X ++ d_con hd k' c (Y ++ X ++ vs) :: nil)
                                     :: env_tele C2 (List.rev (elim_mctx p D k Mk Us)) (X' ++ d_con hd k' c (bs' ++ vs') :: nil) :: nil)).
          { apply rel_chain_cons; [ exact L1' |].
            apply rel_chain_cons; [ rewrite env_extend_tagged_typed; etransitivity; [ symmetry; exact L1 | exact Lc ] |].
            apply rel_chain_of_pair; exact L3. }
          pose proof (per_head_of_typ_resp HRM HAk _ _ _ _ Ch) as ER2.
          rewrite branch_type_eq; unfold Rel; rewrite (blocks_motives_nth _ _ _ Hb), (mctx_tele_at _ _ HMk).
          rewrite HbY, <- List.app_assoc.
          etransitivity; [ exact ER1 | exact ER2 ].
        Qed.

        (** The environments of the branch's context at a related
            constructor's components and recursive results, at any bases. *)
        Lemma canonical_bctx_elem : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
            forall u u' hd k' bs bs' vs vs' ihs ihs',
            G k u u' (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs')
              (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
            rec_results_rel D dr Rel k u u' (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs') T gs vs vs' ihs ihs' ->
            forall RB, EF elim_bctx ak_relevant p D Mk gs As Us ++ Γ ≈ elim_bctx ak_relevant p D Mk gs As Us ++ Γ ∈ per_ctx_env ↘ RB ->
            forall vts1 vts2,
            List.map fst vts1 = List.skipn (im_unu D Mk) bs ++ vs ++ ihs ->
            List.map fst vts2 = List.skipn (im_unu D Mk) bs' ++ vs' ++ ihs' ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts1 ->
            List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts2 ->
            RB (env_extend_typed B1 vts1) (env_extend_typed B2 vts2).
        Proof.
          intros B1 B2 HB1 HB2 * Hm Hir RB HRB vts1 vts2 Hv1 Hv2 Hr1 Hr2.
          destruct (rec_results_rel_vs_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lv Lv'].
          destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
          destruct (ind_rel_con_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMk HrvK Hcon Lv Lv') as [Lbs Lbs'].
          pose proof (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ u0 u0 _ _ _ _ Had Had Had Hm) as Hm0.
          destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMk HrvK Lbs)
            as (gs0 & bs1 & vs1 & Ez & _ & HX & Hcon0 & Lbs1 & _ & _ & Har & Hia).
          rewrite Hcon in Hcon0; injection Hcon0 as <-.
          injection Ez as Ez.
          destruct (app_split_eq _ _ _ _ Ez ltac:(congruence)) as [<- <-].
          pose proof (rec_results_rebase _ _ _ _ _ _ _ _ _ _ _ Hia Hir) as Hir0.
          destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 HMk HrvK Lbs)
            as (gs0 & bs2 & vs2 & Ez0 & _ & _ & Hcon0 & Lbs2 & _ & _ & Har0 & Hia0).
          rewrite Hcon in Hcon0; injection Hcon0 as <-.
          injection Ez0 as Ez0.
          destruct (app_split_eq _ _ _ _ Ez0 ltac:(congruence)) as [<- <-].
          pose proof (canonical_bctx B1 B2 HB1 HB2 _ _ vs vs' ihs ihs' HX Har0 Hia0 Hir0 RB HRB) as HEc.
          (** At the typed extensions: the context's relation reads the
              values only, the entries reading back. *)
          set (TB := List.rev (elim_bctx ak_relevant p D Mk gs As Us)) in *.
          assert (HBr : ⊨ List.rev TB ++ Γ) by (unfold TB; rewrite List.rev_involutive; exact HB).
          assert (HRBr : EF List.rev TB ++ Γ ≈ List.rev TB ++ Γ ∈ per_ctx_env ↘ RB) by (unfold TB; rewrite List.rev_involutive; exact HRB).
          assert (HtaB : all_assumptions TB) by (apply List.Forall_rev; exact (elim_bctx_ass ak_relevant p D k Mk gs As Us Hc HMk)).
          assert (LTB : List.length TB = nb) by (unfold TB; rewrite List.length_rev, length_elim_bctx; unfold nb; lia).
          pose proof HX as H0; rewrite tele_rel_iff in H0; destruct H0 as (LX & LX' & _).
          unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
          assert (Lw1 : List.length (List.skipn (im_unu D Mk) bs ++ vs ++ ihs) = List.length TB)
            by (rewrite !List.length_app, LTB, LX; unfold nb; lia).
          assert (Lw2 : List.length (List.skipn (im_unu D Mk) bs' ++ vs' ++ ihs') = List.length TB)
            by (rewrite !List.length_app, LTB, LX'; unfold nb; lia).
          unfold env_tele in HEc.
          destruct (per_tele_args_of_env_extend _ _ _ _ HRΓ HBr HtaB HRBr _ _ _ _ ltac:(rewrite tele_entries_length; exact Lw1)
                      ltac:(rewrite tele_entries_length; exact Lw2) HEc) as [HB12 Hg].
          rewrite !tele_entries_values, <- Hv1, <- Hv2 in Hg.
          assert (Lv1 : List.length vts1 = List.length TB) by (rewrite <- (List.length_map fst), Hv1; exact Lw1).
          assert (Lv2 : List.length vts2 = List.length TB) by (rewrite <- (List.length_map fst), Hv2; exact Lw2).
          exact (tele_args_env_rel_typed _ _ _ _ HRΓ HBr HtaB HRBr _ _ _ _ HB12 Lv1 Lv2 Hg Hr1 Hr2).
        Qed.
      End Branch.

      (** ** The Branches at the Links of an Elimination *)
      Section Links.
        Hypothesis (HBc : forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
                      ⊨ elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us ++ Γ).

        (** The middle link: the blocks [Bks] at [C1] against blocks [Bks']
            at [C2] whose branches are equal to theirs. *)
        Lemma branch_mid : forall Bks',
            (forall j Mj b b' c gs n B B', ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
               List.nth_error Bks' j = Some b' -> ind_con Mj c = Some gs ->
               brs_lookup (eb_brs b) c = Some (n, B) -> brs_lookup (eb_brs b') c = Some (n, B') ->
               elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B ≈ B' : elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
            forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k' ts ts', ind_member D j = Some Mj -> im_is_rview Mj = false ->
            List.nth_error Bks j = Some ba -> List.nth_error Bks' j = Some bb -> ind_con Mj c = Some gs ->
            brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
            G j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
            rec_results_rel D dr Rel j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (List.rev (im_nparams Mj)) gs
              vs vs' ihs ihs' ->
            List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts ->
            List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts' ->
            exists r r', ⟦ Ba ⟧ env_extend_typed C1 (List.combine (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts) ↘ r /\
              ⟦ Bb ⟧ env_extend_typed C2 (List.combine (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts') ↘ r' /\
              Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs)) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r'.
        Proof.
          intros Bks' HBB * HMj Hrv Hba Hbb Hcon HlBa HlBb Hm Hir Ht Ht'.
          assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
          pose proof (HBc j Mj c gs HMj Hcon) as HB.
          destruct (rel_ctx_wf_per_ctx_env HB) as [RB HRB].
          pose proof (combine_fst_eq _ _ (List.Forall2_length Ht)) as Hv1.
          pose proof (combine_fst_eq _ _ (List.Forall2_length Ht')) as Hv2.
          pose proof (Forall_combine_of_Forall2 _ _ _ Ht) as Hr1; pose proof (Forall_combine_of_Forall2 _ _ _ Ht') as Hr2.
          pose proof (canonical_bctx_elem j Mj c gs HMj Hcon HB Hrv C1 C2 HC11 HC21 _ _ _ _ _ _ _ _ _ _ Hm Hir RB HRB _ _ Hv1 Hv2 Hr1 Hr2)
            as HE.
          destruct (rel_exp_under_ctx_simple_at_evaluated HRB (HBB _ _ _ _ _ _ _ _ _ HMj Hba Hbb Hcon HlBa HlBb) _ _ HE
                      (rel_typ_evaluated_of_kind (branch_type_relevant_at j Mj c gs HMj Hcon HB Hrv ba Hba RB HRB _ _ HE) evaluated_kind_relevant))
            as (r & r' & Er & Er' & Hrr).
          exists r, r'; split; [ exact Er | split; [ exact Er' |] ].
          exact (proj1 (branch_type_rel j Mj c gs HMj Hcon HB Hrv ba Hba C1 C2 HC11 HC21 _ _ _ _ _ _ _ _ _ _ _ _ Hm Hir Hv1 Hv2 Hr1 Hr2 r r')
                   Hrr).
        Qed.

        (** An outer link: blocks [Bks0] moved by a semantic substitution
            [σ0] at [ρ0], against [Bks0] at the value [ρ0σ0] of [σ0], of the
            class of [C1]; their branches are of the types of [Bks]'s. *)
        Lemma branch_out : forall Bks0,
            (forall j Mj b b0 c gs n B0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
               List.nth_error Bks0 j = Some b0 -> ind_con Mj c = Some gs -> brs_lookup (eb_brs b0) c = Some (n, B0) ->
               n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat /\
               elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B0 : elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
            forall Γ' RΓ' σ0 ρ0 ρ0σ0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ ->
            RΓ' ρ0 ρ0 -> ⟦ σ0 : Γ ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
            forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k' ts ts', ind_member D j = Some Mj -> im_is_rview Mj = false ->
            List.nth_error (blocks_sub Bks0 σ0) j = Some ba -> List.nth_error Bks0 j = Some bb -> ind_con Mj c = Some gs ->
            brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
            G j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
            rec_results_rel D dr Rel j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (List.rev (im_nparams Mj)) gs
              vs vs' ihs ihs' ->
            List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts ->
            List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts' ->
            exists r r', ⟦ Ba ⟧ env_extend_typed ρ0 (List.combine (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts) ↘ r /\
              ⟦ Bb ⟧ env_extend_typed ρ0σ0 (List.combine (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts') ↘ r' /\
              Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs)) (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r'.
        Proof.
          intros Bks0 HB0s * HRΓ' Hσ0 Hρ0 Hev0 HρC * HMj Hrv Hba Hbb Hcon HlBa HlBb Hm Hir Ht Ht'.
          assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
          destruct (nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
          rewrite Hbb in Hb0; injection Hb0 as <-.
          rewrite eb_brs_sub in HlBa.
          destruct (brs_lookup_sub_inv _ _ _ _ _ HlBa) as (B0 & HlB0 & ->).
          rewrite HlBb in HlB0; injection HlB0 as <-.
          destruct (HBks _ _ HMj Hrv) as [b Hb].
          destruct (HB0s _ _ _ _ _ _ _ _ HMj Hb Hbb Hcon HlBb) as [-> HBv].
          pose proof (HBc j Mj c gs HMj Hcon) as HB.
          destruct (rel_ctx_wf_per_ctx_env HB) as [RB HRB].
          assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
          destruct (rec_results_rel_vs_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Lv Lv'].
          destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li _].
          destruct (ind_rel_con_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMj Hrv Hcon Lv Lv') as [Lbs _].
          set (X := List.skipn (im_unu D Mj) bs) in *; set (X' := List.skipn (im_unu D Mj) bs') in *.
          assert (LX : List.length X = im_nn Mj) by (unfold X; rewrite List.length_skipn; lia).
          pose proof (combine_fst_eq _ _ (List.Forall2_length Ht)) as Hv1.
          pose proof (combine_fst_eq _ _ (List.Forall2_length Ht')) as Hv2.
          pose proof (Forall_combine_of_Forall2 _ _ _ Ht) as Hr1; pose proof (Forall_combine_of_Forall2 _ _ _ Ht') as Hr2.
          set (vts1 := List.combine (X ++ vs ++ ihs) ts) in *; set (vts2 := List.combine (X' ++ vs' ++ ihs') ts') in *.
          pose proof (canonical_bctx_elem j Mj c gs HMj Hcon HB Hrv ρ0σ0 ρ0σ0 HρC HρC _ _ _ _ _ _ _ _ _ _ Hm Hir RB HRB
                        vts1 vts2 Hv1 Hv2 Hr1 Hr2) as HE.
          assert (HEl : RB (env_extend_typed ρ0σ0 vts1) (env_extend_typed ρ0σ0 vts1))
            by (etransitivity; [ exact HE | symmetry; exact HE ]).
          set (Bc := elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us) in *.
          assert (Ll : List.length vts1 = List.length (List.rev Bc))
            by (rewrite <- (List.length_map fst), Hv1; unfold Bc; rewrite List.length_rev, length_elim_bctx, !List.length_app; lia).
          assert (HBa : all_assumptions Bc) by (unfold Bc; exact (elim_bctx_ass ak_relevant p D j Mj gs _ Us Hc HMj)).
          assert (HBr : ⊨ List.rev (List.rev Bc) ++ Γ) by (rewrite List.rev_involutive; exact HB).
          assert (HRBr : EF List.rev (List.rev Bc) ++ Γ ≈ List.rev (List.rev Bc) ++ Γ ∈ per_ctx_env ↘ RB)
            by (rewrite List.rev_involutive; exact HRB).
          pose proof (proj2 (per_tele_args_of_env_extend _ _ _ _ HRΓ HBr (List.Forall_rev HBa) HRBr _ _ _ _ Ll Ll HEl)) as Hg.
          destruct (outer_exp_link Bc Γ Γ' RΓ' σ0 ρ0 ρ0σ0 _ Bb Bb HBa HB HBv HRΓ' Hσ0 Hρ0 Hev0 _ Hg
                      ltac:(rewrite List.length_rev in Ll; exact Ll) Hr1
                      (rel_typ_evaluated_of_kind (branch_type_relevant_at j Mj c gs HMj Hcon HB Hrv b Hb RB HRB _ _ HEl) evaluated_kind_relevant))
            as (RΔ & F & m & n0 & HRΔ & HF & Em & En0 & Hmn).
          assert (ERB : RΔ <~> RB) by (eapply per_ctx_env_right_irrel; eassumption).
          apply ERB in HF.
          destruct (rel_exp_under_ctx_simple_at_evaluated HRB HBv _ _ HE
                      (rel_typ_evaluated_of_kind (branch_type_relevant_at j Mj c gs HMj Hcon HB Hrv b Hb RB HRB _ _ HE) evaluated_kind_relevant))
            as (n1 & r' & En1 & Er' & Hnr).
          assert (n1 = n0) as -> by (eapply functional_eval_exp; eassumption).
          destruct (presup_rel_exp_under_ctx HBv (branch_type_not_level_sort j Mj c gs HMj Hcon HB Hrv b Hb)) as [iT HT].
          assert (ER : per_head (elim_branch_type p D j Mj c gs (eb_motive b) Us) (elim_branch_type p D j Mj c gs (eb_motive b) Us)
                         F (env_extend_typed ρ0σ0 vts1)
                       <~> per_head (elim_branch_type p D j Mj c gs (eb_motive b) Us) (elim_branch_type p D j Mj c gs (eb_motive b) Us)
                             (env_extend_typed ρ0σ0 vts1) (env_extend_typed ρ0σ0 vts2)).
          { apply (per_head_of_type_resp HRB HT).
            apply rel_chain_cons; [ exact HF |]. apply rel_chain_cons; [ exact HEl |]. apply rel_chain_of_pair; exact HE. }
          exists m, r'; split.
          { unfold Bc in Em; rewrite length_elim_bctx in Em.
            replace (im_nn Mj + List.length gs + cargs_nrec D gs) with (cargs_nrec D gs + List.length gs + im_nn Mj) by lia; exact Em. }
          split; [ exact Er' |].
          apply (proj1 (branch_type_rel j Mj c gs HMj Hcon HB Hrv b Hb ρ0σ0 ρ0σ0 HρC HρC _ _ _ _ _ _ _ _ _ _ _ _ Hm Hir Hv1 Hv2 Hr1 Hr2 m r')).
          eapply (per_head_trans _ _ _ _ _ _ HRB HT HE); [ apply ER; exact Hmn | exact Hnr ].
        Qed.
      End Links.

      (** ** The Motives at the Links of an Elimination

          An outer link: the motives of blocks [Bks0] equal to [Bks]'s,
          moved by [σ0] at [ρ0], against them at [ρ0σ0]. *)
      Lemma motive_link : forall Bks0,
          (forall j Mj b0, ind_member D j = Some Mj -> List.nth_error Bks0 j = Some b0 -> eb_binder_count b0 = S (im_nn Mj)) ->
          (forall j Mj b b0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> List.nth_error Bks0 j = Some b0 ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ eb_motive b0 : Typeω@iA) ->
          forall Γ' RΓ' σ0 ρ0 ρ0σ0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ ->
          RΓ' ρ0 ρ0 -> ⟦ σ0 : Γ ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
          forall j Mj ba bb u u' ns ns' m m' ts ts', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          List.nth_error (blocks_sub Bks0 σ0) j = Some ba -> List.nth_error Bks0 j = Some bb ->
          G j u u' ns ns' m m' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts' ->
          exists a a', ⟦ eb_motive ba ⟧ env_extend_typed ρ0 (List.combine (ns ++ m :: nil) ts) ↘ a /\
            ⟦ eb_motive bb ⟧ env_extend_typed ρ0σ0 (List.combine (ns' ++ m' :: nil) ts') ↘ a' /\
            DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns m ns' m'.
      Proof.
        intros Bks0 Hnm0 HA0s * HRΓ' Hσ0 Hρ0 Hev0 HρC * HMj Hrv Hba Hbb Hm Ht Ht'.
        destruct (nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        rewrite Hbb in Hb0; injection Hb0 as <-.
        rewrite eb_motive_sub, (Hnm0 _ _ _ HMj Hbb).
        destruct (HBks _ _ HMj Hrv) as [b Hb].
        exact (motive_out j Mj b HMj Hb Γ' RΓ' σ0 ρ0 ρ0σ0 (eb_motive bb) HRΓ' Hσ0 Hρ0 Hev0 HρC (HA0s _ _ _ _ HMj Hb Hbb) _ _ _ _ _ _ _ _ Hm Ht Ht').
      Qed.

      (** The left motives of such a link are not [LevelSort], not types of
          levels ([motive_out_not_level_sort]). *)
      Lemma motive_link_not_level_sort : forall Bks0,
          (forall j Mj b0, ind_member D j = Some Mj -> List.nth_error Bks0 j = Some b0 -> eb_binder_count b0 = S (im_nn Mj)) ->
          (forall j Mj b b0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> List.nth_error Bks0 j = Some b0 ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ eb_motive b0 : Typeω@iA) ->
          forall Γ' RΓ' σ0 ρ0 ρ0σ0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ ->
          RΓ' ρ0 ρ0 -> ⟦ σ0 : Γ ⟧s ρ0 ↘ ρ0σ0 -> RΓ ρ0σ0 C1 ->
          forall j Mj ba u u' ns ns' m m' ts a, ind_member D j = Some Mj -> im_is_rview Mj = false ->
          List.nth_error (blocks_sub Bks0 σ0) j = Some ba ->
          G j u u' ns ns' m m' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
          ⟦ eb_motive ba ⟧ env_extend_typed ρ0 (List.combine (ns ++ m :: nil) ts) ↘ a ->
          not_level_sort a /\ domain_kind a <> ak_level.
      (** Over all the section's variables, as [motive_link], so that the two
          are instantiated alike. *)
      Proof using All.
        intros Bks0 Hnm0 HA0s * HRΓ' Hσ0 Hρ0 Hev0 HρC * HMj Hrv Hba Hm Ht Ea.
        destruct (nth_error_blocks_sub_inv _ _ _ _ Hba) as (b0 & Hb0 & ->).
        rewrite eb_motive_sub, (Hnm0 _ _ _ HMj Hb0) in Ea.
        destruct (HBks _ _ HMj Hrv) as [b Hb].
        exact (motive_out_not_level_sort j Mj b HMj Hb Γ' RΓ' σ0 ρ0 ρ0σ0 (eb_motive b0) HRΓ' Hσ0 Hρ0 Hev0 HρC
                 (HA0s _ _ _ _ HMj Hb Hb0) _ _ _ _ _ _ _ _ Hm Ht Ea).
      Qed.

      (** The conditions on the blocks, moved by a substitution. *)
      Lemma blocks_sub_facts : forall Bks0 τ,
          (forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks0 j = Some b) ->
          (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks0 j = Some b -> eb_binder_count b = S (im_nn Mj)) ->
          (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks0 j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
          (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks0 j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) ->
          (forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error (blocks_sub Bks0 τ) j = Some b) /\
          (forall j Mj b, ind_member D j = Some Mj -> List.nth_error (blocks_sub Bks0 τ) j = Some b -> eb_binder_count b = S (im_nn Mj)) /\
          (forall j Mj b, ind_member D j = Some Mj -> List.nth_error (blocks_sub Bks0 τ) j = Some b -> brs_names (im_cons Mj) (eb_brs b)) /\
          (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error (blocks_sub Bks0 τ) j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat).
      Proof.
        intros * H1 H2 H3 H4; repeat split.
        - intros * HMj Hrv; destruct (H1 _ _ HMj Hrv) as [b Hb]; exists (eblock_sub b τ); rewrite nth_error_blocks_sub, Hb; reflexivity.
        - intros * HMj Hb; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->); rewrite eb_binder_count_sub; eauto.
        - intros * HMj Hb; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->); rewrite eb_brs_sub.
          apply brs_names_sub; eauto.
        - intros * HMj Hb Hcon Hin; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->); rewrite eb_brs_sub in Hin.
          destruct (brs_in_sub _ _ _ _ _ Hin) as [B0 Hin0]; eauto.
      Qed.

      (** ** The Elimination at the Three Links

          The eliminator of the member [m], its blocks [Bks] and its
          scrutinee [M], against one with blocks [Bks'] equal to them and a
          scrutinee [M'] equal to [M], carrying uniform parameters [Us']
          equal to [Us]: its values at the four environments of a semantic
          substitution, related at its type. *)
      Lemma elim_stage : forall Us' m Mm bm Bks' Ns M M',
          ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
          List.length Bks = ind_nblk D -> List.length Bks' = ind_nblk D ->
          (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_binder_count b = S (im_nn Mj)) ->
          (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks' j = Some b -> eb_binder_count b = S (im_nn Mj)) ->
          (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
          (forall j b b', List.nth_error Bks j = Some b -> List.nth_error Bks' j = Some b' ->
             List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
          (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) ->
          (forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
             ⊨ elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us ++ Γ) ->
          (forall j Mj b b', ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> List.nth_error Bks' j = Some b' ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ eb_motive b' : Typeω@iA) ->
          (forall j Mj b b' c gs n B B', ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             List.nth_error Bks' j = Some b' -> ind_con Mj c = Some gs ->
             brs_lookup (eb_brs b) c = Some (n, B) -> brs_lookup (eb_brs b') c = Some (n, B') ->
             elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B ≈ B' : elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
          List.length Ns = im_nn Mm ->
          gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) τU ++ Γ) ->
          gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D m Mm Us ++ Γ) ->
          Γ ⊨ M ≈ M' : ind_mty p D m Us Ns ->
          List.length Us' = ind_nu D -> List.Forall (exp_scoped (List.length Γ)) Us' ->
          (forall j U U' T, List.nth_error Us j = Some U -> List.nth_error Us' j = Some U' ->
             List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊨ U ≈ U' : T) ->
          forall Γ' RΓ' σ σ' ρ ρ', EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ' : Γ -> RΓ' ρ ρ' ->
          ⟦ σ : Γ ⟧s ρ ↘ C1 -> ⟦ σ' : Γ ⟧s ρ' ↘ C2 ->
          exists R, rel_exp ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ ρ C1
                      ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ' ρ' C2 (per_univ_elem iA R) /\
            rel_exp (a_elim ak_relevant p Us m Bks M) σ ρ C1 (a_elim ak_relevant p Us' m Bks' M') σ' ρ' C2 R.
      Proof.
        intros * HMm Hbm HLb HLb' HnmA HnmB HnaA HbrsF HarA HBc HAA HBB HNl HgN Hg HMM HUl' HUss' HUU
               * HRΓ' Hσ Hρ Hev Hev'.
        pose proof (block_of_nblk D Bks' Hdt HLb') as HBks'.
        pose proof (block_not_rview D Bks m Mm bm Hdt HLb HMm Hbm) as Hrvm.
        pose proof (rel_exp_under_ctx_refl_left HMM) as HMl.
        assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
        assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
        assert (HC21 : RΓ C2 C1) by (symmetry; exact HC12).
        assert (HC22 : RΓ C2 C2) by (etransitivity; [ exact HC21 | exact HC12 ]).
        assert (HPΓ' : PER RΓ') by (eapply per_env_PER; exact HRΓ').
        assert (Hρρ : RΓ' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
        assert (Hρ'ρ' : RΓ' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
        pose proof (decl_typed_nodup _ _ _ Hdt) as Hnd.
        (** The uniform parameters the four eliminators carry. *)
        destruct (closed_inst_cross (ind_uparams D) Γ Us Us' Ua Usem HΓ (valid_ind_decl_uparams_evaluated _ HD) HUl HUl' HUU
                    HUss HUss')
          as [HrU HlkU'].
        destruct (gsub_props gsub_U) as [HvU HlkU].
        (** The values of [Us'] at [C2], and of its instance. *)
        destruct (closed_instance_values_of_sub _ _ _ _ _ Ua Usem HΓ HRΓ HRU (valid_ind_decl_uparams_evaluated _ HD)
                    (rel_sub_under_ctx_refl_right HrU) HUl' C2 C2 HC22) as [u3 _ Hu3 _ _ Hs3 _].
        assert (Lu3 : List.length u3 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hu3); exact HUl').
        assert (Hu03 : RU (decl_env D u0) (decl_env D u3)).
        { destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ Hres].
          destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
          pose proof (rel_sub_under_ctx_at' HrU HRΓ HRUΓ _ _ _ _ HC12 (uniform_params_sub_eval C1 C1 u0 HC11 HUC) Hs3) as H.
          apply (Hres _ _ HRU HRUΓ) in H.
          rewrite !env_extend_tagged_typed in H.
          assert (Lw : List.length (List.rev (ind_uparams D)) = List.length u0) by (rewrite List.length_rev, u0_len; reflexivity).
          assert (Lu : List.length (List.rev (ind_uparams D)) = List.length u3) by (rewrite List.length_rev, Lu3; reflexivity).
          pose proof (closed_env_tele _ _ _ _ _ _ nil nil Ua Usem HRU
                        ltac:(rewrite tagged_entries_length by exact Lw; rewrite u0_len; reflexivity)
                        ltac:(rewrite tagged_entries_length by exact Lu; rewrite Lu3; reflexivity) H) as H0.
          rewrite !tagged_entries_fst in H0 by assumption; exact H0. }
        destruct (vals_sub_link Us HUl HvU HlkU Γ' RΓ' σ ρ C1 u0 HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HUC)
          as (w1 & Hw1 & Hw10).
        destruct (vals_sub_link Us' HUl' (rel_sub_under_ctx_refl_right HrU) HlkU' Γ' RΓ' σ' ρ' C2 u3 HRΓ'
                    (rel_sub_under_ctx_refl_right Hσ) Hρ'ρ' Hev' Hu3)
          as (w4 & Hw4 & Hw43).
        assert (Lw1 : List.length w1 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw1), List.length_map; exact HUl).
        assert (Lw4 : List.length w4 = ind_nu D) by (rewrite (eval_exps_length _ _ _ Hw4), List.length_map; exact HUl').
        assert (Hu30 : RU (decl_env D u3) (decl_env D u0)) by (symmetry; exact Hu03).
        assert (Hw40 : RU (decl_env D w4) (decl_env D u0)) by (etransitivity; [ exact Hw43 | exact Hu30 ]).
        pose proof (ups_ok w1 u0 Hw10 u0_env Lw1 u0_len) as Hok1.
        pose proof (ups_ok u0 u3 u0_env Hu30 u0_len Lu3) as Hok2.
        pose proof (ups_ok w4 u3 Hw40 Hu30 Lw4 Lu3) as Hok3.
        (** The scrutinee. *)
        destruct HMM as [RΓm HRΓm iM HMg].
        destruct (HMg _ _ HRΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as (RMe & HTm & Hor).
        pose proof HTm as [t1 t2 t3 t4 Et1 Et2 Et3 Et4 Htc].
        destruct (rel_exp_or_prop_evaluated HTm
                    (rel_typ_evaluated_of_kind (ex_intro _ t2 (conj Et2 (ind_mty_relevant _ _ _ _ _ _ _ _ HMm Et2))) evaluated_kind_relevant) Hor)
          as [m1 m2 m3 m4 Em1 Em2 Em3 Em4 Hmc].
        destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMm Hrvm Et2) as (cs2 & ns2 & _ & Ens2 & _).
        destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMm Hrvm Et3) as (cs3 & ns3 & _ & Ens3 & _).
        destruct Htc as (_ & Ht23 & _).
        destruct (scrut_rel m Mm HMm (HMall _ _ HMm) Ns HNl HgN C2 HC12 ns2 ns3 Ens2 Ens3 t2 t3 _ RMe Et2 Et3 Ht23)
          as [Hn23 ERM].
        destruct Hmc as (H12 & H23 & H34).
        apply ERM in H12, H23, H34.
        (** The blocks at the three links. *)
        assert (HAs : forall j Mj b b0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> List.nth_error Bks j = Some b0 ->
                   elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ eb_motive b0 : Typeω@iA).
        { intros * HMj Hb Hb0; rewrite Hb in Hb0; injection Hb0 as <-; exact (HAv _ _ _ HMj Hb). }
        assert (HB0s1 : forall j Mj b b0 c gs n B0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
                   List.nth_error Bks j = Some b0 -> ind_con Mj c = Some gs -> brs_lookup (eb_brs b0) c = Some (n, B0) ->
                   n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat /\
                   elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B0 : elim_branch_type p D j Mj c gs (eb_motive b) Us).
        { intros * HMj Hb Hb0 Hcon Hlb; rewrite Hb in Hb0; injection Hb0 as <-.
          split; [ exact (HarA _ _ _ _ _ _ _ HMj Hb Hcon (brs_lookup_in _ _ _ _ Hlb)) |].
          destruct (HBks' _ _ HMj (block_not_rview D Bks _ _ _ Hdt HLb HMj Hb)) as [b' Hb'].
          destruct (brs_lookup_pair _ _ _ _ _ (HbrsF _ _ _ Hb Hb') Hlb) as (kk & B' & _ & _ & Hlb').
          exact (rel_exp_under_ctx_refl_left (HBB _ _ _ _ _ _ _ _ _ HMj Hb Hb' Hcon Hlb Hlb')). }
        assert (HB0s3 : forall j Mj b b0 c gs n B0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
                   List.nth_error Bks' j = Some b0 -> ind_con Mj c = Some gs -> brs_lookup (eb_brs b0) c = Some (n, B0) ->
                   n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat /\
                   elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B0 : elim_branch_type p D j Mj c gs (eb_motive b) Us).
        { intros * HMj Hb Hb0 Hcon Hlb.
          destruct (brs_lookup_pair _ _ _ _ _ (eq_sym (HbrsF _ _ _ Hb Hb0)) Hlb) as (kk & B & _ & _ & HlB).
          split; [ exact (HarA _ _ _ _ _ _ _ HMj Hb Hcon (brs_lookup_in _ _ _ _ HlB)) |].
          exact (rel_exp_under_ctx_refl_right (HBB _ _ _ _ _ _ _ _ _ HMj Hb Hb0 Hcon HlB Hlb)). }
        assert (HnaB : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks' j = Some b -> brs_names (im_cons Mj) (eb_brs b)).
        { intros * HMj Hb'; destruct (HBks _ _ HMj (block_not_rview D Bks' _ _ _ Hdt HLb' HMj Hb')) as [b0 Hb0].
          exact (brs_names_fst' _ _ _ (HbrsF _ _ _ Hb0 Hb') (HnaA _ _ _ HMj Hb0)). }
        assert (HarB : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks' j = Some b -> ind_con Mj c = Some gs ->
                   In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat).
        { intros * HMj Hb' Hcon Hin; destruct (HBks _ _ HMj (block_not_rview D Bks' _ _ _ Hdt HLb' HMj Hb')) as [b0 Hb0].
          destruct (brs_in_fst _ _ _ _ _ (HbrsF _ _ _ Hb0 Hb') Hin) as (kk & B0 & _ & _ & Hin0).
          exact (HarA _ _ _ _ _ _ _ HMj Hb0 Hcon Hin0). }
        destruct (blocks_sub_facts Bks σ HBks HnmA HnaA HarA) as (HbA1 & HnmA1 & HnaA1 & HarA1).
        destruct (blocks_sub_facts Bks' σ' HBks' HnmB HnaB HarB) as (HbA3 & HnmA3 & HnaA3 & HarA3).
        (** Related indices and elements read back on each side. *)
        pose proof (fun j Mj u u' ns ns' x x' HMj (_ : im_is_rview Mj = false) Hm => mctx_idx_readable j Mj u u' ns ns' x x' HMj Hm)
          as Hidx.
        pose proof (per_ind_elim_all p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had iA ρ C1 (blocks_sub Bks σ) Bks w1 u0 Hok1
                      Rel HbA1 HBks HnmA1 HnmA HnaA1 HnaA HarA1 HarA Hnd
                      (motive_link Bks HnmA HAs Γ' RΓ' σ ρ C1 HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HC11)
                      (motive_link_not_level_sort Bks HnmA HAs Γ' RΓ' σ ρ C1 HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HC11) Hidx
                      (rneut_rel w1 u0 Hw10 u0_env Lw1 u0_len)
                      (branch_out HBc Bks HB0s1 Γ' RΓ' σ ρ C1 HRΓ' (rel_sub_under_ctx_refl_left Hσ) Hρρ Hev HC11)) as [PE1 _].
        pose proof (per_ind_elim_all p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had iA C1 C2 Bks Bks' u0 u3 Hok2
                      Rel HBks HBks' HnmA HnmB HnaA HnaB HarA HarB Hnd
                      (fun j Mj ba bb u u' ns ns' x x' ts ts' HMj _ Hba Hbb Hm Ht Ht' =>
                         motive_mid j Mj ba (eb_motive bb) HMj Hba (HAA _ _ _ _ HMj Hba Hbb) u u' ns ns' x x' ts ts' Hm Ht Ht')
                      (fun j Mj ba u u' ns ns' x x' ts a HMj _ Hba Hm Ht Ea =>
                         motive_mid_not_level_sort j Mj ba (eb_motive ba) HMj Hba (HAs _ _ _ _ HMj Hba Hba) u u' ns ns' x x' ts a Hm Ht Ea) Hidx
                      (rneut_rel u0 u3 u0_env Hu30 u0_len Lu3)
                      (branch_mid HBc Bks' HBB)) as [PE2 _].
        pose proof (per_ind_elim_all p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had iA ρ' C2 (blocks_sub Bks' σ') Bks' w4 u3 Hok3
                      Rel HbA3 HBks' HnmA3 HnmB HnaA3 HnaB HarA3 HarB Hnd
                      (motive_link Bks' HnmB HAA Γ' RΓ' σ' ρ' C2 HRΓ' (rel_sub_under_ctx_refl_right Hσ) Hρ'ρ' Hev' HC21)
                      (motive_link_not_level_sort Bks' HnmB HAA Γ' RΓ' σ' ρ' C2 HRΓ' (rel_sub_under_ctx_refl_right Hσ) Hρ'ρ' Hev' HC21) Hidx
                      (rneut_rel w4 u3 Hw40 Hu30 Lw4 Lu3)
                      (branch_out HBc Bks' HB0s3 Γ' RΓ' σ' ρ' C2 HRΓ' (rel_sub_under_ctx_refl_right Hσ) Hρ'ρ' Hev' HC21)) as [PE3 _].
        destruct (member_results_elim_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (PE1 _ _ _ _ _ _ _ H12 Had Had) HMm Hrvm)
          as (r1 & r2 & Er1 & Er2 & Hr12).
        destruct (member_results_elim_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (PE2 _ _ _ _ _ _ _ H23 Had Had) HMm Hrvm)
          as (r2' & r3 & Er2' & Er3 & Hr23).
        pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Er2' Er2) as ->.
        destruct (member_results_elim_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (PE3 _ _ _ _ _ _ _ (isym _ _ _ _ _ _ _ H34) Had Had) HMm Hrvm)
          as (r4 & r3' & Er4 & Er3' & Hr43).
        pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Er3' Er3) as ->.
        (** The type. *)
        pose proof (rel_exp_under_ctx_gsub Hg (HAv _ _ _ HMm Hbm)) as Hty; cbn [exp_sub] in Hty.
        destruct (rel_exp_of_typ_inversion Hty) as (R0 & HR0 & Hgen).
        pose proof (Hgen _ _ HRΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as Hgz.
        destruct Hgz as [z1 z2 z3 z4 Ez1 Ez2 Ez3 Ez4 Hzc]; apply rel_chain_relevant_univ in Hzc.
        destruct (rel_exp_implies_rel_typ (mk_rel_exp z1 z2 z3 z4 Ez1 Ez2 Ez3 Ez4 Hzc)) as [RT HT].
        exists RT; split; [ exact HT |].
        destruct HT as [y1 y2 y3 y4 Ey1 Ey2 Ey3 Ey4 Hyc].
        destruct Hyc as (_ & Hy23 & _).
        pose proof (per_head_iff Ey2 Ey3 Hy23) as ER1.
        (** The motive's instance at [C1] and [C2]: the terms' values, the
            motive's context being relevant. *)
        destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMm)) as [RM HRM].
        assert (Lτ : List.length (Ns ++ M :: nil) = List.length (elim_mctx p D m Mm Us))
          by (rewrite List.length_app, length_elim_mctx, HNl; cbn [List.length]; lia).
        destruct (sb_of_list_values_of_sub (elim_mctx p D m Mm Us) Γ Γ Id (Ns ++ M :: nil) RΓ RM C1 (ctx_retag Γ C1)
                    (elim_mctx_ass p D m Mm Us Hc HMm) HRΓ HRM (mctx_evaluated m Mm HMm (HMall _ _ HMm)) (gsub_valid Hg) Lτ HC11
                    (eval_sub_id _ _)) as (q1 & Eq1 & Hτ1 & _).
        assert (Eq1' : ⟦ Ns ++ M :: nil ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ ns2 ++ m2 :: nil)
          by (apply eval_exps_app; [ exact Ens2 | econstructor; [ exact Em2 | constructor ] ]).
        pose proof (functional_eval_exps' _ _ _ _ Eq1 Eq1') as ->.
        destruct (rel_exp_under_ctx_simple_at_mty _ _ _ _ _ _ _ _ _ _ HMm HRΓ HMl _ _ HC12) as (mx & my & Emx & Emy & Hmxy).
        assert (mx = m2) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (proj2 (per_head_iff Et2 Et3 Ht23 m2 my) Hmxy) as Hmy; apply ERM in Hmy.
        destruct (sb_of_list_values_of_sub (elim_mctx p D m Mm Us) Γ Γ Id (Ns ++ M :: nil) RΓ RM C2 (ctx_retag Γ C2)
                    (elim_mctx_ass p D m Mm Us Hc HMm) HRΓ HRM (mctx_evaluated m Mm HMm (HMall _ _ HMm)) (gsub_valid Hg) Lτ HC22
                    (eval_sub_id _ _)) as (q2 & Eq2 & Hτ2 & _).
        assert (Eq2' : ⟦ Ns ++ M :: nil ⟧* gc_deps ⍮ gc_stack ⍮ C2 ↘ ns3 ++ my :: nil)
          by (apply eval_exps_app; [ exact Ens3 | econstructor; [ exact Emy | constructor ] ]).
        pose proof (functional_eval_exps' _ _ _ _ Eq2 Eq2') as ->.
        pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ (HAv _ _ _ HMm Hbm) HRΓ (gsub_valid Hg) HC12 Hτ1 Hτ2) as ER2.
        pose proof (rel_resp m Mm HMm Hrvm _ _ _ _ _ _ ns2 m2 ns3 m3 ns2 m2 ns3 my H23 (isym _ _ _ _ _ _ _ H23) Hmy) as ER3.
        (** The instance's environments, against the canonical ones of the
            motive's family. *)
        assert (HPM : PER RM) by (eapply per_env_PER; exact HRM).
        pose proof (rel_sub_under_ctx_at' (gsub_valid Hg) HRΓ HRM _ _ _ _ HC12 Hτ1 Hτ2) as L1.
        pose proof (L1 : RM _ _) as L1'.
        rewrite !env_extend_tagged_typed in L1.
        destruct (mctx_rev_sem _ _ HMm RM HRM) as (HMr & HRMr & Hta).
        pose proof (ind_rel_refl_l _ _ _ _ _ _ _ H23) as M22'.
        destruct (mctx_len _ _ HMm _ _ _ _ _ _ M22') as [Ll _].
        assert (L11 : RM (env_extend_typed (ctx_retag Γ C1)
                            (tagged_entries Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C1) (ns2 ++ m2 :: nil)))
                         (env_extend_typed (ctx_retag Γ C1)
                            (tagged_entries Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C1) (ns2 ++ m2 :: nil))))
          by (etransitivity; [ exact L1 | symmetry; exact L1 ]).
        assert (Lt : List.length (tagged_entries Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C1) (ns2 ++ m2 :: nil))
                     = List.length (List.rev (elim_mctx p D m Mm Us)))
          by (rewrite tagged_entries_length by exact (eq_sym Ll); exact Ll).
        destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ Lt Lt L11) as [Hrd _].
        destruct (mctx_readable _ _ HMm C1 C1 HC11 HC11 _ _ _ _ _ _ M22') as [Hrc _].
        pose proof (mctx_at_typed _ _ HMm _ _ (per_ctx_env_retag_left HRΓ _ _ HC11) HC11 RM HRM _ _ _ _ _ _ M22' _ _
                      (tagged_entries_fst _ Γ (ctx_retag Γ C1) (ns2 ++ m2 :: nil) (eq_sym Ll))
                      (tele_entries_values _ _ _) Hrd Hrc) as Lc.
        pose proof (mctx_at _ _ HMm C1 C2 HC11 HC21 RM HRM _ _ _ _ _ _ Hmy) as L3.
        assert (Ch : rel_chain RM (env_extend_tagged Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C1) (ns2 ++ m2 :: nil)
                                   :: env_extend_tagged Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C2) (ns3 ++ my :: nil)
                                   :: env_tele C1 (List.rev (elim_mctx p D m Mm Us)) (ns2 ++ m2 :: nil)
                                   :: env_tele C2 (List.rev (elim_mctx p D m Mm Us)) (ns3 ++ my :: nil) :: nil)).
        { apply rel_chain_cons; [ exact L1' |].
          apply rel_chain_cons; [ rewrite env_extend_tagged_typed; etransitivity; [ symmetry; exact L1 | exact Lc ] |].
          apply rel_chain_of_pair; exact L3. }
        pose proof (per_head_of_typ_resp HRM (HAv _ _ _ HMm Hbm) _ _ _ _ Ch) as ER4.
        assert (Hfin : forall a b, Rel m ns2 m2 ns3 m3 a b -> RT a b).
        { intros a b H; apply ER1, ER2, ER4; apply ER3 in H; unfold Rel in H.
          rewrite (blocks_motives_nth _ _ _ Hbm), (mctx_tele_at _ _ HMm) in H; exact H. }
        pose proof (rel_per m Mm HMm Hrvm _ _ _ _ _ _ H23) as HPR.
        pose proof (tsym _ _ HMm _ _ Hn23) as Hn32.
        pose proof (ind_rel_idx_u0 _ _ _ _ _ _ _ _ _ _ HMm (ind_rel_refl_r _ _ _ _ _ _ _ H12) (trefl_r _ _ HMm _ _ Hn23) Hn32) as M32.
        pose proof (ind_rel_idx_u0 _ _ _ _ _ _ _ _ _ _ HMm (isym _ _ _ _ _ _ _ H23) Hn32 (trefl_l _ _ HMm _ _ Hn23)) as M22.
        apply (mk_rel_exp r1 r2 r3 r4).
        - rewrite exp_sub_elim; eapply eval_exp_elim; [ exact Hw1 | exact Em1 | exact Er1 ].
        - eapply eval_exp_elim; [ exact HUC | exact Em2 | exact Er2 ].
        - eapply eval_exp_elim; [ exact Hu3 | exact Em3 | exact Er3 ].
        - rewrite exp_sub_elim; eapply eval_exp_elim; [ exact Hw4 | exact Em4 | exact Er4 ].
        - apply rel_chain_cons; [ apply Hfin | apply rel_chain_cons; [ apply Hfin; exact Hr23 | apply rel_chain_of_pair; apply Hfin ] ].
          + apply (proj1 (rel_resp m Mm HMm Hrvm _ _ _ _ _ _ ns2 m1 ns3 m2 ns2 m2 ns3 m3 H12 M32 H23 r1 r2)); exact Hr12.
          + symmetry.
            apply (proj1 (rel_resp m Mm HMm Hrvm _ _ _ _ _ _ ns3 m4 ns2 m3 ns2 m2 ns3 m3 (isym _ _ _ _ _ _ _ H34) M22 H23 r4 r3)); exact Hr43.
      Qed.
    End Motives.
  End Base.
End GroupElim.

(** ** The Eliminator, Its Blocks, Uniform Parameters and Scrutinee Varying

    The semantic eliminator of a valid group [D] at [p], of the member [m],
    at its parameters [Ps], the blocks [Bks] at their motives, against one
    with blocks [Bks'] and parameters [Ps'] equal to them, and a scrutinee
    [M'] equal to [M]. *)
(** The eliminator at its uniform parameters [Us] and [Us'] and the
    non-uniform ones [Ns] of the scrutinee's type, the branches by
    constructor. *)
Theorem rel_exp_under_ctx_elim_at : forall VP p D, valid_groups VP -> VP p D ->
    forall Γ m Mm bm Bks Bks' Us Us' Ns M M' (i : nat),
    ⊨ Γ ->
    ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D -> List.length Bks' = ind_nblk D ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊨ U : T) ->
    List.Forall (exp_scoped (List.length Γ)) Us ->
    List.length Us' = ind_nu D -> List.Forall (exp_scoped (List.length Γ)) Us' ->
    (forall j U U' T, List.nth_error Us j = Some U -> List.nth_error Us' j = Some U' ->
       List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊨ U ≈ U' : T) ->
    List.length Ns = im_nn Mm ->
    (forall j N T, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T ->
       Γ ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ns ->
    Γ ⊨ M ≈ M' : ind_mty p D m Us Ns ->
    exp_scoped (List.length Γ) M ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk, ind_member D k = Some Mk -> ⊨ elim_mctx p D k Mk Us ++ Γ) ->
    (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       elim_mctx p D k Mk Us ++ Γ ⊨ eb_motive b ≈ eb_motive b' : Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> ⊨ elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b b' c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' -> ind_con Mk c = Some gs ->
       brs_lookup (eb_brs b) c = Some (n, B) -> brs_lookup (eb_brs b') c = Some (n, B') ->
       elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) Us ++ Γ ⊨ B ≈ B' : elim_branch_type p D k Mk c gs (eb_motive b) Us) ->
    Γ ⊨ a_elim ak_relevant p Us m Bks M ≈ a_elim ak_relevant p Us' m Bks' M' : (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)].
Proof.
  intros VP p D HP HPD * HΓ HMm Hbm HLb HLb' HUl HUs HUss HUl' HUss' HUU HNl HNs HNss HMM HMs HnmA HnmB HMall HAA HnaA HbrsF HBc HarA
         HBB'.
  pose proof (valid_groups_valid VP HP p D HPD) as Hvg.
  pose proof (valid_group_valid _ _ Hvg) as HD.
  pose proof (block_of_nblk D Bks (valid_group_typed _ _ Hvg) HLb) as HBks.
  pose proof (block_of_nblk D Bks' (valid_group_typed _ _ Hvg) HLb') as HBks'.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
  assert (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@i).
  { intros * HMj Hb; destruct (HBks' _ _ HMj (block_not_rview D Bks _ _ _ (valid_group_typed _ _ Hvg) HLb HMj Hb)) as [b' Hb'].
    exact (rel_exp_under_ctx_refl_left (HAA _ _ _ _ HMj Hb Hb')). }
  pose proof (gsub_ns VP p D HP HPD Γ HΓ _ m Mm HMm (HMall _ _ HMm) _ HNl HNs HNss) as HgN.
  pose proof (gsub_tau VP p D HP HPD Γ HΓ _ HUl m Mm HMm (HMall _ _ HMm) _ M HNl HNs (rel_exp_under_ctx_refl_left HMM)
                (proj2 (List.Forall_app _ _ _) (conj HNss (List.Forall_cons _ HMs (List.Forall_nil _))))) as Hg.
  refine (mk_rel_exp_under_ctx _ _ _ _ RΓ HRΓ i _).
  intros Γ' RΓ' HRΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HC12 : RΓ ρσ ρ'σ') by (eapply (rel_sub_under_ctx_at' Hσ HRΓ' HRΓ); eassumption).
  assert (HC11 : RΓ ρσ ρσ) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
  destruct (us_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU _ HUl HUs HUss ρσ ρσ HC11) as (u0 & u0' & Hu0 & Hu0' & _).
  destruct (elim_stage VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU _ HUl HUs HUss ρσ u0 HC11 Hu0 ρ'σ' HC12 Bks i HBks HMall HAv
              _ m Mm bm Bks' _ M M' HMm Hbm HLb HLb' HnmA HnmB HnaA HbrsF HarA HBc HAA HBB' HNl HgN Hg HMM HUl' HUss' HUU
              Γ' RΓ' σ σ' ρ ρ' HRΓ' Hσ Hρ Hev Hev') as (R & HT & HE).
  exists R; split; [ exact HT | right; exact HE ].
Qed.

Theorem rel_exp_under_ctx_elim_cong : forall VP p D, valid_groups VP -> VP p D ->
    forall Γ m Mm bm Bks Bks' Ps Ps' M M' (i : nat),
    ⊨ Γ ->
    ind_member D m = Some Mm -> List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D -> List.length Bks' = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊨ Pk : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ps ->
    List.length Ps' = im_np D Mm -> List.Forall (exp_scoped (List.length Γ)) Ps' ->
    (forall k Pk Pk' T, List.nth_error Ps k = Some Pk -> List.nth_error Ps' k = Some Pk' ->
       List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊨ Pk ≈ Pk' : T) ->
    Γ ⊨ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    exp_scoped (List.length Γ) M ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk, ind_member D k = Some Mk -> ⊨ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b ≈ eb_motive b' : Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       ⊨ elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b b' j c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' ->
       List.nth_error (eb_brs b) j = Some (c, n, B) -> List.nth_error (eb_brs b') j = Some (c, n, B') ->
       ind_con Mk c = Some gs ->
       elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B ≈ B'
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊨ a_elim ak_relevant p (List.firstn (ind_nu D) Ps) m Bks M ≈ a_elim ak_relevant p (List.firstn (ind_nu D) Ps') m Bks' M'
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros VP p D HP HPD * HΓ HMm Hbm HLb HLb' HPl HPs HPss HPl' HPss' HPP HMM HMs HnmA HnmB HMall HAA HnaA HbrsF HBc HarA HBB.
  pose proof (valid_groups_valid VP HP p D HPD) as Hvg.
  pose proof (valid_group_closed _ _ Hvg) as Hc; pose proof (valid_group_valid _ _ Hvg) as HD.
  destruct (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs) as [HUs HNs].
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HUl' : List.length (List.firstn (ind_nu D) Ps') = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HPl'; lia).
  assert (HNl : List.length (List.skipn (ind_nu D) Ps) = im_nn Mm) by (rewrite List.length_skipn; unfold im_np in HPl; lia).
  assert (Hti : forall Qs, List.length Qs = im_np D Mm ->
             tele_insts (im_params D Mm) Id Qs
             = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Qs)
               ++ tele_insts (im_nparams Mm) (sb_of_list Id (List.firstn (ind_nu D) Qs)) (List.skipn (ind_nu D) Qs)).
  { intros Qs HQ; rewrite <- (List.firstn_skipn (ind_nu D) Qs) at 1; unfold im_params; apply tele_insts_app;
      [ exact (decl_uparams_ass D Hc) | rewrite List.length_firstn; unfold im_np, ind_nu in *; lia ]. }
  assert (HUU : forall j U U' T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U ->
             List.nth_error (List.firstn (ind_nu D) Ps') j = Some U' ->
             List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Γ ⊨ U ≈ U' : T).
  { intros * HU HU' HT.
    apply (HPP j).
    - rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HU.
    - rewrite <- (List.firstn_skipn (ind_nu D) Ps'), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HU'.
    - rewrite (Hti Ps HPl), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HT. }
  assert (HBB' : forall j Mj b b' c gs n B B', ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             List.nth_error Bks' j = Some b' -> ind_con Mj c = Some gs ->
             brs_lookup (eb_brs b) c = Some (n, B) -> brs_lookup (eb_brs b') c = Some (n, B') ->
             elim_bctx ak_relevant p D Mj gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B ≈ B'
               : elim_branch_type p D j Mj c gs (eb_motive b) (List.firstn (ind_nu D) Ps)).
  { intros * HMj Hb Hb' Hcon HlB HlB'.
    destruct (brs_lookup_pair _ _ _ _ _ (HbrsF _ _ _ Hb Hb') HlB) as (kk & B'' & Hk & Hk' & HlB'').
    rewrite HlB' in HlB''; injection HlB'' as <-.
    exact (HBB _ _ _ _ _ _ _ _ _ _ HMj Hb Hb' Hk Hk' Hcon). }
  rewrite <- (List.firstn_skipn (ind_nu D) Ps) in HPss; apply List.Forall_app in HPss as [HUss HNss].
  rewrite <- (List.firstn_skipn (ind_nu D) Ps') in HPss'; apply List.Forall_app in HPss' as [HUss' _].
  exact (rel_exp_under_ctx_elim_at VP p D HP HPD Γ m Mm bm Bks Bks' _ _ _ M M' i HΓ HMm Hbm HLb HLb'
           HUl HUs HUss HUl' HUss' HUU HNl HNs HNss HMM HMs HnmA HnmB HMall HAA HnaA HbrsF HBc HarA HBB').
Qed.

End Fixed_GCtx.

(** ** The Groups along an Embedding

    A group looked up in a well-formed [Θ ⍮ Ξ] is typed and closed; along a
    sound embedding the groups of [Θ ⍮ Ξ] are valid groups of the
    target. *)

Lemma decl_of_glookup : forall Θ Ξ p D,
    ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ p = Some D -> decl_typed Θ Ξ D /\ decl_closed D.
Proof.
  intros * Hg Hl; split.
  - exact (globals_valid_decls _ _ _ _ _ _ (gctx_resolved_globals_typed _ _ Hg) _ _ Hl).
  - exact (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl).
Qed.

Lemma valid_groups_of_embedding : forall Θ Ξ Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 ->
    @valid_groups (gc_mk Θ2 Ξ2) (fun qn G => ind_lookup Θ Ξ qn = Some G).
Proof.
  intros * He.
  pose proof (valid_gctx_embedding_wf _ _ _ _ He) as Hg.
  pose proof (gctx_embedding_resolution _ _ _ _ (valid_gctx_embedding_embedding _ _ _ _ He)) as Hs.
  constructor.
  - intros qn G Hlq.
    destruct (decl_of_glookup _ _ _ _ Hg Hlq) as [Hdt Hc].
    pose proof (gctx_embedding_preserves_decl_typed _ _ _ _ _ (valid_gctx_embedding_embedding _ _ _ _ He) Hdt) as Hdt2.
    pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hlq) as Hl2.
    constructor; [ exact Hl2 | exact (valid_gctx_embedding_ind_field _ _ _ _ He _ _ Hlq) | exact Hc | exact (decl_typed_sort_univ _ _ _ Hdt) | |
                 exact Hdt2 | exact (ind_lookup_mpath _ _ _ _ Hg Hlq) | ].
    2: { intros * HM Hh.
         destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh) as [R HR].
         pose proof (rview_record_lookup _ _ _ _ _ _ HR) as HlR.
         exists R; constructor;
           [ exact (record_lookup_gc_sub _ _ _ _ _ _ Hs HlR) | exact (valid_gctx_embedding_record _ _ _ _ He _ _ HlR)
           | exact (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) HlR)
           | exact (gctx_embedding_preserves_record_typed _ _ _ _ _ (valid_gctx_embedding_embedding _ _ _ _ He) (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR)) ]. }
    apply (@group_structure_of_typed (gc_mk Θ2 Ξ2) G Hdt2).
    intros * HM Hh Hq2.
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (D' & Mk' & Hq & _).
    pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hq) as Hq'.
    cbn in Hq2; rewrite Hq' in Hq2; injection Hq2 as <-.
    exact (gctx_embedding_preserves_decl_typed _ _ _ _ _ (valid_gctx_embedding_embedding _ _ _ _ He) (proj1 (decl_of_glookup _ _ _ _ Hg Hq))).
  - intros * Hlq HM Hh Hq2; cbn in Hq2 |- *.
    destruct (decl_of_glookup _ _ _ _ Hg Hlq) as [Hdt _].
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (D' & Mk' & Hq & _).
    pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hq) as Hq'.
    rewrite Hq' in Hq2; injection Hq2 as <-; exact Hq.
Qed.
