(** * Semantic Member Types

    A module expression is valid in its members when each member type it
    has is represented ([rep]) and types its members at every valid
    environment ([mtyped]), and when the parameters still missing at a chain
    are at least those of the arity there.  The closure of a valid unit is
    valid in its members, and so is a module slot. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases FunctionCases UniverseCases SubstitutionCases SubtypingCases
  VariableCases LetCases TrueFalseCases UnitCases InstanceCases MemberCases MemberTyping MemberReps.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** ** Member Types of a Weakened Unit *)


Lemma pi_view_wk_none : forall A φ, pi_view A = None -> pi_view A[φ]ʷ = None.
Proof.
  induction A; intros φ H; try destruct b; cbn in H |- *; try discriminate; try reflexivity.
  - destruct (pi_view A) eqn:E; [ destruct p; discriminate |].
    rewrite (IHA _ eq_refl); reflexivity.
  - destruct (pi_view A) eqn:E; [ destruct p; discriminate |].
    rewrite (IHA _ eq_refl); reflexivity.
Qed.

Lemma pi_view_wk_inv : forall A φ B C, pi_view A[φ]ʷ = Some (B, C) ->
    exists B0 C0, pi_view A = Some (B0, C0) /\ B = B0[φ]ʷ /\ C = C0[wk_q φ]ʷ.
Proof.
  intros * H.
  destruct (pi_view A) as [[B0 C0] |] eqn:E.
  - rewrite (pi_view_wk _ _ _ _ E) in H; injection H as <- <-; eauto.
  - rewrite (pi_view_wk_none _ _ E) in H; discriminate.
Qed.

Definition wk_mod_inv (φ : wk) (Γ Δ : ctx) : Prop :=
  forall x U', Γ ∋ #(φ x) ⇒ₘ U' -> exists U, Δ ∋ #x ⇒ₘ U /\ U' = gunit_wk U φ.

Lemma wk_mod_inv_shift : forall e Γ, wk_mod_inv wk_shift (e :: Γ) Γ.
Proof. intros * x U' H; inversion H; subst; eauto. Qed.

Lemma wk_mod_inv_q : forall φ Γ Δ e,
    wk_mod_inv φ Γ Δ -> wk_mod_inv (wk_q φ) (centry_wk e φ :: Γ) (e :: Δ).
Proof.
  intros * Hφ [| x] U' H; cbn in H; inversion H; subst.
  - destruct e; cbn in *; try discriminate.
    match goal with Heq : ce_mod _ = ce_mod _ |- _ => injection Heq as -> end.
    eexists; split; [ constructor | symmetry; apply gunit_wk_shift_wk_q ].
  - match goal with Hl : ctx_lookup_mod (φ x) _ Γ |- _ => destruct (Hφ _ _ Hl) as (U0 & HU & ->) end.
    eexists; split; [ constructor; exact HU | symmetry; apply gunit_wk_shift_wk_q ].
Qed.

Lemma wk_mod_inv_ext : forall Ψ φ Γ Δ,
    wk_mod_inv φ Γ Δ -> wk_mod_inv (wk_qn (List.length Ψ) φ) (tele_wk Ψ φ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using wk_mod_inv_q. Qed.

Lemma gm_prefix_upto_wk_inv : forall Φ x φ Φx,
    gm_prefix_upto (gmod_wk Φ φ) x = Some Φx ->
    exists Φ0, gm_prefix_upto Φ x = Some Φ0 /\ Φx = gmod_wk Φ0 φ.
Proof.
  intros * H; rewrite gm_prefix_upto_wk in H.
  destruct (gm_prefix_upto Φ x) eqn:E; cbn in H; [ injection H as <-; eauto | discriminate ].
Qed.

Lemma member_type_strengthen : forall Θ Ξ, gctx_closed Θ Ξ ->
    (forall Γ H' ch k A, member_type Θ Ξ Γ H' ch k A ->
       forall Δ H φ, H' = modexp_wk H φ -> wk_mod_inv φ Γ Δ ->
       exists A0, member_type Θ Ξ Δ H ch k A0 /\ A = A0[φ]ʷ) /\
    (forall Γ U' ch k A, unit_member_type Θ Ξ Γ U' ch k A ->
       forall Δ U φ, U' = gunit_wk U φ -> wk_mod_inv φ Γ Δ ->
       exists A0, unit_member_type Θ Ξ Δ U ch k A0 /\ A = A0[φ]ʷ).
Proof.
  intros Θ Ξ Hc; apply member_type_both_ind.
  - intros Γ qp ch b A B Hne Hr Δ Hm φ Heq Hφ.
    destruct Hm; cbn in Heq; try discriminate; injection Heq as <-.
    destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc Hr) as [HA _].
    exists A; split; [ eapply mt_path_def; eassumption | symmetry; apply exp_closed_wk; assumption ].
  - intros Γ qp ch T Hm' Δ Hm φ Heq Hφ.
    destruct Hm; cbn in Heq; try discriminate; injection Heq as <-.
    pose proof (gctx_closed_module _ _ _ _ Hc Hm') as HT; cbn in HT.
    eexists; split; [ eapply mt_path_mod; eassumption |].
    symmetry; apply exp_closed_wk; apply ctx_pi_scoped; [ assumption | exact I ].
  - intros Γ qp ch U r k A Hm' Hu _ Δ Hm φ Heq Hφ.
    destruct Hm; cbn in Heq; try discriminate; injection Heq as <-.
    pose proof (gctx_closed_module _ _ _ _ Hc Hm') as HU; cbn in HU.
    exists A; split; [ eapply mt_path_alias; eassumption |].
    symmetry; apply exp_closed_wk; exact (proj2 (member_type_scoped Θ Ξ) nil U r k A Hu Hc I HU).
  - intros Γ x U ch k A Hl _ IH Δ Hm φ Heq Hφ.
    destruct Hm; cbn in Heq; try discriminate; injection Heq as Ex; subst x.
    destruct (Hφ _ _ Hl) as (U0 & HU0 & ->).
    destruct (IH _ _ _ eq_refl Hφ) as (A0 & HA0 & ->).
    exists A0; split; [ eapply mt_var; eassumption | reflexivity ].
  - intros Γ U ch k A _ IH Δ Hm φ Heq Hφ.
    destruct Hm; cbn in Heq; try discriminate; injection Heq as EU; subst U.
    destruct (IH _ _ _ eq_refl Hφ) as (A0 & HA0 & ->).
    exists A0; split; [ eapply mt_lit; eassumption | reflexivity ].
  - intros Γ H y ch k A Hk _ IH Δ Hm φ Heq Hφ.
    destruct Hm; cbn in Heq; try discriminate; injection Heq as EH Ey; subst H y.
    destruct (IH _ _ _ eq_refl Hφ) as (A0 & HA0 & ->).
    exists A0; split; [ eapply mt_mem; eassumption | reflexivity ].
  - intros Γ H N ch k A B C _ IH Hp Δ Hm φ Heq Hφ.
    destruct Hm; cbn in Heq; try discriminate; injection Heq as EH EN; subst H N.
    destruct (IH _ _ _ eq_refl Hφ) as (A0 & HA0 & ->).
    destruct (pi_view_wk_inv _ _ _ _ Hp) as (B0 & C0 & Hp0 & -> & ->).
    exists C0[Id,,e]; split; [ eapply mt_app; eassumption | symmetry; apply exp_wk_sub_extend ].
  - intros Γ Δ Φ Δ' U φ Heq Hφ.
    destruct U as [Δ0 [Φ0 | E0]]; rewrite gunit_wk_mk in Heq; cbn in Heq; try discriminate.
    injection Heq as -> ->.
    eexists; split; [ apply umt_self | rewrite ctx_pi_wk; reflexivity ].
  - intros Γ Δ Φ Φ' x b A B Hx Δ' U φ Heq Hφ.
    destruct U as [Δ0 [Φ0 | E0]]; rewrite gunit_wk_mk in Heq; cbn in Heq; try discriminate.
    injection Heq as -> ->.
    destruct (gm_prefix_upto_wk_inv _ _ _ _ Hx) as (Φx & Hx0 & EΦ).
    destruct Φx as [| Φ0' y E0 | Φ0' c]; cbn in EΦ; try discriminate.
    injection EΦ as -> Ey EE; subst y.
    destruct E0 as [b0 pv0 A0 B0 | U0]; cbn in EE; try discriminate.
    injection EE as -> <- -> ->.
    eexists; split; [ eapply umt_def; exact Hx0 | rewrite ctx_pi_body_wk; reflexivity ].
  - intros Γ Δ Φ Φ' y Uy ch k A Hk Hy _ IH Δ' U φ Heq Hφ.
    destruct U as [Δ0 [Φ0 | E0]]; rewrite gunit_wk_mk in Heq; cbn in Heq; try discriminate.
    injection Heq as -> ->.
    destruct (gm_prefix_upto_wk_inv _ _ _ _ Hy) as (Φx & Hy0 & EΦ).
    destruct Φx as [| Φ0' z E0 | Φ0' c]; cbn in EΦ; try discriminate.
    injection EΦ as -> Ez EE; subst z.
    destruct E0 as [b0 pv0 A0 B0 | U0]; cbn in EE; try discriminate.
    injection EE as ->.
    assert (EC : body_ctx (gmod_wk Φ0' (wk_qn (List.length Δ0) φ)) ++ tele_wk Δ0 φ ++ Γ
                 = tele_wk (body_ctx Φ0' ++ Δ0) φ ++ Γ)
      by (rewrite tele_wk_app, body_ctx_wk, <- List.app_assoc; reflexivity).
    assert (EU : gunit_wk U0 (wk_qn (gm_binders Φ0') (wk_qn (List.length Δ0) φ))
                 = gunit_wk U0 (wk_qn (List.length (body_ctx Φ0' ++ Δ0)) φ))
      by (apply gunit_wk_wk_eq; rewrite wk_qn_add, length_app, length_body_ctx; reflexivity).
    destruct (IH (body_ctx Φ0' ++ Δ0 ++ Δ') U0 (wk_qn (List.length (body_ctx Φ0' ++ Δ0)) φ) EU)
      as (Ay & HAy & ->).
    { rewrite EC, List.app_assoc; apply wk_mod_inv_ext; exact Hφ. }
    eexists; split; [ eapply umt_mod; [ exact Hk | exact Hy0 | exact HAy ] |].
    rewrite ctx_pi_body_wk; f_equal.
    apply exp_wk_wk_eq; rewrite wk_qn_add, length_app, length_body_ctx; reflexivity.
  - intros Γ Δ E ch k A _ IH Δ' U φ Heq Hφ.
    destruct U as [Δ0 [Φ0 | E0]]; rewrite gunit_wk_mk in Heq; cbn in Heq; try discriminate.
    injection Heq as -> ->.
    destruct (IH (Δ0 ++ Δ') E0 (wk_qn (List.length Δ0) φ) eq_refl (wk_mod_inv_ext _ _ _ _ Hφ)) as (AE & HAE & ->).
    eexists; split; [ apply umt_alias; exact HAE | rewrite ctx_pi_wk; reflexivity ].
Qed.



Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Bodies *)

Lemma body_shape_lets : forall Φ, body_shape Φ Φ -> lets_only (body_ctx Φ).
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros H; cbn in *; [ constructor | | exact (IH (proj1 H)) ].
  destruct H as (H1 & _ & H3).
  destruct E as [b pv A [M |] | U]; cbn in H3; try contradiction; constructor; try discriminate; exact (IH H1).
Qed.

Lemma body_shape_prefix : forall Φ x Φx, body_shape Φ Φ -> gm_prefix_upto Φ x = Some Φx -> body_shape Φx Φx.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * Hs Hx; cbn in Hx; try discriminate.
  - destruct (String.eqb x y); [ injection Hx as <-; exact Hs | exact (IH _ _ (proj1 Hs) Hx) ].
  - exact (IH _ _ (proj1 Hs) Hx).
Qed.

(** The environment a valid body makes, from a valid one before it. *)
Lemma benv_valid : forall Φ D R ρ,
    ⊨ body_ctx Φ ++ D -> body_shape Φ Φ -> EF D ≈ D ∈ per_ctx_env ↘ R -> R ρ ρ ->
    exists ρ1 R1, eval_benv gc_deps gc_stack ρ Φ ρ1 /\
      EF body_ctx Φ ++ D ≈ body_ctx Φ ++ D ∈ per_ctx_env ↘ R1 /\ R1 ρ1 ρ1.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * HC Hs HD Hρ; cbn in HC, Hs |- *.
  - exists ρ, R; split; [ constructor | split; assumption ].
  - destruct Hs as (Hs & _ & HE).
    destruct E as [b pv A [M |] | U]; cbn in HE, HC; try contradiction.
    + destruct (IH _ _ _ (sem_ctx_tail HC) Hs HD Hρ) as (ρ1 & R1 & Hb & HR1 & Hρ1).
      destruct (sem_ctx_def_inv HC) as [[i HA] HM].
      pose proof (per_ctx_env_of_def HR1 HA HM) as HR2.
      assert (HP1 : PER R1) by (eapply per_env_PER; exact HR1).
      pose proof (rel_exp_of_typ_inversion_simple_at HR1 HA) as HS.
      pose proof (rel_exp_under_ctx_simple_at HR1 HM) as HMs.
      destruct (HMs _ _ Hρ1) as [m [m' [Hm [Hm' Hmm]]]].
      functional_eval_rewrite_clear.
      exists (ρ1 ↦ m), (per_env_extend_def A M R1); split; [ econstructor; eassumption |]; split; [ exact HR2 |].
      eapply per_env_extend_def_intro; [ exact HP1 | exact HS | exact HMs | exact Hρ1 | exact Hmm | exact Hm | exact Hmm ].
    + destruct (IH _ _ _ (sem_ctx_tail HC) Hs HD Hρ) as (ρ1 & R1 & Hb & HR1 & Hρ1).
      pose proof (sem_ctx_mod_inv HC) as (HU & _ & _).
      pose proof (per_ctx_env_of_mod HR1 HU) as HR2.
      pose proof (unit_chain_at HU HR1 _ _ Hρ1) as Hd.
      exists (ρ1 ↦ᵐ dm_local ρ1 U nil), (env_ext_mod U U R1); split; [ econstructor; eassumption |]; split; [ exact HR2 |].
      unfold env_ext_mod; cbn; repeat split; assumption.
  - destruct (IH _ _ _ HC (proj1 Hs) HD Hρ) as (ρ1 & R1 & Hb & HR1 & Hρ1).
    exists ρ1, R1; split; [ econstructor; exact Hb | split; assumption ].
Qed.

(** ** Semantic Member Types *)

Definition mt_val (Γ : ctx) (H : modexp) (ch : list String.string) (k : mkind) (A : typ) : Prop :=
  forall R ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ ->
    forall h, eval_modexp gc_deps gc_stack H ρ h -> exists a, ⟦ A ⟧ ρ ↘ a /\ mtyped h ch k a.

Definition umt_val (Γ : ctx) (U : gunit) (ch : list String.string) (k : mkind) (A : typ) : Prop :=
  forall R ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ ->
    exists a, ⟦ A ⟧ ρ ↘ a /\ mtyped (dm_local ρ U nil) ch k a.

(** A module expression is valid in its members. *)
Definition sem_mt (Γ : ctx) (H : modexp) : Prop :=
  (forall ch k A, member_type gc_deps gc_stack Γ H ch k A -> (k = mk_term -> ch <> nil) ->
     (exists n b, rep Γ A n b) /\ mt_val Γ H ch k A) /\
  (forall ch0 A0 ch k A, member_type gc_deps gc_stack Γ H ch0 mk_mod A0 ->
     member_type gc_deps gc_stack Γ H (ch0 ++ ch) k A -> (k = mk_term -> ch0 ++ ch <> nil) ->
     exists m n, rep Γ A0 m true /\ rep Γ A n false /\ m <= n).

(** The closure of a unit is valid in its members. *)
Definition sem_umt (Γ : ctx) (U : gunit) : Prop :=
  (forall ch k A, unit_member_type gc_deps gc_stack Γ U ch k A -> (k = mk_term -> ch <> nil) ->
     (exists n b, rep Γ A n b) /\ umt_val Γ U ch k A) /\
  (forall ch0 A0 ch k A, unit_member_type gc_deps gc_stack Γ U ch0 mk_mod A0 ->
     unit_member_type gc_deps gc_stack Γ U (ch0 ++ ch) k A -> (k = mk_term -> ch0 ++ ch <> nil) ->
     exists m n, rep Γ A0 m true /\ rep Γ A n false /\ m <= n).

(** The module slots of a context, and the submodules and alias targets of
    their units, are valid in their members. *)
Inductive ctx_mt : ctx -> Prop :=
| cmt_nil : ctx_mt nil
| cmt_ass : forall Γ A, ctx_mt Γ -> ctx_mt (ce_ass A :: Γ)
| cmt_def : forall Γ A M, ctx_mt Γ -> ctx_mt (ce_def A M :: Γ)
| cmt_mod : forall Γ U, ctx_mt Γ -> unit_mt Γ U -> ctx_mt (ce_mod U :: Γ)
with unit_mt : ctx -> gunit -> Prop :=
| uok_body : forall Γ Δ Φ, ctx_mt (body_ctx Φ ++ Δ ++ Γ) -> unit_mt Γ (gu_body Δ Φ)
| uok_alias : forall Γ Δ E, sem_mt (Δ ++ Γ) E -> unit_mt Γ (gu_mk Δ (md_alias E)).

Lemma ctx_mt_app_r : forall Ψ Γ, ctx_mt (Ψ ++ Γ) -> ctx_mt Γ.
Proof. induction Ψ as [| e Ψ IH]; intros * H; cbn in H; [ exact H | inversion H; subst; eauto ]. Qed.

Lemma ctx_mt_mod_inv : forall Γ U, ctx_mt (ce_mod U :: Γ) -> unit_mt Γ U.
Proof. intros * H; inversion H; assumption. Qed.

(** ** Values of Valid Module Expressions *)

Lemma rel_modexp_simple_at : forall {Γ H H' R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> Γ ⊨ᵐ H ≈ H' ->
    forall ρ ρ', R ρ ρ' ->
    exists h h', eval_modexp gc_deps gc_stack H ρ h /\ eval_modexp gc_deps gc_stack H' ρ' h' /\ per_dmod h h'.
Proof.
  intros * HΓ [R0 [HΓ0 HH]] ρ ρ' Hρ.
  assert (E : R <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (HH _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [h1 h2 h3 h4 H1 H2 H3 H4 (_ & H23 & _)].
  exists h2, h3; auto.
Qed.

(** ** Walking the Parameters of a Closure *)

Lemma env_args_snoc : forall ρ args c, env_args ρ (args ++ c :: nil) = env_args ρ args ↦ c.
Proof. intros; unfold env_args; rewrite fold_left_app; reflexivity. Qed.

Lemma walk_typed : forall Γ ρ U ch k R Y,
    tele_ass (gu_params U) -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ ->
    (forall args RΔ, List.length args = List.length (gu_params U) ->
       EF gu_params U ++ Γ ≈ gu_params U ++ Γ ∈ per_ctx_env ↘ RΔ -> RΔ (env_args ρ args) (env_args ρ args) ->
       exists a, ⟦ Y ⟧ env_args ρ args ↘ a /\ mtyped (dm_local ρ U args) ch k a) ->
    forall Δin Δout args RΔ, gu_params U = Δin ++ Δout -> List.length args = List.length Δout ->
      ⊨ Δin ++ Δout ++ Γ -> EF Δout ++ Γ ≈ Δout ++ Γ ∈ per_ctx_env ↘ RΔ ->
      RΔ (env_args ρ args) (env_args ρ args) ->
      exists a, ⟦ ctx_pi Δin Y ⟧ env_args ρ args ↘ a /\ mtyped (dm_local ρ U args) ch k a.
Proof.
  intros * HU HΓ Hρ HS Δin.
  induction Δin as [| e Δin IH] using rev_ind; intros Δout args RΔ EU Hl HC HRΔ Hρa; cbn [app] in *.
  - apply (HS _ RΔ); [ rewrite EU; exact Hl | rewrite EU; exact HRΔ | exact Hρa ].
  - rewrite EU in HU; destruct (tele_ass_app_inv _ _ HU) as [HU1 HU2].
    destruct (tele_ass_app_inv _ _ HU1) as [_ He]; inversion He as [| ? ? [A1 ->] _]; subst.
    rewrite <- app_assoc in HC; cbn [app] in HC.
    destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HC)) as [i HA1].
    pose proof (rel_exp_of_typ_inversion_simple_at HRΔ HA1) as HS1.
    destruct (HS1 _ _ Hρa) as [a0 [a0' [Ha0 [Ha0' [Ra HRa]]]]].
    functional_eval_rewrite_clear.
    rewrite ctx_pi_app; cbn [ctx_pi].
    eexists; split; [ econstructor; exact Ha0 |].
    assert (Hlt : List.length args < List.length (gu_params U))
      by (rewrite EU, !length_app; cbn; lia).
    assert (Hn : nth_error (rev (gu_params U)) (List.length args) = Some (ce_ass A1)).
    { rewrite EU, <- app_assoc, rev_app_distr; cbn [app rev].
      rewrite nth_error_app1 by (rewrite length_app, length_rev; cbn; lia).
      rewrite nth_error_app2 by (rewrite length_rev; lia).
      rewrite length_rev, Hl, Nat.sub_diag; reflexivity. }
    eapply mty_pi; [ left; do 3 eexists; split; [ reflexivity | exact Hlt ] | econstructor; [ exact Hn | exact Ha0 ] | exact HRa |].
    intros c w1 b Hc Hw1 Hb.
    assert (Hw : w1 = dm_local ρ U (args ++ c :: nil))
      by (destruct U as [Δ [Φ | E]]; inversion Hw1; subst; cbn in *; try lia; reflexivity).
    subst w1.
    pose proof (per_ctx_env_of_typ HRΔ HA1) as HRΔ'.
    destruct (IH (ce_ass A1 :: Δout) (args ++ c :: nil) _ ltac:(rewrite EU, <- app_assoc; reflexivity)
                ltac:(rewrite length_app; cbn; lia) HC HRΔ')
      as (b' & Hb' & Hm).
    { rewrite env_args_snoc; split; [ exact Hρa |].
      eapply per_head_of; [ exact Ha0 | exact Ha0 | exact HRa | exact Hc ]. }
    rewrite env_args_snoc in Hb'.
    pose proof (functional_eval_exp _ _ _ _ Hb Hb') as <-; exact Hm.
Qed.

(** ** Closures of Valid Units *)

Lemma rep_lift : forall Γ Ψ Δ X m b,
    ⊨ Γ -> lets_only Ψ -> tele_ass Δ -> ⊨ Ψ ++ Δ ++ Γ -> rep (Ψ ++ Δ ++ Γ) X m b ->
    rep Γ (ctx_pi (Ψ ++ Δ) X) (List.length Δ + m) b.
Proof.
  intros * HΓ HΨ HΔ HC Hr.
  pose proof (rep_nest _ _ _ _ _ _ _ _ (gsub_id _ HΓ) HΔ HΨ HC Hr) as H.
  rewrite exp_sub_id in H; exact H.
Qed.

Lemma rep_forget : forall Γ A n b, rep Γ A n b -> rep Γ A n false.
Proof.
  induction 1 as [Γ X i b HΓ HX Hb | Γ τ D Ψ Δp X m b Hg HΔ HΨ HC Hr IH].
  - eapply rep_leaf; [ eassumption | eassumption | discriminate ].
  - eapply rep_nest; eassumption.
Qed.

Lemma body_entry_def : forall Φ x Φ' b pv A B,
    body_shape Φ Φ -> gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    exists M Ψ, B = Some M /\ body_ctx Φ = Ψ ++ ce_def A M :: body_ctx Φ' /\ body_shape Φ' Φ'.
Proof.
  intros * Hs Hx.
  pose proof (body_shape_prefix _ _ _ Hs Hx) as Hs'; cbn in Hs'.
  destruct Hs' as (Hs' & _ & HE).
  destruct B as [M |]; cbn in HE; [| contradiction ].
  destruct (gm_prefix_upto_body_ctx _ _ _ Hx) as [Ψ HΨ]; cbn in HΨ.
  exists M, Ψ; auto.
Qed.

Lemma body_entry_mod : forall Φ y Φ' Uy,
    body_shape Φ Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
    exists Ψ, body_ctx Φ = Ψ ++ ce_mod Uy :: body_ctx Φ' /\ body_shape Φ' Φ'.
Proof.
  intros * Hs Hx.
  pose proof (body_shape_prefix _ _ _ Hs Hx) as Hs'; cbn in Hs'.
  destruct (gm_prefix_upto_body_ctx _ _ _ Hx) as [Ψ HΨ]; cbn in HΨ.
  exists Ψ; split; [ exact HΨ | exact (proj1 Hs') ].
Qed.

Lemma closure_typed : forall Γ U ch k A, unit_member_type gc_deps gc_stack Γ U ch k A ->
    ⊨ Γ -> sem_unit Γ U -> unit_mt Γ U -> (k = mk_term -> ch <> nil) ->
    (exists n b, rep Γ A n b /\ List.length (gu_params U) <= n) /\ umt_val Γ U ch k A.
Proof.
  induction 1 as [Γ Δ Φ | Γ Δ Φ Φ' x b A B Hx | Γ Δ Φ Φ' y Uy ch k A Hk Hy Hm IH | Γ Δ E ch k A Hm];
    intros HΓ Hs Hok Hch; inversion Hs as [? ? ? HΔ Hsh HC | ? ? ? HΔ HC HE]; subst; cbn [gu_params].
  - pose proof (sem_ctx_app_r _ _ HC) as HC0.
    split.
    + exists (List.length Δ + 0), true; split; [| lia ].
      apply (rep_lift Γ nil Δ a_True 0 true HΓ (Forall_nil _) HΔ HC0).
      eapply rep_leaf; [ exact HC0 | exact (valid_exp_True (i := 0) HC0) | reflexivity ].
    + intros R ρ HR Hρ.
      refine (walk_typed Γ ρ (gu_body Δ Φ) nil mk_mod R a_True HΔ HR Hρ _ Δ nil nil R (eq_sym (app_nil_r Δ)) eq_refl HC0 HR Hρ).
      intros args RΔ Hl HRΔ Hρa.
      exists ⊤ᵈ; split; [ constructor |].
      eapply mty_top; [ apply ms_body; exact Hl | exact (per_univ_elem_True 0) ].
  - destruct (body_entry_def _ _ _ _ _ _ _ Hsh Hx) as (M & Ψ0 & -> & EC & Hsh').
    rewrite EC, <- app_assoc in HC; cbn [app] in HC.
    pose proof (sem_ctx_app_r _ _ HC) as HCd.
    destruct (sem_ctx_def_inv HCd) as [[i HA] _].
    pose proof (sem_ctx_tail HCd) as HC1.
    pose proof (sem_ctx_app_r _ _ HC1) as HC0.
    split.
    + exists (List.length Δ + 0), false; split; [| lia ].
      apply (rep_lift Γ (body_ctx Φ') Δ A 0 false HΓ (body_shape_lets _ Hsh') HΔ HC1).
      eapply rep_leaf; [ exact HC1 | exact HA | discriminate ].
    + intros R ρ HR Hρ.
      rewrite ctx_pi_app.
      refine (walk_typed Γ ρ (gu_body Δ Φ) (x :: nil) mk_term R (ctx_pi (body_ctx Φ') A) HΔ HR Hρ _ Δ nil nil R (eq_sym (app_nil_r Δ)) eq_refl HC0 HR Hρ).
      intros args RΔ Hl HRΔ Hρa.
      destruct (benv_valid Φ' (Δ ++ Γ) RΔ _ HC1 Hsh' HRΔ Hρa) as (ρ1 & R1 & Hb & HR1 & Hρ1).
      destruct (rel_exp_of_typ_inversion_simple_at HR1 HA _ _ Hρ1) as [a0 [a0' [Ha0 [_ [Ra HRa]]]]].
      exists a0; split; [ eapply eval_ctx_pi_body; eassumption |].
      eapply mty_def; [ exact Hl | exact Hx | exact Hb | exact Ha0 |].
      etransitivity; [ exact HRa | symmetry; exact HRa ].
  - destruct (body_entry_mod _ _ _ _ Hsh Hy) as (Ψ0 & EC & Hsh').
    pose proof HC as HCb.
    rewrite EC, <- app_assoc in HC; cbn [app] in HC.
    pose proof (sem_ctx_app_r _ _ HC) as HCm.
    pose proof (sem_ctx_tail HCm) as HC1.
    pose proof (sem_ctx_app_r _ _ HC1) as HC0.
    pose proof (sem_ctx_mod_inv HCm) as (HU & HsU & _).
    inversion Hok as [? ? ? Hok' |]; subst.
    rewrite EC, <- app_assoc in Hok'; cbn [app] in Hok'.
    pose proof (ctx_mt_mod_inv _ _ (ctx_mt_app_r _ _ Hok')) as HokU.
    destruct (IH HC1 HsU HokU Hk) as ((n & b & Hr & _) & Hval).
    split.
    + exists (List.length Δ + n), b; split; [| lia ].
      exact (rep_lift Γ (body_ctx Φ') Δ A n b HΓ (body_shape_lets _ Hsh') HΔ HC1 Hr).
    + intros R ρ HR Hρ.
      rewrite ctx_pi_app.
      refine (walk_typed Γ ρ (gu_body Δ Φ) (y :: ch) k R (ctx_pi (body_ctx Φ') A) HΔ HR Hρ _ Δ nil nil R (eq_sym (app_nil_r Δ)) eq_refl HC0 HR Hρ).
      intros args RΔ Hl HRΔ Hρa.
      destruct (benv_valid Φ' (Δ ++ Γ) RΔ _ HC1 Hsh' HRΔ Hρa) as (ρ1 & R1 & Hb & HR1 & Hρ1).
      destruct (Hval _ _ HR1 Hρ1) as (a & Ha & Hma).
      exists a; split; [ eapply eval_ctx_pi_body; eassumption |].
      eapply mty_sub; eassumption.
  - inversion Hok as [| ? ? ? [HS1 _]]; subst.
    destruct (HS1 _ _ _ Hm Hch) as ((n & b & Hr) & Hval).
    split.
    + exists (List.length Δ + n), b; split; [| lia ].
      exact (rep_lift Γ nil Δ A n b HΓ (Forall_nil _) HΔ HC Hr).
    + intros R ρ HR Hρ.
      refine (walk_typed Γ ρ (gu_mk Δ (md_alias E)) ch k R A HΔ HR Hρ _ Δ nil nil R (eq_sym (app_nil_r Δ)) eq_refl HC HR Hρ).
      intros args RΔ Hl HRΔ Hρa.
      destruct (rel_modexp_simple_at HRΔ HE _ _ Hρa) as (h & _ & Hh & _ & _).
      destruct (Hval _ _ HRΔ Hρa _ Hh) as (a & Ha & Hma).
      exists a; split; [ exact Ha | eapply mty_alias; eassumption ].
Qed.

End Fixed_GCtx.
