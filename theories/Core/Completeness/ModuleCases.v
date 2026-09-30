(** * The Global Rules: Validity up to Sound Module Substitution

    A judgment of the global context [Θ ⍮ Ξ] is valid when it is valid, in the
    fixed-context sense, after every *sound* module substitution out of
    [Θ ⍮ Ξ].  A substitution is sound when what it puts in — for a parameter, a
    global, and a global's unfolding — is typed at the target (the premises of
    [msub_preserves_wf]) and valid there.  The fundamental theorem holds in this
    form for every rule ([kripke_fundamental]); at the identity it is the
    fixed-context theorem, given that every resolved global and parameter of the
    context is valid ([fundamental_at]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic Require Export GlobalInduction.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases NatCases SubstitutionCases SubtypingCases
  UniverseCases VariableCases LogicalRelation.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound module substitutions *)

Section MSub.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (μ : msub) (E : ctx).

  #[local] Notation G2 := (gc_mk Θ2 Ξ2).
  #[local] Notation tctx Γ := (Γ[μ]ᵐ ++ E).
  #[local] Notation tm Γ M := (M[ms_qn (length Γ) μ]ᵐ).

  (** [syn_msub] ([GlobalInduction]) and the semantic counterparts of its
      fields at the target, stated with the *old* (fixed-context) judgments at
      [G2].  The source context is asked to be
      syntactically well formed (the premise every rule reading a global or a
      parameter has) and the target semantically. *)
  Record sem_msub : Prop :=
    { sms_syn : syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E
    ; sms_base : @sem_ctx G2 E
    ; sms_param : forall n U k T Γ,
        List.nth_error Ξ1 n = Some U ->
        gu_params U ∋ #k : T ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        @sem_ctx G2 (tctx Γ) ->
        @rel_exp_under_ctx G2 (tctx Γ) (tm Γ (T[↑ₘ (S n)]ᵐ[sb_params n])) (tm Γ $[n, k]) (tm Γ $[n, k])
    ; sms_glob : forall r Δ b pv A B Γ,
        Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        @sem_ctx G2 (tctx Γ) ->
        @rel_exp_under_ctx G2 (tctx Γ) (tm Γ (ctx_pi Δ A)) (tm Γ (a_glob r)) (tm Γ (a_glob r))
    ; sms_unfold : forall r Δ A M Γ pv,
        Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def true pv A (Some M) ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        @sem_ctx G2 (tctx Γ) ->
        @rel_exp_under_ctx G2 (tctx Γ) (tm Γ (ctx_pi Δ A)) (tm Γ (a_glob r)) (tm Γ (ctx_fn Δ M))
    }.
End MSub.

(** ** 2. Judgments valid up to sound module substitution *)

Definition kctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2 μ E, sem_msub Θ1 Ξ1 Θ2 Ξ2 μ E ->
    @sem_ctx (gc_mk Θ2 Ξ2) (Γ[μ]ᵐ ++ E).

Definition kexp_eq Θ1 Ξ1 Γ A M M' : Prop :=
  forall Θ2 Ξ2 μ E, sem_msub Θ1 Ξ1 Θ2 Ξ2 μ E ->
    @sem_ctx (gc_mk Θ2 Ξ2) (Γ[μ]ᵐ ++ E) /\
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (Γ[μ]ᵐ ++ E)
      A[ms_qn (length Γ) μ]ᵐ M[ms_qn (length Γ) μ]ᵐ M'[ms_qn (length Γ) μ]ᵐ.

Definition ksubtyp Θ1 Ξ1 Γ A A' : Prop :=
  forall Θ2 Ξ2 μ E, sem_msub Θ1 Ξ1 Θ2 Ξ2 μ E ->
    @sem_ctx (gc_mk Θ2 Ξ2) (Γ[μ]ᵐ ++ E) /\
    @subtyp_under_ctx (gc_mk Θ2 Ξ2) (Γ[μ]ᵐ ++ E)
      A[ms_qn (length Γ) μ]ᵐ A'[ms_qn (length Γ) μ]ᵐ.

(** ** 3. The fundamental theorem through the wrapper *)

Theorem kripke_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kexp_eq Θ Ξ Γ A M M) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> kexp_eq Θ Ξ Γ A M M') /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ksubtyp Θ Ξ Γ A A').
Proof.
  apply syntactic_wf_mut_ind; unfold kctx, kexp_eq, ksubtyp; intros;
    repeat match goal with IH : forall _ _ _ _, sem_msub _ _ _ _ _ _ -> _ |- _ =>
      specialize (IH _ _ _ _ ltac:(eassumption)) end;
    destruct_conjs.
  all: cbn [length ctx_msub msubst MSub_ctx MSub_exp exp_msub ms_qn List.app] in *.
  all: try rewrite !exp_msub_sub1 in *; try rewrite !exp_msub_sub2 in *;
      try rewrite !exp_msub_sub_succ in *.
  all: try solve [ eapply sms_base; eassumption | eapply rel_ctx_extend'; eassumption ].
  all: try (split; [ assumption |]).
  (* every ordinary rule: the existing fixed-context case lemma, at the target *)
  all: try solve [ apply valid_exp_typ; assumption | apply valid_exp_nat; assumption
    | apply valid_exp_zero; assumption
    | apply rel_exp_succ_cong; assumption
    | eapply rel_exp_natrec_cong; eassumption
    | eapply rel_exp_pi_cong; eassumption
    | eapply rel_exp_fn_cong; eassumption
    | eapply rel_exp_app_cong; eassumption
    | eapply rel_exp_pi_beta; eassumption
    | eapply rel_exp_nat_beta_zero; eassumption
    | eapply rel_exp_nat_beta_succ; eassumption
    | eapply rel_exp_eq_subtyp; eassumption
    | apply rel_exp_under_ctx_sym; assumption
    | eapply rel_exp_under_ctx_trans; eassumption
    | eapply subtyp_refl; eassumption
    | eapply subtyp_trans; eassumption
    | eapply subtyp_pi; eassumption
    | apply subtyp_univ; [assumption | lia] ].
  (* a variable: looked up in the substituted context *)
  all: try solve [ eapply valid_exp_var;
                   [ apply ctx_lookup_app_left, ctx_lookup_msub; eassumption | assumption ] ].
  (* parameters, globals, δ: what the sound substitution supplies *)
  all: try solve [ eapply sms_param; eassumption ].
  all: try solve [ eapply sms_unfold; eassumption ].
  all: try solve [ eapply sms_glob; eassumption ].
  (* η *)
  rewrite <- exp_msub_shift_wk; eapply rel_exp_fn_eta; eassumption.
Qed.

(** ** 4. Composition *)

Section Compose.
  Variables (Θ1 Θ2 Θ3 : gdeps) (Ξ1 Ξ2 Ξ3 : gstack) (μ ν : msub) (E E' : ctx).
  (** Only the *syntactic* soundness of the first step is needed. *)
  Hypothesis Hμ : syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E.
  Hypothesis Hν : sem_msub Θ2 Ξ2 Θ3 Ξ3 ν E'.

  (** The semantic fields of the composite come from the *fundamental theorem
      at the middle context*, applied to the syntactic derivation [μ]'s
      syntactic field supplies, instantiated at [ν].  [μ]'s own semantic fields
      are not used. *)
  Theorem sem_msub_then : sem_msub Θ1 Ξ1 Θ3 Ξ3 (ms_then μ E ν) (E[ν]ᵐ ++ E').
  Proof.
    destruct (msub_preserves_wf' _ _ _ _ _ _ Hμ) as (Hc1 & _).
    destruct kripke_fundamental as (Kc & Ke & Kq & _).
    pose proof Hμ as [Hb Hp Hg Hu].
    constructor.
    - exact (syn_msub_then _ _ _ _ _ _ _ _ _ _ Hμ (sms_syn _ _ _ _ _ _ Hν)).
    - exact (Kc _ _ _ Hb _ _ _ _ Hν).
    - intros * Hn Hk HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      destruct (Hp _ _ _ _ _ Hn Hk HΓ1 HΓ2) as [D1 _].
      destruct (Ke _ _ _ _ _ D1 _ _ _ _ Hν) as [_ H].
      rewrite tctx_then, !tm_then in H; exact H.
    - intros * Hl HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      destruct (Hg _ _ _ _ _ _ _ Hl HΓ1 HΓ2) as [D1 _].
      destruct (Ke _ _ _ _ _ D1 _ _ _ _ Hν) as [_ H].
      rewrite tctx_then, !tm_then in H; exact H.
    - intros * Hl HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      pose proof (Hu _ _ _ _ _ _ Hl HΓ1 HΓ2) as D2.
      destruct (Kq _ _ _ _ _ _ D2 _ _ _ _ Hν) as [_ H].
      rewrite tctx_then, !tm_then in H; exact H.
  Qed.
End Compose.

(** ** 5. The identity is sound, given the semantics of what resolution hands back

    [sem_rwf]/[sem_pwf] are the semantic [rwf]: every resolved global, and every
    parameter, is valid at [⋅] in the *same* global context.  They are stated
    directly on [a_glob p] / [$[n, k]], i.e. already including δ; section 8
    reduces them to the validity of the resolved type and body. *)

Definition sem_rwf (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall p Δ b pv A B,
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (a_glob p) (a_glob p) /\
    (forall M, b = true -> B = Some M ->
       @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (a_glob p) (ctx_fn Δ M)).

Definition sem_pwf (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall n U k T,
    List.nth_error Ξ n = Some U ->
    gu_params U ∋ #k : T ->
    @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (T[↑ₘ (S n)]ᵐ[sb_params n]) $[n, k] $[n, k].

(** A judgment about closed terms at [⋅] holds in every semantically
    well-formed context: [rel_exp_under_ctx_wk] along [wk_id] from [Γ] to [⋅]. *)
Lemma closed_weaken_sem : forall {GC : GCtx} Γ T N N',
    ⊨ Γ ->
    ⋅ ⊨ N ≈ N' : T ->
    T[wk_id]ʷ = T -> N[wk_id]ʷ = N -> N'[wk_id]ʷ = N' ->
    Γ ⊨ N ≈ N' : T.
Proof.
  intros * HΓ H HT HN HN'.
  rewrite <- HT, <- HN, <- HN'.
  eapply rel_exp_under_ctx_wk; [| exact H ].
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  eapply (rel_wk_under_ctx_intro (R' := fun _ _ => True)); [ exact HR | |].
  - apply per_ctx_env_nil; reflexivity.
  - constructor; [ apply wk_mono_id | intros; exact I ].
Qed.

Section Identity.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.
  Hypothesis HR : sem_rwf Θ Ξ.
  Hypothesis HP : sem_pwf Θ Ξ.

  Theorem sem_msub_id : sem_msub Θ Ξ Θ Ξ ms_id nil.
  Proof.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    constructor.
    - exact (syn_msub_id _ _ Hg).
    - constructor.
    - intros * Hn Hk HΓ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      eapply closed_weaken_sem; [ eassumption | apply (HP _ _ _ _ Hn Hk) | | reflexivity | reflexivity ].
      eapply exp_closed_wk, param_type_scoped; [| eassumption | eassumption ].
      destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb).
    - intros * Hl HΓ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      eapply closed_weaken_sem; [ eassumption | apply (HR _ _ _ _ _ _ Hl) | | reflexivity | reflexivity ].
      eapply exp_closed_wk, wf_gc_lookup_type_closed; eassumption.
    - intros * Hl HΓ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      eapply closed_weaken_sem; [ eassumption | apply (HR _ _ _ _ _ _ Hl); reflexivity | | reflexivity | ].
      + eapply exp_closed_wk, wf_gc_lookup_type_closed; eassumption.
      + eapply exp_closed_wk, wf_gc_lookup_body_closed; eassumption.
  Qed.

  (** Hence the fundamental theorem at a fixed, semantically sound global
      context, in the old form. *)
  Corollary fundamental_at : forall Γ A M M',
      Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      @rel_exp_under_ctx (gc_mk Θ Ξ) Γ A M M'.
  Proof.
    intros * H.
    destruct kripke_fundamental as (_ & _ & Kq & _).
    destruct (Kq _ _ _ _ _ _ H _ _ _ _ sem_msub_id) as [_ H'].
    rewrite ctx_msub_id, List.app_nil_r, !exp_msub_qn_id in H'; exact H'.
  Qed.
End Identity.

(** ** 6. Pushing a frame is sound, given the semantics of the bigger stack *)

Section Push.
  Variables (Θ : gdeps) (U : gunit) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ U :: Ξ.
  Hypothesis HR : sem_rwf Θ (U :: Ξ).
  Hypothesis HP : sem_pwf Θ (U :: Ξ).

  Theorem sem_msub_push : sem_msub Θ Ξ Θ (U :: Ξ) (↑ₘ 1) nil.
  Proof.
    assert (HΘ : units_scoped Θ) by (eapply wf_scoped; eassumption).
    assert (Hb : ⊢ Θ ⍮ U :: Ξ ⍮ ⋅) by (constructor; assumption).
    assert (Hsc : gs_scoped (U :: Ξ)) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb)).
    constructor; [ constructor | | | | ].
    (* the syntactic fields: [push_preserves_wf]'s *)
    - assumption.
    - intros * Hn Hk _ HΓ.
      rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), exp_params_shift.
      cbn [msubst MSub_exp exp_msub ms_param ms_shift lp_mod lp_param].
      split; econstructor; cbn; eassumption.
    - intros * Hl _ HΓ.
      rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_pi_msub, (exp_msub_ext _ _ _ (ms_qn_shift _ _)).
      cbn [msubst MSub_exp exp_msub ms_glob ms_shift].
      pose proof (gc_lookup_push _ U _ _ _ _ _ _ _ HΘ Hl) as Hl'.
      split; econstructor; eassumption.
    - intros * Hl _ HΓ.
      rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_pi_msub, ctx_fn_msub,
        !(exp_msub_ext _ _ _ (ms_qn_shift _ _)).
      cbn [msubst MSub_exp exp_msub ms_glob ms_shift].
      pose proof (gc_lookup_push _ U _ _ _ _ _ _ _ HΘ Hl) as Hl'; cbn in Hl'.
      econstructor; eassumption.
    (* the semantic fields: a parameter or a global of the smaller stack is one
       of the bigger stack, which is sound by [HR]/[HP] *)
    - constructor.
    - intros * Hn Hk _ HΓs.
      rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), exp_params_shift.
      cbn [msubst MSub_exp exp_msub ms_param ms_shift lp_mod lp_param].
      eapply closed_weaken_sem; [ eassumption | apply (HP (S n) U0 k T Hn Hk) | | reflexivity | reflexivity ].
      eapply exp_closed_wk, (param_type_scoped (U :: Ξ) (S n)); eassumption.
    - intros * Hl _ HΓs.
      rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_pi_msub, (exp_msub_ext _ _ _ (ms_qn_shift _ _)).
      cbn [msubst MSub_exp exp_msub ms_glob ms_shift].
      pose proof (gc_lookup_push _ U _ _ _ _ _ _ _ HΘ Hl) as Hl'.
      eapply closed_weaken_sem; [ eassumption | apply (HR _ _ _ _ _ _ Hl') | | reflexivity | reflexivity ].
      eapply exp_closed_wk, wf_gc_lookup_type_closed; eassumption.
    - intros * Hl _ HΓs.
      rewrite !(exp_msub_ext _ _ _ (ms_qn_shift _ _)), ctx_pi_msub, ctx_fn_msub,
        !(exp_msub_ext _ _ _ (ms_qn_shift _ _)).
      cbn [msubst MSub_exp exp_msub ms_glob ms_shift].
      pose proof (gc_lookup_push _ U _ _ _ _ _ _ _ HΘ Hl) as Hl'; cbn in Hl'.
      eapply closed_weaken_sem;
        [ eassumption | apply (HR _ _ _ _ _ _ Hl'); reflexivity | | reflexivity | ].
      + eapply exp_closed_wk, wf_gc_lookup_type_closed; eassumption.
      + eapply exp_closed_wk, wf_gc_lookup_body_closed; eassumption.
  Qed.
End Push.

(** ** 7. [sem_rwf]/[sem_pwf] from the validity of resolved types and bodies

    The δ-rule evaluates the generalized body in the *empty* environment, and a
    global or parameter is a neutral annotated with its type evaluated there.
    [nil] is reached by [sb_zero], which evaluates to [nil] in any environment
    (a list environment reads [zeroᵈ] past its end); so instantiating a [⋅]
    judgment at [sb_zero] relates the value at [nil] to the value anywhere. *)

Definition sb_zero : sub := fun _ => a_zero.

Lemma eval_sub_zero_nil : forall {Θ Ξ} ρ, eval_sub Θ Ξ sb_zero ρ nil.
Proof. intros * x; rewrite env_var_ge by (cbn; lia); constructor. Qed.

Lemma rel_sub_zero_nil : forall {GC : GCtx} Γ R, per_ctx_env R Γ Γ -> Γ ⊨s sb_zero ≈ sb_zero : ⋅.
Proof.
  intros * HR.
  assert (H0 : per_ctx_env (fun _ _ => True) ⋅ ⋅) by (apply per_ctx_env_nil; reflexivity).
  exists R, HR, (fun _ _ => True), H0.
  intros * _ φ _ ρ ρ' _.
  apply (mk_rel_sub nil nil nil nil); try apply eval_sub_zero_nil.
  all: try (intros x; rewrite env_var_ge by (cbn; lia); constructor).
  all: cbn; repeat split.
Qed.

(** δ: a closed term [G] that evaluates anywhere to what [N] evaluates to at
    [nil] is equal to [N]. *)
Lemma rel_exp_delta_nil : forall {GC : GCtx} T N G,
    ⋅ ⊨ N : T ->
    (forall σ, T[σ] = T) -> (forall σ, N[σ] = N) -> (forall σ, G[σ] = G) ->
    (forall ρ m, eval_exp gc_deps gc_stack N nil m -> eval_exp gc_deps gc_stack G ρ m) ->
    ⋅ ⊨ G ≈ N : T.
Proof.
  intros * HN HT HNc HG Hδ.
  destruct HN as [env_rel [Hnil [i HNgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HNgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R1 [Ht1 He1]].
  destruct (HNgen _ _ HΓ' _ _ (rel_sub_zero_nil _ _ HΓ') _ _ _ _ Hρ
              (eval_sub_zero_nil _) (eval_sub_zero_nil _)) as [R2 [Ht2 He2]].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 ? ? Hb4 Hty2].
  destruct He1 as [v1 v2 v3 v4 Hv1 ? ? Hv4 Hc1].
  destruct He2 as [w1 w2 w3 w4 Hw1 ? ? Hw4 Hc2].
  rewrite HT in Ha1, Ha4, Hb1, Hb4.
  rewrite HNc in Hv1, Hv4, Hw1, Hw4.
  functional_eval_rewrite_clear.
  assert (Hm1 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hm2 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  exists R1; split.
  - apply (mk_rel_exp a1 a2 a3 a4); rewrite ?HT; assumption.
  - apply (mk_rel_exp w2 w2 v3 v4); rewrite ?HG, ?HNc; try (apply Hδ; assumption); try assumption.
    merge_rel_chain Hc1 Hc2 v1.
Qed.

(** A neutral: a closed [G] that evaluates anywhere to [⇑ a d], [a] the type at
    [nil]. *)
Lemma rel_exp_neut_nil : forall {GC : GCtx} T G i d,
    ⋅ ⊨ T : Type@i ->
    (forall σ, T[σ] = T) -> (forall σ, G[σ] = G) ->
    per_bot d d ->
    (forall ρ a, eval_exp gc_deps gc_stack T nil a -> eval_exp gc_deps gc_stack G ρ (⇑ a d)) ->
    ⋅ ⊨ G : T.
Proof.
  intros * HT HTc HG Hd Hev0.
  destruct (rel_exp_of_typ_inversion HT) as [env_rel [Hnil HTgen]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_exp_implies_rel_typ (HTgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')) as [R1 Ht1].
  destruct (rel_exp_implies_rel_typ (HTgen _ _ HΓ' _ _ (rel_sub_zero_nil _ _ HΓ') _ _ _ _ Hρ
              (eval_sub_zero_nil _) (eval_sub_zero_nil _))) as [R2 Ht2].
  exists R1; split; [ exact Ht1 |].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 ? ? Hb4 Hty2].
  rewrite HTc in Ha1, Ha4, Hb1, Hb4.
  functional_eval_rewrite_clear.
  assert (Hm1 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hm2 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R2) by pairwise.
  assert (Hb : DF b2 ≈ b2 ∈ per_univ_elem i ↘ R2) by pairwise.
  pose proof (per_bot_then_per_elem Hb Hd) as Hr.
  handle_per_univ_elem_irrel.
  apply (mk_rel_exp (⇑ b2 d) (⇑ b2 d) (⇑ b2 d) (⇑ b2 d)); rewrite ?HG; try (apply Hev0; assumption).
  cbn; repeat split; exact Hr.
Qed.

(** The semantic [rwf]: validity at [⋅] of what resolution hands back. *)
Definition sem_rwf_raw (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall p Δ b pv A B,
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    (exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) (ctx_pi Δ A) (ctx_pi Δ A)) /\
    (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (ctx_fn Δ M) (ctx_fn Δ M)).

Definition sem_pwf_raw (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall n U k T,
    List.nth_error Ξ n = Some U ->
    gu_params U ∋ #k : T ->
    exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) (T[↑ₘ (S n)]ᵐ[sb_params n]) (T[↑ₘ (S n)]ᵐ[sb_params n]).

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  (** One global at a time, so that it can be used inside an induction. *)
  Lemma glob_sem_of_raw : forall p Δ b pv A B,
      Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
      (exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) (ctx_pi Δ A) (ctx_pi Δ A)) /\
      (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (ctx_fn Δ M) (ctx_fn Δ M)) ->
      @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (a_glob p) (a_glob p) /\
      (forall M, b = true -> B = Some M ->
         @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (a_glob p) (ctx_fn Δ M)).
  Proof.
    intros p Δ b pv A B Hl HRp.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    pose proof (wf_gctx_stack _ _ Hg) as HΞ.
    pose proof (gc_resolve_complete _ _ _ _ _ (wf_gstack_canon _ _ HΞ)
                  (wf_gdeps_canon _ (wf_gstack_deps _ _ HΞ)) Hl) as Hr.
    pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hb Hl) as HsT.
    destruct HRp as [[i HT] HM].
    assert (Hdelta : forall M, b = true -> B = Some M ->
               @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (a_glob p) (ctx_fn Δ M)).
    { intros M -> ->.
      pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ _ Hb Hl) as HsM.
      eapply rel_exp_delta_nil; [ apply HM; reflexivity | | | reflexivity |].
      - intros; eapply exp_closed_sub; eassumption.
      - intros; eapply exp_closed_sub; eassumption.
      - intros * Hev; econstructor; eassumption. }
    split; [| exact Hdelta ].
    destruct b; [ destruct B as [M |] |].
    - pose proof (Hdelta M eq_refl eq_refl) as H.
      eapply rel_exp_under_ctx_trans; [ exact H | apply rel_exp_under_ctx_sym; exact H ].
    - eapply rel_exp_neut_nil with (d := d_glob p); [ exact HT | | reflexivity | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros s; eexists; split; constructor.
      + intros * Hev; eapply eval_exp_glob_neut; [ exact Hr | right; reflexivity | exact Hev ].
    - eapply rel_exp_neut_nil with (d := d_glob p); [ exact HT | | reflexivity | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros s; eexists; split; constructor.
      + intros * Hev; eapply eval_exp_glob_neut; [ exact Hr | left; reflexivity | exact Hev ].
  Qed.

  Lemma sem_rwf_of_raw : sem_rwf_raw Θ Ξ -> sem_rwf Θ Ξ.
  Proof. intros HR p * Hl; exact (glob_sem_of_raw _ _ _ _ _ _ Hl (HR _ _ _ _ _ _ Hl)). Qed.

  Lemma sem_pwf_of_raw : sem_pwf_raw Θ Ξ -> sem_pwf Θ Ξ.
  Proof.
    intros HP n U k T Hn Hk.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    assert (Hsc : gs_scoped Ξ) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb)).
    pose proof (param_type_scoped _ _ _ _ _ Hsc Hn Hk) as HsT.
    destruct (HP _ _ _ _ Hn Hk) as [i HT].
    eapply rel_exp_neut_nil with (d := d_param {| lp_mod := n; lp_param := k |});
      [ exact HT | | reflexivity | |].
    - intros; eapply exp_closed_sub; eassumption.
    - intros s; eexists; split; constructor.
    - intros * Hev; eapply eval_exp_param; [| exact Hev ].
      unfold gs_param; cbn; rewrite Hn, (ctx_get_complete _ _ _ Hk); reflexivity.
  Qed.
End Raw.

(** ** 8. Kripke validity moves along *syntactically* sound substitutions

    A consequence of [sem_msub_then] needing only [syn_msub] of its first
    step: closing, pushing and growing need no semantic argument at all to move
    a Kripke-valid judgment.  Semantics is needed only for the *last* step into
    the context where the judgment is finally read off. *)

Lemma kexp_transport_syn : forall Θ1 Ξ1 Θ2 Ξ2 μ E Γ A M M',
    syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E ->
    kexp_eq Θ1 Ξ1 Γ A M M' ->
    kexp_eq Θ2 Ξ2 (Γ[μ]ᵐ ++ E) A[ms_qn (length Γ) μ]ᵐ M[ms_qn (length Γ) μ]ᵐ M'[ms_qn (length Γ) μ]ᵐ.
Proof.
  intros * Hμ H Θ3 Ξ3 ν E' Hν.
  destruct (H _ _ _ _ (sem_msub_then _ _ _ _ _ _ _ _ _ _ Hμ Hν)) as [H1 H2].
  rewrite <- tctx_then in H1, H2; rewrite <- !tm_then in H2.
  split; assumption.
Qed.

(** ** 9. Rebasing (growing a frame, adding a level) is sound, given the
    semantics, *at the target*, of the source's globals only *)

Section Rebase.
  Variables (Θ1 Θ2 : gdeps) (Ξ1 Ξ2 : gstack).
  #[local] Notation G2 := (gc_mk Θ2 Ξ2).
  Hypothesis Hr : forall r Δ b pv A B,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> Θ2 ⍮ Ξ2 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B.
  Hypothesis Hn : forall n U, List.nth_error Ξ1 n = Some U ->
      exists U', List.nth_error Ξ2 n = Some U' /\ gu_params U' = gu_params U.
  Hypothesis Hb : ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅.
  Hypothesis HR : forall p Δ b pv A B,
      Θ1 ⍮ Ξ1 ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
      @rel_exp_under_ctx G2 ⋅ (ctx_pi Δ A) (a_glob p) (a_glob p) /\
      (forall M, b = true -> B = Some M -> @rel_exp_under_ctx G2 ⋅ (ctx_pi Δ A) (a_glob p) (ctx_fn Δ M)).
  Hypothesis HP : forall n U k T,
      List.nth_error Ξ1 n = Some U ->
      gu_params U ∋ #k : T ->
      @rel_exp_under_ctx G2 ⋅ (T[↑ₘ (S n)]ᵐ[sb_params n]) $[n, k] $[n, k].

  Theorem sem_msub_rebase : sem_msub Θ1 Ξ1 Θ2 Ξ2 ms_id nil.
  Proof.
    assert (Hsc : gs_scoped Ξ2) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb)).
    constructor; [ constructor | | | | ].
    - assumption.
    - intros * Hn1 Hk _ HΓ; rewrite !exp_msub_qn_id.
      destruct (Hn _ _ Hn1) as (U' & Hn2 & Hp).
      rewrite <- Hp in Hk; split; econstructor; eassumption.
    - intros * Hl _ HΓ; rewrite !exp_msub_qn_id; split; econstructor; eauto.
    - intros * Hl _ HΓ; rewrite !exp_msub_qn_id; econstructor; eauto.
    - constructor.
    - intros * Hn1 Hk _ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      destruct (Hn _ _ Hn1) as (U' & Hn2 & Hp).
      eapply closed_weaken_sem; [ eassumption | apply (HP _ _ _ _ Hn1 Hk) | | reflexivity | reflexivity ].
      rewrite <- Hp in Hk.
      eapply exp_closed_wk, param_type_scoped; eassumption.
    - intros * Hl HΓ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      eapply closed_weaken_sem; [ eassumption | apply (HR _ _ _ _ _ _ Hl) | | reflexivity | reflexivity ].
      eapply exp_closed_wk, wf_gc_lookup_type_closed; [ exact Hb | apply Hr; eassumption ].
    - intros * Hl HΓ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      eapply closed_weaken_sem; [ eassumption | apply (HR _ _ _ _ _ _ Hl); reflexivity | | reflexivity | ].
      + eapply exp_closed_wk, wf_gc_lookup_type_closed; [ exact Hb | apply Hr; eassumption ].
      + eapply exp_closed_wk, wf_gc_lookup_body_closed; [ exact Hb | apply Hr; eassumption ].
  Qed.
End Rebase.

