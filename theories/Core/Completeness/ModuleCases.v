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
From Mctt.Core.Semantic Require Import Realizability Simulation PERSim Bridge.
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

(** ** 4. The identity is sound, given the semantics of what resolution hands back

    [sem_rwf]/[sem_pwf] are the semantic [rwf]: every resolved global, and every
    parameter, is valid at [⋅] in the *same* global context.  They are stated
    directly on [a_glob p] / [$[n, k]], i.e. already including δ; section 5
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

(** ** 5. [sem_rwf]/[sem_pwf] from the validity of resolved types and bodies

    The δ-rule evaluates the generalized body in the *empty* environment, and a
    global or parameter is a neutral annotated with its type evaluated there.
    [nil] is reached by [sb_zero], which evaluates to [nil] in any environment
    (a list environment reads [zeroᵈ] past its end); so instantiating a [⋅]
    judgment at [sb_zero] relates the value at [nil] to the value anywhere. *)

Definition sb_zero : sub := fun _ => a_zero.

Lemma eval_sub_zero_nil : forall {Θ Ξ κ} ρ, eval_sub Θ Ξ κ sb_zero ρ nil.
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

(** δ: a closed [G] that evaluates anywhere to [g], related to what [N]
    evaluates to at [nil], is equal to [N]. *)
Lemma rel_exp_delta_val : forall {GC : GCtx} T N G g,
    ⋅ ⊨ N : T ->
    (forall σ, T[σ] = T) -> (forall σ, N[σ] = N) -> (forall σ, G[σ] = G) ->
    (forall ρ, eval_exp gc_deps gc_stack me_top G ρ g) ->
    (forall n a i R, eval_exp gc_deps gc_stack me_top N nil n -> eval_exp gc_deps gc_stack me_top T nil a ->
       DF a ≈ a ∈ per_univ_elem i ↘ R -> Dom n ≈ g ∈ R) ->
    ⋅ ⊨ G ≈ N : T.
Proof.
  intros * HN HT HNc HG Hev Hgr.
  destruct HN as [env_rel [Hnil [i HNgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hevσ Hevσ'.
  destruct (HNgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hevσ Hevσ') as [R1 [Ht1 He1]].
  destruct (HNgen _ _ HΓ' _ _ (rel_sub_zero_nil _ _ HΓ') _ _ _ _ Hρ
              (eval_sub_zero_nil _) (eval_sub_zero_nil _)) as [R2 [Ht2 He2]].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 Hb2 ? Hb4 Hty2].
  destruct He1 as [v1 v2 v3 v4 Hv1 ? ? Hv4 Hc1].
  destruct He2 as [w1 w2 w3 w4 Hw1 Hw2 ? Hw4 Hc2].
  rewrite HT in Ha1, Ha4, Hb1, Hb4.
  rewrite HNc in Hv1, Hv4, Hw1, Hw4.
  assert (Hb : DF b2 ≈ b2 ∈ per_univ_elem i ↘ R2) by pairwise.
  pose proof (Hgr _ _ _ _ Hw2 Hb2 Hb) as Hr.
  functional_eval_rewrite_clear.
  assert (Hm1 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hm2 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  assert (Hm : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1) by pairwise.
  exists R1; split.
  - apply (mk_rel_exp a1 a2 a3 a4); rewrite ?HT; assumption.
  - apply (mk_rel_exp g g v3 v4); rewrite ?HG, ?HNc; try apply Hev; try assumption.
    assert (Hw : rel_chain R1 (w2 :: w2 :: v3 :: v4 :: nil)) by merge_rel_chain Hc1 Hc2 v1.
    cbn in Hw |- *; destruct Hw as (Hl1 & Hl2 & Hl3).
    assert (Hgw : R1 g w2) by (eapply per_elem_sym; eassumption).
    repeat split; [ eapply (per_elem_trans _ _ _ _ _ _ _ Hm); eassumption
                  | eapply (per_elem_trans _ _ _ _ _ _ _ Hm); eassumption | exact Hl3 ].
Qed.

(** A closed [G] that evaluates anywhere to [g], an element of the type at
    [nil]. *)
Lemma rel_exp_val_nil : forall {GC : GCtx} T G i g,
    ⋅ ⊨ T : Type@i ->
    (forall σ, T[σ] = T) -> (forall σ, G[σ] = G) ->
    (forall ρ, eval_exp gc_deps gc_stack me_top G ρ g) ->
    (forall a R, eval_exp gc_deps gc_stack me_top T nil a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> Dom g ≈ g ∈ R) ->
    ⋅ ⊨ G : T.
Proof.
  intros * HT HTc HG Hev Hgr.
  destruct (rel_exp_of_typ_inversion HT) as [env_rel [Hnil HTgen]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hevσ Hevσ'.
  destruct (rel_exp_implies_rel_typ (HTgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hevσ Hevσ')) as [R1 Ht1].
  destruct (rel_exp_implies_rel_typ (HTgen _ _ HΓ' _ _ (rel_sub_zero_nil _ _ HΓ') _ _ _ _ Hρ
              (eval_sub_zero_nil _) (eval_sub_zero_nil _))) as [R2 Ht2].
  exists R1; split; [ exact Ht1 |].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 Hb2 ? Hb4 Hty2].
  rewrite HTc in Ha1, Ha4, Hb1, Hb4.
  assert (Hb : DF b2 ≈ b2 ∈ per_univ_elem i ↘ R2) by pairwise.
  pose proof (Hgr _ _ Hb2 Hb) as Hr.
  functional_eval_rewrite_clear.
  assert (Hm1 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hm2 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  apply (mk_rel_exp g g g g); rewrite ?HG; try apply Hev.
  cbn; repeat split; exact Hr.
Qed.

(** A closed type valid at [⋅] evaluates at [nil]. *)
Lemma typ_nil_eval : forall {GC : GCtx} T i,
    ⋅ ⊨ T : Type@i -> exists a R, eval_exp gc_deps gc_stack me_top T nil a /\ DF a ≈ a ∈ per_univ_elem i ↘ R.
Proof.
  intros * HT.
  destruct (rel_exp_of_typ_inversion_simple HT) as [env_rel [Hnil H]].
  assert (Hρ : env_rel nil nil) by (inversion Hnil as [? Heq |]; subst; apply Heq; exact I).
  destruct (H _ _ Hρ) as (a & a' & Ha & Ha' & [R HR]).
  pose proof (functional_eval_exp _ _ _ _ _ Ha Ha') as <-.
  exists a, R; split; assumption.
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
  Proof. (* OPTA-TODO *) Admitted.

  Lemma sem_rwf_of_raw : sem_rwf_raw Θ Ξ -> sem_rwf Θ Ξ.
  Proof. intros HR p * Hl; exact (glob_sem_of_raw _ _ _ _ _ _ Hl (HR _ _ _ _ _ _ Hl)). Qed.

  (** A parameter of an open frame, given that its own type and those of the
      parameters bound before it are valid. *)
  Lemma param_sem_gen : forall n U k T,
      List.nth_error Ξ n = Some U ->
      gu_params U ∋ #k : T ->
      (forall k' T', k <= k' -> gu_params U ∋ #k' : T' ->
         exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) (T'[↑ₘ (S n)]ᵐ[sb_params n]) (T'[↑ₘ (S n)]ᵐ[sb_params n])) ->
      @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (T[↑ₘ (S n)]ᵐ[sb_params n]) $[n, k] $[n, k].
  Proof.
    intros n U k T Hn Hk Hall.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    assert (Hsc : gs_scoped Ξ) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb)).
    pose proof (param_type_scoped _ _ _ _ _ Hsc Hn Hk) as HsT.
    destruct (gs_scoped_nth _ _ _ Hsc Hn) as [HPs _].
    pose proof (ctx_lookup_length _ _ _ Hk) as Hkl.
    destruct (ctx_lookup_nth _ _ _ Hk) as (A & HA & ->).
    rewrite param_type_tsub in HsT.
    (* the types of the parameters from [k] out evaluate at the top level *)
    assert (Hev : forall k' A', k <= k' -> List.nth_error (gu_params U) k' = Some A' ->
                    exists t, eval_exp Θ Ξ me_top (exp_tsub (θp n k') A') nil t).
    { intros k' A' Hle HA'.
      destruct (ctx_lookup_exists (gu_params U) k' ltac:(apply List.nth_error_Some; congruence)) as [T' Hk'].
      destruct (ctx_lookup_nth _ _ _ Hk') as (A'' & HA'' & ->).
      rewrite HA' in HA''; injection HA'' as <-.
      destruct (Hall _ _ Hle Hk') as [i Hi].
      rewrite param_type_tsub in Hi.
      destruct (@typ_nil_eval (gc_mk Θ Ξ) _ _ Hi) as (t & R & Ht & _); eauto. }
    destruct (ptele_exists Θ Ξ _ _ _ Hn HPs (List.length (gu_params U) - k) k ltac:(lia) Hev) as [ρ Hρ].
    destruct (Hall _ _ (le_n _) Hk) as [i Hi].
    rewrite param_type_tsub in Hi |- *.
    destruct (@typ_nil_eval (gc_mk Θ Ξ) _ _ Hi) as (t & R0 & Ht & HR0).
    destruct (param_value Θ Ξ _ _ _ _ _ _ Hn HA (exp_scoped_ok _ _ _ (ctx_scoped_nth _ _ _ _ HPs HA)) Hρ Ht)
      as (a & Ha & Hs).
    eapply (@rel_exp_val_nil (gc_mk Θ Ξ)) with (g := ⇑ a (d_param (lp_mk n k))); [ exact Hi | | reflexivity | |].
    - intros; eapply exp_closed_sub; eassumption.
    - intros ρ0; eapply eval_param_env; exact Ha.
    - intros a0 R Ha0 HR.
      pose proof (functional_eval_exp _ _ _ _ _ Ha0 Ht) as ->.
      assert (Hta : @per_univ_elem (gc_mk Θ Ξ) i R t a) by (eapply (@per_univ_elem_sim_r (gc_mk Θ Ξ)); [ exact HR | exact Hs ]).
      assert (Hd : @per_bot (gc_mk Θ Ξ) (d_param (lp_mk n k)) (d_param (lp_mk n k))) by (intros s; eexists; split; constructor).
      pose proof (@per_bot_then_per_elem (gc_mk Θ Ξ) _ _ _ _ _ _ Hta Hd) as Hr.
      eapply (@per_elem_trans (gc_mk Θ Ξ) _ _ _ _ _ _ _ HR); [ eapply (@per_elem_sym (gc_mk Θ Ξ)); [ exact HR | exact Hr ] | exact Hr ].
  Qed.

  Lemma sem_pwf_of_raw : sem_pwf_raw Θ Ξ -> sem_pwf Θ Ξ.
  Proof. intros HP n U k T Hn Hk; apply (param_sem_gen _ _ _ _ Hn Hk); intros; eapply HP; eassumption. Qed.
End Raw.

