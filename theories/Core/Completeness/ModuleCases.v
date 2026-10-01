(** * The Global Rules: Validity in Every Valid Extension

    Names are absolute and closed entries are stored closed, so the only way a
    judgment of one global context is used in another is by *reading* it there:
    in an extension ([gc_ext]) that resolves what the first one does, the same
    way.  The PER model is not monotone under extension, so the fundamental
    theorem is stated Kripke-style: a judgment of [Θ1 ⍮ Ξ1] is valid, in the
    fixed-context sense, in every well-formed extension in which what
    [Θ1 ⍮ Ξ1] resolves is valid ([sem_ext]).  No term is transformed on the
    way: the ordinary cases are the fixed-context case lemmas at the extension
    as they are ([ext_fundamental]). *)

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

(** ** 1. Valid extensions *)

(** [Θ2 ⍮ Ξ2] extends [Θ1 ⍮ Ξ1], is well formed, and validates what
    [Θ1 ⍮ Ξ1] resolves: each global, its unfolding, and each parameter, at [⋅]
    in the fixed-context sense at [Θ2 ⍮ Ξ2]. *)
Record sem_ext (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { se_ext : gc_ext Θ1 Ξ1 Θ2 Ξ2
  ; se_wf : ⊢g Θ2 ⍮ Ξ2
  ; se_glob : forall r b pv A B,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ ge_def b pv A B ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A (a_glob r) (a_glob r)
  ; se_unfold : forall r pv A M,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ ge_def true pv A (Some M) ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A (a_glob r) M
  ; se_param : forall lp T,
      gs_param Ξ1 lp = Some T ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ T (a_param lp) (a_param lp)
  }.

(** ** 2. Judgments valid in every valid extension *)

Definition kctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2, sem_ext Θ1 Ξ1 Θ2 Ξ2 -> @sem_ctx (gc_mk Θ2 Ξ2) Γ.

Definition kexp_eq Θ1 Ξ1 Γ A M M' : Prop :=
  forall Θ2 Ξ2, sem_ext Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M'.

Definition ksubtyp Θ1 Ξ1 Γ A A' : Prop :=
  forall Θ2 Ξ2, sem_ext Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A'.

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

(** ** 3. The fundamental theorem, Kripke form *)

Theorem ext_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kexp_eq Θ Ξ Γ A M M) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> kexp_eq Θ Ξ Γ A M M') /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ksubtyp Θ Ξ Γ A A').
Proof.
  apply syntactic_wf_mut_ind; unfold kctx, kexp_eq, ksubtyp; intros;
    repeat match goal with IH : forall _ _, sem_ext _ _ _ _ -> _ |- _ =>
      specialize (IH _ _ ltac:(eassumption)) end;
    destruct_conjs.
  all: try solve [ constructor | eapply rel_ctx_extend'; eassumption ].
  all: try (split; [ assumption |]).
  (* every ordinary rule: the existing fixed-context case lemma, at the extension *)
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
    | apply subtyp_univ; [assumption | lia]
    | eapply valid_exp_var; eassumption
    | eapply rel_exp_fn_eta; eassumption ].
  (* parameters, globals, δ: closed, valid at [⋅] in the extension *)
  all: saturate_closed.
  all: match goal with
       | Hp : gs_param _ ?lp = Some _, Hs : sem_ext _ _ _ _ |- _ =>
           eapply closed_weaken_sem; [ eassumption | apply (se_param _ _ _ _ Hs _ _ Hp) | .. ]
       | Hl : _ ⍮ _ ∋ᵍ _ ⇒ ge_def true _ _ (Some _), Hs : sem_ext _ _ _ _ |- _ ⊨ _ ≈ ?M : _ =>
           eapply closed_weaken_sem; [ eassumption | apply (se_unfold _ _ _ _ Hs _ _ _ _ Hl) | .. ]
       | Hl : _ ⍮ _ ∋ᵍ _ ⇒ ge_def _ _ _ _, Hs : sem_ext _ _ _ _ |- _ =>
           eapply closed_weaken_sem; [ eassumption | apply (se_glob _ _ _ _ Hs _ _ _ _ _ Hl) | .. ]
       end.
  all: try reflexivity; eapply exp_closed_wk; eassumption.
Qed.

(** ** 4. The δ-rule and neutrals at [⋅]

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


(** ** 5. Validity of a global and a parameter from that of its type and body *)

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  Lemma glob_sem_of_raw : forall p b pv A B,
      Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
      (exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) A A) ->
      (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A M M) ->
      @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_glob p) (a_glob p) /\
      (forall M, b = true -> B = Some M -> @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_glob p) M).
  Proof.
    intros p b pv A B Hl [i HT] HM.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    pose proof (wf_gctx_stack _ _ Hg) as HΞ.
    pose proof (gc_resolve_complete _ _ _ _ (wf_gstack_canon _ _ HΞ)
                  (wf_gdeps_canon _ (wf_gstack_deps _ _ HΞ)) Hl) as Hr.
    pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ Hb Hl) as HsT.
    assert (Hdelta : forall M, b = true -> B = Some M ->
               @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_glob p) M).
    { intros M -> ->.
      pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ Hb Hl) as HsM.
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

  Lemma param_sem_of_raw : forall lp T,
      gs_param Ξ lp = Some T ->
      (exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) T T) ->
      @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ T (a_param lp) (a_param lp).
  Proof.
    intros * Hp [i HT].
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    pose proof (wf_param_type_closed _ _ _ _ _ Hb Hp) as HsT.
    eapply rel_exp_neut_nil with (d := d_param lp); [ exact HT | | reflexivity | |].
    - intros; eapply exp_closed_sub; eassumption.
    - intros s; eexists; split; constructor.
    - intros * Hev; eapply eval_exp_param; [ exact Hp | exact Hev ].
  Qed.
End Raw.

(** ** 6. A valid extension from the validity of what is resolved *)

Definition sem_valid (Θ : gdeps) (Ξ : gstack) (A M : exp) : Prop :=
  @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A M M.

Lemma sem_ext_of_raw : forall Θ1 Ξ1 Θ2 Ξ2,
    gc_ext Θ1 Ξ1 Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 ->
    SG sem_valid Θ1 Ξ1 Θ2 Ξ2 -> SP sem_valid Θ1 Ξ1 Θ2 Ξ2 ->
    sem_ext Θ1 Ξ1 Θ2 Ξ2.
Proof.
  intros * He Hg HS HP; pose proof He as [Hr Hp]; constructor; [ assumption | assumption | | |].
  - intros * Hl; destruct (HS _ _ _ _ _ Hl) as [HT HM].
    exact (proj1 (glob_sem_of_raw _ _ Hg _ _ _ _ _ (Hr _ _ Hl) HT HM)).
  - intros * Hl; destruct (HS _ _ _ _ _ Hl) as [HT HM].
    exact (proj2 (glob_sem_of_raw _ _ Hg _ _ _ _ _ (Hr _ _ Hl) HT HM) _ eq_refl eq_refl).
  - intros * Hp1; apply (param_sem_of_raw _ _ Hg _ _ (Hp _ _ Hp1) (HP _ _ Hp1)).
Qed.
