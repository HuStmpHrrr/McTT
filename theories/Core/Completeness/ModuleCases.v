(** * The Global Rules: Validity along an Embedding

    A judgment of the global context [Θ1 ⍮ Ξ1] is valid at every [Θ2 ⍮ Ξ2] it
    embeds into, provided what resolves at [Θ1 ⍮ Ξ1] is valid at [Θ2 ⍮ Ξ2] and
    the modules of [Θ2 ⍮ Ξ2] are semantically valid ([sem_emb]).  Entries are
    closed and paths absolute, so an embedding moves nothing: the fundamental
    theorem holds in this form for every rule ([kripke_fundamental]), each case
    being the fixed-context case lemma at the target.  At the identity it is
    the fixed-context theorem. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases LetCases NatCases SubstitutionCases SubtypingCases
  TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases InstanceCases
  MemberCases MemberTyping MemberReps MemberSem ModexpCases PathCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound embeddings *)

Record sem_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { sme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; sme_glob : forall r b pv A B Γ,
      gc_resolve Θ1 Ξ1 r = Some (ge_def b pv A B) ->
      @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A (a_glob r) (a_glob r)
  ; sme_unfold : forall r A M Γ pv,
      gc_resolve Θ1 Ξ1 r = Some (ge_def true pv A (Some M)) ->
      @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A (a_glob r) M
  ; sme_mods : @gsem_ok (gc_mk Θ2 Ξ2)
  }.

(** ** 2. The fundamental theorem along an embedding *)

Definition kctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 -> @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Γ.

Definition kexp_eq Θ1 Ξ1 Γ A M M' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M'.

Definition ksubtyp Θ1 Ξ1 Γ A A' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Γ /\ @subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A'.

Definition kext Θ1 Ξ1 Γ Ψ Ψ' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ' /\
    @ctx_mt (gc_mk Θ2 Ξ2) (Ψ ++ Γ) /\ @ctx_mt (gc_mk Θ2 Ξ2) (Ψ' ++ Γ) /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Γ.

Definition kunit Θ1 Ξ1 Γ U U' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U' /\
    @unit_mt (gc_mk Θ2 Ξ2) Γ U /\ @unit_mt (gc_mk Θ2 Ξ2) Γ U' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Γ.

Definition kmod Θ1 Ξ1 Γ H H' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H' /\
    @sem_mt (gc_mk Θ2 Ξ2) Γ H /\ @sem_mt (gc_mk Θ2 Ξ2) Γ H' /\
    @sem_unf (gc_mk Θ2 Ξ2) Γ H /\ @sem_unf (gc_mk Θ2 Ξ2) Γ H' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Γ.

Ltac kcase :=
  repeat match goal with IH : forall _ _, sem_emb _ _ _ _ -> _, He : sem_emb _ _ _ _ |- _ =>
    specialize (IH _ _ He) end;
  destruct_conjs.

Theorem kripke_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kexp_eq Θ Ξ Γ A M M) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> kexp_eq Θ Ξ Γ A M M') /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ksubtyp Θ Ξ Γ A A') /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> kext Θ Ξ Γ Ψ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> kunit Θ Ξ Γ U U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> kmod Θ Ξ Γ H H').
Proof.
  apply syntactic_wf_mut_ind; unfold kctx, kexp_eq, ksubtyp, kext, kunit, kmod; intros;
    pose proof (em_res _ _ _ _ (sme_emb _ _ _ _ ltac:(eassumption))) as Hsub;
    pose proof (sme_mods _ _ _ _ ltac:(eassumption)) as Hgs;
    kcase.
  all: idtac.
Admitted.

(** ** 3. Closed judgments *)

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

(** ** Globals from the validity of their types and bodies

    The δ-rule evaluates the generalized body in the empty environment, and a
    global or parameter is a neutral annotated with its type evaluated there.
    [nil] is reached by [sb_zero], which evaluates to [nil] in any environment (a
    list environment reads [zeroᵈ] past its end), so instantiating a [⋅] judgment
    at [sb_zero] relates the value at [nil] to the value anywhere. *)

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

(** ** 4. The PER model's notion of a valid entry *)

Definition sem_entry (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) A A) /\
      (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A M M)
  | ge_mod _ _ => True
  end.

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  Lemma glob_sem_of_raw : forall p b pv A B,
      gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
      sem_entry Θ Ξ (ge_def b pv A B) ->
      @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_glob p) (a_glob p) /\
      (forall M, b = true -> B = Some M ->
         @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_glob p) M).
  Proof.
    intros p b pv A B Hr HRp.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    destruct (wf_gc_resolve_closed _ _ _ _ _ _ _ _ Hb Hr) as [HsT HsB].
    destruct HRp as [[i HT] HM].
    assert (Hdelta : forall M, b = true -> B = Some M ->
               @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_glob p) M).
    { intros M -> ->; cbn in HsB.
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
End Raw.

(** An embedding whose source entries are valid at the target is sound. *)
Theorem sem_emb_of : forall Θ1 Ξ1 Θ2 Ξ2,
    Emb Θ1 Ξ1 Θ2 Ξ2 -> GV sem_entry Θ1 Ξ1 Θ2 Ξ2 -> sem_emb Θ1 Ξ1 Θ2 Ξ2.
Proof.
  intros * He HG; pose proof He as [Hg Hs].
  constructor; [ exact He | |].
  - intros * Hr HΓ.
    pose proof (Hs _ _ Hr) as Hr2.
    eapply closed_weaken_sem; [ eassumption | | apply exp_wk_id | apply exp_wk_id | apply exp_wk_id ].
    exact (proj1 (glob_sem_of_raw _ _ Hg _ _ _ _ _ Hr2 (HG _ _ Hr))).
  - intros * Hr HΓ.
    pose proof (Hs _ _ Hr) as Hr2.
    eapply closed_weaken_sem; [ eassumption | | apply exp_wk_id | apply exp_wk_id | apply exp_wk_id ].
    exact (proj2 (glob_sem_of_raw _ _ Hg _ _ _ _ _ Hr2 (HG _ _ Hr)) _ eq_refl eq_refl).
Qed.

Lemma kread : forall Θ1 Ξ1 Θ2 Ξ2 A M,
    sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A M M.
Proof.
  intros * Hμ HM; destruct kripke_fundamental as (_ & Ke & _).
  destruct (Ke _ _ _ _ _ HM _ _ Hμ) as [_ H]; exact H.
Qed.

Lemma sem_entry_def : forall Θ Ξ A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> Good sem_entry Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    sem_entry Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M))).
Proof.
  intros * HM HG He.
  pose proof (sem_emb_of _ _ _ _ He (HG _ _ He)) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kread _ _ _ _ _ _ Hμ HT) |].
  intros ? [= <-]; exact (kread _ _ _ _ _ _ Hμ (ctx_fn_wf0 _ _ _ _ _ _ HA HM)).
Qed.

Lemma sem_entry_ax : forall Θ Ξ A i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Type@i -> Good sem_entry Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    sem_entry Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  pose proof (sem_emb_of _ _ _ _ He (HG _ _ He)) as Hμ.
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kread _ _ _ _ _ _ Hμ HT) | discriminate ].
Qed.

(** Every well-formed global context is semantically sound: the identity is a
    sound embedding. *)
Theorem gctx_sem : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> sem_emb Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply sem_emb_of; [ apply Emb_refl; assumption |].
  exact (global_induction sem_entry sem_entry_def sem_entry_ax _ _ Hg).
Qed.
