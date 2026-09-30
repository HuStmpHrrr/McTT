(** * Experiment: the gluing model up to sound module substitution

    The soundness analogue of [Core/Completeness/ModuleCases.v].  Build from
    [theories/] with
    [rocq c -R . Mctt ../experiments/soundness_kripke/Exp.v]. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Completeness Require Import ModuleCases GlobalCases FundamentalTheorem UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases
  SubtypingCases UniverseCases FunctionCases NatCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound module substitutions for the gluing model

    The syntactic half is [syn_msub] unchanged.  The semantic half needs *no*
    unfolding field: the gluing model has no equality judgment, and δ is only
    ever consumed syntactically (inside the conversions a gluing predicate
    carries), where [syn_unfold] transports it. *)

Section MSub.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (μ : msub) (E : ctx).

  #[local] Notation G2 := (gc_mk Θ2 Ξ2).
  #[local] Notation tctx Γ := (Γ[μ]ᵐ ++ E).
  #[local] Notation tm Γ M := (M[ms_qn (length Γ) μ]ᵐ).

  Record glu_msub : Prop :=
    { gms_syn : syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E
    ; gms_base : @glu_rel_ctx G2 E
    ; gms_param : forall n U k T Γ,
        List.nth_error Ξ1 n = Some U ->
        gu_params U ∋ #k : T ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        @glu_rel_ctx G2 (tctx Γ) ->
        @glu_rel_exp G2 (tctx Γ) (tm Γ $[n, k]) (tm Γ (T[↑ₘ (S n)]ᵐ[sb_params n]))
    ; gms_glob : forall r Δ b pv A B Γ,
        Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
        ⊢ Θ1 ⍮ Ξ1 ⍮ Γ ->
        @glu_rel_ctx G2 (tctx Γ) ->
        @glu_rel_exp G2 (tctx Γ) (tm Γ (a_glob r)) (tm Γ (ctx_pi Δ A))
    }.
End MSub.

(** ** 2. Kripke gluing *)

Definition kglu_ctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2 μ E, glu_msub Θ1 Ξ1 Θ2 Ξ2 μ E ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) (Γ[μ]ᵐ ++ E).

(** [glu_rel_exp] already contains the gluing of its context. *)
Definition kglu_exp Θ1 Ξ1 Γ M A : Prop :=
  forall Θ2 Ξ2 μ E, glu_msub Θ1 Ξ1 Θ2 Ξ2 μ E ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) (Γ[μ]ᵐ ++ E) M[ms_qn (length Γ) μ]ᵐ A[ms_qn (length Γ) μ]ᵐ.

(** ** 3. The fundamental theorem, Kripke form *)

Theorem kglu_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kglu_exp Θ Ξ Γ M A).
Proof.
  apply syntactic_wf_ctx_exp_mut_ind; unfold kglu_ctx, kglu_exp; intros;
    repeat match goal with IH : forall _ _ _ _, glu_msub _ _ _ _ _ _ -> _ |- _ =>
      specialize (IH _ _ _ _ ltac:(eassumption)) end.
  all: cbn [length ctx_msub msubst MSub_ctx MSub_exp exp_msub ms_qn List.app] in *.
  all: try rewrite !exp_msub_sub1 in *; try rewrite !exp_msub_sub2 in *;
      try rewrite !exp_msub_sub_succ in *.
  (* ⋅ : the base of the substitution; ▹ : the ordinary case *)
  all: try solve [ eapply gms_base; eassumption ].
  (* the ordinary rules: the (ported) fixed-context case lemmas, at the target *)
  all: try solve [ apply glu_rel_exp_typ; assumption | apply glu_rel_exp_nat; assumption
    | apply glu_rel_exp_zero; assumption | apply glu_rel_exp_succ; assumption
    | eapply glu_rel_exp_natrec; eassumption
    | eapply glu_rel_exp_pi; eassumption | eapply glu_rel_exp_fn; eassumption
    | eapply glu_rel_exp_app; eassumption ].
  all: try solve [ eapply glu_rel_exp_vlookup;
                   [ assumption | apply ctx_lookup_app_left, ctx_lookup_msub; eassumption ] ].
  (* parameters and globals: what the sound substitution supplies *)
  all: try solve [ eapply gms_param; eassumption ].
  all: try solve [ eapply gms_glob; eassumption ].
  all: try solve [ eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp |]; eassumption ].
  (* subsumption: the subtyping premise is transported syntactically *)
  match goal with Hμ : glu_msub _ _ _ _ _ _ |- _ =>
    destruct (msub_preserves_wf' _ _ _ _ _ _ (gms_syn _ _ _ _ _ _ Hμ)) as (_ & _ & _ & Hsub) end.
  match goal with Hs : wf_subtyp _ _ _ _ _ |- _ => pose proof (Hsub _ _ _ _ _ Hs eq_refl eq_refl) end.
  eapply glu_rel_exp_subtyp; eassumption.
Qed.

(** ** 4. Composition: again only the *syntactic* soundness of the first step *)

Section Compose.
  Variables (Θ1 Θ2 Θ3 : gdeps) (Ξ1 Ξ2 Ξ3 : gstack) (μ ν : msub) (E E' : ctx).
  Hypothesis Hμ : syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E.

  (** [ModuleCases.syn_msub_then] with a syntactic second step (its proof
      only ever uses [sms_syn] of it). *)
  Lemma syn_msub_then' : syn_msub Θ2 Ξ2 Θ3 Ξ3 ν E' ->
      syn_msub Θ1 Ξ1 Θ3 Ξ3 (ms_then μ E ν) (E[ν]ᵐ ++ E').
  Proof.
    intros Hν.
    destruct (msub_preserves_wf' _ _ _ _ _ _ Hμ) as (Hc1 & He1 & Hq1 & _).
    destruct (msub_preserves_wf' _ _ _ _ _ _ Hν) as (Hc2 & He2 & Hq2 & _).
    pose proof Hμ as [Hb Hp Hg Hu].
    constructor.
    - exact (Hc2 _ _ _ Hb eq_refl eq_refl).
    - intros * Hn Hk HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      destruct (Hp _ _ _ _ _ Hn Hk HΓ1 HΓ2) as [D1 D2].
      pose proof (He2 _ _ _ _ _ D1 eq_refl eq_refl) as D1'.
      pose proof (Hq2 _ _ _ _ _ _ D2 eq_refl eq_refl) as D2'.
      rewrite tctx_then, !tm_then in D1', D2'; split; assumption.
    - intros * Hl HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      destruct (Hg _ _ _ _ _ _ _ Hl HΓ1 HΓ2) as [D1 D2].
      pose proof (He2 _ _ _ _ _ D1 eq_refl eq_refl) as D1'.
      pose proof (Hq2 _ _ _ _ _ _ D2 eq_refl eq_refl) as D2'.
      rewrite tctx_then, !tm_then in D1', D2'; split; assumption.
    - intros * Hl HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      pose proof (Hu _ _ _ _ _ _ Hl HΓ1 HΓ2) as D2.
      pose proof (Hq2 _ _ _ _ _ _ D2 eq_refl eq_refl) as D2'.
      rewrite tctx_then, !tm_then in D2'; assumption.
  Qed.

  (** The gluing fields of the composite: [kglu_fundamental] at the middle
      context, applied to the derivations [μ]'s syntactic fields supply. *)
  Theorem glu_msub_then : glu_msub Θ2 Ξ2 Θ3 Ξ3 ν E' ->
      glu_msub Θ1 Ξ1 Θ3 Ξ3 (ms_then μ E ν) (E[ν]ᵐ ++ E').
  Proof.
    intros Hν.
    destruct (msub_preserves_wf' _ _ _ _ _ _ Hμ) as (Hc1 & _).
    destruct kglu_fundamental as (Kc & Ke).
    pose proof Hμ as [Hb Hp Hg Hu].
    constructor.
    - exact (syn_msub_then' (gms_syn _ _ _ _ _ _ Hν)).
    - exact (Kc _ _ _ Hb _ _ _ _ Hν).
    - intros * Hn Hk HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      destruct (Hp _ _ _ _ _ Hn Hk HΓ1 HΓ2) as [D1 _].
      pose proof (Ke _ _ _ _ _ D1 _ _ _ _ Hν) as H.
      rewrite tctx_then, !tm_then in H; exact H.
    - intros * Hl HΓ1 _.
      pose proof (Hc1 _ _ _ HΓ1 eq_refl eq_refl) as HΓ2.
      destruct (Hg _ _ _ _ _ _ _ Hl HΓ1 HΓ2) as [D1 _].
      pose proof (Ke _ _ _ _ _ D1 _ _ _ _ Hν) as H.
      rewrite tctx_then, !tm_then in H; exact H.
  Qed.
End Compose.

(** Kripke gluing moves along any *syntactically* sound substitution. *)
Lemma kglu_transport_syn : forall Θ1 Ξ1 Θ2 Ξ2 μ E Γ M A,
    syn_msub Θ1 Ξ1 Θ2 Ξ2 μ E ->
    kglu_exp Θ1 Ξ1 Γ M A ->
    kglu_exp Θ2 Ξ2 (Γ[μ]ᵐ ++ E) M[ms_qn (length Γ) μ]ᵐ A[ms_qn (length Γ) μ]ᵐ.
Proof.
  intros * Hμ H Θ3 Ξ3 ν E' Hν.
  pose proof (H _ _ _ _ (glu_msub_then _ _ _ _ _ _ _ _ _ _ Hμ Hν)) as H'.
  rewrite <- tctx_then, <- !tm_then in H'; exact H'.
Qed.

(** ** 5. Closed gluing at [⋅] weakens to every glued context

    Simpler than [closed_weaken_sem]: [nil_glu_sub_pred] does not constrain
    the environment, and the terms are the same, so no closedness is needed. *)

Section Weaken.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  Lemma wf_sub_nil : forall Δ σ, ⊢ Δ -> Δ ⊢s σ : ⋅.
  Proof.
    intros * HΔ; constructor; [ exact HΔ | constructor; eapply ctx_wf_gctx; exact HΔ |].
    intros * Hx; inversion Hx.
  Qed.

  Lemma glu_rel_exp_nil_weaken : forall Γ N T, ⊩ Γ -> ⋅ ⊩ N : T -> Γ ⊩ N : T.
  Proof.
    intros * [SbΓ HΓ] [Sb0 [H0 [i Hi]]].
    exists SbΓ; split; [ exact HΓ |]; exists i; intros Δ σ ρ Hσ.
    apply Hi.
    inversion H0 as [Sb' Heq Hg |]; subst.
    apply (Heq Δ σ ρ); cbn.
    apply wf_sub_nil, (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HΓ _ _ _ Hσ)).
  Qed.
End Weaken.

(** ** 6. The identity is sound, given [⊩g]: every resolved global and
    parameter glued at [⋅] *)

Definition glu_rwf (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall p Δ b pv A B,
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    @glu_rel_exp (gc_mk Θ Ξ) ⋅ (a_glob p) (ctx_pi Δ A).

Definition glu_pwf (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall n U k T,
    List.nth_error Ξ n = Some U ->
    gu_params U ∋ #k : T ->
    @glu_rel_exp (gc_mk Θ Ξ) ⋅ $[n, k] (T[↑ₘ (S n)]ᵐ[sb_params n]).

Section Identity.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.
  Hypothesis HR : glu_rwf Θ Ξ.
  Hypothesis HP : glu_pwf Θ Ξ.

  Theorem glu_msub_id : glu_msub Θ Ξ Θ Ξ ms_id nil.
  Proof.
    constructor.
    - exact (syn_msub_id _ _ Hg).
    - apply (@glu_rel_ctx_empty (gc_mk Θ Ξ)); exact Hg.
    - intros * Hn Hk _ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      apply glu_rel_exp_nil_weaken; [ exact HΓs | exact (HP _ _ _ _ Hn Hk) ].
    - intros * Hl _ HΓs; rewrite !exp_msub_qn_id; rewrite ctx_msub_id, List.app_nil_r in *.
      apply glu_rel_exp_nil_weaken; [ exact HΓs | exact (HR _ _ _ _ _ _ Hl) ].
  Qed.

  (** The soundness fundamental theorem at a fixed, glued global context. *)
  Corollary glu_fundamental_at : forall Γ M A,
      Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> @glu_rel_exp (gc_mk Θ Ξ) Γ M A.
  Proof.
    intros * H.
    pose proof (proj2 kglu_fundamental _ _ _ _ _ H _ _ _ _ glu_msub_id) as H'.
    rewrite ctx_msub_id, List.app_nil_r, !exp_msub_qn_id in H'; exact H'.
  Qed.
End Identity.

(** ** 7. [⊩g] from the gluing of resolved types and bodies

    δ evaluates the body at [nil], and a global or parameter is a neutral
    annotated with its type evaluated at [nil].  Since [nil_glu_sub_pred]
    leaves the environment free, the [⋅]-judgment can simply be instantiated at
    [nil]; the only semantic fact needed is that the values of a closed type at
    two environments are related ([typ_nil_rel], from completeness at [⋅]),
    which [glu_univ_elem_resp_per_univ]/[glu_univ_elem_exp_conv] consume. *)

Section Cook.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  Lemma typ_nil_rel : forall T i ρ ρ',
      ⋅ ⊢ T : Type@i ->
      exists a a', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
  Proof.
    intros * HT%completeness_fundamental_exp.
    destruct (rel_exp_of_typ_inversion_simple HT) as [env_rel [Hnil H]].
    apply H.
    inversion Hnil as [? Heq |]; subst.
    apply Heq; exact I.
  Qed.

  Lemma glu_nil_sb : forall Sb Δ σ ρ,
      EG ⋅ ∈ glu_ctx_env ↘ Sb -> Δ ⊢s σ ® ρ ∈ Sb -> forall ρ', Δ ⊢s σ ® ρ' ∈ Sb.
  Proof.
    intros * H0 Hσ ρ'.
    inversion H0 as [Sb' Heq Hg |]; subst.
    apply (Heq Δ σ ρ'); apply (Heq Δ σ ρ) in Hσ; exact Hσ.
  Qed.

  (** A neutral: a closed [G] that evaluates anywhere to [⇑ a d], [a] the value
      of its type at [nil], and reads back to itself. *)
  Lemma glu_neut_nil : forall T G i d,
      ⋅ ⊩ T : Type@i ->
      (forall σ, T[σ] = T) -> (forall σ, G[σ] = G) ->
      (forall φ, T[φ]ʷ = T) -> (forall φ, G[φ]ʷ = G) ->
      (forall Δ, ⊢ Δ -> Δ ⊢ G : T) ->
      Dom d ≈ d ∈ per_bot ->
      (forall s (M' : ne), Rne d in s ↘ M' -> (M' : exp) = G) ->
      (forall ρ a, ⟦ T ⟧ nil ↘ a -> ⟦ G ⟧ ρ ↘ ⇑ a d) ->
      ⋅ ⊩ G : T.
  Proof.
    intros * HT HTs HGs HTw HGw HGty Hd Hrb Hev.
    pose proof (glu_rel_exp_to_wf_exp HT) as HTwf.
    pose proof HT as [Sb0 [H0 _]].
    pose proof (glu_rel_exp_clean_inversion2' H0 HT) as HTi.
    exists Sb0; split; [ exact H0 |]; exists i; intros Δ σ ρ Hσ.
    destruct (HTi _ _ _ Hσ) as [? ? ? ? Hevu HevT Hu HTσ].
    inversion Hevu; subst.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *; destruct_conjs.
    rename H2 into Pa, H3 into Ela, H4 into HPa, H5 into HTPa.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape H0 _ _ _ Hσ)).
    destruct (typ_nil_rel _ _ ρ nil HTwf) as (a1 & a0 & Ha1 & Ha0 & Hrel).
    functional_eval_rewrite_clear.
    assert (HPa0 : glu_univ_elem i Pa Ela a0) by (eapply glu_univ_elem_resp_per_univ; eassumption).
    rewrite HTs in HTPa.
    econstructor; [ exact HevT | apply Hev; exact Ha0 | exact HPa |].
    rewrite HGs, HTs.
    eapply realize_glu_elem_bot; [ exact HPa0 |].
    econstructor; [ apply HGty; exact HΔ | exact HPa0 | exact HTPa | exact Hd |].
    intros * Hk Hr; rewrite (Hrb _ _ Hr), HGw, HTw.
    pose proof (HGty _ (kripke_dom _ _ _ Hk)); mauto 3.
  Qed.

  (** δ: a closed [G] that evaluates anywhere to what [N] evaluates to at
      [nil], and is syntactically [N], is glued. *)
  Lemma glu_delta_nil : forall T N G,
      ⋅ ⊩ N : T ->
      (forall σ, T[σ] = T) -> (forall σ, N[σ] = N) -> (forall σ, G[σ] = G) ->
      (forall Δ, ⊢ Δ -> Δ ⊢ G ≈ N : T) ->
      (forall ρ m, ⟦ N ⟧ nil ↘ m -> ⟦ G ⟧ ρ ↘ m) ->
      ⋅ ⊩ G : T.
  Proof.
    intros * HN HTs HNs HGs Hδ Hev.
    destruct (presup_typ_glu_rel_exp HN) as [k HT].
    pose proof (glu_rel_exp_to_wf_exp HT) as HTwf.
    pose proof HN as [Sb0 [H0 [i HNi]]].
    exists Sb0; split; [ exact H0 |]; exists i; intros Δ σ ρ Hσ.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape H0 _ _ _ Hσ)).
    destruct (HNi _ _ _ Hσ) as [? ? P El HevT HevN HP HNσ].
    destruct (HNi _ _ _ (glu_nil_sb _ _ _ _ H0 Hσ nil)) as [? ? P0 El0 HevT0 HevN0 HP0 HNσ0].
    destruct (typ_nil_rel _ _ nil ρ HTwf) as (b0 & b & Hb0 & Hb & Hrel).
    functional_eval_rewrite_clear.
    econstructor; [ exact HevT | apply Hev; exact HevN0 | exact HP |].
    assert (HTP : Δ ⊢ T[σ] ® P) by (eapply glu_univ_elem_trm_typ; eassumption).
    assert (Δ ⊢ N[σ] : T[σ] ® m0 ∈ El) by (eapply glu_univ_elem_exp_conv; eassumption).
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact HP | eassumption |].
    rewrite HNs, HGs, HTs.
    pose proof (Hδ _ HΔ); mauto 3.
  Qed.
End Cook.

(** The raw [⊩g]: gluing at [⋅] of what resolution hands back. *)
Definition glu_rwf_raw (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall p Δ b pv A B,
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    (exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (Type@i)) /\
    (forall M, B = Some M -> @glu_rel_exp (gc_mk Θ Ξ) ⋅ (ctx_fn Δ M) (ctx_pi Δ A)).

Definition glu_pwf_raw (Θ : gdeps) (Ξ : gstack) : Prop :=
  forall n U k T,
    List.nth_error Ξ n = Some U ->
    gu_params U ∋ #k : T ->
    exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ (T[↑ₘ (S n)]ᵐ[sb_params n]) (Type@i).

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  Lemma glob_glu_of_raw : forall p Δ b pv A B,
      Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
      (exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ (ctx_pi Δ A) (Type@i)) /\
      (forall M, B = Some M -> @glu_rel_exp (gc_mk Θ Ξ) ⋅ (ctx_fn Δ M) (ctx_pi Δ A)) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ (a_glob p) (ctx_pi Δ A).
  Proof.
    intros p Δ b pv A B Hl [[i HT] HM].
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    pose proof (wf_gctx_stack _ _ Hg) as HΞ.
    pose proof (gc_resolve_complete _ _ _ _ _ (wf_gstack_canon _ _ HΞ)
                  (wf_gdeps_canon _ (wf_gstack_deps _ _ HΞ)) Hl) as Hr.
    pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ _ Hb Hl) as HsT.
    destruct b; [ destruct B as [M |] |].
    - pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ _ Hb Hl) as HsM.
      eapply (@glu_delta_nil (gc_mk Θ Ξ)); [ apply HM; reflexivity | | | reflexivity | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros; eapply exp_closed_sub; eassumption.
      + intros Δ' HΔ'; econstructor; eassumption.
      + intros * Hev; econstructor; eassumption.
    - eapply (@glu_neut_nil (gc_mk Θ Ξ)) with (d := d_glob p);
        [ exact HT | | reflexivity | | reflexivity | | | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros; eapply exp_closed_wk; eassumption.
      + intros Δ' HΔ'; econstructor; eassumption.
      + intros s; eexists; split; constructor.
      + intros * Hrb; inversion Hrb; reflexivity.
      + intros * Hev; eapply eval_exp_glob_neut; [ exact Hr | right; reflexivity | exact Hev ].
    - eapply (@glu_neut_nil (gc_mk Θ Ξ)) with (d := d_glob p);
        [ exact HT | | reflexivity | | reflexivity | | | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros; eapply exp_closed_wk; eassumption.
      + intros Δ' HΔ'; econstructor; eassumption.
      + intros s; eexists; split; constructor.
      + intros * Hrb; inversion Hrb; reflexivity.
      + intros * Hev; eapply eval_exp_glob_neut; [ exact Hr | left; reflexivity | exact Hev ].
  Qed.

  Lemma param_glu_of_raw : forall n U k T,
      List.nth_error Ξ n = Some U ->
      gu_params U ∋ #k : T ->
      (exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ (T[↑ₘ (S n)]ᵐ[sb_params n]) (Type@i)) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ $[n, k] (T[↑ₘ (S n)]ᵐ[sb_params n]).
  Proof.
    intros n U k T Hn Hk [i HT].
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    assert (Hsc : gs_scoped Ξ) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb)).
    pose proof (param_type_scoped _ _ _ _ _ Hsc Hn Hk) as HsT.
    eapply (@glu_neut_nil (gc_mk Θ Ξ)) with (d := d_param {| lp_mod := n; lp_param := k |});
      [ exact HT | | reflexivity | | reflexivity | | | |].
    - intros; eapply exp_closed_sub; eassumption.
    - intros; eapply exp_closed_wk; eassumption.
    - intros Δ' HΔ'; econstructor; eassumption.
    - intros s; eexists; split; constructor.
    - intros * Hrb; inversion Hrb; reflexivity.
    - intros * Hev; eapply eval_exp_param; [| exact Hev ].
      unfold gs_param; cbn; rewrite Hn, (ctx_get_complete _ _ _ Hk); reflexivity.
  Qed.

  Lemma glu_rwf_of_raw : glu_rwf_raw Θ Ξ -> glu_rwf Θ Ξ.
  Proof. intros HR p * Hl; exact (glob_glu_of_raw _ _ _ _ _ _ Hl (HR _ _ _ _ _ _ Hl)). Qed.

  Lemma glu_pwf_of_raw : glu_pwf_raw Θ Ξ -> glu_pwf Θ Ξ.
  Proof. intros HP n U k T Hn Hk; exact (param_glu_of_raw _ _ _ _ Hn Hk (HP _ _ _ _ Hn Hk)). Qed.
End Raw.

(** ** 8. The gluing instance of [GlobalCases]' model-specific interface

    [GlobalCases.v] proves [⊢g ⇒ ⊨g] by age induction over *embeddings*
    [Emb]; of its lemmas only [vtyp]/[gent], [sem_msub_emb] and
    [kread]/[kread_entry] mention the PER model.  Here are their gluing
    twins, with the same shapes: the age induction ([good_cons] and the
    frame/level lemmas) would go through verbatim over them. *)

Definition gvtyp (Θ : gdeps) (Ξ : gstack) (X : exp) : Prop :=
  exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ X (Type@i).

Definition ggent (Θ : gdeps) (Ξ : gstack) (μ : msub) (Δ : ctx) (A : exp) (B : option exp) : Prop :=
  gvtyp Θ Ξ ((ctx_pi Δ A)[μ]ᵐ) /\
  (forall M, B = Some M -> @glu_rel_exp (gc_mk Θ Ξ) ⋅ (ctx_fn Δ M)[μ]ᵐ (ctx_pi Δ A)[μ]ᵐ).

Definition GSG Θ1 Ξ1 Θ2 Ξ2 μ : Prop :=
  forall r Δ b pv A B, Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> ggent Θ2 Ξ2 μ Δ A B.

Definition GSP (Θ1 : gdeps) (Ξ1 : gstack) Θ2 Ξ2 μ : Prop :=
  forall n U k T, List.nth_error Ξ1 n = Some U -> gu_params U ∋ #k : T ->
    gvtyp Θ2 Ξ2 (T[↑ₘ (S n)]ᵐ[sb_params n][μ]ᵐ).

Lemma syn_msub_emb : forall Θ1 Ξ1 Θ2 Ξ2 μ,
    Emb Θ1 Ξ1 Θ2 Ξ2 μ -> syn_msub Θ1 Ξ1 Θ2 Ξ2 μ nil.
Proof.
  intros * [Hg Hq Hp Hl].
  assert (Hb : ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅) by (constructor; assumption).
  assert (Hqe : forall n (X : exp), X[ms_qn n μ]ᵐ = X[μ]ᵐ) by (intros; apply exp_msub_ext, Hq).
  constructor.
  - exact Hb.
  - intros * Hn Hk _ HΓ; rewrite !Hqe.
    destruct (Hp _ _ _ _ Hn Hk) as (n' & U' & k' & T' & Heq & Hn' & Hk' & HT).
    rewrite Heq, HT; split; econstructor; eassumption.
  - intros * Hl0 _ HΓ; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    rewrite Heq, ctx_pi_msub_qn by assumption; split; econstructor; eassumption.
  - intros * Hl0 _ HΓ; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    rewrite Heq, ctx_pi_msub_qn, ctx_fn_msub_qn by assumption; econstructor; eassumption.
Qed.

Theorem glu_msub_emb : forall Θ1 Ξ1 Θ2 Ξ2 μ,
    Emb Θ1 Ξ1 Θ2 Ξ2 μ -> GSG Θ1 Ξ1 Θ2 Ξ2 μ -> GSP Θ1 Ξ1 Θ2 Ξ2 μ ->
    glu_msub Θ1 Ξ1 Θ2 Ξ2 μ nil.
Proof.
  intros * He HG HP; pose proof He as [Hg Hq Hp Hl].
  assert (Hqe : forall n (X : exp), X[ms_qn n μ]ᵐ = X[μ]ᵐ) by (intros; apply exp_msub_ext, Hq).
  constructor.
  - exact (syn_msub_emb _ _ _ _ _ He).
  - apply (@glu_rel_ctx_empty (gc_mk Θ2 Ξ2)); exact Hg.
  - intros * Hn Hk _ HΓs; rewrite !Hqe; rewrite List.app_nil_r in *.
    destruct (Hp _ _ _ _ Hn Hk) as (n' & U' & k' & T' & Heq & Hn' & Hk' & HT).
    pose proof (HP _ _ _ _ Hn Hk) as HPv; unfold gvtyp in HPv.
    rewrite Heq, HT in *.
    apply glu_rel_exp_nil_weaken; [ exact HΓs | exact (param_glu_of_raw _ _ Hg _ _ _ _ Hn' Hk' HPv) ].
  - intros * Hl0 _ HΓs; rewrite !Hqe; rewrite List.app_nil_r in *.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    destruct (HG _ _ _ _ _ _ Hl0) as [HT HM].
    rewrite Heq, ctx_pi_msub_qn in * by assumption.
    apply glu_rel_exp_nil_weaken; [ exact HΓs |].
    apply (glob_glu_of_raw _ _ Hg _ _ _ _ _ _ Hl').
    split; [ exact HT |].
    intros M' HB; destruct B as [M |]; cbn in HB; inversion HB; subst.
    rewrite <- ctx_fn_msub_qn by assumption; apply HM; reflexivity.
Qed.

Lemma kglu_read : forall Θ1 Ξ1 Θ2 Ξ2 μ A M,
    glu_msub Θ1 Ξ1 Θ2 Ξ2 μ nil ->
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ M[μ]ᵐ A[μ]ᵐ.
Proof. intros * Hμ HM; exact (proj2 kglu_fundamental _ _ _ _ _ HM _ _ _ _ Hμ). Qed.

Lemma kglu_read_entry : forall Θ1 Ξ1 Θ2 Ξ2 μ Δ A B,
    glu_msub Θ1 Ξ1 Θ2 Ξ2 μ nil ->
    (exists i, Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ ctx_pi Δ A : Type@i) ->
    (forall M, B = Some M -> Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A) ->
    ggent Θ2 Ξ2 μ Δ A B.
Proof.
  intros * Hμ [i HT] HM; split.
  - exists i; exact (kglu_read _ _ _ _ _ _ _ Hμ HT).
  - intros M HB; exact (kglu_read _ _ _ _ _ _ _ Hμ (HM _ HB)).
Qed.

(** ** 9. ⊢g ⇒ ⊩g: [GlobalCases]' age induction, instantiated for gluing

    Sections 5–8 of [GlobalCases.v] ([frame_outer], [good_cons],
    [good_level], [good_deps], [good_stack], [gctx_sem]) copied
    *mechanically*, with the renaming
    [Good/gent/vtyp/sem_msub(_emb)/kread(_entry)] ↦
    [GGood/ggent/gvtyp/glu_msub(_emb)/kglu_read(_entry)] and no other edit.
    Everything model-independent is used from [GlobalCases] as is. *)

Definition GGood Θ Ξ : Prop :=
  forall Θ2 Ξ2 μ, Emb Θ Ξ Θ2 Ξ2 μ -> GSG Θ Ξ Θ2 Ξ2 μ /\ GSP Θ Ξ Θ2 Ξ2 μ.

Lemma gframe_outer : forall Θ U Ξ Θ2 Ξ2 μ,
    GGood Θ Ξ -> ⊢g Θ ⍮ U :: Ξ -> Emb Θ (U :: Ξ) Θ2 Ξ2 μ ->
    (forall r Δ b pv A B, Θ ⍮ U :: Ξ ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B -> p_qual r <> qu_rel 0 ->
       ggent Θ2 Ξ2 μ Δ A B) /\
    (forall n U' k T, List.nth_error Ξ n = Some U' -> gu_params U' ∋ #k : T ->
       gvtyp Θ2 Ξ2 T[↑ₘ (S (S n))]ᵐ[sb_params (S n)][μ]ᵐ).
Proof.
  intros * HG Hg He.
  assert (HΘ : units_scoped Θ) by (eapply wf_scoped; eassumption).
  destruct (HG _ _ _ (Emb_comp _ _ _ _ _ _ _ _ (Emb_push _ _ _ Hg) He)) as [HS HP].
  assert (Hq : forall n, ms_eq (ms_qn n (↑ₘ 1)) (↑ₘ 1)) by (intros; apply ms_qn_shift).
  split.
  - intros * Hl Hr.
    destruct (gc_lookup_pop _ _ _ _ _ _ _ _ _ HΘ Hl Hr) as (Δ0 & A0 & B0 & r0 & Hl0 & -> & -> & ->).
    destruct (HS _ _ _ _ _ _ Hl0) as [HT HM].
    rewrite <- exp_msub_msub, (ctx_pi_msub_qn (↑ₘ 1)) in HT by exact Hq.
    split; [ exact HT |].
    intros M HB; destruct B0 as [M0 |]; cbn in HB; inversion HB; subst.
    specialize (HM _ eq_refl).
    rewrite <- !exp_msub_msub, (ctx_pi_msub_qn (↑ₘ 1)), (ctx_fn_msub_qn (↑ₘ 1)) in HM by exact Hq.
    exact HM.
  - intros * Hn Hk; rewrite <- exp_params_shift, exp_msub_msub; eapply HP; eassumption.
Qed.

Lemma ggood_cons : forall Θ Ξ P Φ,
    wf_gstack Θ Ξ -> Θ ⍮ Ξ ⍮ P ⊢m Φ -> GGood Θ Ξ -> GGood Θ (gu_mk P Φ :: Ξ).
Proof.
  intros * HΞ HΦ HG Θ2 Ξ2 μ He.
  assert (Hg : ⊢g Θ ⍮ gu_mk P Φ :: Ξ) by (eapply ctx_wf_gctx, wf_frame_ctx; eassumption).
  assert (HP0 : ⊢ Θ ⍮ Ξ ⍮ P) by (eapply wf_gmod_ctx; eassumption).
  (* the parameters, outermost first *)
  assert (Hpar : forall Pb Pa, P = Pa ++ Pb -> forall k T, Pb ∋ #k : T ->
            gvtyp Θ2 Ξ2 T[wk_shiftn (length Pa)]ʷ[↑ₘ 1]ᵐ[sb_params 0][μ]ᵐ).
  { induction Pb as [| A Pb IH]; intros Pa HPe k T Hk; [ inversion Hk |].
    assert (HPe' : P = (Pa ++ A :: nil) ++ Pb) by (rewrite <- List.app_assoc; exact HPe).
    inversion Hk as [| ? ? ? ? Hk0]; subst.
    - assert (HAb : ⊢ Θ ⍮ Ξ ⍮ Pb ▹ A) by (eapply ctx_app_wf_right; exact HP0).
      inversion HAb as [| ? ? ? ? ? HA]; subst.
      assert (HgB : ⊢g Θ ⍮ gu_mk Pb ⋄ :: Ξ)
        by (apply wf_gctx_intro, wf_gstack_cons;
            [ assumption | constructor; constructor; eapply presup_exp_ctx; eassumption ]).
      pose proof (Emb_trunc Θ Ξ (Pa ++ A :: nil) Pb Φ ltac:(rewrite <- HPe'; exact Hg)) as Het.
      rewrite <- HPe' in Het.
      pose proof (Emb_comp _ _ _ _ _ _ _ _ Het He) as He'.
      destruct (gframe_outer _ _ _ _ _ _ HG HgB He') as [Ho1 Ho2].
      assert (Hμ : glu_msub Θ (gu_mk Pb ⋄ :: Ξ) Θ2 Ξ2 (ms_comp (ms_off (length (Pa ++ A :: nil))) μ) nil).
      { apply glu_msub_emb; [ exact He' | |].
        - intros r * Hl.
          destruct (p_qual r) as [fp | [| m]] eqn:Hq;
            try solve [ eapply Ho1; [ eassumption | rewrite Hq; discriminate ] ].
          inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; cbn in Hq; [| discriminate ].
          injection Hq as ->; cbn in Hn; injection Hn as <-; cbn in Hm; inversion Hm.
        - intros [| m] U k' T' Hn Hk'; cbn in Hn.
          + injection Hn as <-; cbn in Hk'.
            rewrite <- exp_msub_msub, params_off_here.
            exact (IH (Pa ++ A :: nil) HPe' _ _ Hk').
          + exact (Ho2 _ _ _ _ Hn Hk'). }
      pose proof (kglu_read _ _ _ _ _ _ _ Hμ (wf_frame_typ _ (gu_mk Pb ⋄) _ _ _ HgB HA)) as H.
      rewrite <- (exp_msub_msub (A[↑ₘ 1]ᵐ[sb_params 0])), params_off_here in H.
      rewrite (wk_shiftn_len _ _ A); exists i; exact H.
    - rewrite (wk_shiftn_len _ _ A); exact (IH (Pa ++ A :: nil) HPe' _ _ Hk0). }
  assert (HparF : forall k T, P ∋ #k : T -> gvtyp Θ2 Ξ2 T[↑ₘ 1]ᵐ[sb_params 0][μ]ᵐ).
  { intros * Hk; pose proof (Hpar P nil eq_refl k T Hk) as H; cbn [length] in H.
    rewrite (exp_wk_wk_eq _ _ _ wk_shiftn_zero), exp_wk_id in H; exact H. }
  destruct (gframe_outer _ _ _ _ _ _ HG Hg He) as [Ho1 Ho2].
  (* the members, in insertion order *)
  assert (Hins : ins_typed Θ Ξ P Φ)
    by (destruct presup_global as (_ & _ & _ & _ & _ & Hm & _); exact (Hm _ _ _ _ HΦ)).
  assert (Hmem : forall n Φq ip Δ b pv A B, gm_count Φq < n ->
             gm_ins Φ Φq ip Δ (ge_def b pv A B) -> ggent Θ2 Ξ2 μ Δ A B).
  { induction n as [| n IH]; intros * Hlt Hi; [ lia |].
    pose proof (gm_ins_prefix _ _ _ _ _ Hi) as Hpq.
    assert (Hgq : ⊢g Θ ⍮ gu_mk P Φq :: Ξ)
      by (eapply ctx_wf_gctx, wf_frame_ctx, wf_gmod_prefix; eassumption).
    assert (Heq : Emb Θ (gu_mk P Φq :: Ξ) Θ2 Ξ2 μ).
    { eapply Emb_pre; [ apply grow_lookup; exact Hpq | | exact He ].
      intros [| m] U Hn; cbn in *; [ injection Hn as <- |]; eexists; split; eauto. }
    destruct (gframe_outer _ _ _ _ _ _ HG Hgq Heq) as [Hq1 Hq2].
    destruct (Hins _ _ _ _ _ _ _ Hi) as [HT HM].
    assert (Hμ : glu_msub Θ (gu_mk P Φq :: Ξ) Θ2 Ξ2 μ nil).
    { apply glu_msub_emb; [ exact Heq | |].
      - intros r * Hl.
        destruct (p_qual r) as [fp | [| m]] eqn:Hq;
          try solve [ eapply Hq1; [ eassumption | rewrite Hq; discriminate ] ].
        inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; cbn in Hq; [| discriminate ].
        injection Hq as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
        rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero.
        destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
        pose proof (gm_ins_count _ _ _ _ _ Hir).
        eapply IH; [| exact (gm_prefix_ins _ _ _ _ _ _ Hpq Hir) ]; lia.
      - intros [| m] U k T Hn Hk; cbn in Hn;
          [ injection Hn as <-; cbn in Hk; exact (HparF _ _ Hk) | exact (Hq2 _ _ _ _ Hn Hk) ]. }
    exact (kglu_read_entry _ _ _ _ _ _ _ _ Hμ HT HM). }
  split.
  - intros r * Hl.
    destruct (p_qual r) as [fp | [| m]] eqn:Hq;
      try solve [ eapply Ho1; [ eassumption | rewrite Hq; discriminate ] ].
    inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; cbn in Hq; [| discriminate ].
    injection Hq as ->; cbn in Hn; injection Hn as <-; cbn in Hm.
    rewrite ctx_msub_shift_zero, exp_msub_shift_zero, opt_msub_shift_zero.
    destruct (gm_lookup_ins _ _ _ _ Hm) as [Φr Hir].
    eapply (Hmem (S (gm_count Φr)) Φr); [ lia | exact Hir ].
  - intros [| m] U k T Hn Hk; cbn in Hn;
      [ injection Hn as <-; cbn in Hk; exact (HparF _ _ Hk) | exact (Ho2 _ _ _ _ Hn Hk) ].
Qed.

Lemma ggood_level : forall Θ0 d,
    wf_gdeps Θ0 -> wf_gdep Θ0 d -> GGood Θ0 nil -> GGood (d :: Θ0) nil.
Proof.
  intros * HΘ Hd HG Θ2 Ξ2 μ He.
  pose proof (wf_gdep_fresh _ _ Hd) as Hfr.
  assert (Hgrow : forall fq V, gds_lookup Θ0 fq = Some V -> gds_lookup (d :: Θ0) fq = Some V)
    by (intros; apply gds_lookup_level; assumption).
  assert (Hlow : forall r Δ b pv A B, Θ0 ⍮ nil ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B ->
                   d :: Θ0 ⍮ nil ∋ᵍ r ⇒ Δ ⍮ ge_def b pv A B).
  { intros * Hl; inversion Hl; subst; [ destruct n; discriminate | econstructor; eauto ]. }
  assert (He0 : Emb Θ0 nil Θ2 Ξ2 μ)
    by (eapply Emb_pre; [ exact Hlow | intros [| n] U Hn; discriminate | exact He ]).
  destruct (HG _ _ _ He0) as [HS0 _].
  split; [| intros n U k T Hn; destruct n; discriminate ].
  intros r * Hl.
  inversion Hl as [? ? ? ? ? ? ? ? Hn Hm | ? ? ? ? ? ? ? ? Hf Hm]; subst; [ destruct n; discriminate |].
  pose proof Hf as Hl'; unfold gds_lookup in Hl'; cbn [List.concat] in Hl'.
  apply gd_lookup_app_inv in Hl' as [Hl' | Hl'].
  2: { eapply HS0; econstructor; [ exact Hl' | eassumption ]. }
  apply gd_lookup_in in Hl' as Hin.
  pose proof (wf_gdep_unit _ _ Hd _ _ Hin) as HUw.
  pose proof (Hfr _ _ Hin) as Hfp.
  assert (HinsU : ins_typed Θ0 nil (gu_params U) (gu_mod U))
    by (destruct presup_global as (_ & _ & _ & _ & _ & _ & Hu & _); exact (Hu _ _ _ HUw)).
  inversion HUw as [? ? ? HU]; subst.
  destruct U as [PU ΦU]; cbn [gu_params gu_mod] in *.
  assert (Hmem : forall n Φq ip Δ b pv A B, gm_count Φq < n -> gm_ins ΦU Φq ip Δ (ge_def b pv A B) ->
             ggent Θ2 Ξ2 μ (Δ[close (p_abs fp nil) (length PU)]ᵐ ++ PU)
               A[ms_close (p_abs fp nil) (length PU) (length Δ)]ᵐ
               B[ms_close (p_abs fp nil) (length PU) (length Δ)]ᵐ).
  { induction n as [| n IH]; intros * Hlt Hi; [ lia |].
    pose proof (gm_ins_prefix _ _ _ _ _ Hi) as Hpq.
    set (Θq := ((fp, gu_mk PU Φq) :: nil) :: Θ0).
    assert (HwUq : Θ0 ⍮ nil ⍮ PU ⊢m Φq) by (eapply wf_gmod_prefix; eassumption).
    assert (Hgq : ⊢g Θq ⍮ nil).
    { apply wf_gctx_intro, wf_gstack_nil, wf_gdeps_cons; [ assumption |].
      apply wf_gdep_cons; [ apply wf_gdep_nil; assumption | constructor; exact HwUq | exact Hfp | unfold gd_fresh; cbn; tauto ]. }
    assert (Hgq' : forall fq V, gds_lookup Θ0 fq = Some V -> gds_lookup Θq fq = Some V).
    { intros; apply gds_lookup_level; [| assumption ].
      intros fq' V' [[= <- <-] | []]; exact Hfp. }
    assert (Hlq : forall r Δ' b' pv' A' B', Θq ⍮ nil ∋ᵍ r ⇒ Δ' ⍮ ge_def b' pv' A' B' ->
                    d :: Θ0 ⍮ nil ∋ᵍ r ⇒ Δ' ⍮ ge_def b' pv' A' B').
    { intros * H; inversion H as [? ? ? ? ? ? ? ? Hn' Hm' | ? ? ? ? ? ? ? ? Hf' Hm']; subst;
        [ destruct n0; discriminate |].
      destruct (gds_lookup_single _ _ _ _ _ Hf') as [[-> ->] | Hb].
      - eapply (gcl_abs _ _ _ (gu_mk PU ΦU)); [ exact Hf | cbn in *; eauto using gm_prefix_lookup ].
      - econstructor; [ apply Hgrow; exact Hb | eassumption ]. }
    assert (Heq : Emb Θq nil Θ2 Ξ2 μ)
      by (eapply Emb_pre; [ exact Hlq | intros [| ?] ? ?; discriminate | exact He ]).
    assert (Hμ : glu_msub Θq nil Θ2 Ξ2 μ nil).
    { apply glu_msub_emb; [ exact Heq | | intros [| ?] ? ? ? ?; discriminate ].
      intros r * H; inversion H as [? ? ? ? ? ? ? ? Hn' Hm' | ? ? ? ? ? ? ? ? Hf' Hm']; subst;
        [ destruct n0; discriminate |].
      destruct (gds_lookup_single _ _ _ _ _ Hf') as [[-> ->] | Hb].
      - cbn [gu_params gu_mod] in *.
        destruct (gm_lookup_ins _ _ _ _ Hm') as [Φr Hir].
        pose proof (gm_ins_count _ _ _ _ _ Hir).
        eapply (IH Φr); [ lia | exact (gm_prefix_ins _ _ _ _ _ _ Hpq Hir) ].
      - eapply HS0; econstructor; eassumption. }
    destruct (closable_file_prefix Θ0 Θq fp PU ΦU Φq HU HinsU (gds_lookup_single_here _ _ _) Hgq'
                ltac:(constructor; exact Hgq) (S (gm_count Φq)) Φq _ _ _ _ _ _ ltac:(lia) Hi
                (gmp_refl _)) as [[i HT] HM].
    apply (kglu_read_entry _ _ _ _ _ _ _ _ Hμ).
    - rewrite ctx_pi_app, <- ctx_pi_close; eapply ctx_pi_wf0; eassumption.
    - intros M' HB; destruct B as [M0 |]; cbn in HB; inversion HB; subst.
      rewrite ctx_fn_app, <- ctx_fn_close, ctx_pi_app, <- ctx_pi_close.
      eapply ctx_fn_wf0; [ eassumption | apply HM; reflexivity ]. }
  destruct (gm_lookup_ins _ _ _ _ Hm) as [Φq Hi].
  exact (Hmem (S (gm_count Φq)) Φq _ _ _ _ _ _ ltac:(lia) Hi).
Qed.

Lemma ggood_deps : forall Θ, wf_gdeps Θ -> GGood Θ nil.
Proof.
  induction 1 as [| Θ d HΘ IH Hd].
  - intros Θ2 Ξ2 μ He; split.
    + intros r * Hl; inversion Hl; subst; [ destruct n; discriminate | discriminate ].
    + intros [| n] U k T Hn; discriminate.
  - apply ggood_level; assumption.
Qed.

Lemma ggood_stack : forall Ξ Θ, wf_gstack Θ Ξ -> GGood Θ Ξ.
Proof.
  induction Ξ as [| U Ξ IH]; intros * H; inversion H; subst.
  - apply ggood_deps; assumption.
  - destruct U as [P Φ]; match goal with Hu : _ ⍮ _ ⊢u _ |- _ => inversion Hu; subst end.
    apply ggood_cons; auto.
Qed.

Theorem gctx_glu : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> glu_rwf_raw Θ Ξ /\ glu_pwf_raw Θ Ξ.
Proof.
  intros * Hg.
  destruct (ggood_stack _ _ (wf_gctx_stack _ _ Hg) _ _ _ (Emb_id _ _ Hg)) as [HS HP].
  split.
  - intros p * Hl; destruct (HS _ _ _ _ _ _ Hl) as [HT HM].
    rewrite exp_msub_id in HT; split; [ exact HT |].
    intros M HB; specialize (HM _ HB); rewrite !exp_msub_id in HM; exact HM.
  - intros n U k T Hn Hk; pose proof (HP _ _ _ _ Hn Hk) as H; rewrite exp_msub_id in H; exact H.
Qed.

(** Hence soundness at every well-formed global context, old form. *)
Corollary glu_fundamental_gctx : forall Θ Ξ Γ M A,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> @glu_rel_exp (gc_mk Θ Ξ) Γ M A.
Proof.
  intros * H.
  assert (Hg : ⊢g Θ ⍮ Ξ) by (eapply ctx_wf_gctx, presup_exp_ctx; exact H).
  destruct (gctx_glu _ _ Hg) as [HR HP].
  apply glu_fundamental_at; [ exact Hg | apply glu_rwf_of_raw | apply glu_pwf_of_raw | exact H ]; assumption.
Qed.

Print Assumptions kglu_fundamental.
Print Assumptions glu_msub_then.
Print Assumptions glu_fundamental_at.
Print Assumptions glu_msub_emb.
Print Assumptions gctx_glu.
Print Assumptions glu_fundamental_gctx.
