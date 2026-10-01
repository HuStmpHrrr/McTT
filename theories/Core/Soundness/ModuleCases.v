(** * The Global Rules in the Gluing Model

    As [Core/Completeness/ModuleCases.v], for soundness: a judgment of
    [Θ ⍮ Ξ] glues when it glues after every *sound* module substitution out of
    [Θ ⍮ Ξ] ([glu_msub]: [syn_msub], and what it puts in glued at the
    target).  The fundamental theorem holds in this form for contexts and
    typing ([kglu_fundamental]); at the identity it is the fixed-context
    theorem, given that every resolved global and parameter glues at [⋅]
    ([glu_fundamental_at]).  There is no unfolding field: the gluing model has
    no equality judgment, and δ is used only syntactically, where [syn_msub]
    transports it. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic Require Export GlobalInduction.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases
  SubtypingCases UniverseCases FunctionCases NatCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound module substitutions *)

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

(** ** 4. Closed gluing at [⋅] weakens to every glued context

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

(** ** 5. The identity is sound, given [⊩g]: every resolved global and
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

(** ** 6. [⊩g] from the gluing of resolved types and bodies

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
  Proof. (* OPTA-TODO *) Admitted.

  Lemma param_glu_of_raw : forall n U k T,
      List.nth_error Ξ n = Some U ->
      gu_params U ∋ #k : T ->
      (exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ (T[↑ₘ (S n)]ᵐ[sb_params n]) (Type@i)) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ $[n, k] (T[↑ₘ (S n)]ᵐ[sb_params n]).
  Proof. (* OPTA-TODO *) Admitted.

  Lemma glu_rwf_of_raw : glu_rwf_raw Θ Ξ -> glu_rwf Θ Ξ.
  Proof. intros HR p * Hl; exact (glob_glu_of_raw _ _ _ _ _ _ Hl (HR _ _ _ _ _ _ Hl)). Qed.

  Lemma glu_pwf_of_raw : glu_pwf_raw Θ Ξ -> glu_pwf Θ Ξ.
  Proof. intros HP n U k T Hn Hk; exact (param_glu_of_raw _ _ _ _ Hn Hk (HP _ _ _ _ Hn Hk)). Qed.
End Raw.

(** ** 7. The gluing model's interface to [global_induction] *)

Definition glu_valid (Θ : gdeps) (Ξ : gstack) (A M : exp) : Prop :=
  @glu_rel_exp (gc_mk Θ Ξ) ⋅ M A.

Theorem glu_msub_emb : forall Θ1 Ξ1 Θ2 Ξ2 μ,
    Emb Θ1 Ξ1 Θ2 Ξ2 μ -> SG glu_valid Θ1 Ξ1 Θ2 Ξ2 μ -> SP glu_valid Θ1 Ξ1 Θ2 Ξ2 μ ->
    glu_msub Θ1 Ξ1 Θ2 Ξ2 μ nil.
Proof.
  intros * He HG HP; pose proof He as [Hg Hq Hp Hl].
  assert (Hqe : forall n (X : exp), X[ms_qn n μ]ᵐ = X[μ]ᵐ) by (intros; apply exp_msub_ext, Hq).
  constructor.
  - exact (syn_msub_emb _ _ _ _ _ He).
  - apply (@glu_rel_ctx_empty (gc_mk Θ2 Ξ2)); exact Hg.
  - intros * Hn Hk _ HΓs; rewrite !Hqe; rewrite List.app_nil_r in *.
    destruct (Hp _ _ _ _ Hn Hk) as (n' & U' & k' & T' & Heq & Hn' & Hk' & HT).
    pose proof (HP _ _ _ _ Hn Hk) as HPv; unfold vtyp in HPv.
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
    glu_valid Θ2 Ξ2 A[μ]ᵐ M[μ]ᵐ.
Proof. intros * Hμ HM; exact (proj2 kglu_fundamental _ _ _ _ _ HM _ _ _ _ Hμ). Qed.
