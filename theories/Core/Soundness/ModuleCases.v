(** * The Global Rules in the Gluing Model

    As [Core/Completeness/ModuleCases.v], for soundness: a judgment of
    [Θ1 ⍮ Ξ1] glues in every well-formed extension in which what [Θ1 ⍮ Ξ1]
    resolves glues ([glu_ext]).  The fundamental theorem holds in this form for
    contexts and typing ([kglu_fundamental]).  There is no unfolding field: the
    gluing model has no equality judgment, and δ is used only syntactically,
    where the extension carries it as it is. *)

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

(** ** 1. Glued extensions *)

Record glu_ext (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { gex_ext : gc_ext Θ1 Ξ1 Θ2 Ξ2
  ; gex_wf : ⊢g Θ2 ⍮ Ξ2
  ; gex_glob : forall r b pv A B,
      Θ1 ⍮ Ξ1 ∋ᵍ r ⇒ ge_def b pv A B ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ (a_glob r) A
  ; gex_param : forall lp T,
      gs_param Ξ1 lp = Some T ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ (a_param lp) T
  }.

(** ** 2. Kripke gluing *)

Definition kglu_ctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2, glu_ext Θ1 Ξ1 Θ2 Ξ2 -> @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ.

(** [glu_rel_exp] already contains the gluing of its context. *)
Definition kglu_exp Θ1 Ξ1 Γ M A : Prop :=
  forall Θ2 Ξ2, glu_ext Θ1 Ξ1 Θ2 Ξ2 -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.

(** ** Closed gluing at [⋅] weakens to every glued context

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


(** ** 3. The fundamental theorem, Kripke form *)

Theorem kglu_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kglu_exp Θ Ξ Γ M A).
Proof.
  apply syntactic_wf_ctx_exp_mut_ind; unfold kglu_ctx, kglu_exp; intros;
    repeat match goal with IH : forall _ _, glu_ext _ _ _ _ -> _ |- _ =>
      specialize (IH _ _ ltac:(eassumption)) end.
  (* ⋅ : the extension is well formed *)
  all: try solve [ apply (@glu_rel_ctx_empty (gc_mk _ _)); eapply gex_wf; eassumption ].
  (* the ordinary rules: the (ported) fixed-context case lemmas, at the extension *)
  all: try solve [ apply glu_rel_exp_typ; assumption | apply glu_rel_exp_nat; assumption
    | apply glu_rel_exp_zero; assumption | apply glu_rel_exp_succ; assumption
    | eapply glu_rel_exp_natrec; eassumption
    | eapply glu_rel_exp_pi; eassumption | eapply glu_rel_exp_fn; eassumption
    | eapply glu_rel_exp_app; eassumption ].
  all: try solve [ eapply glu_rel_exp_vlookup; eassumption ].
  (* parameters and globals: glued at [⋅] in the extension *)
  all: try solve [ eapply glu_rel_exp_nil_weaken; [ eassumption | eapply gex_param; eassumption ] ].
  all: try solve [ eapply glu_rel_exp_nil_weaken; [ eassumption | eapply gex_glob; eassumption ] ].
  all: try solve [ eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp |]; eassumption ].
  (* subsumption: the subtyping premise is read in the extension *)
  match goal with Hμ : glu_ext _ _ _ _ |- _ =>
    destruct (rebase_preserves_wf _ _ _ _ (gex_ext _ _ _ _ Hμ)
                ltac:(constructor; exact (gex_wf _ _ _ _ Hμ))) as (_ & _ & _ & Hsub) end.
  match goal with Hs : wf_subtyp _ _ _ _ _ |- _ => pose proof (Hsub _ _ _ Hs) end.
  eapply glu_rel_exp_subtyp; eassumption.
Qed.

(** ** 6. Gluing from the gluing of resolved types and bodies

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

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  Lemma glob_glu_of_raw : forall p b pv A B,
      Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
      (exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ A (Type@i)) ->
      (forall M, B = Some M -> @glu_rel_exp (gc_mk Θ Ξ) ⋅ M A) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ (a_glob p) A.
  Proof.
    intros p b pv A B Hl [i HT] HM.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    pose proof (wf_gctx_stack _ _ Hg) as HΞ.
    pose proof (gc_resolve_complete _ _ _ _ (wf_gstack_canon _ _ HΞ)
                  (wf_gdeps_canon _ (wf_gstack_deps _ _ HΞ)) Hl) as Hr.
    pose proof (wf_gc_lookup_type_closed _ _ _ _ _ _ _ _ Hb Hl) as HsT.
    destruct b; [ destruct B as [M |] |].
    - pose proof (wf_gc_lookup_body_closed _ _ _ _ _ _ _ _ Hb Hl) as HsM.
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

  Lemma param_glu_of_raw : forall lp T,
      gs_param Ξ lp = Some T ->
      (exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ T (Type@i)) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ (a_param lp) T.
  Proof.
    intros * Hp [i HT].
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    pose proof (wf_param_type_closed _ _ _ _ _ Hb Hp) as HsT.
    eapply (@glu_neut_nil (gc_mk Θ Ξ)) with (d := d_param lp);
      [ exact HT | | reflexivity | | reflexivity | | | |].
    - intros; eapply exp_closed_sub; eassumption.
    - intros; eapply exp_closed_wk; eassumption.
    - intros Δ' HΔ'; econstructor; eassumption.
    - intros s; eexists; split; constructor.
    - intros * Hrb; inversion Hrb; reflexivity.
    - intros * Hev; eapply eval_exp_param; [ exact Hp | exact Hev ].
  Qed.
End Raw.

(** ** 7. The gluing model's interface to [global_induction] *)

Definition glu_valid (Θ : gdeps) (Ξ : gstack) (A M : exp) : Prop :=
  @glu_rel_exp (gc_mk Θ Ξ) ⋅ M A.

Lemma glu_ext_of_raw : forall Θ1 Ξ1 Θ2 Ξ2,
    gc_ext Θ1 Ξ1 Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 ->
    SG glu_valid Θ1 Ξ1 Θ2 Ξ2 -> SP glu_valid Θ1 Ξ1 Θ2 Ξ2 ->
    glu_ext Θ1 Ξ1 Θ2 Ξ2.
Proof.
  intros * He Hg HS HP; pose proof He as [Hr Hp]; constructor; [ assumption | assumption | |].
  - intros * Hl; destruct (HS _ _ _ _ _ Hl) as [HT HM].
    exact (glob_glu_of_raw _ _ Hg _ _ _ _ _ (Hr _ _ Hl) HT HM).
  - intros * Hp1; exact (param_glu_of_raw _ _ Hg _ _ (Hp _ _ Hp1) (HP _ _ Hp1)).
Qed.

Lemma kglu_read : forall Θ1 Ξ1 Θ2 Ξ2 A M,
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    gc_ext Θ1 Ξ1 Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 ->
    SG glu_valid Θ1 Ξ1 Θ2 Ξ2 -> SP glu_valid Θ1 Ξ1 Θ2 Ξ2 ->
    glu_valid Θ2 Ξ2 A M.
Proof.
  intros * HM He Hg HS HP; exact (proj2 kglu_fundamental _ _ _ _ _ HM _ _ (glu_ext_of_raw _ _ _ _ He Hg HS HP)).
Qed.
