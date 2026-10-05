(** * The Global Rules in the Gluing Model

    The soundness counterpart of [Core/Completeness/ModuleCases.v]: a judgment
    of [Θ1] glues at every [Θ2] it embeds into, provided every constant
    [Θ1] files glues there ([glu_emb]). An embedding moves
    nothing, so the fundamental theorem holds in this form for contexts and
    typing ([kglu_fundamental]), each case being the fixed-context one at the
    target. The subtyping premise of subsumption is moved syntactically
    ([emb_preserves_wf]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Syntactic.System Require Import MemberWf GlobalPresup.
From Mctt.Core.Completeness Require Import ModexpCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases MemberCases
  SubtypingCases UniverseCases FunctionCases LetCases NatCases TrueFalseCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound embeddings *)

Record glu_emb (Θ1 : gctx) (Θ2 : gctx) : Prop :=
  { gme_emb : Emb Θ1 Θ2
  ; gme_const : forall c A M b Γ,
      gc_const Θ1 c = Some (A, M, b) ->
      @glu_rel_ctx (gc_mk Θ2) Γ ->
      @glu_rel_exp (gc_mk Θ2) Γ (a_const c) A
  }.

(** ** 2. Kripke gluing *)

Definition kglu_ctx Θ1 Γ : Prop :=
  forall Θ2, glu_emb Θ1 Θ2 -> @glu_rel_ctx (gc_mk Θ2) Γ.

Definition kglu_exp Θ1 Γ M A : Prop :=
  forall Θ2, glu_emb Θ1 Θ2 -> @glu_rel_exp (gc_mk Θ2) Γ M A.

(** ** 3. The fundamental theorem, Kripke form *)

(** The other judgments glue their context, which is what a module slot,
    whose premise is a unit judgment, needs. *)
Theorem kglu_fundamental :
  (forall Θ Γ, ⊢ Θ ⍮ Γ -> kglu_ctx Θ Γ) /\
  (forall Θ Γ A M, Θ ⍮ Γ ⊢ M : A -> kglu_exp Θ Γ M A) /\
  (forall Θ Γ A M M', Θ ⍮ Γ ⊢ M ≈ M' : A -> kglu_ctx Θ Γ) /\
  (forall Θ Γ A A', Θ ⍮ Γ ⊢ A ⊆ A' -> kglu_ctx Θ Γ) /\
  (forall Θ Γ Ψ Ψ', Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> kglu_ctx Θ Γ) /\
  (forall Θ Γ U U', Θ ⍮ Γ ⊢ᵘ U ≈ U' -> kglu_ctx Θ Γ) /\
  (forall Θ Γ H H', Θ ⍮ Γ ⊢ᵐ H ≈ H' -> kglu_ctx Θ Γ).
Proof.
  apply syntactic_wf_mut_ind; unfold kglu_ctx, kglu_exp; intros;
    repeat match goal with IH : forall _, glu_emb _ _ -> _ |- _ =>
      specialize (IH _ ltac:(eassumption)) end.
  all: try solve [ apply (@glu_rel_ctx_empty (gc_mk Θ2)); eapply em_wf, gme_emb; eassumption ].
  all: try solve [ apply glu_rel_exp_typ; assumption | apply glu_rel_exp_nat; assumption
    | apply glu_rel_exp_zero; assumption | apply glu_rel_exp_succ; assumption
    | eapply glu_rel_exp_natrec; eassumption
    | apply glu_rel_exp_True; assumption | apply glu_rel_exp_False; assumption
    | apply glu_rel_exp_true; assumption
    | eapply glu_rel_exp_exfalso; eassumption
    | eapply glu_rel_exp_pi; eassumption | eapply glu_rel_exp_fn; eassumption
    | eapply glu_rel_exp_app; eassumption ].
  all: try solve [ eapply glu_rel_exp_vlookup; eassumption ].
  all: try solve [ eapply gme_const; eassumption ].
  all: try solve [ eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp |]; eassumption ].
  all: try solve [ eapply glu_rel_ctx_extend_def; [ eapply presup_ctx_glu_rel_exp | |]; eassumption ].
  all: try solve [ eapply glu_rel_exp_let; eassumption ].
  (** The context of the other judgments. *)
  all: try solve [ assumption | eapply presup_ctx_glu_rel_exp; eassumption
                 | eapply glu_rel_ctx_tail; eassumption
                 | eapply glu_rel_ctx_tail, presup_ctx_glu_rel_exp; eassumption ].
  (** Module slots, module [let]s and members, their premises moved
      syntactically. *)
  all: try solve [
    match goal with Hμ : glu_emb _ _ |- _ =>
      pose proof (gme_emb _ _ Hμ) as Hem;
      destruct (emb_preserves_wf _ _ Hem) as (Ec & Ee & Eq & Est & Ex & Eu & Em) end;
    first
      [ eapply (@glu_rel_ctx_extend_mod (gc_mk _)); [ eassumption | apply Eu; eassumption ]
      | eapply (@glu_rel_exp_let_mod (gc_mk _)); [ apply Eu; eassumption | apply Ee; eassumption | eassumption ]
      | eapply (@glu_rel_exp_mem (gc_mk _));
          [ eassumption | apply Em; eassumption
          | eapply member_type_emb; [ exact (em_res _ _ Hem) | eassumption ]
          | apply Ee; eassumption
          | eapply member_unfold_emb; [ exact (em_res _ _ Hem) | eassumption ]
          | apply Ee; eassumption | eassumption ]
      | eapply (@glu_rel_exp_mem_app (gc_mk _));
          [ apply Em; eassumption | eassumption | eassumption | apply Ee; eassumption
          | apply Ee; eassumption | eassumption ] ] ].
  (* subsumption: the subtyping premise is moved syntactically *)
  match goal with Hμ : glu_emb _ _ |- _ =>
    destruct (emb_preserves_wf _ _ (gme_emb _ _ Hμ)) as (_ & _ & _ & Hsub & _) end.
  match goal with Hs : wf_subtyp _ _ _ _ |- _ => pose proof (Hsub _ _ _ Hs) end.
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
    intros * HΔ; constructor; [ exact HΔ | apply wf_ctx_empty; eapply ctx_wf_gctx; exact HΔ | | |];
      intros * Hx; inversion Hx.
  Qed.

  Lemma glu_rel_exp_nil_weaken : forall Γ N T, ⊩ Γ -> ⋅ ⊩ N : T -> Γ ⊩ N : T.
  Proof.
    intros * [SbΓ HΓ] [Sb0 [H0 [i Hi]]].
    exists SbΓ; split; [ exact HΓ |]; exists i; intros Δ σ ρ Hσ.
    apply Hi.
    inversion H0 as [Sb' Heq Hg | | |]; subst.
    apply (Heq Δ σ ρ); cbn.
    apply wf_sub_nil, (wf_sub_dom _ _ _ _ (glu_ctx_env_sub_escape HΓ _ _ _ Hσ)).
  Qed.
End Weaken.

(** ** Globals from the gluing of their types and bodies

    δ evaluates the body at [nil], and a global or parameter is a neutral
    annotated with its type evaluated at [nil]. Since [nil_glu_sub_pred]
    leaves the environment free, the [⋅]-judgment can be instantiated at
    [nil]. The only semantic fact needed is that the values of a closed type at
    two environments are related ([typ_nil_rel], from completeness at [⋅]),
    which [glu_univ_elem_resp_per_univ] and [glu_univ_elem_exp_conv]
    consume. *)

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
    inversion Hnil as [? Heq | | |]; subst.
    apply Heq; exact I.
  Qed.

  Lemma glu_nil_sb : forall Sb Δ σ ρ,
      EG ⋅ ∈ glu_ctx_env ↘ Sb -> Δ ⊢s σ ® ρ ∈ Sb -> forall ρ', Δ ⊢s σ ® ρ' ∈ Sb.
  Proof.
    intros * H0 Hσ ρ'.
    inversion H0 as [Sb' Heq Hg | | |]; subst.
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
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ (glu_ctx_env_sub_escape H0 _ _ _ Hσ)).
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
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ (glu_ctx_env_sub_escape H0 _ _ _ Hσ)).
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

(** ** 5. Constants glue *)

(** A constant valid at [Θ2]: its type and body, if any, glue at [⋅]. *)
Definition glu_const (Θ2 : gctx) (A : exp) (oM : option exp) : Prop :=
  (exists i, @glu_rel_exp (gc_mk Θ2) ⋅ A (Type@i)) /\
  (forall M, oM = Some M -> @glu_rel_exp (gc_mk Θ2) ⋅ M A).

Definition glu_unit (Θ2 : gctx) (U : gunit) : Prop := True.

Section Raw.
  Variables (Θ : gctx).
  Hypothesis Hg : ⊢g Θ.

  Lemma const_glu_of_raw : forall c A oM b,
      gc_const Θ c = Some (A, oM, b) -> glu_const Θ A oM ->
      @glu_rel_exp (gc_mk Θ) ⋅ (a_const c) A.
  Proof.
    intros c A oM b Hr [[i HT] HM].
    assert (Hb : ⊢ Θ ⍮ ⋅) by (constructor; assumption).
    destruct (wf_gc_const_closed _ _ _ _ _ _ Hb Hr) as [HsT HsM].
    assert (Hc : forall σ, (a_const c)[σ] = a_const c) by reflexivity.
    assert (Hcw : forall φ, (a_const c)[φ]ʷ = a_const c) by reflexivity.
    assert (Hst : b = false \/ oM = None -> @glu_rel_exp (gc_mk Θ) ⋅ (a_const c) A).
    { intros Ho; eapply (@glu_neut_nil (gc_mk Θ)) with (d := d_glob c);
        [ exact HT | | exact Hc | | exact Hcw | | | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros; eapply exp_closed_wk; eassumption.
      + intros Δ' HΔ'; eapply wf_const; eassumption.
      + intros s; eexists; split; constructor.
      + intros * Hrb; inversion Hrb; subst; reflexivity.
      + intros * Hev; eapply eval_exp_const; eassumption. }
    destruct b; [ destruct oM as [M |] |]; [| apply Hst; auto .. ]; cbn in HsM.
    - eapply (@glu_delta_nil (gc_mk Θ)); [ exact (HM _ eq_refl) | | | exact Hc | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros; eapply exp_closed_sub; eassumption.
      + intros Δ' HΔ'; eapply wf_exp_eq_const_unfold; eassumption.
      + intros * Hev; eapply eval_exp_const_unfold; eassumption.
  Qed.
End Raw.

Theorem glu_emb_of : forall Θ1 Θ2,
    Emb Θ1 Θ2 -> GV glu_const glu_unit Θ1 Θ2 -> glu_emb Θ1 Θ2.
Proof.
  intros * He [HC _]; pose proof He as [Hg Hs].
  constructor; [ exact He |].
  intros * Hr HΓs.
  apply glu_rel_exp_nil_weaken; [ exact HΓs |].
  exact (const_glu_of_raw _ Hg _ _ _ _ (gc_sub_const _ _ _ _ Hs Hr) (HC _ _ _ _ Hr)).
Qed.

Lemma kglu_read : forall Θ1 Θ2 A M,
    glu_emb Θ1 Θ2 ->
    Θ1 ⍮ ⋅ ⊢ M : A ->
    @glu_rel_exp (gc_mk Θ2) ⋅ M A.
Proof. intros * Hμ HM; exact (proj1 (proj2 kglu_fundamental) _ _ _ _ HM _ Hμ). Qed.

Lemma glu_const_of : forall Θ A oM Θ2,
    const_wf Θ A oM -> Good glu_const glu_unit Θ -> Emb Θ Θ2 -> glu_const Θ2 A oM.
Proof.
  intros * HM HG He.
  pose proof (glu_emb_of _ _ He (HG _ He)) as Hμ.
  destruct oM as [M |]; cbn in HM.
  - destruct (presup_exp_typ HM) as [i HA].
    split; [ exists i; exact (kglu_read _ _ _ _ Hμ HA) | intros ? [= <-]; exact (kglu_read _ _ _ _ Hμ HM) ].
  - destruct HM as [i HA]; split; [ exists i; exact (kglu_read _ _ _ _ Hμ HA) | discriminate ].
Qed.

Lemma glu_unit_of : forall Θ U Θ2,
    Θ ⍮ ⋅ ⊢ᵘ U ≈ U -> Good glu_const glu_unit Θ -> Emb Θ Θ2 -> glu_unit Θ2 U.
Proof. intros; exact I. Qed.

(** Every well-formed global context glues: the identity is a sound
    embedding. *)
Theorem gctx_glu : forall Θ, ⊢g Θ -> glu_emb Θ Θ.
Proof.
  intros * Hg; apply glu_emb_of; [ apply Emb_refl; assumption |].
  exact (global_induction glu_const glu_unit glu_const_of glu_unit_of _ Hg).
Qed.
