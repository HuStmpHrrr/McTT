(** * The Global Rules in the Gluing Model

    The soundness counterpart of [Core/Completeness/ModuleCases.v]: a judgment
    of [Θ1 ⍮ Ξ1] glues at every [Θ2 ⍮ Ξ2] it embeds into, provided everything
    that resolves at [Θ1 ⍮ Ξ1] glues there ([glu_emb]). An embedding moves
    nothing, so the fundamental theorem holds in this form for contexts and
    typing ([kglu_fundamental]), each case being the fixed-context one at the
    target. The subtyping premise of subsumption is moved syntactically
    ([emb_preserves_wf]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases
  SubtypingCases UniverseCases FunctionCases NatCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound embeddings *)

Record glu_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { gme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; gme_glob : forall r b pv A B Γ,
      gc_resolve Θ1 Ξ1 r = Some (ge_def b pv A B) ->
      @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_glob r) A
  }.

(** ** 2. Kripke gluing *)

Definition kglu_ctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2, glu_emb Θ1 Ξ1 Θ2 Ξ2 -> @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ.

Definition kglu_exp Θ1 Ξ1 Γ M A : Prop :=
  forall Θ2 Ξ2, glu_emb Θ1 Ξ1 Θ2 Ξ2 -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.

(** ** 3. The fundamental theorem, Kripke form *)

Theorem kglu_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kglu_exp Θ Ξ Γ M A).
Proof.
  apply syntactic_wf_ctx_exp_mut_ind; unfold kglu_ctx, kglu_exp; intros;
    repeat match goal with IH : forall _ _, glu_emb _ _ _ _ -> _ |- _ =>
      specialize (IH _ _ ltac:(eassumption)) end.
  all: try solve [ apply (@glu_rel_ctx_empty (gc_mk Θ2 Ξ2)); eapply em_wf, gme_emb; eassumption ].
  all: try solve [ apply glu_rel_exp_typ; assumption | apply glu_rel_exp_nat; assumption
    | apply glu_rel_exp_zero; assumption | apply glu_rel_exp_succ; assumption
    | eapply glu_rel_exp_natrec; eassumption
    | eapply glu_rel_exp_pi; eassumption | eapply glu_rel_exp_fn; eassumption
    | eapply glu_rel_exp_app; eassumption ].
  all: try solve [ eapply glu_rel_exp_vlookup; eassumption ].
  all: try solve [ eapply gme_glob; eassumption ].
  all: try solve [ eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp |]; eassumption ].
  (* subsumption: the subtyping premise is moved syntactically *)
  match goal with Hμ : glu_emb _ _ _ _ |- _ =>
    destruct (emb_preserves_wf _ _ _ _ (gme_emb _ _ _ _ Hμ)) as (_ & _ & _ & Hsub) end.
  match goal with Hs : wf_subtyp _ _ _ _ _ |- _ => pose proof (Hsub _ _ _ Hs) end.
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

(** ** 5. The gluing model's notion of a valid entry *)

Definition glu_entry (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, @glu_rel_exp (gc_mk Θ Ξ) ⋅ A (Type@i)) /\
      (forall M, B = Some M -> @glu_rel_exp (gc_mk Θ Ξ) ⋅ M A)
  | ge_mod _ _ => True
  end.

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  Lemma glob_glu_of_raw : forall p b pv A B,
      gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
      glu_entry Θ Ξ (ge_def b pv A B) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ (a_glob p) A.
  Proof.
    intros p b pv A B Hr [[i HT] HM].
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    destruct (wf_gc_resolve_closed _ _ _ _ _ _ _ _ Hb Hr) as [HsT HsB].
    destruct b; [ destruct B as [M |] |].
    - cbn in HsB.
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
End Raw.

Theorem glu_emb_of : forall Θ1 Ξ1 Θ2 Ξ2,
    Emb Θ1 Ξ1 Θ2 Ξ2 -> GV glu_entry Θ1 Ξ1 Θ2 Ξ2 -> glu_emb Θ1 Ξ1 Θ2 Ξ2.
Proof.
  intros * He HG; pose proof He as [Hg Hs].
  constructor; [ exact He |].
  intros * Hr HΓs.
  apply glu_rel_exp_nil_weaken; [ exact HΓs |].
  exact (glob_glu_of_raw _ _ Hg _ _ _ _ _ (Hs _ _ Hr) (HG _ _ Hr)).
Qed.

Lemma kglu_read : forall Θ1 Ξ1 Θ2 Ξ2 A M,
    glu_emb Θ1 Ξ1 Θ2 Ξ2 ->
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ M A.
Proof. intros * Hμ HM; exact (proj2 kglu_fundamental _ _ _ _ _ HM _ _ Hμ). Qed.

Lemma glu_entry_def : forall Θ Ξ A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> Good glu_entry Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    glu_entry Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M))).
Proof.
  intros * HM HG He.
  pose proof (glu_emb_of _ _ _ _ He (HG _ _ He)) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kglu_read _ _ _ _ _ _ Hμ HT) |].
  intros ? [= <-]; exact (kglu_read _ _ _ _ _ _ Hμ (ctx_fn_wf0 _ _ _ _ _ _ HA HM)).
Qed.

Lemma glu_entry_ax : forall Θ Ξ A i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Type@i -> Good glu_entry Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    glu_entry Θ2 Ξ2 (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  pose proof (glu_emb_of _ _ _ _ He (HG _ _ He)) as Hμ.
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kglu_read _ _ _ _ _ _ Hμ HT) | discriminate ].
Qed.

(** Every well-formed global context glues: the identity is a sound
    embedding. *)
Theorem gctx_glu : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> glu_emb Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply glu_emb_of; [ apply Emb_refl; assumption |].
  exact (global_induction glu_entry glu_entry_def glu_entry_ax _ _ Hg).
Qed.
