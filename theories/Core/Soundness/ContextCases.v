From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import LogicalRelation VariableCases.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** As [wf_ctx_empty], relative to a well-formed global context. *)
Lemma glu_rel_ctx_empty : ⊢ᵍ gc_deps ⍮ gc_stack -> ⊩ ⋅.
Proof.
  intros; do 2 econstructor; [reflexivity | assumption].
Qed.

Hint Resolve glu_rel_ctx_empty : mctt.

(** A term of a sort of the kind [κ] is a type glued at an index [i], of
    the sort of [κ] next to [Typeω@i]: a type of a universe at the
    universe's index, a proposition or a type of levels at any. *)
Lemma glu_rel_exp_sort_typ : forall {Γ A S κ},
    Γ ⊩ A : S ->
    sort_kind S κ ->
    exists Sb (i : nat),
      EG Γ ∈ glu_ctx_env ↘ Sb /\
      Γ ⊢ A : abs_kind_sort κ Typeω@i /\
      (forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_typ_with_sub i Δ A σ ρ).
Proof.
  intros * HA HS.
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt.
  destruct HA as [Sb HSb L HAg].
  destruct HS as [j | |].
  - (** A type of a universe *)
    exists Sb, j; repeat split; [ exact HSb | exact HAt |].
    intros Δ σ ρ Hσ; destruct (HAg _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
    simplify_evals; cbn [domain_kind glu_term_value] in Hm.
    basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
    destruct HAs as [_ _ [Pm Elm Hgm Hpm]].
    econstructor; [ exact Hm | exact Hgm | exact Hpm ].
  - (** A proposition: glued as one at any index *)
    exists Sb, 0; repeat split; [ exact HSb | exact HAt |].
    intros Δ σ ρ Hσ; destruct (HAg _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
    simplify_evals; cbn [domain_kind glu_term_value] in Hm.
    basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
    destruct HAs as [_ _ Hpm HP].
    econstructor; [ exact Hm | | exact HP ].
    simp glu_univ_elem; eapply glu_univ_elem_core_prop; [ exact Hpm | reflexivity | reflexivity ].
  - (** A type of levels: glued at the least small index, so at any *)
    exists Sb, 0; repeat split; [ exact HSb | exact HAt |].
    intros Δ σ ρ Hσ; destruct (HAg _ _ _ Hσ) as [s m Ps Els Es Hm Hgs HAs].
    simplify_evals; cbn [domain_kind glu_term_value] in Hm.
    basic_invert_glu_univ_elem Hgs; apply_predicate_equivalence.
    destruct HAs as [_ _ _ [Pm Elm Hgm Hpm]].
    assert (Hle : universe_index_le (us (ordinal_of_nat 0)) (ul 0)) by exact I.
    destruct (glu_univ_elem_cumu_ge_universe_index Hle Hgm) as (P0 & El0 & Hg0).
    econstructor; [ exact Hm | exact Hg0 |].
    eapply glu_univ_elem_typ_cumu_ge_universe_index; [ exact Hle | exact Hgm | exact Hg0 | exact Hpm ].
Qed.

(** A term glued at a type glued at the index [i] is glued at [i]: its
    gluing moves along the indices ([glu_univ_elem_exp_conv]). *)
Lemma glu_rel_exp_at_typ_index : forall {Sb Γ M A} {i : nat},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_typ_with_sub i Δ A σ ρ) ->
    Γ ⊩ M : A ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb -> glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * HSb HA HM.
  destruct (glu_rel_exp_clean_inversion1 HSb HM) as [k Hk].
  intros Δ σ ρ Hσ.
  destruct (HA _ _ _ Hσ) as [a P El Ea Hg HAg].
  destruct (Hk _ _ _ Hσ) as [a' m P' El' Ea' Hm Hg' HMg].
  functional_eval_rewrite_clear.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hg') as [R HR].
  econstructor; [ eassumption | exact Hm | exact Hg |].
  eapply (glu_univ_elem_exp_conv (k := k)); [ eexists; exact HR | exact Hg' | exact Hg | exact HMg | exact HAg ].
Qed.

(** An assumption of a type of a sort of its kind. *)
Lemma glu_rel_ctx_extend : forall {Γ A S κ},
    ⊩ Γ ->
    Γ ⊩ A : S ->
    sort_kind S κ ->
    ⊩ Γ ▹{κ} A.
Proof.
  intros * _ HA HS.
  destruct (glu_rel_exp_sort_typ HA HS) as (Sb & i & HSb & HAt & HAg).
  eexists; econstructor; [ exact HSb | exact HAt | exact HAg | reflexivity ].
Qed.

Hint Resolve glu_rel_ctx_extend : mctt.

(** A definition, of a type of a sort. *)
Lemma glu_rel_ctx_extend_def : forall {Γ A S M},
    ⊩ Γ ->
    Γ ⊩ A : S ->
    type_sort S ->
    Γ ⊩ M : A ->
    ⊩ Γ ▸ A ≔ M.
Proof.
  intros * _ HA HS HM.
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  assert (HSk : exists κ, sort_kind S κ) by (destruct HS; eexists; constructor).
  destruct HSk as [κ HSk].
  destruct (glu_rel_exp_sort_typ HA HSk) as (Sb & i & HSb & HAt & HAg).
  pose proof (glu_rel_exp_at_typ_index HSb HAg HM) as HMg.
  eexists; econstructor; [ exact HSb | exact HAt | exact HMt | exact HAg | exact HMg | reflexivity ].
Qed.

Hint Resolve glu_rel_ctx_extend_def : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_ctx_empty : mctt.
#[export]
Hint Resolve glu_rel_ctx_extend glu_rel_ctx_extend_def : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

Lemma glu_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊩ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. glu_intro; eapply glu_rel_ctx_empty; eapply gctx_embedding_wf, glu_gctx_embedding_embedding; eassumption. Qed.

Lemma glu_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹{κ} A ).
Proof. glu_intro; eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp | |]; eassumption. Qed.

Lemma glu_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof. glu_intro; eapply glu_rel_ctx_extend_def; [ eapply presup_ctx_glu_rel_exp | | |]; eassumption. Qed.
