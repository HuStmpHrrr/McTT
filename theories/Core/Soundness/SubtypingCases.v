(** * Subtyping and Conversion

    The gluing model has subsumption and conversion rules for terms only: there
    is no substitution judgment, and context subtyping is the syntactic
    relation [ctx_sub]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation VariableCases.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Subsumption: the term's gluing moves to the larger type, glued as a
    type of a sort ([glu_rel_exp_sort_typ]), along the semantic subtyping
    of the two types' values ([glu_univ_elem_per_subtyp_trm_conv]); the
    term's value is at the same kind ([per_subtyp_kind]). *)
Lemma glu_rel_exp_subtyp : forall {Γ M A A' S},
    Γ ⊩ M : A ->
    Γ ⊩ A' : S ->
    type_sort S ->
    Γ ⊢ A ⊆ A' ->
    Γ ⊩ M : A'.
Proof.
  intros * HM HA' HS Hsub%completeness_fundamental_subtyp.
  destruct HM as [Sb HSb k HMg].
  assert (HSk : exists κ, sort_kind S κ) by (destruct HS; eexists; constructor).
  destruct HSk as [κ HSk].
  destruct (glu_rel_exp_sort_typ HA' HSk) as (Sb' & i & HSb' & _ & HA'g).
  assert (E : Sb <∙> Sb') by (eapply functional_glu_ctx_env; eassumption).
  pose proof (rel_subtyp_under_ctx_simple Hsub) as [env_relΓ [HΓ [k' Hss]]].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HSb |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_per_env HSb HΓ Hσ) as Hρ.
  destruct (Hss _ _ Hρ) as (a1 & a2 & Ea1 & Ea2 & Hsa).
  destruct (HMg _ _ _ Hσ) as [a0 m P El Ea0 Hm Hg HN].
  destruct (HA'g _ _ _ (proj1 (E _ _ _) Hσ)) as [a3 P' El' Ea3 Hg' HA'σ].
  functional_eval_rewrite_clear.
  econstructor; [ eassumption | rewrite <- (per_subtyp_kind _ _ _ Hsa); exact Hm | exact Hg' |].
  eapply glu_univ_elem_per_subtyp_trm_conv; [ exact Hsa | exact Hg | exact Hg' | exact HA'σ | exact HN ].
Qed.

Hint Resolve glu_rel_exp_subtyp : mctt.

Lemma glu_rel_exp_conv : forall {Γ M A A' S},
    Γ ⊩ M : A ->
    Γ ⊩ A' : S ->
    type_sort S ->
    Γ ⊢ A ≈ A' : S ->
    Γ ⊩ M : A'.
Proof.
  intros * HM HA' HS Heq.
  eapply glu_rel_exp_subtyp; [ exact HM | exact HA' | exact HS |].
  eapply wf_subtyp_refl; [ exact (glu_rel_exp_to_wf_exp HA') | exact HS | exact Heq ].
Qed.

Hint Resolve glu_rel_exp_conv : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_subtyp : mctt.
#[export]
Hint Resolve glu_rel_exp_conv : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

Lemma glu_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A' ).
Proof.
  glu_intro; glu_gctx_embedding_wf;
    eapply glu_rel_exp_subtyp; [ eassumption | eassumption | eassumption | apply Hwst; eassumption ].
Qed.

Lemma glu_exp_eq_subtyp :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Srt ->
     type_sort Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_sym :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_trans :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_refl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M' : Srt ->
     type_sort Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_trans :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_univ :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     i < j ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_level :
  `( m <= n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : abs_kind_sort κd Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : abs_kind_sort κd Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ⊩ B' : abs_kind_sort κc Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ->
     pi_kinds κd κc ->
     evaluated_kind κc ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
