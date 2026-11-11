(** * Glued Module Values

    The gluing of module values ([glu_dmod]) read through substitutions
    and equations of module expressions, the environment of a body glued
    along the body's context ([glu_body_env]), and the closure of a glued
    unit's literal glued as the literal ([glu_lit_modexp_at]): the
    producer of the slot clause of the context gluing. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import LetPeeling.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Reading a Glued Module Value Through a Substitution *)

(** A factorization of [σ1] weakened, through [ζ2], gives one of [σ0]
    weakened, through [ζ ⨟ ζ2], when [σ0] is [ζ ⨟ σ1]. *)
Lemma glu_sub_through_compose : forall {Δ σ0 Γ0 Γ1 ζ σ1 Δ' φ Γ2 ζ2 σ2},
    Γ1 ⊢ˢ ζ : Γ0 ->
    Δ ⊢ˢ σ0 ≈ ζ ⨟ σ1 : Γ0 ->
    glu_sub_through Δ σ1 Γ1 Δ' φ Γ2 ζ2 σ2 ->
    glu_sub_through Δ σ0 Γ0 Δ' φ Γ2 (ζ ⨟ ζ2) σ2.
Proof.
  intros * Hζ Heq [Hφ Hζ2 Hσ2 E].
  constructor; [ exact Hφ | exact (wf_sub_compose _ _ _ _ _ _ _ Hζ Hζ2) | exact Hσ2 |].
  eapply wf_sub_eq_trans; [ eapply wf_sub_eq_sb_wk; [ exact Heq | exact Hφ ] |].
  eapply wf_sub_eq_respects_sb_eq; [| symmetry; apply sb_compose_assoc ].
  assert (Hw : sb_eq (ζ ⨟ sb_wk σ1 φ) (sb_wk (ζ ⨟ σ1) φ)).
  { rewrite (sb_wk_compose (ζ ⨟ σ1)), sb_compose_assoc, <- sb_wk_compose; reflexivity. }
  apply wf_sub_eq_sym; eapply wf_sub_eq_respects_sb_eq; [| exact Hw ].
  apply wf_sub_eq_sym; eapply wf_sub_eq_compose_right; [ exact Hζ | exact E ].
Qed.

(** A module value glued as [H0[σ0]] is glued as [H0[ζ][σ1]] when [σ0]
    is [ζ ⨟ σ1]: the factorizations of [σ1] are ones of [σ0]. *)
Lemma glu_dmod_through :
  (forall Δ σ0 Γ0 H0 h, glu_dmod Δ σ0 Γ0 H0 h ->
     forall Γ1 ζ σ1, Γ1 ⊢ˢ ζ : Γ0 -> Δ ⊢ˢ σ1 : Γ1 -> Δ ⊢ˢ σ0 ≈ ζ ⨟ σ1 : Γ0 -> glu_dmod Δ σ1 Γ1 H0[ζ]ᵐ h) /\
  (forall Δ ts ρ Ms Ns args, glu_tele_args Δ ts ρ Ms Ns args -> True).
Proof.
  apply glu_dmod_mut_ind_all; [ | | | intros; exact I | intros; exact I ].
  - (** A global module *)
    intros * Hσ HH0 HH0p Hl Hlen Hargs _ Γ1 ζ σ1 Hζ Hσ1 Heq.
    eapply glu_dmod_global; [ exact Hσ1 | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) | | exact Hl | exact Hlen | exact Hargs ].
    rewrite modexp_sub_sub.
    eapply wf_me_trans; [| exact HH0p ].
    apply wf_me_sym; exact (sub_eq_preserves_modexp _ _ _ _ _ HH0 _ _ _ Heq).
  - (** A body *)
    intros * Hσ HH0 Hmem Hsub IHsub Γ1 ζ σ1 Hζ Hσ1 Heq.
    apply glu_dmod_body; [ exact Hσ1 | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) | | ].
    + intros * Hp Ht Hk Hb.
      destruct (Hmem _ _ _ _ _ _ Hp Ht Hk Hb) as (a & m & [Ea Em Hg]).
      exists a, m; constructor; [ exact Ea | exact Em |].
      intros * Hst Hm; rewrite modexp_sub_sub in Hm |- *.
      exact (Hg _ _ _ _ _ _ _ _ (glu_sub_through_compose Hζ Heq Hst) Hm).
    + intros * Hp Hu Hb Hc; exact (IHsub _ _ _ _ _ _ _ Hp Hu Hb Hc _ _ _ Hζ Hσ1 Heq).
  - (** A value lacking a parameter *)
    intros * Hσ HH0 Hn Hpar Hex Happ _ Γ1 ζ σ1 Hζ Hσ1 Heq.
    eapply glu_dmod_fun; [ exact Hσ1 | exact (sub_preserves_modexp _ _ _ _ _ _ _ HH0 Hζ) | exact Hn | | exact Hex | ].
    + intros * Hst Hm; rewrite modexp_sub_sub in Hm.
      exact (Hpar _ _ _ _ _ _ _ _ _ _ (glu_sub_through_compose Hζ Heq Hst) Hm).
    + intros * Hst Hm; rewrite modexp_sub_sub in Hm; rewrite (modexp_sub_sub H0 ζ ζ0).
      exact (Happ _ _ _ _ _ _ _ _ _ _ (glu_sub_through_compose Hζ Heq Hst) Hm).
Qed.

End Fixed_GCtx.
