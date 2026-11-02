(** * Semantic Contexts of Member Types

    The canonical type of a member is built from the unit's parameters, the
    body before the member and the member's own type.  This file holds what
    the member lemmas need of the contexts these are checked in: extension
    by slots and by definitions with a module part, the inversions of a
    valid context's entries, the validity of the two ends of a
    [gsub], and the generalization of a type over a telescope
    ([valid_exp_under_ctx_ctx_pi]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import SubtypingCases VariableCases LetCases PropCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Semantic Contexts *)

Lemma rel_ctx_wf_extend_mod : forall {Γ U}, ⊨ Γ -> Γ ⊨ᵘ U ≈ U -> ⊨ Γ ▹ₘ U.
Proof.
  intros * HΓ [HU HsU _].
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
  econstructor; [ exact HΓ | exact (per_ctx_env_of_mod HR HU) | exact HU | exact HsU ].
Qed.

Lemma rel_ctx_wf_extend_dm : forall {Γ A M U} {i : nat},
    ⊨ Γ -> Γ ⊨ A : Typeω@i -> Γ ⊨ M : A -> Γ ⊨ᵘ U ≈ U -> ⊨ Γ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * HΓ HA HM [HU HsU _].
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
  econstructor; [ exact HΓ | exact (per_ctx_env_of_dm HR HA HM HU) | exact HA | exact HM | exact HU | exact HsU ].
Qed.

End Fixed_GCtx.

Lemma sem_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ).
Proof.
  intros * HU; sem_intro.
  apply valid_ctx_mod; [ assumption | eapply rel_ctx_wf_extend_mod; eassumption | assumption ].
Qed.

Lemma sem_ctx_extend_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ).
Proof.
  intros * HA HM HU; sem_intro.
  apply valid_ctx_dm; [ assumption | eapply rel_ctx_wf_extend_dm; eassumption | assumption ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The type of an assumption is a type of either sort. *)
Lemma rel_ctx_wf_ass_inv : forall {Γ A}, ⊨ Γ ▹ A -> exists Srt, type_sort Srt /\ Γ ⊨ A : Srt.
Proof. intros * H; inversion H; subst; eauto. Qed.

(** And so is that of a definition, its body valid at it. *)
Lemma rel_ctx_wf_def_inv : forall {Γ A M}, ⊨ Γ ▸ A ≔ M ->
    (exists Srt, type_sort Srt /\ Γ ⊨ A : Srt) /\ Γ ⊨ M : A.
Proof. intros * H; inversion H; subst; eauto. Qed.

(** The type of an assumption is a type of every index from some index on. *)
Corollary rel_ctx_wf_ass_type : forall {Γ A}, ⊨ Γ ▹ A ->
    exists i, forall j, i <= j -> Γ ⊨ᵗ A ≈ A at j.
Proof.
  intros * H; destruct (rel_ctx_wf_ass_inv H) as (Srt & HS & HA).
  exact (rel_type_of_sort_ge HS HA).
Qed.

(** In particular it is a type of an index. *)
Corollary rel_ctx_wf_ass_typ : forall {Γ A}, ⊨ Γ ▹ A -> exists i, Γ ⊨ᵗ A ≈ A at i.
Proof. intros * H; destruct (rel_ctx_wf_ass_type H) as [i Hi]; exists i; exact (Hi i (le_n i)). Qed.

Lemma rel_ctx_wf_mod_inv : forall {Γ U}, ⊨ Γ ▹ₘ U -> Γ ⊨ᵘ U ≈ U.
Proof. intros * H; inversion H; subst; constructor; assumption. Qed.

Lemma rel_ctx_wf_dm_inv : forall {Γ A M U}, ⊨ Γ ▸ₘ A ≔ M ‖ U ->
    (exists i, Γ ⊨ A : Typeω@i) /\ Γ ⊨ M : A /\ Γ ⊨ᵘ U ≈ U.
Proof. intros * H; inversion H; subst; repeat split; eauto; constructor; assumption. Qed.

(** A context entry's unit is valid where the entry is. *)
Lemma rel_ctx_wf_unit_inv : forall {Γ e U}, ⊨ e :: Γ -> centry_unit e = Some U -> Γ ⊨ᵘ U ≈ U.
Proof.
  intros * H He; destruct e; cbn in He; try discriminate; injection He as <-.
  - exact (rel_ctx_wf_mod_inv H).
  - exact (proj2 (proj2 (rel_ctx_wf_dm_inv H))).
Qed.

(** The context entry of a body entry with a module part holds its unit. *)
Lemma body_ctx_unit : forall Φ x E U, entry_unit E = Some U ->
    exists e, body_ctx (gm_ext Φ x E) = e :: body_ctx Φ /\ centry_unit e = Some U.
Proof.
  intros * HE; destruct E as [| pv U' | | pv A M U' |]; cbn in HE; try discriminate;
    injection HE as <-; eexists; split; reflexivity.
Qed.

Lemma gsub_sem : forall {Γ τ Δ}, gsub Γ τ Δ -> ⊨ Γ /\ ⊨ Δ.
Proof.
  induction 1 as [? HΓ | ? ? ? ? ? ? ? [IH1 IH2] HS HB HN _ | ? ? ? ? ? ? ? [IH1 IH2] HS HB HM _
                 | ? ? ? ? ? [IH1 IH2] HU _ | ? ? ? ? ? ? ? ? [IH1 IH2] HB HM HU _ _
                 | ? ? ? ? ? [IH1 IH2] Eq | ? ? ? ? ? HG [IH1 IH2] HS HB
                 | ? ? ? ? ? ? HG [IH1 IH2] HS HB HM | ? ? ? ? HG [IH1 IH2] HU HU'
                 | ? ? ? ? ? ? ? HG [IH1 IH2] HB HM HU HU'
                 | ? ? ? ? ? ? [IH1 IH2] HΓ Hσ Hl ];
    try (split; assumption).
  - split; [ assumption | eapply rel_ctx_wf_extend_sort; eassumption ].
  - split; [ assumption | eapply rel_ctx_wf_extend_def_sort; eassumption ].
  - split; [ assumption | eapply rel_ctx_wf_extend_mod; eassumption ].
  - split; [ assumption | eapply rel_ctx_wf_extend_dm; eassumption ].
  - pose proof (rel_exp_under_ctx_gsub HG HB) as H; rewrite (type_sort_sub _ _ HS) in H.
    split; eapply rel_ctx_wf_extend_sort; [ exact IH1 | exact HS | exact H | exact IH2 | exact HS | exact HB ].
  - pose proof (rel_exp_under_ctx_gsub HG HB) as H1; rewrite (type_sort_sub _ _ HS) in H1.
    pose proof (rel_exp_under_ctx_gsub HG HM) as H2.
    split; eapply rel_ctx_wf_extend_def_sort;
      [ exact IH1 | exact HS | exact H1 | exact H2 | exact IH2 | exact HS | exact HB | exact HM ].
  - split; eapply rel_ctx_wf_extend_mod; eassumption.
  - pose proof (rel_exp_under_ctx_gsub HG HB) as H1; cbn in H1.
    pose proof (rel_exp_under_ctx_gsub HG HM) as H2.
    split; eapply rel_ctx_wf_extend_dm; eassumption.
Qed.

(** ** Generalizing over a Telescope *)

(** A type of a universe, or a proposition, generalized over a telescope
    of assumptions: a [Π] into a type of a universe, or a [∀] into a
    proposition. *)
Lemma valid_exp_under_ctx_ctx_pi_at : forall r Ψ D X i, tele_ass Ψ -> ⊨ Ψ ++ D ->
    Ψ ++ D ⊨ X : relevance_sort r Typeω@i ->
    exists j, D ⊨ ctx_pi_at r Ψ X : relevance_sort r Typeω@j.
Proof.
  induction Ψ as [| e Ψ IH]; intros * HΨa HΨ HX; cbn in *; [ eauto |].
  inversion HΨa as [| ? ? [B ->] HΨa']; subst.
  destruct (rel_ctx_wf_ass_type HΨ) as [k HB].
  eapply IH; [ exact HΨa' | exact (rel_ctx_wf_tail HΨ) |].
  destruct r; cbn [relevance_sort] in *.
  - apply (rel_exp_under_ctx_pi_cong (i := max i k));
      [ apply HB; lia | apply HB; lia | eapply rel_exp_cumu_ge; [| exact HX ]; lia ].
  - exact (rel_exp_under_ctx_all (HB k (le_n k)) (HB k (le_n k)) HX).
Qed.

Corollary valid_exp_under_ctx_ctx_pi : forall Ψ D X i, tele_ass Ψ -> ⊨ Ψ ++ D -> Ψ ++ D ⊨ X : Typeω@i ->
    exists j, D ⊨ ctx_pi Ψ X : Typeω@j.
Proof. intros * HΨa HΨ HX; exact (valid_exp_under_ctx_ctx_pi_at relevant _ _ _ _ HΨa HΨ HX). Qed.

(** ** Telescopes of Parameters *)

Lemma tele_ass_app_inv : forall Δ1 Δ2, tele_ass (Δ1 ++ Δ2) -> tele_ass Δ1 /\ tele_ass Δ2.
Proof. intros * H; apply Forall_app in H; exact H. Qed.

End Fixed_GCtx.
