(** * Paths to Global Modules

    A path names a closed module, so its value and its member types do not
    depend on the local context: what holds at [⋅] holds everywhere.  What
    holds at [⋅] is the semantic validity of the global context's modules
    ([gsem_ok]), which the global context's well-formedness provides. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases
  MemberCases MemberTyping MemberReps MemberSem ModexpCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** [nil] is reached by [sb_zero], which evaluates to [nil] in any environment
    (a list environment reads [zeroᵈ] past its end). *)
Definition sb_zero : sub := fun _ => se_exp a_zero.

Lemma eval_sub_zero_nil : forall {Θ Ξ} ρ, eval_sub Θ Ξ sb_zero ρ nil.
Proof. intros * x; cbn; rewrite env_entry_ge by (cbn; lia); eexists; split; [ reflexivity | constructor ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma rel_sub_zero_nil : forall Γ R, per_ctx_env R Γ Γ -> Γ ⊨s sb_zero ≈ sb_zero : ⋅.
Proof.
  intros * HR.
  assert (H0 : per_ctx_env (fun _ _ => True) ⋅ ⋅) by (apply per_ctx_env_nil; reflexivity).
  exists R, HR, (fun _ _ => True), H0.
  intros * _ φ _ ρ ρ' _.
  apply (mk_rel_sub nil nil nil nil); try apply eval_sub_zero_nil.
  all: cbn; repeat split.
Qed.

Lemma per_ctx_env_nil_total : forall R, per_ctx_env R ⋅ ⋅ -> forall ρ ρ', R ρ ρ'.
Proof. intros * H; inversion H; subst; intros; apply H0; exact I. Qed.

Lemma sub_link_zero : forall Γ, sub_link Γ ⋅ sb_zero.
Proof.
  intros Γ Γ' R' HΓ' σ σ' Hσ RΔ HΔ ρ ρσ Hρ Hev.
  exists nil; split; [| intros; apply (per_ctx_env_nil_total _ HΔ) ].
  intros x; cbn; rewrite env_entry_ge by (cbn; lia); eexists; split; [ reflexivity | constructor ].
Qed.

Lemma gsub_zero : forall Γ, ⊨ Γ -> gsub Γ sb_zero ⋅.
Proof.
  intros * HΓ.
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  pose proof (gsub_comp _ _ _ _ _ (gsub_id _ sem_ctx_nil) HΓ (rel_sub_zero_nil _ _ HR) (sub_link_zero _)) as Hg.
  eapply gsub_eq; [ exact Hg | apply sb_compose_id_left ].
Qed.

Lemma rep_lift_nil : forall Γ A n b, ⊨ Γ -> rep ⋅ A n b -> exp_scoped 0 A -> rep Γ A n b.
Proof.
  intros * HΓ Hr Hs.
  pose proof (rep_sub _ _ _ _ Hr _ _ (gsub_zero _ HΓ)) as H.
  rewrite exp_closed_sub in H by exact Hs; exact H.
Qed.

(** ** Paths Do Not Depend on the Local Context *)

Lemma mt_path_ctx : forall Γ Γ' p ch k A,
    member_type gc_deps gc_stack Γ (me_path p) ch k A -> member_type gc_deps gc_stack Γ' (me_path p) ch k A.
Proof.
  intros * H; inversion H; subst; [ eapply mt_path_def | eapply mt_path_mod | eapply mt_path_alias ]; eassumption.
Qed.

Lemma eval_path_any : forall p ρ ρ' h,
    eval_modexp gc_deps gc_stack (me_path p) ρ h -> eval_modexp gc_deps gc_stack (me_path p) ρ' h.
Proof. intros * H; inversion H; subst; [ apply eval_me_path | eapply eval_me_path_alias ]; eassumption. Qed.

(** A path is valid when its member types and δ-reducts are valid at [⋅],
    and, if it names a module, its value is. *)
Definition gpath_at (p : path) : Prop :=
  sem_mt ⋅ (me_path p) /\ sem_unf ⋅ (me_path p) /\
  (forall A, member_type gc_deps gc_stack ⋅ (me_path p) nil mk_mod A ->
     exists h, eval_modexp gc_deps gc_stack (me_path p) nil h /\ per_dmod h h).

Lemma sem_mt_path : gmod_ok -> forall Γ p, gpath_at p -> ⊨ Γ -> sem_mt Γ (me_path p).
Proof.
  intros (HGc & HGap & Hc) * [[S1 S2] _] HΓ.
  assert (Hcl : forall ch k A, member_type gc_deps gc_stack ⋅ (me_path p) ch k A -> exp_scoped 0 A)
    by (intros * Hm; exact (proj1 (member_type_scoped _ _) _ _ _ _ _ Hm Hc I I)).
  split.
  - intros * Hm Hch.
    pose proof (mt_path_ctx _ ⋅ _ _ _ _ Hm) as Hm0.
    destruct (S1 _ _ _ Hm0 Hch) as ((n & b & Hr) & Hv).
    split; [ exists n, b; exact (rep_lift_nil _ _ _ _ HΓ Hr (Hcl _ _ _ Hm0)) |].
    intros R ρ HR Hρ h Hh.
    assert (H0 : per_ctx_env (fun _ _ => True) ⋅ ⋅) by (apply per_ctx_env_nil; reflexivity).
    exact (Hv _ _ H0 I _ Hh).
  - intros * Hm0 Hm Hch.
    destruct (S2 _ _ _ _ _ (mt_path_ctx _ ⋅ _ _ _ _ Hm0) (mt_path_ctx _ ⋅ _ _ _ _ Hm) Hch) as (m & n & Hr0 & Hr & Hmn).
    exists m, n; split; [| split; [| exact Hmn ] ];
      eapply rep_lift_nil; try eassumption; eapply Hcl, mt_path_ctx; eassumption.
Qed.

Lemma sem_unf_path : forall Γ p, gpath_at p -> sem_unf Γ (me_path p).
Proof.
  intros * (_ & HU & _) ch A M Hm HM R ρ HR Hρ h Hh.
  assert (H0 : per_ctx_env (fun _ _ => True) ⋅ ⋅) by (apply per_ctx_env_nil; reflexivity).
  exact (HU _ _ _ (mt_path_ctx _ ⋅ _ _ _ _ Hm) HM _ _ H0 I _ Hh).
Qed.

Lemma rel_me_path : forall Γ p A, gpath_at p -> ⊨ Γ ->
    member_type gc_deps gc_stack Γ (me_path p) nil mk_mod A -> Γ ⊨ᵐ me_path p ≈ me_path p.
Proof.
  intros * (_ & _ & HV) HΓ Hm.
  destruct (HV _ (mt_path_ctx _ ⋅ _ _ _ _ Hm)) as (h & Hh & Hhh).
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  exists R, HR; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  apply (mk_rel_mod h h h h); cbn [modexp_sub]; try (eapply eval_path_any; exact Hh).
  split; [ exact Hhh | split; exact Hhh ].
Qed.

Lemma path_app_nil : forall p, path_app p nil = p.
Proof. intros [u m]; unfold path_app; cbn; rewrite app_nil_r; reflexivity. Qed.

Lemma member_type_path_module : forall Θ Ξ Γ p A,
    member_type Θ Ξ Γ (me_path p) nil mk_mod A -> exists r, gc_module Θ Ξ p = Some r.
Proof. intros * H; inversion H; subst; rewrite path_app_nil in *; eauto. Qed.

End Fixed_GCtx.
