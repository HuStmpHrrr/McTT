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
From Mctt.Core.Syntactic.System Require Import MemberLemmas MemberWf.
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
  Variables (Θm : gdeps) (Ξm : gstack).

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

Lemma mt_unit_ctx : forall Γ Γ' fp ch R,
    member_type Θm Ξm Γ (me_unit fp) ch R -> member_type Θm Ξm Γ' (me_unit fp) ch R.
Proof.
  intros * H; inversion H; subst; [ eapply mt_unit_def | eapply mt_unit_mod | eapply mt_unit_alias ]; eassumption.
Qed.

Lemma mt_chain_ctx : forall H Γ Γ' p ch R, mod_qname H = Some p ->
    member_type Θm Ξm Γ H ch R -> member_type Θm Ξm Γ' H ch R.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hp Hm; cbn in Hp; try discriminate.
  - eapply mt_unit_ctx; exact Hm.
  - destruct (mod_qname H) eqn:E; [| discriminate ].
    inversion Hm; subst; eapply mt_mem; [ assumption | eapply IH; eauto ].
Qed.

Lemma mt_path_ctx : forall Γ Γ' p ch R,
    member_type Θm Ξm Γ (qname_mod p) ch R -> member_type Θm Ξm Γ' (qname_mod p) ch R.
Proof. intros *; apply mt_chain_ctx with (p := p), qname_mod_qname. Qed.

Lemma unfold_path_ctx : forall Γ Γ' p ch,
    member_unfold_ch Θm Ξm Γ (qname_mod p) ch = member_unfold_ch Θm Ξm Γ' (qname_mod p) ch.
Proof. intros; unfold qname_mod; rewrite !me_mems_unfold; reflexivity. Qed.

Lemma eval_chain_any : forall H p ρ ρ' h, mod_qname H = Some p ->
    ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h -> ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hp He; cbn in Hp; try discriminate.
  - inversion He; subst; constructor.
  - destruct (mod_qname H) eqn:E; [| discriminate ].
    inversion He; subst; econstructor; [ eapply IH; eauto | eassumption ].
Qed.

Lemma eval_path_any : forall p ρ ρ' h,
    ⟦ qname_mod p ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h -> ⟦ qname_mod p ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h.
Proof. intros *; apply eval_chain_any with (p := p), qname_mod_qname. Qed.

(** A path is valid when its member types and δ-reducts are valid at [⋅],
    and, if it names a module, its value is. *)
Definition gpath_at (p : qname) : Prop :=
  sem_mt Θm Ξm ⋅ (qname_mod p) /\ sem_unf Θm Ξm ⋅ (qname_mod p) /\
  (forall T, member_type Θm Ξm ⋅ (qname_mod p) nil (mr_mod T) ->
     exists h, eval_modexp gc_deps gc_stack (qname_mod p) nil h /\ per_dmod h h).

Lemma sem_mt_path : gmod_ok Θm Ξm -> forall Γ p, gpath_at p -> ⊨ Γ -> sem_mt Θm Ξm Γ (qname_mod p).
Proof.
  intros (HGc & HGap & Hc) * [[S1 S2] _] HΓ.
  assert (Hcl : forall ch R, member_type Θm Ξm ⋅ (qname_mod p) ch R -> exp_scoped 0 (mres_ty R))
    by (intros * Hm; apply mres_ty_scoped;
        exact (proj1 (member_type_scoped _ _) _ _ _ _ Hm Hc I (mod_qname_scoped _ _ _ (qname_mod_qname p)))).
  split.
  - intros * Hm Hch.
    pose proof (mt_path_ctx _ ⋅ _ _ _ Hm) as Hm0.
    destruct (S1 _ _ Hm0 Hch) as ((n & b & Hr) & Hv).
    split; [ exists n, b; exact (rep_lift_nil _ _ _ _ HΓ Hr (Hcl _ _ Hm0)) |].
    intros P ρ HR Hρ h Hh.
    assert (H0 : per_ctx_env (fun _ _ => True) ⋅ ⋅) by (apply per_ctx_env_nil; reflexivity).
    exact (Hv _ _ H0 I _ Hh).
  - intros * Hm0 Hk0 Hm Hch.
    destruct (S2 _ _ _ _ (mt_path_ctx _ ⋅ _ _ _ Hm0) Hk0 (mt_path_ctx _ ⋅ _ _ _ Hm) Hch) as (m & n & Hr0 & Hr & Hmn).
    exists m, n; split; [| split; [| exact Hmn ] ];
      eapply rep_lift_nil; try eassumption; eapply Hcl, mt_path_ctx; eassumption.
Qed.

Lemma sem_unf_path : forall Γ p, gpath_at p -> sem_unf Θm Ξm Γ (qname_mod p).
Proof.
  intros * (_ & HU & _) ch A M Hm HM R ρ HR Hρ h Hh.
  assert (H0 : per_ctx_env (fun _ _ => True) ⋅ ⋅) by (apply per_ctx_env_nil; reflexivity).
  rewrite (unfold_path_ctx _ ⋅) in HM.
  exact (HU _ _ _ (mt_path_ctx _ ⋅ _ _ _ Hm) HM _ _ H0 I _ Hh).
Qed.

Lemma rel_me_path : forall Γ p T, gpath_at p -> ⊨ Γ ->
    member_type Θm Ξm Γ (qname_mod p) nil (mr_mod T) -> Γ ⊨ᵐ qname_mod p ≈ qname_mod p.
Proof.
  intros * (_ & _ & HV) HΓ Hm.
  destruct (HV _ (mt_path_ctx _ ⋅ _ _ _ Hm)) as (h & Hh & Hhh).
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  exists R, HR; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  apply (mk_rel_mod h h h h); try rewrite (mod_qname_sub _ _ _ (qname_mod_qname p)); try (eapply eval_path_any; exact Hh).
  split; [ exact Hhh | split; exact Hhh ].
Qed.

Lemma member_type_path_module : forall Θ Ξ Γ p T,
    member_type Θ Ξ Γ (qname_mod p) nil (mr_mod T) -> exists r, gc_module Θ Ξ p = Some r.
Proof.
  intros * H; apply me_mems_member_type_inv in H; rewrite app_nil_r in H.
  inversion H; subst; destruct p; eauto.
Qed.

End Fixed_GCtx.

#[global] Arguments sem_mt_path {GC Θm Ξm}.
#[global] Arguments sem_unf_path {GC Θm Ξm}.
#[global] Arguments rel_me_path {GC Θm Ξm}.
#[global] Arguments mt_path_ctx {Θm Ξm}.
