(** * The Set Rules of Inductive Types and Constructors

    A type former and a constructor are their global values, of their
    closed types; a closed type has one value at every environment
    ([set_interp_closed_term]), so it is read in any context as at the
    empty one ([set_denotes_closed]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import UniverseCases ValidUnit Sel.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
Import ListNotations.

Section Inductives.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** ** Closed Terms Read Anywhere *)

(** A closed term of the empty context has one value at every
    environment: both are read at the environment holding both. *)
Lemma set_interp_closed_term : forall M ρ1 ρ2 v1 v2, exp_scoped 0 M ->
    set_env_eq γ ρ1 ρ1 -> set_env_eq γ ρ2 ρ2 ->
    set_interp T γ nil ρ1 M v1 -> set_interp T γ nil ρ2 M v2 -> set_eq v1 v2.
Proof.
  intros * HM E1 E2 Hv1 Hv2. pose proof (wf_ctx_empty _ _ Hgw) as Hc.
  assert (Hwk : forall φ, gc_deps ⍮ gc_stack ⍮ nil ⊢ʷ φ : nil)
    by (intros φ; constructor; [exact Hc | exact Hc | intros ? ? Hl; inversion Hl | intros ? ? ? Hl; inversion Hl
                               | intros ? ? Hl; inversion Hl]).
  set (ρ3 := set_env_merge ρ1 ρ2).
  assert (Hm : forall ρ φ v, set_interp T γ nil ρ M v -> (forall x, ρ x = ρ3 (φ x)) -> set_interp T γ nil ρ3 M v).
  { intros ρ φ v H Hag. pose proof (set_interp_wk T γ _ _ _ _ H nil nil nil φ ρ3 eq_refl (Hwk φ) Hag) as H'.
    cbn [tele_wk List.app List.length wk_qn] in H'.
    rewrite (proj1 syn_scoped_wk_id M 0 _ HM ltac:(intros x Hx; lia)) in H'. exact H'. }
  assert (A1 : forall x, ρ1 x = ρ3 (x + x)) by (intros x; unfold ρ3; rewrite set_env_merge_even; reflexivity).
  assert (A2 : forall x, ρ2 x = ρ3 (S (x + x))) by (intros x; unfold ρ3; rewrite set_env_merge_odd; reflexivity).
  assert (E3 : set_env_eq γ ρ3 ρ3) by (intros x; unfold ρ3, set_env_merge; destruct (Nat.even x); [apply E1 | apply E2]).
  exact (set_interp_functional T γ Hfn Hmods _ _ _ _ (Hm _ (fun x => x + x) _ Hv1 A1) _ _ E3 (Hm _ (fun x => S (x + x)) _ Hv2 A2)).
Qed.

(** A closed term denoting in the empty context denotes in any context:
    read below the context, by weakening. *)
Lemma set_denotes_closed : forall Γ M F, exp_scoped 0 M -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    set_denotes T γ nil M F -> set_denotes T γ Γ M (fun ρ => F (set_env_drop (List.length Γ) ρ)).
Proof.
  intros * HM Hc HΓ HF. apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
  assert (Hρ0 : set_env_in T γ nil (set_env_drop (List.length Γ) ρ))
    by (rewrite <- (List.app_nil_r Γ) in Hρ; exact (set_env_rel_drop T γ _ _ _ _ Hρ)).
  assert (Hφ : gc_deps ⍮ gc_stack ⍮ Γ ⊢ʷ (fun x => List.length Γ + x) : nil)
    by (constructor; [exact Hc | exact (wf_ctx_empty _ _ Hgw) | intros ? ? Hl; inversion Hl | intros ? ? ? Hl; inversion Hl
                     | intros ? ? Hl; inversion Hl]).
  pose proof (set_interp_wk T γ _ _ _ _ (set_denotes_exists _ _ _ _ _ HF _ Hρ0) nil nil Γ _ ρ eq_refl Hφ
                ltac:(intros x; reflexivity)) as Hw.
  cbn [tele_wk List.app List.length wk_qn] in Hw.
  rewrite (proj1 syn_scoped_wk_id M 0 _ HM ltac:(intros x Hx; lia)) in Hw. exact Hw.
Qed.

(** Its value at every environment of the context is its value at the
    empty environment. *)
Lemma set_denotes_closed_value : forall Γ M F ρ, exp_scoped 0 M -> set_env_in T γ Γ ρ -> set_denotes T γ nil M F ->
    set_eq (F (set_env_drop (List.length Γ) ρ)) (F empty_set_env).
Proof.
  intros * HM Hρ HF.
  assert (Hρ0 : set_env_in T γ nil (set_env_drop (List.length Γ) ρ))
    by (rewrite <- (List.app_nil_r Γ) in Hρ; exact (set_env_rel_drop T γ _ _ _ _ Hρ)).
  assert (He : set_env_in T γ nil empty_set_env) by (intros x; constructor; apply set_eq_refl).
  exact (set_interp_closed_term _ _ _ _ _ HM Hρ0 He (set_denotes_exists _ _ _ _ _ HF _ Hρ0) (set_denotes_exists _ _ _ _ _ HF _ He)).
Qed.

(** A closed type's value at every environment holds a member of it at
    the empty environment. *)
Lemma set_exp_eq_closed_global : forall Γ A c F, exp_scoped 0 A -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    set_denotes T γ nil A F -> set_mem c (code_carrier (F empty_set_env)) -> forall M, (forall ρ, set_interp T γ Γ ρ M c) ->
    set_exp_eq T γ Γ A M M.
Proof.
  intros * HA Hc HΓ HF Hmem M HM.
  assert (HMd : set_denotes T γ Γ M (fun _ => c))
    by (apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ); intros ρ _; exact (HM ρ)).
  exists (fun ρ => F (set_env_drop (List.length Γ) ρ)), (fun _ => c), (fun _ => c).
  constructor; [exact (set_denotes_closed _ _ _ HA Hc HΓ HF) | exact HMd | exact HMd | intros; apply set_eq_refl |].
  intros ρ Hρ. eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact (set_denotes_closed_value _ _ _ _ HA Hρ HF) |].
  exact Hmem.
Qed.

(** ** The Rules *)

Lemma set_rule_ind : forall Γ p k D Mk, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    set_exp_eq T γ Γ (ind_ty D Mk) (a_ind p k) (a_ind p k).
Proof.
  intros * Hc HΓ HD Hk. pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  destruct (set_group_ok_former_types _ _ _ _ _ HG _ _ Hk) as (FA & HFA).
  apply (set_exp_eq_closed_global _ _ (global_former γ p k) FA); try assumption.
  - exact (decl_closed_ind_ty _ _ _ (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hgw) HD) Hk).
  - exact (set_group_ok_formers_typed _ _ _ _ _ HG _ _ _ Hk HFA).
  - intros ρ. constructor.
Qed.

Lemma set_rule_con : forall Γ p k c D Mk gs i, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gc_deps ⍮ gc_stack ⍮ nil ⊢ con_ty p D k Mk gs : a_typ i -> set_exp_eq T γ nil (a_typ i) (con_ty p D k Mk gs) (con_ty p D k Mk gs) ->
    set_exp_eq T γ Γ (con_ty p D k Mk gs) (a_con p k c) (a_con p k c).
Proof.
  intros * Hc HΓ HD Hk Hcon Hw (FS & FA & FA' & [_ HFA _ _ _]). pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  apply (set_exp_eq_closed_global _ _ (global_constructor γ p k c) FA); try assumption.
  - exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ Hw))).
  - exact (set_group_ok_constructors_typed _ _ _ _ _ HG _ _ _ _ _ Hk Hcon HFA).
  - intros ρ. constructor.
Qed.

End Inductives.
