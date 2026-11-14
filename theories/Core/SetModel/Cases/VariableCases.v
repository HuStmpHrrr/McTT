(** * The Set Rules of Variables

    A variable denotes its entry's term in the environment; at an
    environment of a valid context it is of its type, the type of its
    context entry weakened past the entries after it. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Cases Require Export FunctionCases.
From Mctt.Core.SetModel.Interpretation Require Import Weakening.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

Section Variables.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

Lemma set_denotes_var : forall Γ x, set_denotes T γ Γ (a_var x) (fun ρ => set_entry_value (ρ x)).
Proof.
  intros. constructor; [intros; constructor |]. intros ρ ρ' v Hr Hv. inversion Hv; subst.
  apply (set_entry_value_resp (γ := γ)). apply set_entry_eq_sym. exact (set_env_rel_eq _ _ _ _ _ Hr x).
Qed.

(** A type weakened past one more entry denotes, read below it. *)
Lemma set_denotes_shift : forall Γ e A FA, set_ctx T γ (e :: Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ e :: Γ -> set_denotes T γ Γ A FA ->
    set_denotes T γ (e :: Γ) (exp_wk A wk_shift) (fun ρ => FA (set_env_tail ρ)).
Proof.
  intros * HΓ Hc HA. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ [Ht _].
  exact (set_interp_wk T γ _ _ _ _ (set_denotes_exists _ _ _ _ _ HA _ Ht) nil Γ _ wk_shift _ eq_refl (wf_wk_shift _ _ _ _ Hc)
           (fun y => eq_refl)).
Qed.

(** A variable's type denotes, and its value is of it. *)
Lemma set_lookup_denotes : forall Γ x A, Γ ∋ #x : A -> set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    exists FA, set_denotes T γ Γ A FA /\ forall ρ, set_env_in T γ Γ ρ -> set_mem (set_entry_value (ρ x)) (code_carrier (FA ρ)).
Proof.
  intros * H. induction H as [Γ κ A | Γ A M | Γ A M U | Γ n A e H IH]; intros HΓ Hc.
  - destruct HΓ as [HΓ' [FA HA]]. exists (fun ρ => FA (set_env_tail ρ)). split; [apply set_denotes_shift; [split; [exact HΓ' | exists FA; exact HA] | exact Hc | exact HA] |].
    intros ρ [Ht (y & y' & a & [E1 E2 Ha Hy _])]. rewrite E1. cbn [set_entry_value].
    eapply set_mem_eq_r; [| exact Hy]. apply code_carrier_resp. exact (set_denotes_unique _ _ _ _ _ HA _ _ _ Ht Ha).
  - destruct HΓ as [HΓ' HAM]. pose proof HAM as (FA & FM & FM' & [HA HM _ _ HMm]).
    exists (fun ρ => FA (set_env_tail ρ)). split; [apply set_denotes_shift; [split; assumption | exact Hc | exact HA] |].
    intros ρ [Ht (r & v & v' & w & [E1 E2 Hw Ev _])]. rewrite E1. cbn [set_entry_value].
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact Ev | exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Ht Hw)] |].
    apply HMm. exact Ht.
  - destruct HΓ as [HΓ' HAM]. pose proof HAM as [(FA & FM & FM' & [HA HM _ _ HMm]) _].
    exists (fun ρ => FA (set_env_tail ρ)). split; [apply set_denotes_shift; [split; assumption | exact Hc | exact HA] |].
    intros ρ [Ht (v & v' & w & m & m' & k & [E1 E2 Hw _ Ev _ _ _])]. rewrite E1. cbn [set_entry_value].
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact Ev | exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Ht Hw)] |].
    apply HMm. exact Ht.
  - destruct (IH (proj1 HΓ) (ctx_decomp_tail Hc)) as [FA [HA Hm]].
    exists (fun ρ => FA (set_env_tail ρ)). split; [apply set_denotes_shift; assumption |].
    intros ρ [Ht _]. exact (Hm _ Ht).
Qed.

(** [Γ ∋ #x : A] gives [#x : A]. *)
Lemma set_rule_var : forall Γ x A, Γ ∋ #x : A -> set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_rel_exp_eq T γ Γ A (a_var x) (a_var x).
Proof.
  intros * H HΓ Hc. destruct (set_lookup_denotes _ _ _ H HΓ Hc) as [FA [HA Hm]].
  exists FA, (fun ρ => set_entry_value (ρ x)), (fun ρ => set_entry_value (ρ x)).
  constructor; [exact HA | apply set_denotes_var .. | intros; apply set_eq_refl | exact Hm].
Qed.

(** A definition's body denotes, and its variable's value is the body's. *)
Lemma set_lookup_def_denotes : forall Γ x A M, Γ ∋ #x ≔ M : A -> set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    exists FM, set_denotes T γ Γ M FM /\ forall ρ, set_env_in T γ Γ ρ -> set_eq (set_entry_value (ρ x)) (FM ρ).
Proof.
  intros * H. induction H as [Γ A M | Γ A M U | Γ n A M e H IH]; intros HΓ Hc.
  - destruct HΓ as [HΓ' HAM]. pose proof HAM as (FA & FM & FM' & [HA HM _ _ HMm]).
    exists (fun ρ => FM (set_env_tail ρ)). split; [apply set_denotes_shift; [split; assumption | exact Hc | exact HM] |].
    intros ρ [Ht (r & v & v' & w & [E1 E2 Hw Ev _])]. rewrite E1. cbn [set_entry_value].
    eapply set_eq_trans; [exact Ev | exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Ht Hw)].
  - destruct HΓ as [HΓ' HAM]. pose proof HAM as [(FA & FM & FM' & [HA HM _ _ HMm]) _].
    exists (fun ρ => FM (set_env_tail ρ)). split; [apply set_denotes_shift; [split; assumption | exact Hc | exact HM] |].
    intros ρ [Ht (v & v' & w & m & m' & k & [E1 E2 Hw _ Ev _ _ _])]. rewrite E1. cbn [set_entry_value].
    eapply set_eq_trans; [exact Ev | exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Ht Hw)].
  - destruct (IH (proj1 HΓ) (ctx_decomp_tail Hc)) as [FM [HM Hm]].
    exists (fun ρ => FM (set_env_tail ρ)). split; [apply set_denotes_shift; assumption |].
    intros ρ [Ht _]. exact (Hm _ Ht).
Qed.

(** δ: a defined variable is its definition's body. *)
Lemma set_rule_var_delta : forall Γ x A M, Γ ∋ #x : A -> Γ ∋ #x ≔ M : A -> set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    set_rel_exp_eq T γ Γ A (a_var x) M.
Proof.
  intros * H Hd HΓ Hc. destruct (set_lookup_denotes _ _ _ H HΓ Hc) as [FA [HA Hm]].
  destruct (set_lookup_def_denotes _ _ _ _ Hd HΓ Hc) as [FM [HM EM]].
  exists FA, (fun ρ => set_entry_value (ρ x)), FM.
  constructor; [exact HA | apply set_denotes_var | exact HM | exact EM | exact Hm].
Qed.

End Variables.
