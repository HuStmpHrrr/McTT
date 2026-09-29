(** * Module Substitution and Context Lookup

    What [ModSubst] cannot state without the judgments: how module
    substitution acts on a variable lookup.  A context is a telescope, so each
    binding is substituted under the bindings below it; a lookup weakens the
    binding past those above it, and the two commute. *)

From Stdlib Require Import Lia List Morphisms PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Telescopes *)

(** Generalizing over [Δ ++ Δ'] is generalizing over the inner [Δ] first. *)
Lemma ctx_pi_app : forall Δ Δ' A, ctx_pi (Δ ++ Δ') A = ctx_pi Δ' (ctx_pi Δ A).
Proof.
  induction Δ; intros; cbn; [ reflexivity |]. apply IHΔ.
Qed.

Lemma ctx_fn_app : forall Δ Δ' M, ctx_fn (Δ ++ Δ') M = ctx_fn Δ' (ctx_fn Δ M).
Proof.
  induction Δ; intros; cbn; [ reflexivity |]. apply IHΔ.
Qed.

(** ** Lookup *)

Lemma ctx_lookup_msub : forall μ Γ x A,
    Γ ∋ #x : A -> Γ[μ]ᵐ ∋ #x : A[ms_qn (length Γ) μ]ᵐ.
Proof.
  intros μ Γ x A; induction 1; cbn;
    rewrite <- exp_msub_shift_wk; constructor; assumption.
Qed.

Lemma ctx_lookup_msub_inv : forall μ Γ x A,
    Γ[μ]ᵐ ∋ #x : A -> exists A0, Γ ∋ #x : A0 /\ A = A0[ms_qn (length Γ) μ]ᵐ.
Proof.
  intros μ Γ; induction Γ as [| B Γ IH]; intros * H; cbn in H; inversion H; subst.
  - exists B[↑]ʷ; split; [ constructor | rewrite exp_msub_shift_wk; reflexivity ].
  - destruct (IH _ _ ltac:(eassumption)) as [A1 [HA ->]].
    exists A1[↑]ʷ; split; [ constructor; eassumption | rewrite exp_msub_shift_wk; reflexivity ].
Qed.

#[export]
Hint Resolve ctx_lookup_msub : mctt.

(** ** Parameters as a Function *)

Lemma ctx_get_sound : forall Γ k T, ctx_get Γ k = Some T -> Γ ∋ #k : T.
Proof.
  induction Γ as [| A Γ IH]; intros [| k] T H; cbn in H; try discriminate.
  - injection H as <-; constructor.
  - destruct (ctx_get Γ k) eqn:E; cbn in H; [ injection H as <- | discriminate ].
    constructor; auto.
Qed.

Lemma ctx_get_complete : forall Γ k T, Γ ∋ #k : T -> ctx_get Γ k = Some T.
Proof. induction 1; cbn; [| rewrite IHctx_lookup ]; reflexivity. Qed.

Lemma gs_param_sound : forall Ξ n k T,
    gs_param Ξ {| lp_mod := n; lp_param := k |} = Some T ->
    exists U T0, List.nth_error Ξ n = Some U /\ gu_params U ∋ #k : T0 /\
      T = T0[↑ₘ (S n)]ᵐ[sb_params n].
Proof.
  unfold gs_param; cbn; intros * H.
  destruct (List.nth_error Ξ n) as [U |] eqn:Hn; [| discriminate ].
  destruct (ctx_get (gu_params U) k) as [T0 |] eqn:Hk; cbn in H; [| discriminate ].
  injection H as <-; exists U, T0; auto using ctx_get_sound.
Qed.

Lemma gs_param_complete : forall Ξ n U k T,
    List.nth_error Ξ n = Some U -> gu_params U ∋ #k : T ->
    gs_param Ξ {| lp_mod := n; lp_param := k |} = Some T[↑ₘ (S n)]ᵐ[sb_params n].
Proof.
  unfold gs_param; cbn; intros * Hn Hk; rewrite Hn, (ctx_get_complete _ _ _ Hk); reflexivity.
Qed.
