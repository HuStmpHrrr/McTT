(** * NbE Commutes with Weakening

    The semantic route to "the normal form of a weakened term is the
    weakened normal form" ([nbe_wk]):

    - [M] is a term of [Γ], so the fundamental theorem of the PER model,
      along the semantic weakening [Γ ▹ A ⊨w ↑ : Γ], relates the value of
      [M[↑]] at the initial environment of [Γ ▹ A] to the value of [M] at its
      tail, the initial environment of [Γ];
    - related values read back equally at every length ([per_top]), so the
      normal form of [M[↑]] in [Γ ▹ A] is the readback of [⟦M⟧ρΓ] at
      [|Γ| + 1];
    - that is the weakening of its readback at [|Γ|], the normal form of [M]
      in [Γ] ([Core.Semantic.Rename.read_shift]).

    Two consequences follow: the normal form of a weakened term is fresh at
    the new variable ([nbe_wk_fresh_sem], an alternative proof of
    [Core.Semantic.Avoid.nbe_wk_fresh] for well-typed terms), and an equation
    between two terms of [Γ] that holds in [Γ ▹ A] holds in [Γ]
    ([exp_eq_strengthen_sem], the case [Δ = nil] of
    [Algorithmic.Strengthening.exp_eq_strengthen]). *)
From Stdlib Require Import Arith Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Completeness Soundness.
From Mctt.Core.Completeness Require Import FundamentalTheorem SubstitutionCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Semantic Require Import Realizability Rename.
From Mctt.Core.Syntactic Require Import Fresh NfRename.
Import Domain_Notations Fixed_Notations Wk_Notations.

Section Fixed_GCtx.
Context {GC : GCtx}.

(** [nbe] of a type, at a large universe it lives in. *)
Lemma nbe_ty_to_nbe_type : forall Γ T i W, nbe_ty_f Γ T W -> nbe_f Γ T Typeω@i W.
Proof. intros * H; inversion_clear H; econstructor; [ eassumption | constructor | eassumption | constructor; eassumption ]. Qed.

(** ** NbE Commutes with Weakening *)
Theorem nbe_wk : forall Γ A M T W,
    ⊢ Γ ▹ A ->
    Γ ⊢ M : T ->
    nbe_f Γ M T W ->
    nbe_f (Γ ▹ A) M[↑]ʷ T[↑]ʷ (nf_wk ↑ W).
Proof.
  intros * HΓA HM Hn.
  assert (HA : ⊨ Γ ▹ A) by (apply completeness_fundamental_ctx; exact HΓA).
  assert (exists R1, EF (Γ ▹ A) ≈ (Γ ▹ A) ∈ per_ctx_env ↘ R1) as [R1 HR1]
      by mauto 3 using sem_ctx_per_ctx_env.
  apply completeness_fundamental_exp in HM as [R0 [HR0 [j HMg]]].
  (** The initial environment of [Γ ▹ A], related to itself. *)
  destruct (per_ctx_then_per_env_initial_env HR1) as (ρ1 & ρ1' & Hρ1 & Hρ1' & Hrel1).
  assert (ρ1' = ρ1) as -> by (eapply functional_initial_env; eassumption).
  (** [M] along the weakening: its values at [ρ1] and at the tail of [ρ1]. *)
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_shift HA)) as Hs.
  pose proof (@eval_sub_of_wk gc_deps gc_stack ↑ ρ1 _) as Hev.
  destruct (HMg _ _ HR1 _ _ Hs _ _ _ _ Hrel1 Hev Hev) as [er [Ht He]].
  destruct Ht as [aσ a ? ? Haσ Ha ? ? [Htc _]].
  destruct He as [mσ m ? ? Hmσ Hm ? ? [Hmc _]].
  rewrite !exp_sub_of_wk, !eval_wk_shift in *.
  (** The tail of [ρ1] is the initial environment of [Γ], where [M] has the
      normal form [W]. *)
  inversion Hρ1 as [| ? ρ ? ? Hρ | |]; subst.
  change (drop_env (ρ ↦ ?x)) with ρ in *.
  inversion_clear Hn as [? ? ? ? ? ? ? Hρ' Ha' Hm' HW].
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  (** One variable further out, the short value reads back as the weakening
      of [W] ([read_shift]), and the long value as the short one. *)
  pose proof (read_shift _ _ Γ ρ T M _ _ W Hρ ltac:(eassumption) ltac:(eassumption) HW) as HW1.
  destruct (per_elem_then_per_top Htc Hmc (S (length Γ))) as [W' [HW' HW'']].
  functional_read_rewrite_clear.
  econstructor; eassumption.
Qed.

Corollary nbe_ty_wk : forall Γ A T i W,
    ⊢ Γ ▹ A ->
    Γ ⊢ T : Typeω@i ->
    nbe_ty_f Γ T W ->
    nbe_ty_f (Γ ▹ A) T[↑]ʷ (nf_wk ↑ W).
Proof.
  intros * HΓA HT Hn.
  eapply nbe_type_to_nbe_ty, (nbe_wk _ _ _ _ _ HΓA HT), nbe_ty_to_nbe_type; eassumption.
Qed.

(** ** NbE Invents No Variables, Semantically *)
Corollary nbe_wk_fresh_sem : forall Γ A M T W,
    ⊢ Γ ▹ A ->
    Γ ⊢ M : T ->
    nbe_f (Γ ▹ A) M[↑]ʷ T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * HΓA HM Hn.
  destruct (soundness HM) as [W1 [Hn1 _]].
  pose proof (nbe_wk _ _ _ _ _ HΓA HM Hn1) as Hn2.
  functional_nbe_rewrite_clear.
  apply (proj1 nf_wk_fresh); intros x; cbn; lia.
Qed.

Corollary nbe_ty_wk_fresh_sem : forall Γ A T i W,
    ⊢ Γ ▹ A ->
    Γ ⊢ T : Typeω@i ->
    nbe_ty_f (Γ ▹ A) T[↑]ʷ W ->
    nf_fresh 0 W.
Proof.
  intros * HΓA HT Hn.
  destruct (soundness_ty HT) as [W1 [Hn1 _]].
  pose proof (nbe_ty_wk _ _ _ _ _ HΓA HT Hn1) as Hn2.
  functional_nbe_rewrite_clear.
  apply (proj1 nf_wk_fresh); intros x; cbn; lia.
Qed.

(** ** Strengthening an Equation

    Both ends are terms of [Γ]: their normal forms in [Γ ▹ A] are the
    weakenings of their normal forms in [Γ], the long equation makes the
    former equal, and the weakening is injective. *)
Theorem exp_eq_strengthen_sem : forall Γ A M N T,
    ⊢ Γ ▹ A ->
    Γ ⊢ M : T ->
    Γ ⊢ N : T ->
    Γ ▹ A ⊢ M[↑]ʷ ≈ N[↑]ʷ : T[↑]ʷ ->
    Γ ⊢ M ≈ N : T.
Proof.
  intros * HΓA HM HN HMN.
  destruct (soundness HM) as [WM [HnM HeqM]].
  destruct (soundness HN) as [WN [HnN HeqN]].
  destruct (completeness HMN) as [W [HnM' HnN']].
  pose proof (nbe_wk _ _ _ _ _ HΓA HM HnM).
  pose proof (nbe_wk _ _ _ _ _ HΓA HN HnN).
  functional_nbe_rewrite_clear.
  assert (WM = WN) as <-
      by (eapply (proj1 nf_wk_inj); [ apply wk_inj_shift | eassumption ]).
  etransitivity; [ exact HeqM | symmetry; exact HeqN ].
Qed.

End Fixed_GCtx.
