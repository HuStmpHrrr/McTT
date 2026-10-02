(** * Inverting the Typing Rules

    Every term former is introduced by exactly one rule, so a typing derivation
    for a term whose head is known says exactly what that rule says — except that
    [wf_exp_subtyp] may have been applied any number of times afterwards, which
    replaces "the type is [A]" by "the type refines to [A]".  Each lemma below is
    that observation for one former, proved by induction on the derivation with
    only two cases: the introduction rule, where refinement is reflexivity, and
    [wf_exp_subtyp], where it is transitivity.

    Substitutions need no inversion lemmas:

    - [M[σ]] is not a term former, so there is nothing to invert;
    - [wf_sub] is a record, not an inductive family, so a derivation of
      [Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ] carries no information beyond its two fields;
      in particular [Θ ⍮ Ξ ⍮ Γ ⊢s Id : Δ] is itself a context refinement. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SubEq.
Import Syntax_Notations Wk_Notations.

Lemma wf_typ_inversion : forall {Θ Ξ Γ i A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@i : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@(S i) ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_typ_inversion : mctt.

Lemma wf_nat_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_nat_inversion : mctt.

Corollary wf_zero_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ zero : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_zero_inversion : mctt.

Corollary wf_succ_inversion : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ succ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ /\ Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ eq_refl);
    destruct_conjs; mautosolve.
Qed.

#[export]
Hint Resolve wf_succ_inversion : mctt.

Lemma wf_natrec_inversion : forall Θ Ξ Γ A M A' MZ MS,
    Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A'[Id,,zero] /\
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A' ⊢ MS : A'[Wk ⨟ Wk,,succ #1] /\
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ /\
    Θ ⍮ Ξ ⍮ Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mctt.

Lemma wf_True_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_True_inversion : mctt.

Corollary wf_true_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⋆ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_true_inversion : mctt.

Lemma wf_False_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_False_inversion : mctt.

Lemma wf_exfalso_inversion : forall Θ Ξ Γ A M A',
    Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A' : A ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A' : Type@i) /\
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ /\
    Θ ⍮ Ξ ⍮ Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_exfalso_inversion : mctt.

Lemma wf_pi_inversion : forall {Θ Ξ Γ A B C},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : C ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ Type@i ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups; eexists; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mctt.

(** The level the domain and the codomain are checked at can always be taken to
    be the level of the [Π]-type itself.  Moving the refinement [Type@j ⊆ Type@i]
    from [Γ] into [Γ ▹ A] is a weakening, and it is the only step that needs any
    work: both sides are unchanged by it ([Type@j[↑]ʷ] is [Type@j]), but only by
    computation, so the step is taken by hand. *)
Corollary wf_pi_inversion' : forall {Θ Ξ Γ A B i},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i.
Proof.
  intros * [j [? []]]%wf_pi_inversion.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (wf_subtyp Θ Ξ (Γ ▹ A) (exp_wk Type@j ↑) (exp_wk Type@i ↑)) as H'
      by (eapply wk_preserves_subtyp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ Type@j ⊆ Type@i) by exact H'.
  split; mauto 3.
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mctt.

Corollary wf_fn_inversion : forall {Θ Ξ Γ A M C},
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : C ->
    exists B, Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B /\ Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; split; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mctt.

Lemma wf_app_inversion : forall {Θ Ξ Γ M N C},
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : C ->
    exists A B, Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ B[Id,,N] ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    do 2 eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_app_inversion : mctt.

Lemma wf_vlookup_inversion : forall {Θ Ξ Γ x A},
    Θ ⍮ Ξ ⍮ Γ ⊢ #x : A ->
    exists A', Γ ∋ #x : A' /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ eq_refl));
    destruct_conjs; gen_core_presups; eexists; split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mctt.

(** We omit [wf_exp_subtyp] as it does not give a useful inversion. *)
