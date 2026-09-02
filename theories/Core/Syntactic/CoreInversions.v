(** * Inverting the Typing Rules

    Every term former is introduced by exactly one rule, so a typing derivation
    for a term whose head is known says exactly what that rule says — except that
    [wf_exp_subtyp] may have been applied any number of times afterwards, which
    replaces "the type is [A]" by "the type refines to [A]".  Each lemma below is
    that observation for one former, proved by induction on the derivation with
    only two cases: the introduction rule, where refinement is reflexivity, and
    [wf_exp_subtyp], where it is transitivity.

    Making substitution an operation removes half of this file.  The original
    development also inverted the substitution judgments — [M[σ] : A], [Id : Δ],
    [Wk : Δ], [σ ⨟ τ : Δ], [σ ,, M : Δ] — because each of those was an inductive
    rule that could be the last step of a derivation.  None of them is a rule any
    more:

    - [M[σ]] is not a term former, so there is nothing to invert; the
      corresponding fact is [sub_preserves_exp] read backwards, which
      is not needed anywhere;
    - [wf_sub] is a record, not an inductive family, so a derivation of
      [Γ ⊢s σ : Δ] carries no information beyond its two fields;
    - in particular [Γ ⊢s Id : Δ] *is* the context refinement that
      [wf_sub_id_inversion] used to extract. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SubEq.
Import Syntax_Notations Wk_Notations.

Lemma wf_typ_inversion : forall {Γ i A},
    Γ ⊢ Type@i : A ->
    Γ ⊢ Type@(S i) ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_typ_inversion : mctt.

Lemma wf_nat_inversion : forall Γ A,
    Γ ⊢ ℕ : A ->
    Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_nat_inversion : mctt.

Corollary wf_zero_inversion : forall Γ A,
    Γ ⊢ zero : A ->
    Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_zero_inversion : mctt.

Corollary wf_succ_inversion : forall Γ A M,
    Γ ⊢ succ M : A ->
    Γ ⊢ M : ℕ /\ Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ eq_refl);
    destruct_conjs; mautosolve.
Qed.

#[export]
Hint Resolve wf_succ_inversion : mctt.

Lemma wf_natrec_inversion : forall Γ A M A' MZ MS,
    Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A ->
    Γ ⊢ MZ : A'[Id,,zero] /\
    Γ ▹ ℕ ▹ A' ⊢ MS : A'[Wk ⨟ Wk,,succ #1] /\
    Γ ⊢ M : ℕ /\
    Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mctt.

Lemma wf_pi_inversion : forall {Γ A B C},
    Γ ⊢ Π A B : C ->
    exists i, Γ ⊢ A : Type@i /\ Γ ▹ A ⊢ B : Type@i /\ Γ ⊢ Type@i ⊆ C.
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
    work: both sides are unchanged by it — [Type@j⟨↑⟩] *is* [Type@j] — but only by
    computation, so the step is taken by hand. *)
Corollary wf_pi_inversion' : forall {Γ A B i},
    Γ ⊢ Π A B : Type@i ->
    Γ ⊢ A : Type@i /\ Γ ▹ A ⊢ B : Type@i.
Proof.
  intros * [j [? []]]%wf_pi_inversion.
  assert (⊢ Γ ▹ A) by mauto 3.
  assert (Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (wf_subtyp (Γ ▹ A) (exp_wk Type@j ↑) (exp_wk Type@i ↑)) as H'
      by (eapply wk_preserves_subtyp; eassumption).
  assert (Γ ▹ A ⊢ Type@j ⊆ Type@i) by exact H'.
  split; mauto 3.
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mctt.

Corollary wf_fn_inversion : forall {Γ A M C},
    Γ ⊢ λ A M : C ->
    exists B, Γ ▹ A ⊢ M : B /\ Γ ⊢ Π A B ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; split; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mctt.

Lemma wf_app_inversion : forall {Γ M N C},
    Γ ⊢ M $ N : C ->
    exists A B, Γ ⊢ M : Π A B /\ Γ ⊢ N : A /\ Γ ⊢ B[Id,,N] ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    do 2 eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_app_inversion : mctt.

Lemma wf_vlookup_inversion : forall {Γ x A},
    Γ ⊢ #x : A ->
    exists A', Γ ∋ #x : A' /\ Γ ⊢ A' ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ eq_refl));
    destruct_conjs; gen_core_presups; eexists; split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mctt.

(** We omit [wf_exp_subtyp] as it does not give a useful inversion. *)
