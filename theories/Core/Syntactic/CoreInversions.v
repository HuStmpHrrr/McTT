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
      [Θ ⍮ Γ ⊢s σ : Δ] carries no information beyond its two fields;
      in particular [Θ ⍮ Γ ⊢s Id : Δ] is itself a context refinement. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SubEq.
Import Syntax_Notations Wk_Notations.

Lemma wf_typ_inversion : forall {Θ Γ i A},
    Θ ⍮ Γ ⊢ Type@i : A ->
    Θ ⍮ Γ ⊢ Type@(S i) ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_typ_inversion : mctt.

Lemma wf_nat_inversion : forall Θ Γ A,
    Θ ⍮ Γ ⊢ ℕ : A ->
    Θ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_nat_inversion : mctt.

Corollary wf_zero_inversion : forall Θ Γ A,
    Θ ⍮ Γ ⊢ zero : A ->
    Θ ⍮ Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_zero_inversion : mctt.

Corollary wf_succ_inversion : forall Θ Γ A M,
    Θ ⍮ Γ ⊢ succ M : A ->
    Θ ⍮ Γ ⊢ M : ℕ /\ Θ ⍮ Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ eq_refl);
    destruct_conjs; mautosolve.
Qed.

#[export]
Hint Resolve wf_succ_inversion : mctt.

Lemma wf_natrec_inversion : forall Θ Γ A M A' MZ MS,
    Θ ⍮ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A ->
    Θ ⍮ Γ ⊢ MZ : A'[Id,,zero] /\
    Θ ⍮ Γ ▹ ℕ ▹ A' ⊢ MS : A'[Wk ⨟ Wk,,succ #1] /\
    Θ ⍮ Γ ⊢ M : ℕ /\
    Θ ⍮ Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mctt.

Lemma wf_True_inversion : forall Θ Γ A,
    Θ ⍮ Γ ⊢ ⊤ : A ->
    Θ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_True_inversion : mctt.

Corollary wf_true_inversion : forall Θ Γ A,
    Θ ⍮ Γ ⊢ ⋆ : A ->
    Θ ⍮ Γ ⊢ ⊤ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_true_inversion : mctt.

Lemma wf_False_inversion : forall Θ Γ A,
    Θ ⍮ Γ ⊢ ⊥ : A ->
    Θ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_False_inversion : mctt.

Lemma wf_exfalso_inversion : forall Θ Γ A M A',
    Θ ⍮ Γ ⊢ efq M return A' : A ->
    (exists i, Θ ⍮ Γ ▹ ⊥ ⊢ A' : Type@i) /\
    Θ ⍮ Γ ⊢ M : ⊥ /\
    Θ ⍮ Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_exfalso_inversion : mctt.

Lemma wf_pi_inversion : forall {Θ Γ A B C},
    Θ ⍮ Γ ⊢ Π A B : C ->
    exists i, Θ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Γ ▹ A ⊢ B : Type@i /\ Θ ⍮ Γ ⊢ Type@i ⊆ C.
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
Corollary wf_pi_inversion' : forall {Θ Γ A B i},
    Θ ⍮ Γ ⊢ Π A B : Type@i ->
    Θ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Γ ▹ A ⊢ B : Type@i.
Proof.
  intros * [j [? []]]%wf_pi_inversion.
  assert (⊢ Θ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (Θ ⍮ Γ ▹ A ⊢ exp_wk Type@j ↑ ⊆ exp_wk Type@i ↑) as H'
      by (eapply wk_preserves_subtyp; eassumption).
  assert (Θ ⍮ Γ ▹ A ⊢ Type@j ⊆ Type@i) by exact H'.
  split; mauto 3.
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mctt.

Corollary wf_fn_inversion : forall {Θ Γ A M C},
    Θ ⍮ Γ ⊢ λ A M : C ->
    exists B, Θ ⍮ Γ ▹ A ⊢ M : B /\ Θ ⍮ Γ ⊢ Π A B ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; split; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mctt.

Lemma wf_app_inversion : forall {Θ Γ M N C},
    Θ ⍮ Γ ⊢ M $ N : C ->
    exists A B, Θ ⍮ Γ ⊢ M : Π A B /\ Θ ⍮ Γ ⊢ N : A /\ Θ ⍮ Γ ⊢ B[Id,,N] ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    do 2 eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_app_inversion : mctt.

Lemma wf_let_inversion : forall {Θ Γ oA M B T},
    Θ ⍮ Γ ⊢ a_let (b_def oA M) B : T ->
    exists A i C, let_ann oA A /\ Θ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    do 3 eexists; repeat split; first [ solve [ eassumption ] | mautosolve 4 ].
Qed.

(** For an annotated definition, the type is the annotation. *)
Corollary wf_let_ann_inversion : forall {Θ Γ A M B T},
    Θ ⍮ Γ ⊢ ℓ A ≔ M in B : T ->
    exists i C, Θ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H; destruct (wf_let_inversion H) as (A' & i & C & [[=] | [= <-]] & ?); eauto.
Qed.

#[export]
Hint Resolve wf_let_inversion : mctt.

Lemma wf_let_mod_inversion : forall {Θ Γ U B T},
    Θ ⍮ Γ ⊢ ℓₘ U in B : T ->
    exists C, Θ ⍮ Γ ⊢ᵘ U ≈ U /\
         Θ ⍮ Γ ▹ₘ U ⊢ B : C /\ Θ ⍮ Γ ⊢ C[Id ,,ₘ me_lit U] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_let_mod_inversion : mctt.

Lemma wf_vlookup_inversion : forall {Θ Γ x A},
    Θ ⍮ Γ ⊢ #x : A ->
    exists A', Γ ∋ #x : A' /\ Θ ⍮ Γ ⊢ A' ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ eq_refl));
    destruct_conjs; gen_core_presups; eexists; split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mctt.

(** We omit [wf_exp_subtyp] as it does not give a useful inversion. *)
