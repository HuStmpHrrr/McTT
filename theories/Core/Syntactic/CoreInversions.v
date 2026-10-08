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
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@(S i) ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_typ_inversion : mctt.

Lemma wf_univ_inversion : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl M⟩ ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

(** The level of a universe that is a type is a level: the only rule that
    gives a universe a type asks for it. *)
Lemma wf_univ_lvl_inversion : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_univ_inversion wf_univ_lvl_inversion : mctt.

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

(** The level forms.  A level is of type [Level] up to subtyping, and so is
    every argument of [succl] and [maxl]. *)
Lemma wf_level_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ Level : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_level_inversion : mctt.

Corollary wf_llit_inversion : forall Θ Ξ Γ A o,
    Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Level ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_llit_inversion : mctt.

Corollary wf_succl_inversion : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ succl M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ eq_refl);
    destruct_conjs; mautosolve.
Qed.

#[export]
Hint Resolve wf_succl_inversion : mctt.

Corollary wf_maxl_inversion : forall Θ Ξ Γ A M N,
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : Level /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; mautosolve.
Qed.

#[export]
Hint Resolve wf_maxl_inversion : mctt.

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
    (exists i, Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A' : Typeω@i) /\
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

(** A [Π] is in a large universe, or in a small one at a level. *)
Lemma wf_pi_inversion : forall {Θ Ξ Γ A B C},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : C ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ⊆ C) \/
    (exists L, Θ ⍮ Ξ ⍮ Γ ⊢ L : Level /\ Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ /\
               Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨L⟩ ⊆ C).
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    try destruct IHwf_exp1 as [(j & ? & ? & ?) | (L' & ? & ? & ? & ?)];
    gen_core_presups.
  - left; eexists; mautosolve 4.
  - right; exists L; repeat split; try assumption; mautosolve 4.
  - left; exists j; repeat split; try assumption; mautosolve 4.
  - right; exists L'; repeat split; try assumption; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mctt.

(** The level the domain and the codomain are checked at can always be taken to
    be the level of the [Π]-type itself.  Moving the refinement [Typeω@j ⊆ Typeω@i]
    from [Γ] into [Γ ▹ A] is a weakening, and it is the only step that needs any
    work: both sides are unchanged by it ([Typeω@j[↑]ʷ] is [Typeω@j]), but only by
    computation, so the step is taken by hand. *)
Corollary wf_pi_inversion' : forall {Θ Ξ Γ A B i},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i.
Proof.
  intros * [[j [? []]] | [L [? [? []]]]]%wf_pi_inversion.
  2:{ assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
      assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
      assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ L[↑]ʷ : Level) by (eapply (wk_preserves_exp _ _ _ _ Level); eassumption).
      split; eapply wf_exp_suniv_large; eassumption. }
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ exp_wk Typeω@j ↑ ⊆ exp_wk Typeω@i ↑) as H'
      by (eapply wk_preserves_subtyp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ Typeω@j ⊆ Typeω@i) by exact H'.
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

Lemma wf_let_inversion : forall {Θ Ξ Γ oA M B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B : T ->
    exists A i C, let_ann oA A /\ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    do 3 eexists; repeat split; first [ solve [ eassumption ] | mautosolve 4 ].
Qed.

(** For an annotated definition, the type is the annotation. *)
Corollary wf_let_ann_inversion : forall {Θ Ξ Γ A M B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : T ->
    exists i C, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H; destruct (wf_let_inversion H) as (A' & i & C & [[=] | [= <-]] & ?); eauto.
Qed.

#[export]
Hint Resolve wf_let_inversion : mctt.

Lemma wf_let_mod_inversion : forall {Θ Ξ Γ U B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : T ->
    exists C, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U /\
         Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id ,,ₘ me_lit U] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_let_mod_inversion : mctt.

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
