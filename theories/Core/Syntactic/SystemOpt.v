(** * The Rules with the Redundant Premises Removed

    Every rule carries the premises a presupposition-free formulation
    needs: the [Π]-rules check the domain and the codomain, the
    [ℕ]-eliminator checks the motive, the congruence rules check the left-hand
    side.  Once presupposition is available all of those are consequences of the
    remaining premises, and this file restates each rule without them.  The
    primed version is registered as a hint and the rule itself is unregistered,
    so [mauto] searches the small statement and never rediscovers a premise it
    could have presupposed.

    [gen_presups] does all the work; [impl_opt_constructor] is the whole proof of
    most of them.  Where more is needed it is always the same two things: a level
    at which the domain and the codomain of a [Π]-type are both types
    ([lift_exp_pi_common], or [wf_pi_inversion'] when the [Π]-type is already
    known to be one), and cumulativity.

    The rewriting morphisms come first.  Together with [wf_exp_eq_morphism_iff1]
    and [wf_exp_eq_morphism_iff2] from [Definitions] they let [rewrite] replace a
    term by an equal one anywhere in a judgment, including in the type.

    Equations such as [(Π A B)[σ] = Π A[σ] B[q σ]] are not rules but
    equalities of [exp], proved in [Core.Syntactic.Substitution] and used by
    [rewrite] or [simpl_sub], so they need no optimized form.  Neither does
    context equality, which is [Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ] in both directions. *)

From Stdlib Require Import Lia Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CoreInversions.
Import Syntax_Notations Wk_Notations.

(** ** Rewriting the Type of a Judgment *)

Add Parametric Morphism i Θ Ξ Γ : (wf_exp Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ Type@i ==> eq ==> iff as wf_exp_morphism_iff3.
Proof.
  split; intros; gen_presups; mautosolve.
Qed.

Add Parametric Morphism i Θ Ξ Γ : (wf_exp_eq Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ Type@i ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof.
  split; intros; gen_presups; mautosolve.
Qed.

Add Parametric Morphism Θ Ξ Γ i : (wf_subtyp Θ Ξ Γ)
    with signature (wf_exp_eq Θ Ξ Γ Type@i) ==> eq ==> iff as wf_subtyp_morphism_iff1.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 4.
Qed.

Add Parametric Morphism Θ Ξ Γ j : (wf_subtyp Θ Ξ Γ)
    with signature eq ==> (wf_exp_eq Θ Ξ Γ Type@j) ==> iff as wf_subtyp_morphism_iff2.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 3.
Qed.

(** ** The Optimized Rules *)

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.

Corollary wf_subtyp_refl' : forall Θ Ξ Γ M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_refl' : mctt.
#[export]
Remove Hints wf_subtyp_refl : mctt.

Corollary wf_conv' : forall Θ Ξ Γ M A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv' : mctt.
#[export]
Remove Hints wf_conv : mctt.

Corollary wf_exp_eq_conv' : forall Θ Ξ Γ M M' A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv' : mctt.
#[export]
Remove Hints wf_exp_eq_conv : mctt.

(** [ℕ] is a type at every level, not only at [0]. *)
Corollary wf_nat' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : Type@i.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_nat' : mctt.
#[export]
Remove Hints wf_nat : mctt.

Corollary wf_exp_eq_nat_cong' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ≈ ℕ : Type@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_cong : mctt.

(** The motive of the [ℕ]-eliminator is a type because the step case is checked
    in a context that ends with it. *)
Corollary wf_natrec' : forall Θ Ξ Γ A MZ MS M,
    Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_natrec' : mctt.
#[export]
Remove Hints wf_natrec : mctt.

Corollary wf_fn' : forall Θ Ξ Γ A B M,
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : Π A B.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_fn' : mctt.
#[export]
Remove Hints wf_fn : mctt.

(** Whenever a [Π]-type is the type of a term, [wf_pi_inversion'] recovers its
    two components at the level the [Π]-type itself is a type at — which is the
    level the elimination rules want them at. *)
Corollary wf_app' : forall Θ Ξ Γ A B M N,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : B[Id,,N].
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_app' : mctt.
#[export]
Remove Hints wf_app : mctt.

Corollary wf_exp_eq_natrec_cong' : forall Θ Ξ Γ A A' i MZ MZ' MS MS' M M',
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] ->
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS ≈ MS' : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ℕ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end
         ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mctt.

Corollary wf_exp_eq_nat_beta_zero' : forall Θ Ξ Γ A MZ MS,
    Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mctt.

Corollary wf_exp_eq_nat_beta_succ' : forall Θ Ξ Γ A MZ MS M,
    Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end
         ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mctt.

Corollary wf_exp_eq_pi_cong' : forall Θ Ξ Γ A A' B B' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type@i.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_cong : mctt.

(** The domain and the codomain rarely arrive at the same level; this is the
    congruence that takes them as they come, and the counterpart of
    [wf_pi_max]. *)
Corollary wf_exp_eq_pi_cong_max : forall Θ Ξ Γ A A' B B' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type@(max i j).
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@(max i j)) by eauto using lift_exp_eq_max_left.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@(max i j)) by eauto using lift_exp_eq_max_right.
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mctt.

Corollary wf_exp_eq_fn_cong' : forall Θ Ξ Γ A A' B M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_cong : mctt.

Corollary wf_exp_eq_app_cong' : forall Θ Ξ Γ A B M M' N N',
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Π A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N].
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_app_cong : mctt.

(** Here the [Π]-type is not the type of anything, so its two components arrive
    at unrelated levels and [lift_exp_pi_common] is what raises them. *)
Corollary wf_exp_eq_pi_beta' : forall Θ Ξ Γ A B M N,
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N].
Proof.
  intros.
  gen_presups.
  assert (exists k, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@k /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@k) as [? []]
      by (eapply lift_exp_pi_common; mauto 2).
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_beta : mctt.

Corollary wf_exp_eq_fn_eta' : forall Θ Ξ Γ A B M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : Π A B.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_eta' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_eta : mctt.

(** A term equation presupposes that both sides are well-typed, so the
    refinement between two contexts extended by equal types needs nothing else. *)
Corollary wf_sub_id_extend_eq' : forall Θ Ξ Γ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢s Id : Γ ▹ A.
Proof.
  intros * H; gen_presups; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_id_extend_eq' : mctt.
#[export]
Remove Hints wf_sub_id_extend_eq : mctt.

(** Refinement of [Π]-types needs only the equation between the domains and the
    refinement between the codomains; that the four components are types, and at
    a common level, is presupposition and cumulativity.  The codomain [B] is
    checked in [Γ ▹ A'] by the premise and in [Γ ▹ A] by the rule, and the two
    are related by context conversion along the domain equation. *)
Lemma wf_subtyp_pi' : forall Θ Ξ Γ A A' B B' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ Π A' B'.
Proof.
  intros * ? Hsub.
  assert (exists j, Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B : Type@j /\ Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B' : Type@j) as [j []]
      by (apply presup_subtyp_types; assumption).
  gen_presups.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢s Id : Γ ▹ A') by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@j) by mauto 2.
  eapply wf_subtyp_pi with (i := max i j);
    mauto 3 using lift_exp_max_left, lift_exp_max_right, lift_exp_eq_max_left.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mctt.
#[export]
Remove Hints wf_subtyp_pi : mctt.
