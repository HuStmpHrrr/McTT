(** * The Rules with the Redundant Premises Removed

    Every rule carries the premises a *presupposition-free*
    formulation needs: the [Π]-rules check the domain and the codomain, the
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

    Making substitution an operation removes a third of this file.  The original
    development also restated every [_sub] rule — [Type@i[σ] ≈ Type@i],
    [ℕ[σ] ≈ ℕ], [(Π A B)[σ] ≈ Π A[σ] B[q σ]], and the [λ], application and
    [ℕ]-eliminator equations — because those were rules with premises of their
    own.  They are now definitional equalities, proved once in
    [Core.Syntactic.Substitution] and used by [rewrite] or by [simpl_sub]; there
    is nothing left to optimize.  [wf_ctx_eq_extend'] goes the same way, since
    context equality is [{{ Δ ⊢s Id : Γ }}] in both directions. *)

From Stdlib Require Import Lia Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CoreInversions.
Import Syntax_Notations Wk_Notations.

(** ** Rewriting the Type of a Judgment *)

Add Parametric Morphism i Γ : (wf_exp Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> iff as wf_exp_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups...
Qed.

Add Parametric Morphism i Γ : (wf_exp_eq Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups...
Qed.

Add Parametric Morphism Γ i : (wf_subtyp Γ)
    with signature (wf_exp_eq Γ {{{ Type@i }}}) ==> eq ==> iff as wf_subtyp_morphism_iff1.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 4.
Qed.

Add Parametric Morphism Γ j : (wf_subtyp Γ)
    with signature eq ==> (wf_exp_eq Γ {{{ Type@j }}}) ==> iff as wf_subtyp_morphism_iff2.
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

Corollary wf_subtyp_refl' : forall Γ M M' i,
    {{ Γ ⊢ M ≈ M' : Type@i }} ->
    {{ Γ ⊢ M ⊆ M' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_refl' : mctt.
#[export]
Remove Hints wf_subtyp_refl : mctt.

Corollary wf_conv' : forall Γ M A A' i,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv' : mctt.
#[export]
Remove Hints wf_conv : mctt.

Corollary wf_exp_eq_conv' : forall Γ M M' A A' i,
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv' : mctt.
#[export]
Remove Hints wf_exp_eq_conv : mctt.

(** [ℕ] is a type at every level, not only at [0]. *)
Corollary wf_nat' : forall Γ i,
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ ℕ : Type@i }}.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_nat' : mctt.
#[export]
Remove Hints wf_nat : mctt.

Corollary wf_exp_eq_nat_cong' : forall Γ i,
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ ℕ ≈ ℕ : Type@i }}.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_cong : mctt.

(** The motive of the [ℕ]-eliminator is a type because the step case is checked
    in a context that ends with it. *)
Corollary wf_natrec' : forall Γ A MZ MS M,
    {{ Γ ⊢ MZ : A[Id ,, zero] }} ->
    {{ Γ , ℕ , A ⊢ MS : A[Wk ⨟ Wk ,, succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id ,, M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_natrec' : mctt.
#[export]
Remove Hints wf_natrec : mctt.

Corollary wf_fn' : forall Γ A B M,
    {{ Γ , A ⊢ M : B }} ->
    {{ Γ ⊢ λ A M : Π A B }}.
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
Corollary wf_app' : forall Γ A B M N,
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M N : B[Id ,, N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ , A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_app' : mctt.
#[export]
Remove Hints wf_app : mctt.

Corollary wf_exp_eq_natrec_cong' : forall Γ A A' i MZ MZ' MS MS' M M',
    {{ Γ , ℕ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ MZ ≈ MZ' : A[Id ,, zero] }} ->
    {{ Γ , ℕ , A ⊢ MS ≈ MS' : A[Wk ⨟ Wk ,, succ #1] }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end
         ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id ,, M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mctt.

Corollary wf_exp_eq_nat_beta_zero' : forall Γ A MZ MS,
    {{ Γ ⊢ MZ : A[Id ,, zero] }} ->
    {{ Γ , ℕ , A ⊢ MS : A[Wk ⨟ Wk ,, succ #1] }} ->
    {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id ,, zero] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mctt.

Corollary wf_exp_eq_nat_beta_succ' : forall Γ A MZ MS M,
    {{ Γ ⊢ MZ : A[Id ,, zero] }} ->
    {{ Γ , ℕ , A ⊢ MS : A[Wk ⨟ Wk ,, succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end
         ≈ MS[Id ,, M ,, rec M return A | zero -> MZ | succ -> MS end] : A[Id ,, succ M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mctt.

Corollary wf_exp_eq_pi_cong' : forall Γ A A' B B' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A ⊢ B ≈ B' : Type@i }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }}.
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
Corollary wf_exp_eq_pi_cong_max : forall Γ A A' B B' i j,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A ⊢ B ≈ B' : Type@j }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i j) }} by eauto using lift_exp_eq_max_left.
  assert {{ Γ , A ⊢ B ≈ B' : Type@(max i j) }} by eauto using lift_exp_eq_max_right.
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mctt.

Corollary wf_exp_eq_fn_cong' : forall Γ A A' B M M' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A ⊢ M ≈ M' : B }} ->
    {{ Γ ⊢ λ A M ≈ λ A' M' : Π A B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_cong : mctt.

Corollary wf_exp_eq_app_cong' : forall Γ A B M M' N N',
    {{ Γ ⊢ M ≈ M' : Π A B }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M N ≈ M' N' : B[Id ,, N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ , A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_app_cong : mctt.

(** Here the [Π]-type is not the type of anything, so its two components arrive
    at unrelated levels and [lift_exp_pi_common] is what raises them. *)
Corollary wf_exp_eq_pi_beta' : forall Γ A B M N,
    {{ Γ , A ⊢ M : B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ (λ A M) N ≈ M[Id ,, N] : B[Id ,, N] }}.
Proof.
  intros.
  gen_presups.
  assert (exists k, {{ Γ ⊢ A : Type@k }} /\ {{ Γ , A ⊢ B : Type@k }}) as [? []]
      by (eapply lift_exp_pi_common; mauto 2).
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_beta : mctt.

Corollary wf_exp_eq_fn_eta' : forall Γ A B M,
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ M ≈ λ A (M⟨↑⟩ #0) : Π A B }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ , A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_eta' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_eta : mctt.

(** A term equation presupposes that both sides are well-typed, so the
    refinement between two contexts extended by equal types needs nothing else. *)
Corollary wf_sub_id_extend_eq' : forall Γ A A' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A' ⊢s Id : Γ , A }}.
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
    checked in [Γ , A'] by the premise and in [Γ , A] by the rule, and the two
    are related by context conversion along the domain equation. *)
Lemma wf_subtyp_pi' : forall Γ A A' B B' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A' ⊢ B ⊆ B' }} ->
    {{ Γ ⊢ Π A B ⊆ Π A' B' }}.
Proof.
  intros * ? Hsub.
  assert (exists j, {{ Γ , A' ⊢ B : Type@j }} /\ {{ Γ , A' ⊢ B' : Type@j }}) as [j []]
      by (apply presup_subtyp; assumption).
  gen_presups.
  assert {{ Γ , A ⊢s Id : Γ , A' }} by mauto 3.
  assert {{ Γ , A ⊢ B : Type@j }} by mauto 2.
  eapply wf_subtyp_pi with (i := max i j);
    mauto 3 using lift_exp_max_left, lift_exp_max_right, lift_exp_eq_max_left.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mctt.
#[export]
Remove Hints wf_subtyp_pi : mctt.
