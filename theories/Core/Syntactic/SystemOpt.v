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
    context equality, which is [Θ ⍮ Δ ⊢s Id : Γ] in both directions. *)

From Stdlib Require Import Lia Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CoreInversions.
Import Syntax_Notations Wk_Notations.

(** ** Rewriting the Type of a Judgment *)

Add Parametric Morphism i Θ Γ : (wf_exp Θ Γ)
    with signature wf_exp_eq Θ Γ Type@i ==> eq ==> iff as wf_exp_morphism_iff3.
Proof.
  split; intros; gen_presups; mautosolve.
Qed.

Add Parametric Morphism i Θ Γ : (wf_exp_eq Θ Γ)
    with signature wf_exp_eq Θ Γ Type@i ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof.
  split; intros; gen_presups; mautosolve.
Qed.

Add Parametric Morphism Θ Γ i : (wf_subtyp Θ Γ)
    with signature (wf_exp_eq Θ Γ Type@i) ==> eq ==> iff as wf_subtyp_morphism_iff1.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 4.
Qed.

Add Parametric Morphism Θ Γ j : (wf_subtyp Θ Γ)
    with signature eq ==> (wf_exp_eq Θ Γ Type@j) ==> iff as wf_subtyp_morphism_iff2.
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

Corollary wf_subtyp_refl' : forall Θ Γ M M' i,
    Θ ⍮ Γ ⊢ M ≈ M' : Type@i ->
    Θ ⍮ Γ ⊢ M ⊆ M'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_refl' : mctt.
#[export]
Remove Hints wf_subtyp_refl : mctt.

Corollary wf_conv' : forall Θ Γ M A A' i,
    Θ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ⊢ M : A'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv' : mctt.
#[export]
Remove Hints wf_conv : mctt.

Corollary wf_exp_eq_conv' : forall Θ Γ M M' A A' i,
    Θ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv' : mctt.
#[export]
Remove Hints wf_exp_eq_conv : mctt.

(** [ℕ] is a type at every level, not only at [0]. *)
Corollary wf_nat' : forall Θ Γ i,
    ⊢ Θ ⍮ Γ ->
    Θ ⍮ Γ ⊢ ℕ : Type@i.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_nat' : mctt.
#[export]
Remove Hints wf_nat : mctt.

Corollary wf_exp_eq_nat_cong' : forall Θ Γ i,
    ⊢ Θ ⍮ Γ ->
    Θ ⍮ Γ ⊢ ℕ ≈ ℕ : Type@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_cong : mctt.

(** So are [⊤] and [⊥]. *)
Corollary wf_True' : forall Θ Γ i,
    ⊢ Θ ⍮ Γ ->
    Θ ⍮ Γ ⊢ ⊤ : Type@i.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_True' : mctt.
#[export]
Remove Hints wf_True : mctt.

Corollary wf_exp_eq_True_cong' : forall Θ Γ i,
    ⊢ Θ ⍮ Γ ->
    Θ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Type@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_True_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_True_cong : mctt.

Corollary wf_False' : forall Θ Γ i,
    ⊢ Θ ⍮ Γ ->
    Θ ⍮ Γ ⊢ ⊥ : Type@i.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_False' : mctt.
#[export]
Remove Hints wf_False : mctt.

Corollary wf_exp_eq_False_cong' : forall Θ Γ i,
    ⊢ Θ ⍮ Γ ->
    Θ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Type@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_False_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_False_cong : mctt.

(** The motive of the [ℕ]-eliminator is a type because the step case is checked
    in a context that ends with it. *)
Corollary wf_natrec' : forall Θ Γ A MZ MS M,
    Θ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
    Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Γ ⊢ M : ℕ ->
    Θ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_natrec' : mctt.
#[export]
Remove Hints wf_natrec : mctt.

Corollary wf_fn' : forall Θ Γ A B M,
    Θ ⍮ Γ ▹ A ⊢ M : B ->
    Θ ⍮ Γ ⊢ λ A M : Π A B.
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
Corollary wf_app' : forall Θ Γ A B M N,
    Θ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Γ ⊢ M $ N : B[Id,,N].
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert (Θ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Γ ▹ A ⊢ B : Type@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_app' : mctt.
#[export]
Remove Hints wf_app : mctt.

Corollary wf_exp_eq_natrec_cong' : forall Θ Γ A A' i MZ MZ' MS MS' M M',
    Θ ⍮ Γ ▹ ℕ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] ->
    Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS ≈ MS' : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Γ ⊢ M ≈ M' : ℕ ->
    Θ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end
         ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mctt.

Corollary wf_exp_eq_exfalso_cong' : forall Θ Γ A A' i M M',
    Θ ⍮ Γ ▹ ⊥ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ⊢ M ≈ M' : ⊥ ->
    Θ ⍮ Γ ⊢ efq M return A ≈ efq M' return A' : A[Id,,M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_exfalso_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_exfalso_cong : mctt.

Corollary wf_exp_eq_nat_beta_zero' : forall Θ Γ A MZ MS,
    Θ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
    Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mctt.

Corollary wf_exp_eq_nat_beta_succ' : forall Θ Γ A MZ MS M,
    Θ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
    Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
    Θ ⍮ Γ ⊢ M : ℕ ->
    Θ ⍮ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end
         ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mctt.

Corollary wf_exp_eq_pi_cong' : forall Θ Γ A A' B B' i,
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@i ->
    Θ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type@i.
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
Corollary wf_exp_eq_pi_cong_max : forall Θ Γ A A' B B' i j,
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@j ->
    Θ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type@(max i j).
Proof.
  intros.
  assert (Θ ⍮ Γ ⊢ A ≈ A' : Type@(max i j)) by eauto using lift_exp_eq_max_left.
  assert (Θ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@(max i j)) by eauto using lift_exp_eq_max_right.
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mctt.

Corollary wf_exp_eq_fn_cong' : forall Θ Γ A A' B M M' i,
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
    Θ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_cong : mctt.

Corollary wf_exp_eq_app_cong' : forall Θ Γ A B M M' N N',
    Θ ⍮ Γ ⊢ M ≈ M' : Π A B ->
    Θ ⍮ Γ ⊢ N ≈ N' : A ->
    Θ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N].
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert (Θ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Γ ▹ A ⊢ B : Type@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_app_cong : mctt.

(** Here the [Π]-type is not the type of anything, so its two components arrive
    at unrelated levels and [lift_exp_pi_common] is what raises them. *)
Corollary wf_exp_eq_pi_beta' : forall Θ Γ A B M N,
    Θ ⍮ Γ ▹ A ⊢ M : B ->
    Θ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N].
Proof.
  intros.
  gen_presups.
  assert (exists k, Θ ⍮ Γ ⊢ A : Type@k /\ Θ ⍮ Γ ▹ A ⊢ B : Type@k) as [? []]
      by (eapply lift_exp_pi_common; mauto 2).
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_beta : mctt.

Corollary wf_exp_eq_fn_eta' : forall Θ Γ A B M,
    Θ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : Π A B.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert (Θ ⍮ Γ ⊢ A : Type@i /\ Θ ⍮ Γ ▹ A ⊢ B : Type@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_eta' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_eta : mctt.

(** A let presupposes its context, which carries the type of its annotation and
    of its body. *)
Corollary wf_let' : forall Θ Γ A M B C,
    Θ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    Θ ⍮ Γ ⊢ ℓ A ≔ M in B : C[Id,,M].
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_let' : mctt.
#[export]
Remove Hints wf_let : mctt.

Corollary wf_ctx_extend_def' : forall Θ Γ A M,
    Θ ⍮ Γ ⊢ M : A ->
    ⊢ Θ ⍮ Γ ▸ A ≔ M.
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_ctx_extend_def' : mctt.
#[export]
Remove Hints wf_ctx_extend_def : mctt.

Corollary wf_exp_eq_let_cong' : forall Θ Γ A A' M M' B B' C i,
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
    Θ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_let_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_let_cong : mctt.

Corollary wf_exp_eq_let_zeta' : forall Θ Γ A M B C,
    Θ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    Θ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M].
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_let_zeta' : mctt.
#[export]
Remove Hints wf_exp_eq_let_zeta : mctt.

(** A term equation presupposes that both sides are well-typed, so the
    refinement between two contexts extended by equal types needs nothing else. *)
Corollary wf_sub_id_extend_eq' : forall Θ Γ A A' i,
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ▹ A' ⊢s Id : Γ ▹ A.
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
Lemma wf_subtyp_pi' : forall Θ Γ A A' B B' i,
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
    Θ ⍮ Γ ⊢ Π A B ⊆ Π A' B'.
Proof.
  intros * ? Hsub.
  assert (exists j, Θ ⍮ Γ ▹ A' ⊢ B : Type@j /\ Θ ⍮ Γ ▹ A' ⊢ B' : Type@j) as [j []]
      by (apply presup_subtyp_types; assumption).
  gen_presups.
  assert (Θ ⍮ Γ ▹ A ⊢s Id : Γ ▹ A') by mauto 3.
  assert (Θ ⍮ Γ ▹ A ⊢ B : Type@j) by mauto 2.
  eapply wf_subtyp_pi with (i := max i j);
    mauto 3 using lift_exp_max_left, lift_exp_max_right, lift_exp_eq_max_left.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mctt.
#[export]
Remove Hints wf_subtyp_pi : mctt.
