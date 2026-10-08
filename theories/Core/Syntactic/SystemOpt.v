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
    with signature wf_exp_eq Θ Ξ Γ Typeω@i ==> eq ==> iff as wf_exp_morphism_iff3.
Proof.
  split; intros; gen_presups; mautosolve.
Qed.

Add Parametric Morphism i Θ Ξ Γ : (wf_exp_eq Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ Typeω@i ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof.
  split; intros; gen_presups; mautosolve.
Qed.

Add Parametric Morphism Θ Ξ Γ i : (wf_subtyp Θ Ξ Γ)
    with signature (wf_exp_eq Θ Ξ Γ Typeω@i) ==> eq ==> iff as wf_subtyp_morphism_iff1.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 4.
Qed.

Add Parametric Morphism Θ Ξ Γ j : (wf_subtyp Θ Ξ Γ)
    with signature eq ==> (wf_exp_eq Θ Ξ Γ Typeω@j) ==> iff as wf_subtyp_morphism_iff2.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Typeω@i ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv' : mctt.
#[export]
Remove Hints wf_exp_eq_conv : mctt.

(** The closed small types and the small universes are types of every
    universe, in either tier: these are the small-tier counterparts of the
    primed rules below, so that a search is never stuck on the tier.  [wf_nat]
    and friends are removed from the database for the same reason the large
    forms replace them: their own level is fixed. *)
Corollary wf_nat_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : Type@n.
Proof. intros; eapply (lift_exp_uidx _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_nat; assumption ]. Qed.

Corollary wf_level_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Level : Type@n.
Proof. intros; eapply (lift_exp_uidx _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_level; assumption ]. Qed.

Corollary wf_True_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : Type@n.
Proof. intros; eapply (lift_exp_uidx _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_True; assumption ]. Qed.

Corollary wf_False_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Type@n.
Proof. intros; eapply (lift_exp_uidx _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_False; assumption ]. Qed.

Corollary wf_univ' : forall Θ Ξ Γ n m,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    n < m ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@n : Type@m.
Proof.
  intros; eapply (lift_exp_uidx _ _ _ _ (us (S n)) (us m)); [ cbn; lia | apply wf_univ_lit; assumption ].
Qed.

Corollary wf_exp_eq_nat_cong_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ≈ ℕ : Type@n.
Proof. intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_exp_eq_nat_cong; assumption ]. Qed.

Corollary wf_exp_eq_level_cong_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Level ≈ Level : Type@n.
Proof. intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_exp_eq_level_cong; assumption ]. Qed.

Corollary wf_exp_eq_True_cong_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Type@n.
Proof. intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_exp_eq_True_cong; assumption ]. Qed.

Corollary wf_exp_eq_False_cong_small : forall Θ Ξ Γ n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Type@n.
Proof. intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us 0) (us n)); [ cbn; lia | apply wf_exp_eq_False_cong; assumption ]. Qed.

Corollary wf_exp_eq_univ_cong_small : forall Θ Ξ Γ n m,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    n < m ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@n ≈ Type@n : Type@m.
Proof.
  intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us (S n)) (us m));
    [ cbn; lia | apply wf_exp_eq_univ_cong_lit; assumption ].
Qed.

(** As hints these are guarded on the goal's universe being a small one, and
    fix an open level to [0], exactly as the large forms are: an unguarded
    [Hint Resolve] would make every search in the database try to solve an
    arithmetic side condition. *)
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ℕ : Type@?n) =>
  fix_open_level n; (apply wf_nat_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Level : Type@?n) =>
  fix_open_level n; (apply wf_level_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Level ≈ Level : Type@?n) =>
  fix_open_level n; (apply wf_exp_eq_level_cong_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊤ : Type@?n) =>
  fix_open_level n; (apply wf_True_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊥ : Type@?n) =>
  fix_open_level n; (apply wf_False_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ℕ ≈ ℕ : Type@?n) =>
  fix_open_level n; (apply wf_exp_eq_nat_cong_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊤ ≈ ⊤ : Type@?n) =>
  fix_open_level n; (apply wf_exp_eq_True_cong_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊥ ≈ ⊥ : Type@?n) =>
  fix_open_level n; (apply wf_exp_eq_False_cong_small; assumption) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type@_ : Type@?m) =>
  fix_open_level m; (apply wf_univ'; [ assumption | lia ]) : mctt.
#[export] Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type@_ ≈ Type@_ : Type@?m) =>
  fix_open_level m; (apply wf_exp_eq_univ_cong_small; [ assumption | lia ]) : mctt.

(** [ℕ] is a type at every level, not only at [0]. *)
Corollary wf_nat' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : Typeω@i.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_nat' : mctt.
#[export]
Remove Hints wf_nat : mctt.

Corollary wf_exp_eq_nat_cong' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ≈ ℕ : Typeω@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_cong : mctt.

(** So are [⊤] and [⊥]. *)
Corollary wf_True' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : Typeω@i.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_True' : mctt.
#[export]
Remove Hints wf_True : mctt.

Corollary wf_exp_eq_True_cong' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Typeω@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_True_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_True_cong : mctt.

Corollary wf_False' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Typeω@i.
Proof.
  intros; eapply lift_exp_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_False' : mctt.
#[export]
Remove Hints wf_False : mctt.

Corollary wf_exp_eq_False_cong' : forall Θ Ξ Γ i,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Typeω@i.
Proof.
  intros; eapply lift_exp_eq_ge; [ | mauto 2 ]; lia.
Qed.

#[export]
Hint Resolve wf_exp_eq_False_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_False_cong : mctt.

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
  exvar nat ltac:(fun i => assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_app' : mctt.
#[export]
Remove Hints wf_app : mctt.

Corollary wf_exp_eq_natrec_cong' : forall Θ Ξ Γ A A' i MZ MZ' MS MS' M M',
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A ≈ A' : Typeω@i ->
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

Corollary wf_exp_eq_exfalso_cong' : forall Θ Ξ Γ A A' i M M',
    Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ⊥ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A ≈ efq M' return A' : A[Id,,M].
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_exfalso_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_exfalso_cong : mctt.

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
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Typeω@i.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Typeω@(max i j).
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(max i j)) by eauto using lift_exp_eq_max_left.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Typeω@(max i j)) by eauto using lift_exp_eq_max_right.
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mctt.

Corollary wf_exp_eq_fn_cong' : forall Θ Ξ Γ A A' B M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
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
  exvar nat ltac:(fun i => assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i) as [] by eauto using wf_pi_inversion').
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
  assert (exists k, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@k /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@k) as [? []]
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
  exvar nat ltac:(fun i => assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_eta' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_eta : mctt.

(** A let presupposes its context, which carries the type of its annotation and
    of its body. *)
Corollary wf_let' : forall Θ Ξ Γ A M B C,
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : C[Id,,M].
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_let' : mctt.
#[export]
Remove Hints wf_let : mctt.

Corollary wf_ctx_extend_def' : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M.
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_ctx_extend_def' : mctt.
#[export]
Remove Hints wf_ctx_extend_def : mctt.

Corollary wf_exp_eq_let_cong' : forall Θ Ξ Γ A A' M M' B B' C i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_let_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_let_cong : mctt.

Corollary wf_exp_eq_let_zeta' : forall Θ Ξ Γ A M B C,
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M].
Proof.
  intros; gen_presups; mautosolve 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_let_zeta' : mctt.
#[export]
Remove Hints wf_exp_eq_let_zeta : mctt.

(** A term equation presupposes that both sides are well-typed, so the
    refinement between two contexts extended by equal types needs nothing else. *)
Corollary wf_sub_id_extend_eq' : forall Θ Ξ Γ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ Π A' B'.
Proof.
  intros * ? Hsub.
  assert (exists j, Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B : Typeω@j /\ Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B' : Typeω@j) as [j []]
      by (apply presup_subtyp_types; assumption).
  gen_presups.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢s Id : Γ ▹ A') by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@j) by mauto 2.
  eapply wf_subtyp_pi with (i := max i j);
    mauto 3 using lift_exp_max_left, lift_exp_max_right, lift_exp_eq_max_left.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mctt.
#[export]
Remove Hints wf_subtyp_pi : mctt.

(** Conversion along an equation in any universe, large or small: the gluing
    model states every type equation in the ambient universe of its index. *)
Corollary wf_conv_univ : forall Θ Ξ Γ M A A' u,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  intros * HM HA.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(ulvl u))
    by (eapply (lift_exp_eq_uidx _ _ _ _ _ u (ulvl u)); [ apply uidx_le_ulvl | exact HA ]).
  eapply wf_exp_subtyp'; [ exact HM | mauto 3 ].
Qed.

Corollary wf_exp_eq_conv_univ : forall Θ Ξ Γ M M' A A' u,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  intros * HM HA.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(ulvl u))
    by (eapply (lift_exp_eq_uidx _ _ _ _ _ u (ulvl u)); [ apply uidx_le_ulvl | exact HA ]).
  eapply wf_exp_eq_subtyp'; [ exact HM | mauto 3 ].
Qed.

#[export]
Hint Resolve wf_conv_univ wf_exp_eq_conv_univ : mctt.

(** [Π] and its congruence in any universe, large or small: the two rules
    [wf_pi]/[wf_pi_small] and [wf_exp_eq_pi_cong]/[wf_exp_eq_pi_cong_small]
    as one statement over the index. *)
Corollary wf_pi_univ : forall Θ Ξ Γ A B u,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : ulvl_tm u.
Proof.
  intros * HA HB; destruct u; cbn in *; [ apply wf_pi_small_lit | apply wf_pi ]; assumption.
Qed.

(** The principal universe of a [Π] is the join of those of its parts. *)
Corollary wf_pi_umax : forall Θ Ξ Γ A B u v,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : ulvl_tm v ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : ulvl_tm (umax u v).
Proof.
  intros * HA HB; apply wf_pi_univ;
    [ eapply (lift_exp_uidx _ _ _ _ u); [ apply uidx_le_umax_left | exact HA ]
    | eapply (lift_exp_uidx _ _ _ _ v); [ apply uidx_le_umax_right | exact HB ] ].
Qed.

Corollary wf_exp_eq_pi_cong_univ : forall Θ Ξ Γ A A' B B' u,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : ulvl_tm u.
Proof.
  intros * HA HB; destruct u; cbn in *;
    [ apply wf_exp_eq_pi_cong_small_lit; [ gen_presups; eassumption | assumption | assumption ]
    | apply wf_exp_eq_pi_cong'; assumption ].
Qed.

#[export]
Hint Resolve wf_pi_univ wf_pi_umax wf_exp_eq_pi_cong_univ : mctt.

(** The [λ] congruence with the domain equation in any universe. *)
Corollary wf_exp_eq_fn_cong_univ : forall Θ Ξ Γ A A' B M M' u,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B.
Proof.
  intros * HA HM.
  eapply wf_exp_eq_fn_cong'; [| eassumption ].
  eapply (lift_exp_eq_uidx _ _ _ _ _ u (ulvl u)); [ apply uidx_le_ulvl | exact HA ].
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong_univ : mctt.

(** The same keyed on an equation in any universe, large or small: the gluing
    model rewrites types along equations in the ambient universe of its
    index. *)
Add Parametric Morphism u Θ Ξ Γ : (wf_exp Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ (ulvl_tm u) ==> eq ==> iff as wf_exp_morphism_iff_univ.
Proof.
  split; intros; eapply wf_conv_univ; [ eassumption | eassumption | eassumption | symmetry; eassumption ].
Qed.

Add Parametric Morphism u Θ Ξ Γ : (wf_exp_eq Θ Ξ Γ)
    with signature wf_exp_eq Θ Ξ Γ (ulvl_tm u) ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff_univ.
Proof.
  split; intros; eapply wf_exp_eq_conv_univ; [ eassumption | eassumption | eassumption | symmetry; eassumption ].
Qed.

(** An equation in any universe lifts to the large level the index lives at,
    which is where [wf_subtyp_refl] takes it. *)
#[local] Ltac subtyp_univ_step HAA' :=
  let H := fresh "H" in
  pose proof (lift_exp_eq_uidx _ _ _ _ _ _ _ (uidx_le_ulvl _) HAA') as H;
  eapply wf_subtyp_refl; [ gen_presups; eassumption | first [ exact H | symmetry; exact H ] ].

Add Parametric Morphism u Θ Ξ Γ : (wf_subtyp Θ Ξ Γ)
    with signature (wf_exp_eq Θ Ξ Γ (ulvl_tm u)) ==> eq ==> iff as wf_subtyp_morphism_iff1_univ.
Proof.
  intros A A' HAA' B; split; intros Hsub;
    ((etransitivity; [ idtac | exact Hsub ]) || (etransitivity; [ exact Hsub | idtac ]));
    subtyp_univ_step HAA'.
Qed.

Add Parametric Morphism u Θ Ξ Γ : (wf_subtyp Θ Ξ Γ)
    with signature eq ==> (wf_exp_eq Θ Ξ Γ (ulvl_tm u)) ==> iff as wf_subtyp_morphism_iff2_univ.
Proof.
  intros A B B' HBB'; split; intros Hsub;
    (etransitivity; [ exact Hsub | idtac ]);
    subtyp_univ_step HBB'.
Qed.

