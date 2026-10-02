From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Algorithmic.Subtyping Require Export Lemmas.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import Consequences.Rules.
From Mctt.Core.Semantic Require Import Consequences.
From Mctt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma functional_alg_type_infer : forall {Γ A A' M},
    Γ ⊢a M ⟹ A ->
    Γ ⊢a M ⟹ A' ->
    A = A'.
Proof.
  intros * HM1 HM2. gen A'.
  induction HM1; intros;
    inversion_clear HM2;
    functional_nbe_rewrite_clear;
    f_equiv;
    try reflexivity;
    intuition.
  - assert (Typeⁿ@i = Typeⁿ@i0) as [= <-] by intuition.
    assert (Typeⁿ@j = Typeⁿ@j0) as [= <-] by intuition.
    reflexivity.
  - assert (Πⁿ A B = Πⁿ A0 B0) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (C = C0) as <- by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (A = A0) as <- by mauto using ctx_lookup_functional.
    functional_nbe_rewrite_clear.
    reflexivity.
  (** Globals are resolved by a function, so both derivations read the same
      type. *)
  - assert (A = A0) as <- by congruence.
    functional_nbe_rewrite_clear.
    reflexivity.
Qed.

#[local]
Hint Resolve functional_alg_type_infer : mctt.

End Fixed_GCtx.

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (?Γ ⊢a ?M ⟹ ?A1), H2 : (?Γ ⊢a ?M ⟹ ?A2) |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2 using functional_alg_type_infer] | tactic_error A2 A1]; clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma alg_type_sound :
  (forall {Γ A M}, Γ ⊢a M ⟸ A -> ⊢ Γ -> forall i, Γ ⊢ A : Type@i -> Γ ⊢ M : A) /\
    (forall {Γ A M}, Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A).
Proof.
  apply alg_type_mut_ind; intros; try mautosolve 4.
  - assert (Γ ⊢ M : A) by mauto 3.
    assert (exists i, Γ ⊢ A : Type@i) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Type@(max i j)) by mauto 3 using lift_exp_max_right.
    assert (Γ ⊢ B : Type@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Γ ⊢ A ⊆ B) by mauto 2 using alg_subtyping_sound.
    mauto 3.
  - assert (Γ ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ Γ ▹ ℕ) by mauto 2.
    assert (Γ ▹ ℕ ⊢ A : Type@i) by mauto 2.
    assert (⊢ Γ ▹ ℕ ▹ A) by mauto 3.
    assert (Γ ⊢ M : ℕ) by mauto 2.
    assert (Γ ⊢ A[Id,,zero] : Type@i) by mauto 3.
    assert (Γ ▹ ℕ ▹ A ⊢ A[Wk ⨟ Wk,,succ #1] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ B : Type@i) as <- by mauto 4 using soundness_ty'.
    mauto 4.
  - assert (Γ ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ Γ ▹ ⊥) by mauto 2.
    assert (Γ ▹ ⊥ ⊢ A : Type@i) by mauto 2.
    assert (Γ ⊢ M : ⊥) by mauto 2.
    assert (Γ ⊢ A[Id,,M] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ B : Type@i) as <- by mauto 4 using soundness_ty'.
    mauto 4.
  - assert (Γ ⊢ A : Type@i) by mauto 2.
    assert (⊢ Γ ▹ A) by mauto 3.
    mauto 3.
  - assert (Γ ⊢ A : Type@i) by mauto 2.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ⊢ A ≈ C : Type@i) by mauto 2 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 2.
    assert (exists j, Γ ▹ A ⊢ B : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ Π A B ≈ Π C B : Type@(max i j)) as <- by mauto 3.
    mauto 3.
  - assert (Γ ⊢ M : Π A B) by mauto 2.
    assert (exists i, Γ ⊢ Π A B : Type@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Type@i /\ Γ ▹ (A : exp) ⊢ B : Type@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 2.
    assert (Γ ⊢ B[Id,,N] ≈ C : Type@i) as <- by mauto 4 using soundness_ty'.
    mauto 3.
  - assert (Γ ⊢ A : Type@i) by mauto 2.
    assert (Γ ⊢ M : A) by mauto 2.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 2.
    assert (exists j, Γ ▸ A ≔ M ⊢ C : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Type@j) by mauto 3.
    assert (Γ ⊢ C[Id,,M] ≈ D : Type@j) as <- by mauto 3 using soundness_ty'.
    mauto 3.
  - assert (Γ ⊢ #x : A) by mauto 2.
    assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 2.
    assert (Γ ⊢ A ≈ B : Type@i) as <- by mauto 2 using soundness_ty'.
    mauto 3.
  (** The resolution premise of [wf_glob] is the same function call, so the
      declarative rule applies directly; [soundness_ty'] relates the inferred
      normal form to the declarative type. *)
  - assert (Γ ⊢ a_glob p : A) by mauto 3.
    assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 3 using wf_glob_typ.
    assert (Γ ⊢ A ≈ C : Type@i) as <- by mauto 2 using soundness_ty'.
    mauto 3.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    Γ ⊢ A : Type@i ->
    Γ ⊢ M : A.
Proof.
  pose proof alg_type_sound; intuition.
Qed.

Lemma alg_type_infer_sound : forall {Γ A M},
    Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A.
Proof.
  pose proof alg_type_sound; intuition.
Qed.

Lemma alg_type_infer_normal : forall {Γ A A' M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A' ->
    A = A'.
Proof.
  intros * ? Hinfer Hnbe. gen A'.
  assert (Γ ⊢ M : A) by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  - assert (Γ ⊢ ℕ : Type@0) by mauto 3.
    assert (Γ ⊢ M : ℕ) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▹ ℕ) by mauto 3.
    assert (Γ ▹ ℕ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ ⊥ : Type@0) by mauto 3.
    assert (Γ ⊢ M : ⊥) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▹ ⊥) by mauto 3.
    assert (Γ ▹ ⊥ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound.
    assert (Γ ⊢ A ≈ C : Type@i) by mauto 3 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B : Type@j) as [j] by (gen_presups; eauto 2).
    assert (⊨ Γ ▹ (C : exp) ≈ Γ ▹ A) by mauto 3.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    assert (initial_env_f (Γ ▹ (C : exp)) (ρ ↦ ⇑! a (length Γ))) by mauto 3.
    assert (nbe_ty_f Γ A C) by mauto 3.
    assert (nbe_ty_f Γ C A0) by mauto 3.
    replace A0 with C by mauto 3.
    assert (nbe_ty_f (Γ ▹ (C : exp)) B B') by mauto 3.
    assert (nbe_ty_f (Γ ▹ A) B B') by mauto 4 using ctxeq_nbe_ty_eq'; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ M : Πⁿ A B) by mauto 3 using alg_type_infer_sound.
    assert (exists i, Γ ⊢ Π A B : Type@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Type@i /\ Γ ▹ (A : exp) ⊢ B : Type@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 3 using alg_type_check_sound.
    assert (Γ ⊢ B[Id,,N] : Type@i) by mauto 3; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound.
    assert (Γ ⊢ M : A) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▸ A ≔ M ⊢ C : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Type@j) by mauto 3; (f_equiv; mautosolve 4).
  - assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 2; (f_equiv; mautosolve 4).
  (** A global infers the normal form of a type of the ambient context, so
      [idempotent_nbe_ty] closes it; that it is a type is [wf_glob_typ]. *)
  - assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 3 using wf_glob_typ.
    (f_equiv; mautosolve 4).
Qed.

Hint Resolve alg_type_infer_normal : mctt.

Lemma alg_type_check_typ_implies_alg_type_infer_typ : forall {Γ A i},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Type@i ->
    exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  firstorder.
Qed.

Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.

Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M A B i},
    ⊢ Γ ->
    Γ ⊢ Π A B : Type@i ->
    Γ ⊢a M ⟸ Π A B ->
    exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Type@i /\ Γ ▹ A ⊢a B' ⊆ B.
Proof.
  intros * ? ? Hcheck.
  assert (Γ ⊢ A : Type@i /\ Γ ▹ A ⊢ B : Type@i) as [] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' C Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  inversion Hnbe1; subst.
  functional_initial_env_rewrite_clear.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  simpl in *.
  assert (Γ ⊢ M : Πⁿ A0 B0) by mauto 3 using alg_type_infer_sound.
  assert (exists j, Γ ⊢ Π A0 B0 : Type@j) as [j] by (gen_presups; eauto 2).
  assert (Γ ⊢ A0 : Type@j /\ Γ ▹ (A0 : exp) ⊢ B0 : Type@j) as [] by mauto 3.
  do 2 eexists.
  assert (nbe_ty_f Γ A A0) by mauto 3.
  assert (Γ ⊢ A ≈ A0 : Type@i) by mauto 3 using soundness_ty'.
  repeat split; mauto 3.
  assert (initial_env_f (Γ ▹ A) (ρ ↦ ⇑! a (length Γ))) by mauto 3.
  assert (nbe_ty_f (Γ ▹ A) B B') by mauto 3.
  assert (initial_env_f (Γ ▹ (A0 : exp)) (ρ ↦ ⇑! a0 (length Γ))) by mauto 3.
  assert (nbe_ty_f (Γ ▹ (A0 : exp)) B0 B0) by mauto 3.
  assert (⊨ Γ ▹ (A0 : exp) ≈ Γ ▹ A) by mauto 3.
  assert (nbe_ty_f (Γ ▹ A) B0 B0) by mauto 4 using ctxeq_nbe_ty_eq'.
  mauto 3.
Qed.

Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.

Lemma alg_type_check_subtyp : forall {Γ A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ⊆ A' ->
    Γ ⊢a M ⟸ A'.
Proof.
  intros * [] **.
  assert (Γ0 ⊢a B ⊆ A') by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

Hint Resolve alg_type_check_subtyp : mctt.

Corollary alg_type_check_conv : forall {Γ i A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ≈ A' : Type@i ->
    Γ ⊢a M ⟸ A'.
Proof.
  mauto 3.
Qed.

Hint Resolve alg_type_check_conv : mctt.

Lemma alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    Γ ⊢a M ⟸ A.
Proof.
  (** The global context is an index of [wf_exp], so it is fixed for the
      induction, as in [subtyp_spec].  [user_exp] is reverted so that the two
      equations come first in every case and the induction hypotheses keep
      their [user_exp] premise. *)
  intros * Hue H.
  revert Hue.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  induction H; subst;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
    intros Hue;
    gen_presups; inversion Hue; subst; clear Hue; mauto 4 using alg_subtyping_complete, alg_type_check_subtyp.
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists j, Γ ▹ ℕ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (Γ ⊢ A[Id,,M] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Type@i) as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists j, Γ ▹ ⊥ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (Γ ⊢ A[Id,,M] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Type@i) as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - assert (exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (exists j, Γ ▹ A ⊢a B ⟹ Typeⁿ@j /\ j <= i) as [j' []] by mauto 3.
    assert (max j j' <= i) by lia.
    econstructor; mauto 3 using alg_subtyping_complete.
  - assert (exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (Γ ▹ A ⊢a M ⟸ B) by mauto 3.
    assert (exists B', Γ ▹ A ⊢a M ⟹ B' /\ Γ ▹ A ⊢a B' ⊆ B) as [B' []] by (inversion_clear_by_head alg_type_check; firstorder).
    assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Type@i) as [W []] by mauto 3 using soundness_ty.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ▹ A ⊢ M : B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B' : Type@j) as [] by (gen_presups; eauto 2).
    econstructor; mauto 3.
    eapply alg_subtyping_complete.
    eapply wf_subtyp_pi'; mauto 2.
    mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
  - assert (Γ ⊢a M ⟸ Π A B) by mauto 2.
    assert (Γ ⊢a N ⟸ A) by mauto 2.
    assert (exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Type@i /\ Γ ▹ A ⊢a B' ⊆ B) as [A' [B' [? []]]] by mauto 3.
    assert (Γ ⊢ M : Πⁿ A' B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ⊢ Π A' B' : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A' : Type@j /\ Γ ▹ (A' : exp) ⊢ B' : Type@j) as [] by mauto 3.
    assert (Γ ⊢ N : A') by mauto 3.
    assert (Γ ⊢ B'[Id,,N] : Type@j) by mauto 3.
    assert (exists W, nbe_ty_f Γ B'[Id,,N] W /\ Γ ⊢ B'[Id,,N] ≈ W : Type@j) as [W []] by (eapply soundness_ty; mauto 3).
    assert (Γ ▹ A ⊢ B' : Type@j) by mauto 4.
    assert (Γ ▹ A ⊢ B' ⊆ B) by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ B'[Id,,N] ⊆ B[Id,,N]) by mauto 3.
    assert (Γ ⊢ W ⊆ B[Id,,N]) by (transitivity B'[Id,,N]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢a B ⟸ C) by mauto 2.
    assert (exists C', Γ ▸ A ≔ M ⊢a B ⟹ C' /\ Γ ▸ A ≔ M ⊢a C' ⊆ C) as [C' []]
        by (inversion_clear_by_head alg_type_check; firstorder).
    assert (Γ ▸ A ≔ M ⊢ B : C') by mauto 3 using alg_type_infer_sound.
    assert (exists k, Γ ▸ A ≔ M ⊢ C' : Type@k) as [k] by (gen_presups; eauto 2).
    assert (exists k', Γ ▸ A ≔ M ⊢ C : Type@k') as [k'] by (gen_presups; eauto 2).
    assert (Γ ▸ A ≔ M ⊢ C' ⊆ C)
      by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ C'[Id,,M] : Type@k) by mauto 3.
    assert (exists W, nbe_ty_f Γ C'[Id,,M] W /\ Γ ⊢ C'[Id,,M] ≈ W : Type@k) as [W []]
        by (eapply soundness_ty; mauto 3).
    assert (Γ ⊢ C'[Id,,M] ⊆ C[Id,,M]) by mauto 3.
    assert (Γ ⊢ W ⊆ C[Id,,M]) by (transitivity C'[Id,,M]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Type@i) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  (** Resolution is the same function call in both systems. *)
  - assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 3 using wf_glob_typ.
    assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Type@i) as [W []]
        by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
Qed.

Hint Resolve alg_type_check_complete : mctt.

Corollary alg_type_infer_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    exists B, Γ ⊢a M ⟹ B /\ Γ ⊢a B ⊆ A.
Proof.
  intros.
  assert (Γ ⊢a M ⟸ A) as Hcheck by mauto 4 using alg_type_check_complete.
  inversion_clear Hcheck.
  firstorder.
Qed.

Hint Resolve alg_type_infer_complete : mctt.

Corollary alg_type_infer_typ_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Type@i ->
    exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

Hint Resolve alg_type_infer_typ_complete : mctt.

Corollary alg_type_infer_pi_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Type@i ->
    exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

Hint Resolve alg_type_infer_pi_complete : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve alg_type_infer_normal : mctt.
#[export]
Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.
#[export]
Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.
#[export]
Hint Resolve alg_type_check_subtyp : mctt.
#[export]
Hint Resolve alg_type_check_conv : mctt.
#[export]
Hint Resolve alg_type_check_complete : mctt.
#[export]
Hint Resolve alg_type_infer_complete : mctt.
#[export]
Hint Resolve alg_type_infer_typ_complete : mctt.
#[export]
Hint Resolve alg_type_infer_pi_complete : mctt.
