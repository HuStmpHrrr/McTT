(** * Soundness of Normalization by Evaluation

    The fundamental theorem of the gluing model, instantiated at the identity
    embedding and the identity substitution.

    During milestone M1 of the Prop landing the gluing model
    ([Core/Soundness/*]) is not ported to relevance-directed evaluation: the
    files are out of the build, and the theorems below keep their statements
    with their proofs pending ([PENDING M2]).  The proofs before the landing
    are in the history of this file. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Levels Require Export LevelEq.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The readback of a level of sort [n] is a canonical level of sort [n]:
    its constant is of a tier at most [n], and each atom is a level of its
    own sort ([level_atoms_well_scoped]).  The atoms' sorts are read off the
    types of the neutrals, and this is what makes them reliable: the
    equations of a canonical form drop an atom by absorption, which needs it
    typed at its sort. *)
Definition nf_lvl_well_scoped (n : nat) (Δ : ctx) (L : nf) : Prop :=
  match L with
  | nf_lvl c xs => fst c <= n /\ @level_atoms_well_scoped gc_deps gc_stack n Δ xs
  | _ => False
  end.

End Fixed_GCtx.

(** A typed term has a normal form, equal to it: it glues by the
    fundamental theorem of the gluing model, read at the identity
    embedding. *)
Theorem soundness : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists W, nbe Θ Ξ Γ M A W /\ Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ W : A.
Proof.
  (* PENDING M2: the gluing model for the Prop core *)
Admitted.

(** Two terms of one type whose normal forms are equal up to their proofs
    ([nf_erase]) are equal: completeness compares normal forms only up to
    erasure, and proofs are equal by proof irrelevance wherever they occur.
    For example, with [f : P → ℕ] and [h1 h2 : P], the normal forms of
    [f h1] and [f h2] are [⇑ⁿ (f $ⁿ nf_proof #1)] and
    [⇑ⁿ (f $ⁿ nf_proof #0)], equal erased, and [f h1 ≈ f h2 : ℕ] holds by
    proof irrelevance under the application.  Milestone M2 proves it from
    the gluing model. *)
Theorem soundness_erased : forall {Θ Ξ Γ M M' A W W'},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A ->
    nbe Θ Ξ Γ M A W ->
    nbe Θ Ξ Γ M' A W' ->
    nf_erase W = nf_erase W' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A.
Proof.
  (* PENDING M2: the gluing model for the Prop core *)
Admitted.

(** The normal form NbE computes is equal to the term. *)
Theorem soundness' : forall {Θ Ξ Γ M A W},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    nbe Θ Ξ Γ M A W ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ W : A.
Proof.
  intros * [? []]%soundness ?.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma soundness_ty : forall {Γ} {i : nat} {A},
    Γ ⊢ A : Typeω@i ->
    exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i.
Proof.
  intros.
  assert (exists W', nbe_f Γ A Typeω@i W' /\ Γ ⊢ A ≈ W' : Typeω@i) as [? [?%nbe_type_to_nbe_ty Heq]] by mauto using soundness.
  firstorder.
Qed.

Lemma soundness_ty' : forall {Γ} {i : nat} {A B},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    Γ ⊢ A ≈ B : Typeω@i.
Proof.
  intros.
  assert (exists B', nbe_ty_f Γ A B' /\ Γ ⊢ A ≈ B' : Typeω@i) as [? [? Heq]] by mauto using soundness_ty.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

(** [nbe] of a type, at a large universe it lives in. *)
Lemma nbe_ty_to_nbe_type : forall Γ T i W, nbe_ty_f Γ T W -> nbe_f Γ T Typeω@i W.
Proof.
  intros * H; inversion_clear H.
  eapply nbe_relevant_intro; [ eassumption | constructor | eassumption | constructor; eassumption | reflexivity ].
Qed.

(** [nbe] of a type, at [Prop]: a proposition is a relevant term of
    [Prop], read back as a type. *)
Lemma nbe_ty_to_nbe_prop : forall Γ T W, nbe_ty_f Γ T W -> nbe_f Γ T Propₘ W.
Proof.
  intros * H; inversion_clear H.
  econstructor; [ eassumption | constructor | eapply nbe_term_relevant; [ reflexivity | eassumption | constructor; eassumption ] ].
Qed.

(** The same at [LevelSort]: a type of levels is a relevant term of
    [LevelSort], read back as a type. *)
Lemma nbe_ty_to_nbe_level_sort : forall Γ T W, nbe_ty_f Γ T W -> nbe_f Γ T LevelSort W.
Proof.
  intros * H; inversion_clear H.
  econstructor; [ eassumption | constructor | eapply nbe_term_relevant; [ reflexivity | eassumption | constructor; eassumption ] ].
Qed.

(** A type of a sort ([type_sort]) is equal there to its normal form. *)
Lemma soundness_ty_at_sort : forall {Γ S A W},
    type_sort S ->
    Γ ⊢ A : S ->
    nbe_ty_f Γ A W ->
    Γ ⊢ A ≈ W : S.
Proof.
  intros * [i | |] HA Hn;
    [ exact (soundness_ty' HA Hn)
    | exact (soundness' HA (nbe_ty_to_nbe_prop _ _ _ Hn))
    | exact (soundness' HA (nbe_ty_to_nbe_level_sort _ _ _ Hn)) ].
Qed.

(** The normal form of a level of sort [n] is a canonical level of sort [n]:
    its constant is of a tier at most [n], and each atom is a level of its
    own sort ([nf_lvl_well_scoped]).  It is read off the gluing of the level,
    whose atoms are glued at their types.  The algorithmic layer needs it to
    trust the sorts an atom of a normal form carries. *)
Theorem soundness_lvl_well_scoped : forall {Γ M n W},
    Γ ⊢ M : Level@n ->
    nbe_f Γ M Level@n W ->
    nf_lvl_well_scoped n Γ W.
Proof.
  (* PENDING M2: read off the gluing of levels *)
Admitted.

End Fixed_GCtx.
