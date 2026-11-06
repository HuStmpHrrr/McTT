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
    ([nf_eq_upto_proofs]) are equal: completeness compares normal forms
    only up to proofs, and proofs are equal by proof irrelevance wherever
    they occur.  For example, with [f : P → ℕ] and [h1 h2 : P], the normal
    forms of [f h1] and [f h2] are [⇑ⁿ{ak_relevant} (f $ⁿ nf_proof #1)] and
    [⇑ⁿ{ak_relevant} (f $ⁿ nf_proof #0)], related, and [f h1 ≈ f h2 : ℕ] holds by
    proof irrelevance under the application.  Milestone M2 proves it from
    the gluing model. *)
Theorem soundness_upto_proofs : forall {Θ Ξ Γ M M' A W W'},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A ->
    nbe Θ Ξ Γ M A W ->
    nbe Θ Ξ Γ M' A W' ->
    nf_eq_upto_proofs W W' ->
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
  eapply nbe_evaluated_intro; [ eassumption | constructor | eassumption | constructor; eassumption | constructor ].
Qed.

(** [nbe] of a type, at [Prop]: a proposition is a relevant term of
    [Prop], read back as a type. *)
Lemma nbe_ty_to_nbe_prop : forall Γ T W, nbe_ty_f Γ T W -> nbe_f Γ T Propₘ W.
Proof.
  intros * H; inversion_clear H.
  econstructor; [ eassumption | constructor | eapply nbe_term_evaluated; [ constructor | eassumption | constructor; eassumption ] ].
Qed.

(** The same at [LevelSort]: a type of levels is a relevant term of
    [LevelSort], read back as a type. *)
Lemma nbe_ty_to_nbe_level_sort : forall Γ T W, nbe_ty_f Γ T W -> nbe_f Γ T LevelSort W.
Proof.
  intros * H; inversion_clear H.
  econstructor; [ eassumption | constructor | eapply nbe_term_evaluated; [ constructor | eassumption | constructor; eassumption ] ].
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

(** A neutral is an atom of sort [s] of the normal form of a typed level:
    the atoms whose coherence soundness gives
    ([soundness_nbe_atoms_upto_proofs]).  The atom is one of the list
    ([List.In]), not a neutral equal to one up to proofs. *)
#[warnings="-cannot-define-projection"]
Record nbe_level_atom (Γ : ctx) (s : nat) (a : ne) : Prop := mk_nbe_level_atom
  { (** The level *)
    nbe_level_atom_exp : exp
    (** Its sort *)
  ; nbe_level_atom_level_sort : nat
    (** The constant of its normal form *)
  ; nbe_level_atom_constant : o2
    (** The atoms of its normal form *)
  ; nbe_level_atom_atoms : list level_atom
    (** The offset of the atom *)
  ; nbe_level_atom_offset : nat
    (** The level is a level of its sort *)
  ; nbe_level_atom_typed : Γ ⊢ nbe_level_atom_exp : Level@nbe_level_atom_level_sort
    (** Its normal form *)
  ; nbe_level_atom_nbe : nbe_f Γ nbe_level_atom_exp Level@nbe_level_atom_level_sort
                           (nf_lvl nbe_level_atom_constant nbe_level_atom_atoms)
    (** The atom is one of its atoms, at sort [s] *)
  ; nbe_level_atom_in : List.In (mk_level_atom nbe_level_atom_offset s a) nbe_level_atom_atoms }.

(** Two atoms of normal forms of levels, of one sort and equal up to their
    proofs, are equal levels: a canonical form keeps one of them in place
    of the other ([level_atoms_coherent]), and proofs are equal by proof
    irrelevance wherever they occur.  For example, with [h : P],
    [F : P → LevelSort] and [g : (F h → F h) → Level@0], the atom of
    [g (λ x : F h. x)] holds the proof [h] in the annotation of the
    abstraction, and two such atoms differing only in that proof are
    equal. *)
Theorem soundness_nbe_atoms_upto_proofs : forall {Γ s a b},
    nbe_level_atom Γ s a ->
    nbe_level_atom Γ s b ->
    ne_eq_upto_proofs a b ->
    Γ ⊢ (a : exp) ≈ (b : exp) : Level@s.
Proof.
  (* PENDING M2: read off the gluing of levels *)
Admitted.

(** The atoms of the normal forms of typed levels are coherent. *)
Lemma level_atoms_coherent_of_nbe : forall {Γ} xs,
    (forall j s a, List.In (mk_level_atom j s a) xs -> nbe_level_atom Γ s a) ->
    @level_atoms_coherent gc_deps gc_stack Γ xs.
Proof.
  intros * Hxs j s a j' b Ha Hb Hab.
  exact (soundness_nbe_atoms_upto_proofs (Hxs _ _ _ Ha) (Hxs _ _ _ Hb) Hab).
Qed.

(** The atoms of the normal form of a typed level are atoms of normal
    forms of typed levels. *)
Lemma nbe_level_atom_of_nbe : forall {Γ M n c xs},
    Γ ⊢ M : Level@n ->
    nbe_f Γ M Level@n (nf_lvl c xs) ->
    forall j s a, List.In (mk_level_atom j s a) xs -> nbe_level_atom Γ s a.
Proof. intros * HM Hnbe j s a Hin; exact (mk_nbe_level_atom _ _ _ _ _ _ _ _ HM Hnbe Hin). Qed.

End Fixed_GCtx.
