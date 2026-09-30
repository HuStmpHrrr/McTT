(** * (c) The naive monotonicity statement for [per_univ_elem], attempted

    The strongest natural statement: a type at [G1] is a type at [G2], and the
    element relation only grows.  Induction on the [G1] derivation goes
    through for [ℕ] and neutral types, and gets stuck exactly at [Π] (and at
    [𝕌@j], which needs the statement at [j] — hence at [Π] again). *)

From Stdlib Require Import Relation_Definitions RelationClasses.
From Equations Require Import Equations.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.
From ExtInv Require Import Ext PERExt.
Import Domain_Notations.

Section Attempt.
  Variables (G1 G2 : GCtx).
  Hypothesis Hext : gc_ext G1 G2.

  Theorem per_univ_elem_mono_attempt : forall i R a b,
      @per_univ_elem G1 i R a b ->
      exists R', @per_univ_elem G2 i R' a b /\ (forall x y, R x y -> R' x y).
  Proof.
    intros i R a b H.
    (* the eliminator, applied by hand (the motive is ours) *)
    revert i R a b H.
    refine (@per_univ_elem_ind G1 (fun i R a b =>
      exists R', @per_univ_elem G2 i R' a b /\ (forall x y, R x y -> R' x y)) _ _ _ _).
    - (* 𝕌@j: R <~> per_univ j at G1.  Take R' := per_univ j at G2; the
         inclusion per_univ j (G1) ⊆ per_univ j (G2) is the IH at j, available.
         So this case is FINE *given* the theorem at j < i. *)
      intros i j j' elem_rel Hlt <- HE IH.
      exists (@per_univ G2 j); split.
      + apply (@per_univ_elem_core_univ' G2); [ exact Hlt | reflexivity ].
      + intros x y Hxy%HE; destruct Hxy as [R0 H0].
        destruct (IH _ _ _ H0) as [R1 [H1 _]]; exists R1; exact H1.
    - (* ℕ *)
      intros i elem_rel HE; exists (@per_nat G2); split.
      + simp per_univ_elem; apply per_univ_elem_core_nat; reflexivity.
      + intros x y Hxy%HE; apply (per_nat_mono _ _ Hext); exact Hxy.
    - (* Π: STUCK.  See the comment. *)
      intros i a ρ B a' ρ' B' in_rel out_rel elem_rel Ha [in_rel2 [Ha2 Hin]] Hper HB HE.
      (* To build [per_univ_elem G2 i ?R' (Πᵈ a ρ B) (Πᵈ a' ρ' B')] we must give,
         for EVERY [c ≈ c' ∈ in_rel2] (G2-related arguments), evaluations of
         [B] at [ρ ↦ c] and of [B'] at [ρ' ↦ c'] at G2 and their relatedness.
         The hypotheses [HB] only speak about [c ≈ c' ∈ in_rel], and [Hin] is
         an inclusion in_rel ⊆ in_rel2, i.e. the WRONG direction: the
         argument position is contravariant.  [in_rel2 ⊆ in_rel] is false in
         general ([per_nat_not_antimono]: [⇑ ℕ m_bad] is in per_nat at G2
         only).  The same holds for the inclusion of element relations:
         [f ∈ elem_rel] says nothing about [f] applied to [c ∈ in_rel2 \ in_rel].
         Nothing in [per_univ_elem] constrains how [B] (an arbitrary piece of
         syntax) evaluates outside [in_rel]. *)
      admit.
    - (* neutral *)
      intros i a b a' b' elem_rel Hb HE; exists (@per_ne G2); split.
      + simp per_univ_elem; apply per_univ_elem_core_neut;
          [ apply (per_bot_mono _ _ Hext); exact Hb | reflexivity ].
      + intros x y Hxy%HE; apply (per_ne_mono _ _ Hext); exact Hxy.
  Abort.
End Attempt.
