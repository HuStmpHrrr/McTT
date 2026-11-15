(** * Least Fixed Points

    The Knaster–Tarski least fixed point of an operator [Φ] on the subsets
    of a bound [B]: the members of [B] in every subset of [B] closed under
    [Φ].  Rocq's impredicative [Prop] lets the separation quantify over all
    such subsets.  The carriers of inductive types are such fixed points,
    over a bound in their universe. *)

From Mctt.Core.SetModel.Sets Require Export Aczel.

Section LeastFixedPoint.
  Variable B : aczel_set.
  Variable Φ : aczel_set -> aczel_set.

(** [Φ] is monotone on the subsets of [B]. *)
Definition monotone_operator : Prop :=
  forall S S', set_sub S B -> set_sub S' B -> set_sub S S' -> set_sub (Φ S) (Φ S').

(** [Φ] maps the subsets of [B] into [B]. *)
Definition bounded_operator : Prop := forall S, set_sub S B -> set_sub (Φ S) B.

(** [z] is in every subset of [B] closed under [Φ]. *)
Definition in_every_closed_subset (z : aczel_set) : Prop :=
  forall S, set_sub S B -> set_sub (Φ S) S -> set_mem z S.

Lemma in_every_closed_subset_resp : respects_set_eq in_every_closed_subset.
Proof. intros x y E H S HS HΦ. eapply set_mem_eq_l; [exact E | apply H; assumption]. Qed.

(** The least fixed point of [Φ] below [B]. *)
Definition least_fixed_point_set : aczel_set := separation_set B in_every_closed_subset.

Lemma least_fixed_point_bound : set_sub least_fixed_point_set B.
Proof. intros z Hz. apply (set_mem_separation _ _ _ in_every_closed_subset_resp) in Hz as [Hz _]. exact Hz. Qed.

(** It is included in every subset of [B] closed under [Φ]. *)
Lemma least_fixed_point_least : forall S, set_sub S B -> set_sub (Φ S) S -> set_sub least_fixed_point_set S.
Proof.
  intros S HS HΦ z Hz. apply (set_mem_separation _ _ _ in_every_closed_subset_resp) in Hz as [_ Hz]. apply Hz; assumption.
Qed.

Hypothesis Hmono : monotone_operator.
Hypothesis Hbound : bounded_operator.

(** It is closed under [Φ]. *)
Lemma least_fixed_point_closed : set_sub (Φ least_fixed_point_set) least_fixed_point_set.
Proof.
  intros z Hz. apply (set_mem_separation _ _ _ in_every_closed_subset_resp). split.
  - exact (Hbound _ least_fixed_point_bound _ Hz).
  - intros S HS HΦ. apply HΦ. eapply Hmono; [exact least_fixed_point_bound | exact HS | | exact Hz].
    apply least_fixed_point_least; assumption.
Qed.

(** Induction: a property that respects equality and holds of every
    member of [Φ] of the members having it holds of every member. *)
Lemma least_fixed_point_ind : forall P, respects_set_eq P ->
    set_sub (Φ (separation_set least_fixed_point_set P)) (separation_set least_fixed_point_set P) ->
    forall z, set_mem z least_fixed_point_set -> P z.
Proof.
  intros P HP Hcl z Hz.
  assert (Hs : set_sub (separation_set least_fixed_point_set P) B).
  { intros w Hw. apply (set_mem_separation _ _ _ HP) in Hw as [Hw _]. exact (least_fixed_point_bound _ Hw). }
  pose proof (least_fixed_point_least _ Hs Hcl _ Hz) as H.
  apply (set_mem_separation _ _ _ HP) in H as [_ H]. exact H.
Qed.

End LeastFixedPoint.
