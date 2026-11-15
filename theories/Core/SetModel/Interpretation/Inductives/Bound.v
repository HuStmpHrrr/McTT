(** * Points, Fields and Arguments of the Carriers

    Three facts about the carriers of a group ([Carriers.v]) that the
    eliminator and the records use: the points of a list of domains
    ([points_fit]), the members of a tuple's code, and the length of the
    arguments that fit a constructor. *)

From Stdlib Require Import String List Lia.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export Carriers.
Import ListNotations.

Section Bound.
  Variable G : set_group.
  Variable us : list aczel_set.

(** ** Positions *)

(** [points_fit ds pre points pts]: [pts] are points of the domains [ds]
    after the points [points]. *)
Inductive points_fit : list (list aczel_set -> aczel_set) -> list aczel_set -> list aczel_set -> list aczel_set -> Prop :=
(** No domain left *)
| points_fit_nil : forall pre points, points_fit nil pre points nil
(** A point of the next domain, then the rest *)
| points_fit_cons : forall d ds pre points b pts,
    set_mem b (code_carrier (d (pre ++ points))) ->
    points_fit ds pre (points ++ [b]) pts ->
    points_fit (d :: ds) pre points (b :: pts).

Lemma set_mem_tuple_code : forall z fs,
    set_mem z (tuple_code fs) <-> Exists (fun f => set_eq z (ordered_pair (string_code (fst f)) (snd f))) fs.
Proof.
  intros z fs. unfold tuple_code. rewrite set_mem_set_of_list. rewrite Exists_map. reflexivity.
Qed.

Lemma arguments_fit_length : forall bound S pre gs vals, arguments_fit G bound S pre gs vals -> List.length vals = List.length gs.
Proof. intros * H. induction H; cbn; congruence. Qed.

End Bound.
