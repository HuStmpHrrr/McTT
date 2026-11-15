(** * The Elements of Inductive and Record Types

    The elements of an inductive type are flat: a constructor's name and
    the values of its non-uniform parameters and arguments ([con_val]).
    A tuple is the graph of its fields on their names ([tuple_code]). *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Sets Require Export Encodings.
From Mctt.Core.SetModel.Interpretation.Global Require Export Valuation.
Import ListNotations.

(** The element of a constructor [c] at the values [vals] of the
    non-uniform parameters and the arguments. *)
Definition con_val (c : string) (vals : list aczel_set) : aczel_set := ordered_pair (string_code c) (list_code vals).

(** The tuple of the fields [fs], by name: a graph on the fields' names. *)
Definition tuple_code (fs : list (string * aczel_set)) : aczel_set :=
  set_of_list (List.map (fun f => ordered_pair (string_code (fst f)) (snd f)) fs).

(** The field [f] of a tuple: tuples are graphs on the fields' names. *)
Definition tuple_field (t : aczel_set) (f : string) : aczel_set := set_apply t (string_code f).

(** A function of a list of sets respects their equality. *)
Definition list_function_respects (f : list aczel_set -> aczel_set) : Prop :=
  forall l l', list_set_eq l l' -> set_eq (f l) (f l').

(** A list-valued function of a list of sets respects their equality. *)
Definition list_list_function_respects (f : list aczel_set -> list aczel_set) : Prop :=
  forall l l', list_set_eq l l' -> list_set_eq (f l) (f l').
