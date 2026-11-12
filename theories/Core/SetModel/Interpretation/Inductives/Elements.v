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

(** Two functions on equal sets, equal at every point, are equal. *)
Lemma is_function_on_ext : forall D D' g h, set_eq D D' -> is_function_on D g -> is_function_on D' h ->
    (forall b, set_mem b D -> set_eq (set_apply g b) (set_apply h b)) -> set_eq g h.
Proof.
  intros D D' g h ED Hg Hh Hpt.
  pose proof (is_function_on_resp _ _ _ _ (set_eq_sym _ _ ED) (set_eq_refl _) Hh) as Hh'.
  destruct Hg as [Pg [Tg Fg]]. destruct Hh' as [Ph [Th Fh]].
  apply set_eq_intro.
  - intros p Hp. destruct (Pg p Hp) as [b [y [Hb E]]].
    assert (Hby : set_mem (ordered_pair b y) g) by (eapply set_mem_eq_l; [exact E | exact Hp]).
    destruct (Th b Hb) as [y' Hy'].
    assert (Ey : set_eq y y').
    { eapply set_eq_trans; [apply set_eq_sym; apply (is_function_on_apply D g b y (conj Pg (conj Tg Fg)) Hby) |].
      eapply set_eq_trans; [apply Hpt; exact Hb | apply (is_function_on_apply D h b y' (conj Ph (conj Th Fh)) Hy')]. }
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | exact Ey]] | exact Hy'].
  - intros p Hp. destruct (Ph p Hp) as [b [y [Hb E]]].
    assert (Hby : set_mem (ordered_pair b y) h) by (eapply set_mem_eq_l; [exact E | exact Hp]).
    destruct (Tg b Hb) as [y' Hy'].
    assert (Ey : set_eq y y').
    { eapply set_eq_trans; [apply set_eq_sym; apply (is_function_on_apply D h b y (conj Ph (conj Th Fh)) Hby) |].
      eapply set_eq_trans; [apply set_eq_sym; apply Hpt; exact Hb | apply (is_function_on_apply D g b y' (conj Pg (conj Tg Fg)) Hy')]. }
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | exact Ey]] | exact Hy'].
Qed.
