(** * Encodings of Lists and Names as Sets

    A list of sets is a chain of ordered pairs ending in the empty set
    ([list_code]); a name is the list of its characters' numerals
    ([string_code]).  Both are injective, so constructor values and the
    fields of tuples can be told apart by their names. *)

From Stdlib Require Import List String Ascii.
From Mctt.Core.SetModel.Sets Require Export Pairs Numbers.
Import ListNotations.

(** The set coding a list of sets. *)
Fixpoint list_code (xs : list aczel_set) : aczel_set :=
  match xs with
  | nil => empty_set
  | x :: xs' => ordered_pair x (list_code xs')
  end.

(** Two lists of sets, equal entry by entry. *)
Definition list_set_eq (xs ys : list aczel_set) : Prop := Forall2 set_eq xs ys.

Lemma list_set_eq_refl : forall xs, list_set_eq xs xs.
Proof. induction xs; constructor; [apply set_eq_refl | assumption]. Qed.

Lemma list_set_eq_sym : forall xs ys, list_set_eq xs ys -> list_set_eq ys xs.
Proof. intros xs ys H. induction H; constructor; [apply set_eq_sym; assumption | assumption]. Qed.

Lemma list_set_eq_trans : forall xs ys zs, list_set_eq xs ys -> list_set_eq ys zs -> list_set_eq xs zs.
Proof.
  intros xs ys zs H. revert zs. induction H as [| x y xs ys Hxy H IH]; intros zs H'; inversion H'; subst; constructor.
  - eapply set_eq_trans; eassumption.
  - apply IH. assumption.
Qed.

Lemma list_set_eq_app : forall xs ys xs' ys', list_set_eq xs xs' -> list_set_eq ys ys' -> list_set_eq (xs ++ ys) (xs' ++ ys').
Proof. intros. apply Forall2_app; assumption. Qed.

Lemma list_set_eq_length : forall xs ys, list_set_eq xs ys -> List.length xs = List.length ys.
Proof. intros. eapply Forall2_length. eassumption. Qed.

(** Equal concatenations with equally long first parts have equal parts. *)
Lemma list_set_eq_app_split : forall xs ys xs' ys', list_set_eq (xs ++ ys) (xs' ++ ys') -> List.length xs = List.length xs' ->
    list_set_eq xs xs' /\ list_set_eq ys ys'.
Proof.
  induction xs as [| x xs IH]; intros ys [| x' xs'] ys' H Hl; cbn in *; try discriminate.
  - split; [constructor | exact H].
  - inversion H; subst. destruct (IH _ _ _ ltac:(eassumption) ltac:(congruence)) as [H1 H2].
    split; [constructor; assumption | exact H2].
Qed.

Lemma list_set_eq_skipn : forall n xs ys, list_set_eq xs ys -> list_set_eq (List.skipn n xs) (List.skipn n ys).
Proof.
  induction n; intros xs ys H; [exact H |]. destruct H; cbn; [constructor | apply IHn; assumption].
Qed.

Lemma list_code_resp : forall xs ys, list_set_eq xs ys -> set_eq (list_code xs) (list_code ys).
Proof.
  intros xs ys H. induction H; cbn [list_code]; [apply set_eq_refl | apply ordered_pair_resp; assumption].
Qed.

Lemma list_code_inj : forall xs ys, set_eq (list_code xs) (list_code ys) -> list_set_eq xs ys.
Proof.
  induction xs as [| x xs IH]; intros [| y ys] E; cbn [list_code] in E.
  - constructor.
  - exfalso. exact (ordered_pair_not_empty _ _ (set_eq_sym _ _ E)).
  - exfalso. exact (ordered_pair_not_empty _ _ E).
  - apply ordered_pair_inj in E as [Ex Exs]. constructor; [exact Ex | exact (IH _ Exs)].
Qed.

(** The set of the entries of a list. *)
Fixpoint set_of_list (xs : list aczel_set) : aczel_set :=
  match xs with
  | nil => empty_set
  | x :: xs' => union_set (unordered_pair_set (singleton_set x) (set_of_list xs'))
  end.

Lemma set_mem_set_of_list : forall z xs, set_mem z (set_of_list xs) <-> Exists (set_eq z) xs.
Proof.
  intros z; induction xs as [| x xs IH]; cbn [set_of_list].
  - split; [intros H; exfalso; exact (set_mem_empty _ H) | intros H; inversion H].
  - rewrite set_mem_union. split.
    + intros [w [Hw Hz]]. apply set_mem_unordered_pair in Hw as [Hw | Hw].
      * left. apply set_mem_singleton. eapply set_mem_eq_r; [exact Hw | exact Hz].
      * right. apply IH. eapply set_mem_eq_r; [exact Hw | exact Hz].
    + intros H. inversion H as [? ? Hzx | ? ? Hzs]; subst.
      * exists (singleton_set x). split; [apply set_mem_unordered_pair; left; apply set_eq_refl | apply set_mem_singleton; exact Hzx].
      * exists (set_of_list xs). split; [apply set_mem_unordered_pair; right; apply set_eq_refl | apply IH; exact Hzs].
Qed.

Lemma set_of_list_resp : forall xs ys, list_set_eq xs ys -> set_eq (set_of_list xs) (set_of_list ys).
Proof.
  intros xs ys H. induction H; cbn [set_of_list]; [apply set_eq_refl |].
  apply union_set_resp. apply unordered_pair_set_resp; [apply singleton_set_resp |]; assumption.
Qed.

(** The set coding a name: the numerals of its characters, in order. *)
Fixpoint string_code (s : string) : aczel_set :=
  match s with
  | EmptyString => empty_set
  | String a s' => ordered_pair (numeral_set (nat_of_ascii a)) (string_code s')
  end.

Lemma string_code_inj : forall s s', set_eq (string_code s) (string_code s') -> s = s'.
Proof.
  induction s as [| a s IH]; intros [| a' s'] E; cbn [string_code] in E.
  - reflexivity.
  - exfalso. exact (ordered_pair_not_empty _ _ (set_eq_sym _ _ E)).
  - exfalso. exact (ordered_pair_not_empty _ _ E).
  - apply ordered_pair_inj in E as [Ea Es]. apply numeral_set_inj in Ea.
    rewrite <- (ascii_nat_embedding a), <- (ascii_nat_embedding a'), Ea. f_equal. exact (IH _ Es).
Qed.
