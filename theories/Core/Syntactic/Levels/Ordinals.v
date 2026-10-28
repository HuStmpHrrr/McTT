From Stdlib Require Import Compare_dec Lia PeanoNat Relation_Operators Setoid Wf_nat Lexicographic_Product.

(** * Ordinals below ω²

    A pair [(a, b)] is the ordinal [ω·a + b], and the order is
    lexicographic.  These are the constants of levels and the indices of the
    small universes: [(0, n)] is the finite level [n], [(1, 0)] is [ω].

    Only the operations levels need are here: the join [ordinal_max], the successor
    [ordinal_succ] (which adds [1] on the right: [ω + 1] is [(1, 1)], and there is no
    ordinal addition), and the order.  The join computes on literals of the
    same tier ([ordinal_max (0, n) (0, m) = (0, Nat.max n m)] by [reflexivity]), so
    that finite levels compute as they did on naturals.

    [ord] decides the goals of the linear arithmetic of pairs, the
    counterpart of [lia]. *)

Definition o2 : Set := (nat * nat)%type.

(** The finite ordinal [n].  An abbreviation rather than a definition, so
    that a finite literal is always the pair itself, which the notations of
    the finite levels match on. *)
Abbreviation ofin n := (@pair nat nat 0 n).

Definition ordinal_zero : o2 := (0, 0).

Definition ordinal_lt (x y : o2) : Prop := fst x < fst y \/ (fst x = fst y /\ snd x < snd y).

Definition ordinal_le (x y : o2) : Prop := fst x < fst y \/ (fst x = fst y /\ snd x <= snd y).

Definition ordinal_max (x y : o2) : o2 :=
  if fst x <? fst y then y
  else if fst y <? fst x then x
  else (fst x, Nat.max (snd x) (snd y)).

Definition ordinal_succ (x : o2) : o2 := (fst x, S (snd x)).

(** [x + k], [k] successors *)
Definition ordinal_add_nat (k : nat) (x : o2) : o2 := (fst x, k + snd x).

(** The operations are opaque to [cbn]: a [cbn] would unfold [ordinal_max] to a
    [match] on [Nat.ltb] that [ord] no longer recognises.  They still compute
    by conversion. *)
#[global] Arguments ordinal_max : simpl never.
#[global] Arguments ordinal_succ : simpl never.
#[global] Arguments ordinal_add_nat : simpl never.

(** An ordinal that [ord] treats as opaque: one that is neither a variable
    nor built by the operations above. *)
Ltac o2_atom t :=
  lazymatch type of t with
  | o2 => idtac
  | (nat * nat)%type => idtac
  end;
  lazymatch t with
  | (_, _) => fail
  | ordinal_max _ _ => fail
  | ordinal_succ _ => fail
  | ordinal_add_nat _ _ => fail
  | ordinal_zero => fail
  | _ => tryif is_var t then fail else idtac
  end.

(** Names every opaque ordinal of the goal and of the ordinal hypotheses
    ([=], [ordinal_lt], [ordinal_le]), so that [ord] can split it into its two parts. *)
Ltac ord_abstract :=
  repeat first
    [ match goal with
      | |- context [?t] => o2_atom t; let x := fresh "w" in set (x := t) in *; clearbody x
      end
    | match goal with
      | H : ?T |- _ =>
          lazymatch T with
          | @eq _ _ _ => idtac
          | ordinal_lt _ _ => idtac
          | ordinal_le _ _ => idtac
          | ~ ordinal_lt _ _ => idtac
          | ~ ordinal_le _ _ => idtac
          end;
          match T with
          | context [?t] => o2_atom t; let x := fresh "w" in set (x := t) in *; clearbody x
          end
      end ].

Ltac ord :=
  intros; ord_abstract; unfold ordinal_lt, ordinal_le, ordinal_max, ordinal_succ, ordinal_add_nat, ordinal_zero in *;
  repeat match goal with p : o2 |- _ => destruct p end;
  repeat match goal with p : (nat * nat)%type |- _ => destruct p end;
  cbn [fst snd] in *;
  repeat match goal with
         | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
         | H : context [?a <? ?b] |- _ => destruct (Nat.ltb_spec a b)
         end;
  cbn [fst snd] in *;
  repeat match goal with H : (_, _) = (_, _) |- _ => injection H; clear H; intros end;
  repeat match goal with
         | H : context [(_, _) = (_, _)] |- _ => setoid_rewrite pair_equal_spec in H
         end;
  try (apply pair_equal_spec; split);
  try lia; try (exfalso; lia); intuition lia.

Lemma ordinal_max_fin : forall n m, ordinal_max (ofin n) (ofin m) = ofin (Nat.max n m).
Proof. reflexivity. Qed.

Lemma ordinal_succ_fin : forall n, ordinal_succ (ofin n) = ofin (S n).
Proof. reflexivity. Qed.

Lemma ordinal_lt_irrefl : forall x, ~ ordinal_lt x x. Proof. intros; ord. Qed.
Lemma ordinal_lt_trans : forall x y z, ordinal_lt x y -> ordinal_lt y z -> ordinal_lt x z. Proof. intros; ord. Qed.
Lemma ordinal_lt_ordinal_le_trans : forall x y z, ordinal_lt x y -> ordinal_le y z -> ordinal_lt x z. Proof. intros; ord. Qed.
Lemma ordinal_le_ordinal_lt_trans : forall x y z, ordinal_le x y -> ordinal_lt y z -> ordinal_lt x z. Proof. intros; ord. Qed.
Lemma ordinal_lt_ordinal_le : forall x y, ordinal_lt x y -> ordinal_le x y. Proof. intros; ord. Qed.
Lemma ordinal_le_refl : forall x, ordinal_le x x. Proof. intros; ord. Qed.
Lemma ordinal_le_trans : forall x y z, ordinal_le x y -> ordinal_le y z -> ordinal_le x z. Proof. intros; ord. Qed.
Lemma ordinal_le_antisym : forall x y, ordinal_le x y -> ordinal_le y x -> x = y. Proof. intros; ord. Qed.
Lemma ordinal_le_or_ordinal_lt : forall x y, ordinal_le x y \/ ordinal_lt y x. Proof. intros; ord. Qed.
Lemma ordinal_le_zero : forall x, ordinal_le ordinal_zero x. Proof. intros; ord. Qed.
Lemma ordinal_le_fin : forall n m, n <= m -> ordinal_le (ofin n) (ofin m). Proof. intros; ord. Qed.
Lemma ordinal_lt_fin : forall n m, n < m -> ordinal_lt (ofin n) (ofin m). Proof. intros; ord. Qed.

Lemma ordinal_max_comm : forall x y, ordinal_max x y = ordinal_max y x. Proof. intros; ord. Qed.
Lemma ordinal_max_assoc : forall x y z, ordinal_max (ordinal_max x y) z = ordinal_max x (ordinal_max y z). Proof. intros; ord. Qed.
Lemma ordinal_max_idem : forall x, ordinal_max x x = x. Proof. intros; ord. Qed.
Lemma ordinal_max_zero_l : forall x, ordinal_max ordinal_zero x = x. Proof. intros; ord. Qed.
Lemma ordinal_max_zero_r : forall x, ordinal_max x ordinal_zero = x. Proof. intros; ord. Qed.
Lemma ordinal_le_ordinal_max_l : forall x y, ordinal_le x (ordinal_max x y). Proof. intros; ord. Qed.
Lemma ordinal_le_ordinal_max_r : forall x y, ordinal_le y (ordinal_max x y). Proof. intros; ord. Qed.
Lemma ordinal_max_lub : forall x y z, ordinal_le x z -> ordinal_le y z -> ordinal_le (ordinal_max x y) z. Proof. intros; ord. Qed.
Lemma ordinal_max_lub_lt : forall x y z, ordinal_lt x z -> ordinal_lt y z -> ordinal_lt (ordinal_max x y) z. Proof. intros; ord. Qed.
Lemma ordinal_max_r : forall x y, ordinal_le x y -> ordinal_max x y = y. Proof. intros; ord. Qed.
Lemma ordinal_max_l : forall x y, ordinal_le y x -> ordinal_max x y = x. Proof. intros; ord. Qed.
Lemma ordinal_succ_ordinal_max : forall x y, ordinal_succ (ordinal_max x y) = ordinal_max (ordinal_succ x) (ordinal_succ y). Proof. intros; ord. Qed.
Lemma ordinal_le_ordinal_succ : forall x, ordinal_le x (ordinal_succ x). Proof. intros; ord. Qed.
Lemma ordinal_lt_ordinal_succ : forall x, ordinal_lt x (ordinal_succ x). Proof. intros; ord. Qed.
Lemma ordinal_lt_ordinal_succ_ordinal_le : forall x y, ordinal_lt x (ordinal_succ y) <-> ordinal_le x y. Proof. intros; ord. Qed.
Lemma ordinal_succ_mono : forall x y, ordinal_le x y -> ordinal_le (ordinal_succ x) (ordinal_succ y). Proof. intros; ord. Qed.
Lemma ordinal_succ_inj : forall x y, ordinal_succ x = ordinal_succ y -> x = y. Proof. intros; ord. Qed.
Lemma ordinal_max_fst_le : forall x y n, fst x <= n -> fst y <= n -> fst (ordinal_max x y) <= n. Proof. intros; ord. Qed.
Lemma ordinal_succ_fst : forall x, fst (ordinal_succ x) = fst x. Proof. reflexivity. Qed.

Definition o2_eq_dec : forall x y : o2, {x = y} + {x <> y}.
Proof. intros [a b] [c d]; decide equality; apply Nat.eq_dec. Defined.

Definition ordinal_lt_dec : forall x y, {ordinal_lt x y} + {~ ordinal_lt x y}.
Proof.
  intros [a b] [c d]; unfold ordinal_lt; cbn.
  destruct (lt_dec a c); [ left; auto |].
  destruct (Nat.eq_dec a c); [| right; lia ].
  destruct (lt_dec b d); [ left; auto | right; lia ].
Defined.

Definition ordinal_le_dec : forall x y, {ordinal_le x y} + {~ ordinal_le x y}.
Proof.
  intros [a b] [c d]; unfold ordinal_le; cbn.
  destruct (lt_dec a c); [ left; auto |].
  destruct (Nat.eq_dec a c); [| right; lia ].
  destruct (le_dec b d); [ left; auto | right; lia ].
Defined.

(** The order is the standard library's strict lexicographic product of
    [lt] with itself, so its well-foundedness is [wf_slexprod]. *)
Lemma ordinal_lt_slexprod : forall x y, ordinal_lt x y <-> slexprod nat nat lt lt x y.
Proof.
  intros [a b] [c d]; unfold ordinal_lt; cbn; split.
  - intros [H | [-> H]]; [ apply left_slex; exact H | apply right_slex; exact H ].
  - intros H; inversion H; subst; [ left; assumption | right; split; [ reflexivity | assumption ] ].
Qed.

Lemma ordinal_lt_wf : well_founded ordinal_lt.
Proof.
  intros x; pose proof (wf_slexprod nat nat lt lt lt_wf lt_wf x) as H.
  induction H as [x _ IH]; constructor; intros y Hy; apply IH, ordinal_lt_slexprod, Hy.
Qed.
