From Stdlib Require Import Compare_dec Lia PeanoNat Relation_Operators Setoid Wf_nat Lexicographic_Product.

(** * Ordinals below ω²

    A pair [(a, b)] is the ordinal [ω·a + b], and the order is
    lexicographic.  These are the constants of levels and the indices of the
    small universes: [(0, n)] is the finite level [n], [(1, 0)] is [ω].

    Only the operations levels need are here: the join [omax], the successor
    [osuc] (which adds [1] on the right: [ω + 1] is [(1, 1)], and there is no
    ordinal addition), and the order.  The join computes on literals of the
    same tier ([omax (0, n) (0, m) = (0, Nat.max n m)] by [reflexivity]), so
    that finite levels compute as they did on naturals.

    [ord] decides the goals of the linear arithmetic of pairs, the
    counterpart of [lia]. *)

Definition o2 : Set := (nat * nat)%type.

(** The finite ordinal [n].  An abbreviation rather than a definition, so
    that a finite literal is always the pair itself, which the notations of
    the finite levels match on. *)
Abbreviation ofin n := (@pair nat nat 0 n).

Definition oz : o2 := (0, 0).

Definition olt (x y : o2) : Prop := fst x < fst y \/ (fst x = fst y /\ snd x < snd y).

Definition ole (x y : o2) : Prop := fst x < fst y \/ (fst x = fst y /\ snd x <= snd y).

Definition omax (x y : o2) : o2 :=
  if fst x <? fst y then y
  else if fst y <? fst x then x
  else (fst x, Nat.max (snd x) (snd y)).

Definition osuc (x : o2) : o2 := (fst x, S (snd x)).

(** [x + k], [k] successors *)
Definition osucn (k : nat) (x : o2) : o2 := (fst x, k + snd x).

(** The operations are opaque to [cbn]: a [cbn] would unfold [omax] to a
    [match] on [Nat.ltb] that [ord] no longer recognises.  They still compute
    by conversion. *)
#[global] Arguments omax : simpl never.
#[global] Arguments osuc : simpl never.
#[global] Arguments osucn : simpl never.

(** An ordinal that [ord] treats as opaque: one that is neither a variable
    nor built by the operations above. *)
Ltac o2_atom t :=
  lazymatch type of t with
  | o2 => idtac
  | (nat * nat)%type => idtac
  end;
  lazymatch t with
  | (_, _) => fail
  | omax _ _ => fail
  | osuc _ => fail
  | osucn _ _ => fail
  | oz => fail
  | _ => tryif is_var t then fail else idtac
  end.

(** Names every opaque ordinal of the goal and of the ordinal hypotheses
    ([=], [olt], [ole]), so that [ord] can split it into its two parts. *)
Ltac ord_abstract :=
  repeat first
    [ match goal with
      | |- context [?t] => o2_atom t; let x := fresh "w" in set (x := t) in *; clearbody x
      end
    | match goal with
      | H : ?T |- _ =>
          lazymatch T with
          | @eq _ _ _ => idtac
          | olt _ _ => idtac
          | ole _ _ => idtac
          | ~ olt _ _ => idtac
          | ~ ole _ _ => idtac
          end;
          match T with
          | context [?t] => o2_atom t; let x := fresh "w" in set (x := t) in *; clearbody x
          end
      end ].

Ltac ord :=
  intros; ord_abstract; unfold olt, ole, omax, osuc, osucn, oz in *;
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

Lemma omax_fin : forall n m, omax (ofin n) (ofin m) = ofin (Nat.max n m).
Proof. reflexivity. Qed.

Lemma osuc_fin : forall n, osuc (ofin n) = ofin (S n).
Proof. reflexivity. Qed.

Lemma olt_irrefl : forall x, ~ olt x x. Proof. intros; ord. Qed.
Lemma olt_trans : forall x y z, olt x y -> olt y z -> olt x z. Proof. intros; ord. Qed.
Lemma olt_ole_trans : forall x y z, olt x y -> ole y z -> olt x z. Proof. intros; ord. Qed.
Lemma ole_olt_trans : forall x y z, ole x y -> olt y z -> olt x z. Proof. intros; ord. Qed.
Lemma olt_ole : forall x y, olt x y -> ole x y. Proof. intros; ord. Qed.
Lemma ole_refl : forall x, ole x x. Proof. intros; ord. Qed.
Lemma ole_trans : forall x y z, ole x y -> ole y z -> ole x z. Proof. intros; ord. Qed.
Lemma ole_antisym : forall x y, ole x y -> ole y x -> x = y. Proof. intros; ord. Qed.
Lemma ole_or_olt : forall x y, ole x y \/ olt y x. Proof. intros; ord. Qed.
Lemma ole_zero : forall x, ole oz x. Proof. intros; ord. Qed.
Lemma ole_fin : forall n m, n <= m -> ole (ofin n) (ofin m). Proof. intros; ord. Qed.
Lemma olt_fin : forall n m, n < m -> olt (ofin n) (ofin m). Proof. intros; ord. Qed.

Lemma omax_comm : forall x y, omax x y = omax y x. Proof. intros; ord. Qed.
Lemma omax_assoc : forall x y z, omax (omax x y) z = omax x (omax y z). Proof. intros; ord. Qed.
Lemma omax_idem : forall x, omax x x = x. Proof. intros; ord. Qed.
Lemma omax_zero_l : forall x, omax oz x = x. Proof. intros; ord. Qed.
Lemma omax_zero_r : forall x, omax x oz = x. Proof. intros; ord. Qed.
Lemma ole_omax_l : forall x y, ole x (omax x y). Proof. intros; ord. Qed.
Lemma ole_omax_r : forall x y, ole y (omax x y). Proof. intros; ord. Qed.
Lemma omax_lub : forall x y z, ole x z -> ole y z -> ole (omax x y) z. Proof. intros; ord. Qed.
Lemma omax_lub_lt : forall x y z, olt x z -> olt y z -> olt (omax x y) z. Proof. intros; ord. Qed.
Lemma omax_r : forall x y, ole x y -> omax x y = y. Proof. intros; ord. Qed.
Lemma omax_l : forall x y, ole y x -> omax x y = x. Proof. intros; ord. Qed.
Lemma osuc_omax : forall x y, osuc (omax x y) = omax (osuc x) (osuc y). Proof. intros; ord. Qed.
Lemma ole_osuc : forall x, ole x (osuc x). Proof. intros; ord. Qed.
Lemma olt_osuc : forall x, olt x (osuc x). Proof. intros; ord. Qed.
Lemma olt_osuc_ole : forall x y, olt x (osuc y) <-> ole x y. Proof. intros; ord. Qed.
Lemma osuc_mono : forall x y, ole x y -> ole (osuc x) (osuc y). Proof. intros; ord. Qed.
Lemma osuc_inj : forall x y, osuc x = osuc y -> x = y. Proof. intros; ord. Qed.
Lemma omax_fst_le : forall x y n, fst x <= n -> fst y <= n -> fst (omax x y) <= n. Proof. intros; ord. Qed.
Lemma osuc_fst : forall x, fst (osuc x) = fst x. Proof. reflexivity. Qed.

Definition o2_eq_dec : forall x y : o2, {x = y} + {x <> y}.
Proof. intros [a b] [c d]; decide equality; apply Nat.eq_dec. Defined.

Definition olt_dec : forall x y, {olt x y} + {~ olt x y}.
Proof.
  intros [a b] [c d]; unfold olt; cbn.
  destruct (lt_dec a c); [ left; auto |].
  destruct (Nat.eq_dec a c); [| right; lia ].
  destruct (lt_dec b d); [ left; auto | right; lia ].
Defined.

Definition ole_dec : forall x y, {ole x y} + {~ ole x y}.
Proof.
  intros [a b] [c d]; unfold ole; cbn.
  destruct (lt_dec a c); [ left; auto |].
  destruct (Nat.eq_dec a c); [| right; lia ].
  destruct (le_dec b d); [ left; auto | right; lia ].
Defined.

(** The order is the standard library's strict lexicographic product of
    [lt] with itself, so its well-foundedness is [wf_slexprod]. *)
Lemma olt_slexprod : forall x y, olt x y <-> slexprod nat nat lt lt x y.
Proof.
  intros [a b] [c d]; unfold olt; cbn; split.
  - intros [H | [-> H]]; [ apply left_slex; exact H | apply right_slex; exact H ].
  - intros H; inversion H; subst; [ left; assumption | right; split; [ reflexivity | assumption ] ].
Qed.

Lemma olt_wf : well_founded olt.
Proof.
  intros x; pose proof (wf_slexprod nat nat lt lt lt_wf lt_wf x) as H.
  induction H as [x _ IH]; constructor; intros y Hy; apply IH, olt_slexprod, Hy.
Qed.
