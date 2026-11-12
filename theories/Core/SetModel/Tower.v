(** * The Universe Tower

    The hypothesis of the consistency theorems: one universe of sets per
    universe index of McTT ([universe_index]: [Type@{L}] at each level
    below ω², then [Typeω@i]), each a Grothendieck universe, smaller ones
    members of larger ones.  It is a hypothesis, not an axiom: by Gödel's
    second incompleteness theorem no proof inside Rocq can give McTT's
    consistency, and the record is satisfiable in a set-theoretic model of
    Rocq with enough inaccessible cardinals (V_κ for each index).

    A level's value is the von Neumann ordinal of its index
    ([universe_index_set]); [small_universe_set] gives the universe at a
    level value, the universe of [Type@{L}]. *)

From Mctt.Core.SetModel.Sets Require Export Grothendieck Ordinals.
From Mctt.Core.Syntactic Require Import Syntax.

(** One universe of sets per universe index of McTT. *)
Record universe_tower : Type := mk_universe_tower
  { (** The universe of [Type@{L}] at the level index [us o], and of
        [Typeω@i] at [ul i] *)
    tower : universe_index -> aczel_set
    (** Each is a universe of sets *)
  ; tower_grothendieck : forall i, grothendieck (tower i)
    (** A smaller universe is a member of a larger one *)
  ; tower_increasing : forall i j, universe_index_lt i j -> set_mem (tower i) (tower j) }.

(** The ordinal of a universe index: [ω·a + b] at [us (a, b)], [ω² + k] at
    [ul k]. *)
Definition universe_index_set (i : universe_index) : aczel_set :=
  match i with
  | us o => pair_ordinal_set o
  | ul k => large_ordinal_set k
  end.

Lemma universe_index_set_lt : forall i j, universe_index_lt i j -> set_mem (universe_index_set i) (universe_index_set j).
Proof.
  intros [o | k] [o' | k'] H; cbn in H |- *.
  - apply pair_ordinal_set_lt. exact H.
  - apply pair_ordinal_set_below_large.
  - destruct H.
  - apply large_ordinal_set_lt. exact H.
Qed.

Lemma universe_index_set_inj : forall i j, set_eq (universe_index_set i) (universe_index_set j) -> i = j.
Proof.
  intros [o | k] [o' | k'] E; cbn in E.
  - f_equal. apply pair_ordinal_set_inj. exact E.
  - exfalso. exact (pair_large_ordinal_set_distinct _ _ E).
  - exfalso. exact (pair_large_ordinal_set_distinct _ _ (set_eq_sym _ _ E)).
  - f_equal. apply large_ordinal_set_inj. exact E.
Qed.

Section Tower.
  Variable T : universe_tower.

(** A smaller universe is included in a larger one. *)
Lemma tower_sub : forall i j, universe_index_le i j -> set_sub (tower T i) (tower T j).
Proof.
  intros [o | k] [o' | k'] H x Hx; cbn in H.
  - destruct (o2_eq_dec o o') as [<- | Hne]; [exact Hx |].
    apply (grothendieck_transitive _ (tower_grothendieck T (us o')) (tower T (us o))); [| exact Hx].
    apply tower_increasing. cbn. unfold ordinal_le, ordinal_lt in *.
    destruct o as [a b], o' as [a' b']; cbn in *. destruct H as [H | [-> H]]; [left; exact H |].
    right. split; [reflexivity |]. destruct (PeanoNat.Nat.eq_dec b b') as [-> | Hb]; [exfalso; apply Hne; reflexivity |].
    apply PeanoNat.Nat.le_neq; split; assumption.
  - apply (grothendieck_transitive _ (tower_grothendieck T (ul k')) (tower T (us o))); [apply tower_increasing; exact I | exact Hx].
  - destruct H.
  - destruct (PeanoNat.Nat.eq_dec k k') as [<- | Hne]; [exact Hx |].
    apply (grothendieck_transitive _ (tower_grothendieck T (ul k')) (tower T (ul k))); [| exact Hx].
    apply tower_increasing. cbn. apply PeanoNat.Nat.le_neq; split; assumption.
Qed.

(** The universe at a level value [l]: the tower at the small index whose
    ordinal [l] is, empty when [l] is no such ordinal. *)
Definition small_universe_set (l : aczel_set) : aczel_set :=
  union_set (family_set {o : o2 | set_eq l (pair_ordinal_set o)} (fun p => tower T (us (proj1_sig p)))).

Lemma set_mem_small_universe : forall l x, set_mem x (small_universe_set l) <->
    exists o, set_eq l (pair_ordinal_set o) /\ set_mem x (tower T (us o)).
Proof.
  intros l x. unfold small_universe_set. rewrite set_mem_union. split.
  - intros [w [[[o Ho] Hw] Hx]]. exists o. split; [exact Ho | eapply set_mem_eq_r; [exact Hw | exact Hx]].
  - intros [o [Ho Hx]]. exists (tower T (us o)). split; [exists (exist _ o Ho); apply set_eq_refl | exact Hx].
Qed.

(** At the ordinal of a small index, the universe is the tower there. *)
Lemma small_universe_set_eq : forall l o, set_eq l (pair_ordinal_set o) -> set_eq (small_universe_set l) (tower T (us o)).
Proof.
  intros l o Ho. apply set_eq_intro; intros x Hx.
  - apply set_mem_small_universe in Hx as [o' [Ho' Hx]].
    assert (o' = o) as -> by (apply pair_ordinal_set_inj; eapply set_eq_trans; [apply set_eq_sym; exact Ho' | exact Ho]).
    exact Hx.
  - apply set_mem_small_universe. exists o. split; assumption.
Qed.

Lemma small_universe_set_resp : forall l l', set_eq l l' -> set_eq (small_universe_set l) (small_universe_set l').
Proof.
  intros l l' E. apply set_eq_intro; intros x Hx; apply set_mem_small_universe in Hx as [o [Ho Hx]]; apply set_mem_small_universe;
    exists o; split; try exact Hx.
  - eapply set_eq_trans; [apply set_eq_sym; exact E | exact Ho].
  - eapply set_eq_trans; [exact E | exact Ho].
Qed.

End Tower.
