(** * The Ordinals Below ω²+ω as Sets

    The von Neumann ordinals [ω·a + b] ([pair_ordinal_set (a, b)]) and
    [ω² + k] ([large_ordinal_set k]): the values of McTT's universe
    indices.  Smaller ordinals are members of larger ones, so distinct
    indices give distinct sets. *)

From Stdlib Require Import PeanoNat Lia.
From Mctt.Core.SetModel.Sets Require Export Numbers.

(** [n] successors of [x]. *)
Fixpoint iterate_successor (n : nat) (x : aczel_set) : aczel_set :=
  match n with 0 => x | S m => successor_set (iterate_successor m x) end.

(** The limit ordinal [ω·a]. *)
Fixpoint limit_ordinal_set (a : nat) : aczel_set :=
  match a with
  | 0 => empty_set
  | S a' => union_set (family_set nat (fun n => iterate_successor n (limit_ordinal_set a')))
  end.

(** The ordinal [ω²]. *)
Definition omega_square_set : aczel_set := union_set (family_set nat limit_ordinal_set).

(** The ordinal [ω·a + b] of the pair [(a, b)]. *)
Definition pair_ordinal_set (o : nat * nat) : aczel_set := iterate_successor (snd o) (limit_ordinal_set (fst o)).

(** The ordinal [ω² + k]. *)
Definition large_ordinal_set (k : nat) : aczel_set := iterate_successor k omega_square_set.

(** The lexicographic order of pairs: [ω·a + b < ω·a' + b']. *)
Definition pair_lt (x y : nat * nat) : Prop := fst x < fst y \/ (fst x = fst y /\ snd x < snd y).

Lemma iterate_successor_numeral : forall n, iterate_successor n empty_set = numeral_set n.
Proof. induction n; cbn; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma set_sub_successor : forall x, set_sub x (successor_set x).
Proof. intros x z Hz. apply set_mem_successor. left. exact Hz. Qed.

Lemma set_mem_successor_self : forall x, set_mem x (successor_set x).
Proof. intros x. apply set_mem_successor. right. apply set_eq_refl. Qed.

Lemma set_sub_iterate_successor : forall n x, set_sub x (iterate_successor n x).
Proof. induction n; intros x z Hz; cbn; [exact Hz | apply set_sub_successor; apply IHn; exact Hz]. Qed.

Lemma iterate_successor_add : forall k m x, iterate_successor k (iterate_successor m x) = iterate_successor (k + m) x.
Proof. induction k; intros; cbn; [reflexivity | rewrite IHk; reflexivity]. Qed.

Lemma set_mem_iterate_successor : forall b b' x, b < b' -> set_mem (iterate_successor b x) (iterate_successor b' x).
Proof.
  intros b b' x H. replace b' with ((b' - S b) + S b) by lia. rewrite <- iterate_successor_add.
  apply set_sub_iterate_successor. cbn. apply set_mem_successor_self.
Qed.

Lemma set_mem_limit_ordinal_succ : forall a b, set_mem (iterate_successor b (limit_ordinal_set a)) (limit_ordinal_set (S a)).
Proof.
  intros a b. cbn [limit_ordinal_set]. apply set_mem_union. exists (iterate_successor (S b) (limit_ordinal_set a)).
  split; [exists (S b); apply set_eq_refl | apply set_mem_successor_self].
Qed.

Lemma set_sub_limit_ordinal_succ : forall a, set_sub (limit_ordinal_set a) (limit_ordinal_set (S a)).
Proof.
  intros a z Hz. cbn [limit_ordinal_set]. apply set_mem_union. exists (limit_ordinal_set a).
  split; [exists 0; apply set_eq_refl | exact Hz].
Qed.

Lemma set_sub_limit_ordinal : forall a a', a <= a' -> set_sub (limit_ordinal_set a) (limit_ordinal_set a').
Proof. intros a a' H. induction H; intros z Hz; [exact Hz | apply set_sub_limit_ordinal_succ; apply IHle; exact Hz]. Qed.

Lemma set_sub_limit_ordinal_omega_square : forall a, set_sub (limit_ordinal_set a) omega_square_set.
Proof. intros a z Hz. apply set_mem_union. exists (limit_ordinal_set a). split; [exists a; apply set_eq_refl | exact Hz]. Qed.

Lemma pair_ordinal_set_lt : forall x y, pair_lt x y -> set_mem (pair_ordinal_set x) (pair_ordinal_set y).
Proof.
  intros [a b] [a' b'] [H | [H1 H2]]; cbn in *; unfold pair_ordinal_set; cbn.
  - apply set_sub_iterate_successor. apply (set_sub_limit_ordinal (S a) a'); [lia | apply set_mem_limit_ordinal_succ].
  - subst a'. apply set_mem_iterate_successor. exact H2.
Qed.

Lemma pair_ordinal_set_below_large : forall x k, set_mem (pair_ordinal_set x) (large_ordinal_set k).
Proof.
  intros [a b] k. unfold pair_ordinal_set, large_ordinal_set; cbn.
  apply set_sub_iterate_successor. apply (set_sub_limit_ordinal_omega_square (S a)). apply set_mem_limit_ordinal_succ.
Qed.

Lemma large_ordinal_set_lt : forall k k', k < k' -> set_mem (large_ordinal_set k) (large_ordinal_set k').
Proof. intros. apply set_mem_iterate_successor. assumption. Qed.

Lemma pair_lt_trichotomy : forall x y, x = y \/ pair_lt x y \/ pair_lt y x.
Proof.
  intros [a b] [a' b']; unfold pair_lt; cbn.
  destruct (Nat.lt_trichotomy a a') as [H | [-> | H]]; [right; left; left; exact H | | right; right; left; exact H].
  destruct (Nat.lt_trichotomy b b') as [H | [-> | H]]; [right; left; right; auto | left; reflexivity | right; right; right; auto].
Qed.

Lemma pair_ordinal_set_inj : forall x y, set_eq (pair_ordinal_set x) (pair_ordinal_set y) -> x = y.
Proof.
  intros x y E. destruct (pair_lt_trichotomy x y) as [H | [H | H]]; [exact H | |]; exfalso.
  - apply (set_mem_irrefl (pair_ordinal_set y)). eapply set_mem_eq_l; [exact E | exact (pair_ordinal_set_lt _ _ H)].
  - apply (set_mem_irrefl (pair_ordinal_set y)). eapply set_mem_eq_r; [exact E | exact (pair_ordinal_set_lt _ _ H)].
Qed.

Lemma large_ordinal_set_inj : forall k k', set_eq (large_ordinal_set k) (large_ordinal_set k') -> k = k'.
Proof.
  intros k k' E. destruct (Nat.lt_trichotomy k k') as [H | [H | H]]; [exfalso | exact H | exfalso].
  - apply (set_mem_irrefl (large_ordinal_set k')). eapply set_mem_eq_l; [exact E | exact (large_ordinal_set_lt _ _ H)].
  - apply (set_mem_irrefl (large_ordinal_set k')). eapply set_mem_eq_r; [exact E | exact (large_ordinal_set_lt _ _ H)].
Qed.

Lemma pair_large_ordinal_set_distinct : forall x k, ~ set_eq (pair_ordinal_set x) (large_ordinal_set k).
Proof.
  intros x k E. apply (set_mem_irrefl (large_ordinal_set k)).
  eapply set_mem_eq_l; [exact E | apply pair_ordinal_set_below_large].
Qed.

Lemma pair_ordinal_set_finite : forall n, set_eq (pair_ordinal_set (0, n)) (numeral_set n).
Proof. intros n. unfold pair_ordinal_set; cbn. rewrite iterate_successor_numeral. apply set_eq_refl. Qed.

Lemma pair_ordinal_set_omega : set_eq (pair_ordinal_set (1, 0)) omega_set.
Proof.
  change (set_eq (union_set (family_set nat (fun n => iterate_successor n empty_set))) omega_set).
  apply set_eq_intro; intros z Hz.
  - apply set_mem_union in Hz as [w [[n Hw] Hz]]. eapply set_mem_eq_r in Hz; [| exact Hw]. cbn [family_set aczel_element] in Hz.
    rewrite iterate_successor_numeral in Hz. apply set_mem_numeral in Hz as [k [_ Ek]]. exists k. exact Ek.
  - destruct Hz as [k Ek]. apply set_mem_union. exists (iterate_successor (S k) empty_set).
    split; [exists (S k); apply set_eq_refl |].
    rewrite iterate_successor_numeral. eapply set_mem_eq_l; [apply set_eq_sym; exact Ek | apply set_mem_successor_self].
Qed.

(** ** The Members of an Ordinal Below ω² *)

Lemma set_mem_iterate_limit : forall a, (forall z, set_mem z (limit_ordinal_set a) -> exists x, pair_lt x (a, 0) /\ set_eq z (pair_ordinal_set x)) ->
    forall b z, set_mem z (iterate_successor b (limit_ordinal_set a)) -> exists x, pair_lt x (a, b) /\ set_eq z (pair_ordinal_set x).
Proof.
  intros a Ha. induction b as [| b IH]; intros z Hz; cbn [iterate_successor] in Hz.
  - exact (Ha z Hz).
  - apply set_mem_successor in Hz as [Hz | Hz].
    + destruct (IH z Hz) as [x [Hx E]]. exists x. split; [| exact E]. unfold pair_lt in *; cbn in *. lia.
    + exists (a, b). split; [unfold pair_lt; cbn; lia | exact Hz].
Qed.

Lemma set_mem_limit_ordinal : forall a z, set_mem z (limit_ordinal_set a) -> exists x, pair_lt x (a, 0) /\ set_eq z (pair_ordinal_set x).
Proof.
  induction a as [| a IH]; intros z Hz; cbn [limit_ordinal_set] in Hz; [destruct (set_mem_empty _ Hz) |].
  apply set_mem_union in Hz as [w [[n Ew] Hz]]. eapply set_mem_eq_r in Hz; [| exact Ew]. cbn in Hz.
  destruct (set_mem_iterate_limit a IH n z Hz) as [x [Hx E]]. exists x. split; [| exact E]. unfold pair_lt in *; cbn in *. lia.
Qed.

(** The members of [ω·a + b] are the smaller ordinals. *)
Lemma set_mem_pair_ordinal : forall y z, set_mem z (pair_ordinal_set y) <-> exists x, pair_lt x y /\ set_eq z (pair_ordinal_set x).
Proof.
  intros [a b] z. split.
  - intros Hz. exact (set_mem_iterate_limit a (set_mem_limit_ordinal a) b z Hz).
  - intros [x [Hx E]]. eapply set_mem_eq_l; [apply set_eq_sym; exact E | apply pair_ordinal_set_lt; exact Hx].
Qed.

Lemma pair_lt_trans : forall x y z, pair_lt x y -> pair_lt y z -> pair_lt x z.
Proof. intros [a b] [a' b'] [a'' b'']; unfold pair_lt; cbn; lia. Qed.

(** A smaller ordinal is included in a larger one. *)
Lemma pair_ordinal_set_sub : forall x y, pair_lt x y \/ x = y -> set_sub (pair_ordinal_set x) (pair_ordinal_set y).
Proof.
  intros x y [H | <-] z Hz; [| exact Hz].
  apply set_mem_pair_ordinal in Hz as [w [Hw E]]. apply set_mem_pair_ordinal. exists w. split; [eapply pair_lt_trans; eassumption | exact E].
Qed.

(** The larger of two ordinals. *)
Definition pair_max (x y : nat * nat) : nat * nat :=
  if Nat.ltb (fst x) (fst y) then y
  else if Nat.ltb (fst y) (fst x) then x
  else (fst x, Nat.max (snd x) (snd y)).

Lemma pair_max_cases : forall x y, (pair_lt x y \/ x = y) /\ pair_max x y = y \/ (pair_lt y x \/ x = y) /\ pair_max x y = x.
Proof.
  intros [a b] [a' b']. unfold pair_max, pair_lt; cbn [fst snd].
  destruct (Nat.ltb_spec a a'); [left; split; [left; left; exact H | reflexivity] |].
  destruct (Nat.ltb_spec a' a); [right; split; [left; left; exact H0 | reflexivity] |].
  assert (a = a') by lia. subst a'.
  destruct (Nat.lt_trichotomy b b') as [Hb | [<- | Hb]].
  - left. split; [left; right; split; [reflexivity | exact Hb] |]. f_equal. lia.
  - left. split; [right; reflexivity |]. f_equal. lia.
  - right. split; [left; right; split; [reflexivity | exact Hb] |]. f_equal. lia.
Qed.

(** The union of two ordinals is the larger. *)
Lemma union_pair_ordinal_set : forall x y,
    set_eq (union_set (unordered_pair_set (pair_ordinal_set x) (pair_ordinal_set y))) (pair_ordinal_set (pair_max x y)).
Proof.
  intros x y. apply set_eq_intro; intros z Hz.
  - apply set_mem_union in Hz as [w [Hw Hz]]. apply set_mem_unordered_pair in Hw.
    destruct (pair_max_cases x y) as [[Hle ->] | [Hle ->]]; destruct Hw as [Ew | Ew]; eapply set_mem_eq_r in Hz; try exact Ew;
      first [exact Hz | apply (pair_ordinal_set_sub _ _ Hle); exact Hz | idtac].
    + destruct Hle as [Hle | <-]; [apply (pair_ordinal_set_sub _ _ (or_introl Hle)); exact Hz | exact Hz].
  - apply set_mem_union. destruct (pair_max_cases x y) as [[_ E] | [_ E]]; rewrite E in Hz.
    + exists (pair_ordinal_set y). split; [apply set_mem_unordered_pair; right; apply set_eq_refl | exact Hz].
    + exists (pair_ordinal_set x). split; [apply set_mem_unordered_pair; left; apply set_eq_refl | exact Hz].
Qed.
