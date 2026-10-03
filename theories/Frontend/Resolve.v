From Stdlib Require Import Lia List PeanoNat Relation_Operators String.


(** * Names in Scope

    The elaborator resolves a name by its position in a list of names: a
    parameter of an open frame is the variable of its index. *)

Fixpoint index_of (x : string) (xs : list string) : option nat :=
  match xs with
  | nil => None
  | y :: xs' => if String.eqb x y then Some 0 else option_map S (index_of x xs')
  end.

(** * Import Depths

    Starting at [0] and replacing the depth [n] by [max(n, m + 1)] for each
    import of depth [m] assigns every module the length of the longest import
    chain below it.  Such a ranking exists exactly when the import graph is
    acyclic: [depth_acyclic] and [depths_ranks] are the two directions. *)
Section ImportDepth.

  (** A finite import graph in declaration order: node [i] imports the nodes
      listed in [nth i g nil]. *)
  Definition graph : Set := list (list nat).

  Definition edge (g : graph) (i j : nat) : Prop :=
    i < List.length g /\ List.In j (List.nth i g nil).

  Definition ranks (g : graph) (d : list nat) : Prop :=
    forall i j, edge g i j -> List.nth j d 0 < List.nth i d 0.

  Lemma ranks_clos_trans : forall g d,
      ranks g d ->
      forall i j, clos_trans nat (edge g) i j -> List.nth j d 0 < List.nth i d 0.
  Proof.
    induction 2; [ eauto | lia ].
  Qed.

  (** A ranked graph has no import cycles. *)
  Theorem depth_acyclic : forall g d,
      ranks g d ->
      forall i, ~ clos_trans nat (edge g) i i.
  Proof.
    intros * Hr * Hc.
    pose proof (ranks_clos_trans _ _ Hr _ _ Hc). lia.
  Qed.

  (** Conversely, depths exist for a graph in declaration order, which is
      every acyclic graph up to a topological sort. *)
  Definition ordered (g : graph) : Prop := forall i j, edge g i j -> j < i.

  Definition rank_of (d : list nat) (is : list nat) : nat :=
    List.fold_left (fun n j => Nat.max n (S (List.nth j d 0))) is 0.

  Fixpoint depths_from (d : list nat) (g : graph) : list nat :=
    match g with
    | nil => d
    | is :: g' => depths_from (d ++ cons (rank_of d is) nil) g'
    end.

  Definition depths (g : graph) : list nat := depths_from nil g.

  Lemma rank_of_acc : forall is d n,
      n <= List.fold_left (fun n j => Nat.max n (S (List.nth j d 0))) is n.
  Proof.
    induction is; intros; simpl; [ lia |].
    transitivity (Nat.max n (S (List.nth a d 0))); [ lia | auto ].
  Qed.

  Lemma rank_of_gt : forall is d j,
      List.In j is ->
      List.nth j d 0 < rank_of d is.
  Proof.
    unfold rank_of. intros * Hin.
    enough (forall n, List.nth j d 0 < List.fold_left (fun n j => Nat.max n (S (List.nth j d 0))) is n) by auto.
    induction is; intros; simpl in *; [ contradiction |].
    destruct Hin as [-> |]; [| auto ].
    pose proof (rank_of_acc is d (Nat.max n (S (List.nth j d 0)))). lia.
  Qed.

  Lemma depths_from_prefix : forall g d, exists e, depths_from d g = d ++ e.
  Proof.
    induction g; intros; simpl.
    - exists nil. rewrite app_nil_r. reflexivity.
    - destruct (IHg (d ++ cons (rank_of d a) nil)) as [e ->].
      exists (rank_of d a :: e). rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma depths_from_nth_low : forall g d j,
      j < List.length d ->
      List.nth j (depths_from d g) 0 = List.nth j d 0.
  Proof.
    intros * ?.
    destruct (depths_from_prefix g d) as [e ->].
    rewrite app_nth1; auto.
  Qed.

  Lemma depths_from_ranks : forall g d,
      (forall i j, i < List.length g -> List.In j (List.nth i g nil) -> j < List.length d + i) ->
      forall i j, i < List.length g ->
             List.In j (List.nth i g nil) ->
             List.nth j (depths_from d g) 0 < List.nth (List.length d + i) (depths_from d g) 0.
  Proof.
    induction g as [| is g IHg]; intros * Hlt * Hi Hin; simpl in *; [ lia |].
    destruct i as [| i]; simpl in *.
    - pose proof (Hlt 0 j Hi Hin) as Hj. rewrite Nat.add_0_r in *.
      rewrite depths_from_nth_low by (rewrite length_app; simpl; lia).
      destruct (depths_from_prefix g (d ++ cons (rank_of d is) nil)) as [e Heq].
      rewrite Heq, <- app_assoc, app_nth1 by lia.
      rewrite app_nth2, Nat.sub_diag by lia.
      simpl. apply rank_of_gt. assumption.
    - replace (List.length d + S i) with (List.length (d ++ cons (rank_of d is) nil) + i)
        by (rewrite length_app; simpl; lia).
      apply IHg; auto with arith.
      intros i' j' Hi' Hin'. rewrite length_app. simpl.
      specialize (Hlt (S i') j' (proj1 (Nat.succ_lt_mono _ _) Hi') Hin'). lia.
  Qed.

  Theorem depths_ranks : forall g, ordered g -> ranks g (depths g).
  Proof.
    unfold ranks, depths, ordered, edge. intros * Hord * [? ?].
    replace i with (List.length (@nil nat) + i) by (simpl; lia).
    apply depths_from_ranks; simpl; auto.
  Qed.

  (** The depth rule rules out cycles. *)
  Corollary ordered_acyclic : forall g,
      ordered g ->
      forall i, ~ clos_trans nat (edge g) i i.
  Proof.
    intros. eapply depth_acyclic, depths_ranks. assumption.
  Qed.

End ImportDepth.
