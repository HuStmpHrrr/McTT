(** * Natural Numbers as Sets

    The von Neumann successor, the finite ordinals [numeral_set n] and the
    set [omega_set] of them. *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From Mctt.Core.SetModel.Sets Require Export Aczel.

(** The successor of a set: [x ∪ {x}]. *)
Definition successor_set (x : aczel_set) : aczel_set := union_set (unordered_pair_set x (singleton_set x)).

Lemma set_mem_successor : forall z x, set_mem z (successor_set x) <-> set_mem z x \/ set_eq z x.
Proof.
  intros z x. unfold successor_set. rewrite set_mem_union. split.
  - intros [w [Hw Hz]]. apply set_mem_unordered_pair in Hw as [H | H].
    + left. eapply set_mem_eq_r; eauto.
    + right. apply set_mem_singleton. eapply set_mem_eq_r; eauto.
  - intros [H | H].
    + exists x. split; [apply set_mem_unordered_pair; left; apply set_eq_refl | exact H].
    + exists (singleton_set x). split; [apply set_mem_unordered_pair; right; apply set_eq_refl | apply set_mem_singleton; exact H].
Qed.

Lemma successor_set_resp : forall x y, set_eq x y -> set_eq (successor_set x) (successor_set y).
Proof. intros. unfold successor_set. apply union_set_resp. apply unordered_pair_set_resp; [| apply singleton_set_resp]; auto. Qed.

(** The finite ordinal [n]. *)
Fixpoint numeral_set (n : nat) : aczel_set :=
  match n with 0 => empty_set | S m => successor_set (numeral_set m) end.

Lemma set_mem_numeral : forall n z, set_mem z (numeral_set n) <-> exists k, k < n /\ set_eq z (numeral_set k).
Proof.
  induction n; intros z; cbn.
  - split; [intros H; exfalso; exact (set_mem_empty _ H) | intros [k [Hk _]]; lia].
  - rewrite set_mem_successor, IHn. split.
    + intros [[k [Hk E]] | E]; [exists k; split; [lia | exact E] | exists n; split; [lia | exact E]].
    + intros [k [Hk E]]. destruct (Nat.eq_dec k n) as [-> | Ne]; [right; exact E | left; exists k; split; [lia | exact E]].
Qed.

Lemma numeral_set_irrefl : forall n, ~ set_mem (numeral_set n) (numeral_set n).
Proof.
  induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros H.
  apply set_mem_numeral in H as [k [Hk E]]. apply (IH k Hk).
  eapply set_mem_eq_r; [exact E |]. apply set_mem_numeral. exists k. split; [exact Hk | apply set_eq_refl].
Qed.

Lemma numeral_set_inj : forall n m, set_eq (numeral_set n) (numeral_set m) -> n = m.
Proof.
  intros n m E. destruct (Nat.lt_trichotomy n m) as [Hl | [Heq | Hl]]; [exfalso | exact Heq | exfalso].
  - apply (numeral_set_irrefl n). eapply set_mem_eq_r; [apply set_eq_sym; exact E |].
    apply set_mem_numeral. exists n. split; [exact Hl | apply set_eq_refl].
  - apply (numeral_set_irrefl m). eapply set_mem_eq_r; [exact E |].
    apply set_mem_numeral. exists m. split; [exact Hl | apply set_eq_refl].
Qed.

(** The set of the finite ordinals. *)
Definition omega_set : aczel_set := family_set nat numeral_set.
