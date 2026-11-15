(** * Truth Values and Codes

    A proposition of the set model is a subsingleton: [truth_set P], whose
    only possible member is the empty set, there exactly when [P] holds.
    A type is a code: a tag, a datum and the carrier, the set of its
    elements.  A proposition's code has the tag [prop_tag] and its truth
    set as carrier, so a proof is the empty set. *)

From Mctt.Core.SetModel.Sets Require Export Pairs Numbers.

(** ** Truth Values *)

(** The subsingleton of [P]: the empty set, when [P] holds. *)
Definition truth_set (P : Prop) : aczel_set := family_set P (fun _ => empty_set).

Lemma set_mem_truth : forall z P, set_mem z (truth_set P) <-> P /\ set_eq z empty_set.
Proof. intros z P. split; [intros [p H]; auto | intros [p H]; exists p; exact H]. Qed.

Lemma truth_set_eq : forall P Q, set_eq (truth_set P) (truth_set Q) <-> (P <-> Q).
Proof.
  intros P Q. rewrite set_extensionality. split.
  - intros H. split; intros p.
    + destruct (proj1 (H empty_set) (proj2 (set_mem_truth _ _) (conj p (set_eq_refl _)))) as [q _]. exact q.
    + destruct (proj2 (H empty_set) (proj2 (set_mem_truth _ _) (conj p (set_eq_refl _)))) as [q _]. exact q.
  - intros E z. rewrite !set_mem_truth. tauto.
Qed.

(** ** Codes *)

(** The code of tag [t], datum [d] and carrier [c]. *)
Definition type_code (t : nat) (d c : aczel_set) : aczel_set := ordered_pair (numeral_set t) (ordered_pair d c).

(** The carrier of a code: the set of its elements. *)
Definition code_carrier (C : aczel_set) : aczel_set := pair_second (pair_second C).

(** The datum of a code. *)
Definition code_datum (C : aczel_set) : aczel_set := pair_first (pair_second C).

Lemma code_carrier_type_code : forall t d c, set_eq (code_carrier (type_code t d c)) c.
Proof.
  intros. unfold code_carrier, type_code.
  eapply set_eq_trans; [apply pair_second_resp; apply pair_second_ordered_pair | apply pair_second_ordered_pair].
Qed.

Lemma code_datum_type_code : forall t d c, set_eq (code_datum (type_code t d c)) d.
Proof.
  intros. unfold code_datum, type_code.
  eapply set_eq_trans; [apply pair_first_resp; apply pair_second_ordered_pair | apply pair_first_ordered_pair].
Qed.

Lemma code_carrier_resp : forall C C', set_eq C C' -> set_eq (code_carrier C) (code_carrier C').
Proof. intros. unfold code_carrier. apply pair_second_resp, pair_second_resp. auto. Qed.

Lemma type_code_inj : forall t d c t' d' c', set_eq (type_code t d c) (type_code t' d' c') ->
    t = t' /\ set_eq d d' /\ set_eq c c'.
Proof.
  intros * E. apply ordered_pair_inj in E as [Et E]. apply ordered_pair_inj in E as [Ed Ec].
  apply numeral_set_inj in Et. auto.
Qed.

Lemma type_code_resp : forall t d c d' c', set_eq d d' -> set_eq c c' -> set_eq (type_code t d c) (type_code t d' c').
Proof. intros. unfold type_code. apply ordered_pair_resp; [apply set_eq_refl | apply ordered_pair_resp; auto]. Qed.

(** ** Propositions *)

(** The tag of the codes of propositions. *)
Definition prop_tag : nat := 0.

(** The code of the proposition [P]. *)
Definition prop_code (P : Prop) : aczel_set := type_code prop_tag empty_set (truth_set P).

(** The set of the codes of propositions: the carrier of [Prop]. *)
Definition prop_codes_set : aczel_set := family_set Prop prop_code.

(** A code is a proposition's. *)
Definition is_prop_code (C : aczel_set) : Prop := exists P, set_eq C (prop_code P).

(** A code is a relevant type's: of another tag than a proposition's. *)
Definition is_relevant_code (C : aczel_set) : Prop := exists t d c, set_eq C (type_code t d c) /\ t <> prop_tag.

(** A proposition's code is true: the empty set is its element. *)
Definition prop_true (C : aczel_set) : Prop := set_mem empty_set (code_carrier C).

Lemma is_prop_code_resp : respects_set_eq is_prop_code.
Proof. intros x y E [P H]. exists P. eapply set_eq_trans; [apply set_eq_sym; exact E | exact H]. Qed.

Lemma is_relevant_code_resp : respects_set_eq is_relevant_code.
Proof. intros x y E [t [d [c [H Ht]]]]. exists t, d, c. split; [eapply set_eq_trans; [apply set_eq_sym; exact E | exact H] | exact Ht]. Qed.

Lemma prop_true_resp : respects_set_eq prop_true.
Proof. intros C C' E H. unfold prop_true in *. eapply set_mem_eq_r; [apply code_carrier_resp; exact E | exact H]. Qed.

Lemma prop_true_prop_code : forall P, prop_true (prop_code P) <-> P.
Proof.
  intros P. unfold prop_true, prop_code. split.
  - intros H. eapply set_mem_eq_r in H; [| apply code_carrier_type_code]. apply set_mem_truth in H. tauto.
  - intros p. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply set_mem_truth. split; [exact p | apply set_eq_refl].
Qed.

Lemma prop_code_eq : forall P Q, set_eq (prop_code P) (prop_code Q) <-> (P <-> Q).
Proof.
  intros P Q. split.
  - intros E. apply type_code_inj in E as [_ [_ E]]. apply truth_set_eq. exact E.
  - intros E. apply type_code_resp; [apply set_eq_refl | apply truth_set_eq; exact E].
Qed.

(** The members of a proposition's code are the empty set: proofs are
    irrelevant. *)
Lemma prop_code_carrier_empty : forall C z, is_prop_code C -> set_mem z (code_carrier C) -> set_eq z empty_set.
Proof.
  intros C z [P E] Hz. eapply set_mem_eq_r in Hz; [| eapply set_eq_trans; [apply code_carrier_resp; exact E | apply code_carrier_type_code]].
  apply set_mem_truth in Hz. tauto.
Qed.
