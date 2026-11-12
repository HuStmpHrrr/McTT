(** * Aczel Sets

    The sets of the set model: well-founded trees [aczel_sup A f], with an
    index type [A] and the children [f]; equality ([set_eq]) is
    bisimulation, and membership ([set_mem]) is being equal to a child.
    Rocq's impredicative [Prop] gives separation and power sets
    ([separation_set], [power_set]).  Everything is constructive, without
    axioms, and nothing here mentions the syntax of McTT. *)

From Stdlib Require Export Setoid.

(** A set: a family of sets indexed by a type. *)
Inductive aczel_set : Type :=
(** The set of the members [f a], for every index [a : A] *)
| aczel_sup (A : Type) (f : A -> aczel_set).

(** The index type of a set. *)
Definition aczel_index (x : aczel_set) : Type := match x with aczel_sup A _ => A end.

(** The member of a set at an index. *)
Definition aczel_element (x : aczel_set) : aczel_index x -> aczel_set :=
  match x with aczel_sup _ f => f end.

(** Equality of sets: every member of each is equal to a member of the
    other. *)
Fixpoint set_eq (x y : aczel_set) {struct x} : Prop :=
  match x, y with
  | aczel_sup A f, aczel_sup B g =>
      (forall a, exists b, set_eq (f a) (g b)) /\ (forall b, exists a, set_eq (f a) (g b))
  end.

Lemma set_eq_refl : forall x, set_eq x x.
Proof. fix IH 1. intros [A f]. cbn. split; intros a; exists a; apply IH. Qed.

Lemma set_eq_sym : forall x y, set_eq x y -> set_eq y x.
Proof.
  fix IH 1. intros [A f] [B g] [H1 H2]. cbn. split.
  - intros b. destruct (H2 b) as [a Ha]. exists a. apply IH. exact Ha.
  - intros a. destruct (H1 a) as [b Hb]. exists b. apply IH. exact Hb.
Qed.

Lemma set_eq_trans : forall x y z, set_eq x y -> set_eq y z -> set_eq x z.
Proof.
  fix IH 1. intros [A f] [B g] [C h] [H1 H2] [K1 K2]. cbn. split.
  - intros a. destruct (H1 a) as [b Hb]. destruct (K1 b) as [c Hc]. exists c. eapply IH; eauto.
  - intros c. destruct (K2 c) as [b Hb]. destruct (H2 b) as [a Ha]. exists a. eapply IH; eauto.
Qed.

(** Membership: [z] is equal to a member of [x]. *)
Definition set_mem (z x : aczel_set) : Prop := exists a : aczel_index x, set_eq z (aczel_element x a).

(** Inclusion. *)
Definition set_sub (x y : aczel_set) : Prop := forall z, set_mem z x -> set_mem z y.

Lemma set_mem_eq_l : forall z z' x, set_eq z z' -> set_mem z x -> set_mem z' x.
Proof. intros z z' x E [a Ha]. exists a. eapply set_eq_trans; [apply set_eq_sym; exact E | exact Ha]. Qed.

Lemma set_mem_eq_r : forall z x x', set_eq x x' -> set_mem z x -> set_mem z x'.
Proof.
  intros z [A f] [B g] [H1 H2] [a Ha]. cbn in *. destruct (H1 a) as [b Hb]. exists b. eapply set_eq_trans; eauto.
Qed.

(** Extensionality: two sets are equal exactly when they have the same
    members. *)
Lemma set_extensionality : forall x y, set_eq x y <-> (forall z, set_mem z x <-> set_mem z y).
Proof.
  intros [A f] [B g]. split.
  - intros E z. split; intros Hz; [eapply set_mem_eq_r; eauto | eapply set_mem_eq_r; [apply set_eq_sym; exact E | exact Hz]].
  - intros H. cbn. split.
    + intros a. assert (Hm : set_mem (f a) (aczel_sup A f)) by (exists a; apply set_eq_refl).
      destruct (proj1 (H _) Hm) as [b Hb]. exists b. exact Hb.
    + intros b. assert (Hm : set_mem (g b) (aczel_sup B g)) by (exists b; apply set_eq_refl).
      destruct (proj2 (H _) Hm) as [a Ha]. exists a. apply set_eq_sym. exact Ha.
Qed.

Lemma set_eq_intro : forall x y, (forall z, set_mem z x -> set_mem z y) -> (forall z, set_mem z y -> set_mem z x) -> set_eq x y.
Proof. intros x y H1 H2. apply set_extensionality. intros z; split; auto. Qed.

(** Well-foundedness: no set is a member of itself. *)
Lemma set_mem_irrefl : forall x, ~ set_mem x x.
Proof.
  induction x as [A f IH]. intros [a Ha].
  apply (IH a). eapply set_mem_eq_r; [exact Ha |]. exists a. apply set_eq_refl.
Qed.

(** A predicate on sets that respects equality. *)
Definition respects_set_eq (P : aczel_set -> Prop) : Prop := forall x y, set_eq x y -> P x -> P y.

(** A function on sets that respects equality. *)
Definition respects_set_eq_fun (F : aczel_set -> aczel_set) : Prop := forall x y, set_eq x y -> set_eq (F x) (F y).

(** ** Constructions *)

(** The set of a family of sets indexed by a type. *)
Definition family_set (A : Type) (f : A -> aczel_set) : aczel_set := aczel_sup A f.

Lemma set_mem_family : forall A f z, set_mem z (family_set A f) <-> exists a, set_eq z (f a).
Proof. intros. exact (iff_refl _). Qed.

(** The empty set. *)
Definition empty_set : aczel_set := aczel_sup False (fun e => match e with end).

Lemma set_mem_empty : forall z, ~ set_mem z empty_set.
Proof. intros z [[] _]. Qed.

(** The set whose one member is [x]. *)
Definition singleton_set (x : aczel_set) : aczel_set := aczel_sup unit (fun _ => x).

Lemma set_mem_singleton : forall z x, set_mem z (singleton_set x) <-> set_eq z x.
Proof. intros. split; [intros [u H]; exact H | intros H; exists tt; exact H]. Qed.

(** The set whose members are [x] and [y]. *)
Definition unordered_pair_set (x y : aczel_set) : aczel_set := aczel_sup bool (fun b => if b then x else y).

Lemma set_mem_unordered_pair : forall z x y, set_mem z (unordered_pair_set x y) <-> set_eq z x \/ set_eq z y.
Proof.
  intros. split.
  - intros [[|] H]; auto.
  - intros [H | H]; [exists true | exists false]; exact H.
Qed.

(** The union of the members of [X]. *)
Definition union_set (X : aczel_set) : aczel_set :=
  aczel_sup {a : aczel_index X & aczel_index (aczel_element X a)}
    (fun p => aczel_element (aczel_element X (projT1 p)) (projT2 p)).

Lemma set_mem_union : forall z X, set_mem z (union_set X) <-> exists w, set_mem w X /\ set_mem z w.
Proof.
  intros z X. split.
  - intros [[a b] H]. exists (aczel_element X a). split; [exists a; apply set_eq_refl | exists b; exact H].
  - intros [w [[a Ha] Hz]]. pose proof (set_mem_eq_r _ _ _ Ha Hz) as [b Hb]. exists (existT _ a b). exact Hb.
Qed.

(** The members of [X] satisfying [P]. *)
Definition separation_set (X : aczel_set) (P : aczel_set -> Prop) : aczel_set :=
  aczel_sup {a : aczel_index X | P (aczel_element X a)} (fun p => aczel_element X (proj1_sig p)).

Lemma set_mem_separation : forall z X P, respects_set_eq P -> (set_mem z (separation_set X P) <-> set_mem z X /\ P z).
Proof.
  intros z X P HP. split.
  - intros [[a Pa] H]. split; [exists a; exact H | eapply HP; [apply set_eq_sym; exact H | exact Pa]].
  - intros [[a Ha] Pz]. exists (exist _ a (HP _ _ Ha Pz)). exact Ha.
Qed.

(** The subsets of [X]. *)
Definition power_set (X : aczel_set) : aczel_set :=
  aczel_sup (aczel_index X -> Prop) (fun S => aczel_sup {a : aczel_index X | S a} (fun p => aczel_element X (proj1_sig p))).

Lemma set_mem_power : forall z X, set_mem z (power_set X) <-> set_sub z X.
Proof.
  intros z X. split.
  - intros [S H] w Hw. pose proof (set_mem_eq_r _ _ _ H Hw) as [[a Sa] Ha]. exists a. exact Ha.
  - intros Hs. exists (fun a => set_mem (aczel_element X a) z). apply set_eq_intro.
    + intros w Hw. destruct (Hs _ Hw) as [a Ha].
      assert (Hm : set_mem (aczel_element X a) z) by (eapply set_mem_eq_l; [exact Ha | exact Hw]).
      exists (exist _ a Hm). exact Ha.
    + intros w [[a Ha] Hw]. cbn in Hw. eapply set_mem_eq_l; [apply set_eq_sym; exact Hw | exact Ha].
Qed.

(** ** The Constructions Respect Equality *)

Lemma singleton_set_resp : forall x y, set_eq x y -> set_eq (singleton_set x) (singleton_set y).
Proof.
  intros x y E. apply set_eq_intro; intros z Hz; apply set_mem_singleton; apply set_mem_singleton in Hz;
    [eapply set_eq_trans; eauto | eapply set_eq_trans; [exact Hz | apply set_eq_sym; exact E]].
Qed.

Lemma unordered_pair_set_resp : forall x y x' y', set_eq x x' -> set_eq y y' ->
    set_eq (unordered_pair_set x y) (unordered_pair_set x' y').
Proof.
  intros * E1 E2. apply set_eq_intro; intros z Hz; apply set_mem_unordered_pair; apply set_mem_unordered_pair in Hz;
    destruct Hz as [H | H].
  - left. eapply set_eq_trans; eauto.
  - right. eapply set_eq_trans; eauto.
  - left. eapply set_eq_trans; [exact H | apply set_eq_sym; exact E1].
  - right. eapply set_eq_trans; [exact H | apply set_eq_sym; exact E2].
Qed.

Lemma union_set_resp : forall X Y, set_eq X Y -> set_eq (union_set X) (union_set Y).
Proof.
  intros X Y E. apply set_eq_intro; intros z Hz; apply set_mem_union; apply set_mem_union in Hz;
    destruct Hz as [w [Hw Hz]]; exists w; split; auto.
  - eapply set_mem_eq_r; eauto.
  - eapply set_mem_eq_r; [apply set_eq_sym; exact E | exact Hw].
Qed.

Lemma separation_set_resp : forall X Y P Q, respects_set_eq P -> respects_set_eq Q -> set_eq X Y ->
    (forall z, set_mem z X -> (P z <-> Q z)) -> set_eq (separation_set X P) (separation_set Y Q).
Proof.
  intros * HP HQ E EPQ. apply set_eq_intro; intros z Hz.
  - apply (set_mem_separation _ _ _ HP) in Hz as [Hz Pz]. apply (set_mem_separation _ _ _ HQ).
    split; [eapply set_mem_eq_r; eauto | apply EPQ; auto].
  - apply (set_mem_separation _ _ _ HQ) in Hz as [Hz Qz].
    assert (HzX : set_mem z X) by (eapply set_mem_eq_r; [apply set_eq_sym; exact E | exact Hz]).
    apply (set_mem_separation _ _ _ HP). split; [exact HzX | apply EPQ; auto].
Qed.

Lemma power_set_resp : forall X Y, set_eq X Y -> set_eq (power_set X) (power_set Y).
Proof.
  intros X Y E. apply set_eq_intro; intros z Hz; apply set_mem_power; apply set_mem_power in Hz; intros w Hw;
    [eapply set_mem_eq_r; [exact E | apply Hz; exact Hw] | eapply set_mem_eq_r; [apply set_eq_sym; exact E | apply Hz; exact Hw]].
Qed.

(** The union of a nonempty set whose members are all equal to [y] is [y]. *)
Lemma union_set_const : forall X y, (exists w, set_mem w X) -> (forall w, set_mem w X -> set_eq w y) ->
    set_eq (union_set X) y.
Proof.
  intros X y [w0 Hw0] H. apply set_eq_intro.
  - intros z Hz. apply set_mem_union in Hz as [w [Hw Hz]]. eapply set_mem_eq_r; [apply H; exact Hw | exact Hz].
  - intros z Hz. apply set_mem_union. exists w0. split; auto.
    eapply set_mem_eq_r; [apply set_eq_sym; apply H; exact Hw0 | exact Hz].
Qed.

(** The member of [S] with the property [P], when there is one and only
    one up to equality: a definite description, without choice. *)
Definition set_describe (S : aczel_set) (P : aczel_set -> Prop) : aczel_set := union_set (separation_set S P).

Lemma set_describe_eq : forall S P z, respects_set_eq P -> set_mem z S -> P z ->
    (forall w, set_mem w S -> P w -> set_eq w z) -> set_eq (set_describe S P) z.
Proof.
  intros S P z HP Hz Pz Hu. apply union_set_const.
  - exists z. apply (set_mem_separation _ _ _ HP). split; assumption.
  - intros w Hw. apply (set_mem_separation _ _ _ HP) in Hw as [Hw Pw]. exact (Hu _ Hw Pw).
Qed.
