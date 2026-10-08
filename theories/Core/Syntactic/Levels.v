From Stdlib Require Import Ascii Lia List PeanoNat String.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** * Canonical Levels

    A level is flat: [max (c, k₁ + a₁, …, kₙ + aₙ)], a constant and a finite
    multiset of atoms under offsets, where an atom is a neutral normal form.
    Evaluation only flattens, so the same level has many flat forms; readback
    canonicalises, and the canonical form is unique:

    - the atoms are strictly sorted by [ne_cmp] and so without repetition,
      duplicates having been merged at the larger offset;
    - the constant is [0] unless it exceeds every offset, a smaller one being
      dominated.

    [lvl_canon_iff]: two levels have the same canonical form exactly when they
    agree under every assignment of ordinals below ω² to atoms.  That is the
    uniqueness-of-normal-forms theorem for levels, and with it the level
    equations ([maxl] is a semilattice, [succl] distributes over it, and a
    level is below its successor) hold on canonical forms.  [lvl_le] is the
    decidable order the universe subtyping rule uses. *)

(** ** A Total Order on Normal Forms

    The order is structural, with variables first by de Bruijn index; it is
    obtained by coding a normal form into a tree of naturals, and ordering
    those lexicographically.  Only the three properties of a strict total
    order are needed, so they are proved once for the trees and transported
    along the coding, which is injective.

    A tree node is [lt_node lbl child sibling]: the coding is first child,
    next sibling, so the children of a node are its [sibling]-chain. *)
Inductive ltree : Set :=
| lt_nil : ltree
| lt_node : nat -> ltree -> ltree -> ltree.

Fixpoint lt_cmp (s t : ltree) : comparison :=
  match s, t with
  | lt_nil, lt_nil => Eq
  | lt_nil, _ => Lt
  | _, lt_nil => Gt
  | lt_node a c r, lt_node b c' r' =>
      match Nat.compare a b with
      | Eq => match lt_cmp c c' with
             | Eq => lt_cmp r r'
             | x => x
             end
      | x => x
      end
  end.

Lemma lt_cmp_eq : forall s t, lt_cmp s t = Eq <-> s = t.
Proof.
  induction s as [| a c IHc r IHr]; intros [| b c' r']; cbn; split; intros H;
    try discriminate; try reflexivity.
  - destruct (Nat.compare_spec a b); try discriminate.
    destruct (lt_cmp c c') eqn:E; try discriminate.
    apply IHc in E; apply IHr in H; subst; reflexivity.
  - injection H as -> -> ->.
    rewrite Nat.compare_refl.
    assert (lt_cmp c' c' = Eq) as -> by (apply IHc; reflexivity).
    apply IHr; reflexivity.
Qed.

Lemma lt_cmp_refl : forall s, lt_cmp s s = Eq.
Proof. intros; apply lt_cmp_eq; reflexivity. Qed.

Lemma lt_cmp_opp : forall s t, lt_cmp t s = CompOpp (lt_cmp s t).
Proof.
  induction s as [| a c IHc r IHr]; intros [| b c' r']; cbn; try reflexivity.
  rewrite (Nat.compare_antisym a b), IHc.
  destruct (Nat.compare a b); cbn; try reflexivity.
  destruct (lt_cmp c c'); cbn; auto.
Qed.

Lemma lt_cmp_trans : forall s t u, lt_cmp s t = Lt -> lt_cmp t u = Lt -> lt_cmp s u = Lt.
Proof.
  induction s as [| a c IHc r IHr]; intros [| b c' r'] [| d c'' r'']; cbn;
    intros H1 H2; try discriminate; try reflexivity.
  destruct (Nat.compare_spec a b), (Nat.compare_spec b d), (Nat.compare_spec a d);
    subst; try lia; try discriminate; try reflexivity.
  destruct (lt_cmp c c') eqn:E1, (lt_cmp c' c'') eqn:E2; try discriminate.
  - apply lt_cmp_eq in E1, E2; subst.
    rewrite lt_cmp_refl; eapply IHr; eassumption.
  - apply lt_cmp_eq in E1; subst; rewrite E2; reflexivity.
  - apply lt_cmp_eq in E2; subst; rewrite E1; reflexivity.
  - rewrite (IHc _ _ E1 E2); reflexivity.
Qed.

(** The coding of strings and qualified names, which a global's neutral
    carries. *)
Fixpoint str_code (x : string) (t : ltree) : ltree :=
  match x with
  | EmptyString => lt_node 0 lt_nil t
  | String ch r => lt_node (S (nat_of_ascii ch)) lt_nil (str_code r t)
  end.

Fixpoint strs_code (l : list string) (t : ltree) : ltree :=
  match l with
  | nil => lt_node 0 lt_nil t
  | x :: r => lt_node 1 (str_code x lt_nil) (strs_code r t)
  end.

(** A qualified name is coded by its two lists.  Both codings are stuck
    fixpoints on a projection, so [injection] stops there and
    [qname_code_inj] takes the hypothesis apart. *)
#[global] Arguments str_code : simpl never.
#[global] Arguments strs_code : simpl never.

Lemma str_code_inj : forall x y t t', str_code x t = str_code y t' -> x = y /\ t = t'.
Proof.
  induction x as [| ch x IH]; intros [| ch' y] t t' H; cbn in H; injection H as; subst;
    try discriminate; try (split; reflexivity).
  match goal with Hs : str_code _ _ = str_code _ _ |- _ => apply IH in Hs as [-> ->] end.
  split; [| reflexivity].
  f_equal.
  rewrite <- (ascii_nat_embedding ch), <- (ascii_nat_embedding ch'); congruence.
Qed.

Lemma strs_code_inj : forall l l' t t', strs_code l t = strs_code l' t' -> l = l' /\ t = t'.
Proof.
  induction l as [| x l IH]; intros [| y l'] t t' H; cbn in H; injection H as; subst;
    try discriminate; try (split; reflexivity).
  match goal with H : str_code _ _ = str_code _ _ |- _ => apply str_code_inj in H as [-> _] end.
  match goal with H : strs_code _ _ = strs_code _ _ |- _ => apply IH in H as [-> ->] end.
  split; reflexivity.
Qed.

Lemma qname_code_inj : forall p p',
    strs_code (q_unit p) (strs_code (q_chain p) lt_nil)
    = strs_code (q_unit p') (strs_code (q_chain p') lt_nil) -> p = p'.
Proof.
  intros [u ch] [u' ch'] H; cbn in H.
  apply strs_code_inj in H as [-> H]; apply strs_code_inj in H as [-> _]; reflexivity.
Qed.

(** The coding of normal forms.  The tags order the constructors; in a
    neutral, [ne_var] comes first, so variables precede every other atom and
    are ordered by their index. *)
Fixpoint nf_code (M : nf) (t : ltree) : ltree :=
  match M with
  | nf_typ i => lt_node 0 (lt_node i lt_nil lt_nil) t
  | nf_univ (a, b) xs => lt_node 1 (lt_node a (lt_node b (la_code xs lt_nil) lt_nil) lt_nil) t
  | nf_level => lt_node 2 lt_nil t
  | nf_lvl (a, b) xs => lt_node 3 (lt_node a (lt_node b (la_code xs lt_nil) lt_nil) lt_nil) t
  | nf_nat => lt_node 4 lt_nil t
  | nf_zero => lt_node 5 lt_nil t
  | nf_succ M' => lt_node 6 (nf_code M' lt_nil) t
  | nf_True => lt_node 7 lt_nil t
  | nf_true => lt_node 8 lt_nil t
  | nf_False => lt_node 9 lt_nil t
  | nf_pi A B => lt_node 10 (nf_code A (nf_code B lt_nil)) t
  | nf_fn A M' => lt_node 11 (nf_code A (nf_code M' lt_nil)) t
  | nf_neut m => lt_node 12 (ne_code m lt_nil) t
  end
with ne_code (m : ne) (t : ltree) : ltree :=
  match m with
  | ne_var x => lt_node 0 (lt_node x lt_nil lt_nil) t
  | ne_glob p => lt_node 1 (strs_code (q_unit p) (strs_code (q_chain p) lt_nil)) t
  | ne_app m' N => lt_node 2 (ne_code m' (nf_code N lt_nil)) t
  | ne_natrec A MZ MS m' => lt_node 3 (nf_code A (nf_code MZ (nf_code MS (ne_code m' lt_nil)))) t
  | ne_exfalso A m' => lt_node 4 (nf_code A (ne_code m' lt_nil)) t
  end
with la_code (xs : lvl_atoms) (t : ltree) : ltree :=
  match xs with
  | la_nil => lt_node 0 lt_nil t
  | la_cons k m r => lt_node 1 (lt_node k (ne_code m lt_nil) lt_nil) (la_code r t)
  end.

Lemma nf_code_inj : forall M N t t', nf_code M t = nf_code N t' -> M = N /\ t = t'
with ne_code_inj : forall m m' t t', ne_code m t = ne_code m' t' -> m = m' /\ t = t'
with la_code_inj : forall xs ys t t', la_code xs t = la_code ys t' -> xs = ys /\ t = t'.
Proof.
  all: [> destruct M, N | destruct m, m' | destruct xs, ys ].
  all: repeat match goal with p : o2 |- _ => destruct p end.
  all: intros t t' H; cbn in H; injection H as; subst; try discriminate.
  all: repeat match goal with
         | H : nf_code _ _ = nf_code _ _ |- _ => apply nf_code_inj in H as [-> H]
         | H : ne_code _ _ = ne_code _ _ |- _ => apply ne_code_inj in H as [-> H]
         | H : la_code _ _ = la_code _ _ |- _ => apply la_code_inj in H as [-> H]
         | H : strs_code _ _ = strs_code _ _ |- _ => apply qname_code_inj in H as ->
       end.
  all: split; first [ reflexivity | assumption ].
Qed.

(** The order on the atoms of a level. *)
Definition ne_cmp (m m' : ne) : comparison := lt_cmp (ne_code m lt_nil) (ne_code m' lt_nil).

Lemma ne_cmp_eq : forall m m', ne_cmp m m' = Eq <-> m = m'.
Proof.
  intros; unfold ne_cmp; rewrite lt_cmp_eq; split; [| intros ->; reflexivity ].
  intros H; apply ne_code_inj in H as [-> _]; reflexivity.
Qed.

Lemma ne_cmp_refl : forall m, ne_cmp m m = Eq.
Proof. intros; apply ne_cmp_eq; reflexivity. Qed.

Lemma ne_cmp_opp : forall m m', ne_cmp m' m = CompOpp (ne_cmp m m').
Proof. intros; apply lt_cmp_opp. Qed.

Lemma ne_cmp_trans : forall m m' m'', ne_cmp m m' = Lt -> ne_cmp m' m'' = Lt -> ne_cmp m m'' = Lt.
Proof. intros; eapply lt_cmp_trans; eassumption. Qed.

(** ** Levels and Their Canonical Forms

    A level is a constant, an ordinal below ω², and a list of atoms under
    finite offsets.  [lvl_ev ν] evaluates it at an assignment [ν] of
    ordinals below ω² to atoms; two levels are equal exactly when they agree
    at every [ν].  An atom ranges over all of ω², so a constant [ω] does not
    absorb an atom ([max (ω, u)] is not [ω]: take [u := ω + 1]).  The type
    [lvl] itself is in [Core.Syntactic.Syntax], with the normal forms it
    indexes. *)
Fixpoint la_ev (ν : ne -> o2) (xs : lvl_atoms) : o2 :=
  match xs with
  | la_nil => oz
  | la_cons k a r => omax (osucn k (ν a)) (la_ev ν r)
  end.

Definition lvl_ev (ν : ne -> o2) (l : lvl) : o2 := omax (fst l) (la_ev ν (snd l)).

Definition lvl_zero : lvl := (oz, la_nil).

Fixpoint la_suc (xs : lvl_atoms) : lvl_atoms :=
  match xs with
  | la_nil => la_nil
  | la_cons k a r => la_cons (S k) a (la_suc r)
  end.

Definition lvl_suc (l : lvl) : lvl := (osuc (fst l), la_suc (snd l)).

Fixpoint la_app (xs ys : lvl_atoms) : lvl_atoms :=
  match xs with
  | la_nil => ys
  | la_cons k a r => la_cons k a (la_app r ys)
  end.

Definition lvl_max (l l' : lvl) : lvl := (omax (fst l) (fst l'), la_app (snd l) (snd l')).

(** Insertion into a sorted list of atoms, merging at the larger offset. *)
Fixpoint la_ins (k : nat) (a : ne) (ys : lvl_atoms) : lvl_atoms :=
  match ys with
  | la_nil => la_cons k a la_nil
  | la_cons k' b r =>
      match ne_cmp a b with
      | Lt => la_cons k a ys
      | Eq => la_cons (Nat.max k k') b r
      | Gt => la_cons k' b (la_ins k a r)
      end
  end.

Fixpoint la_sort (xs : lvl_atoms) : lvl_atoms :=
  match xs with
  | la_nil => la_nil
  | la_cons k a r => la_ins k a (la_sort r)
  end.

Fixpoint la_maxoff (xs : lvl_atoms) : nat :=
  match xs with
  | la_nil => 0
  | la_cons k _ r => Nat.max k (la_maxoff r)
  end.

(** A constant is dominated by atoms whose largest offset is [m] when it is
    at most [m]: that is the least value of the atoms, at the assignment of
    [0] to every atom.  A constant [≥ ω] is never dominated. *)
Definition o2_dominated (c : o2) (m : nat) : bool := (fst c =? 0) && (snd c <=? m).

Lemma o2_dominated_spec : forall c m, o2_dominated c m = true <-> ole c (ofin m).
Proof.
  intros [a b] m; unfold o2_dominated; cbn.
  rewrite Bool.andb_true_iff, Nat.eqb_eq, Nat.leb_le; ord.
Qed.

(** The canonical form: sort and merge the atoms, then drop the constant if
    the atoms dominate it. *)
Definition lvl_canon (l : lvl) : lvl :=
  let ys := la_sort (snd l) in
  (if o2_dominated (fst l) (la_maxoff ys) then oz else fst l, ys).

Lemma la_ev_ins : forall ν k a ys, la_ev ν (la_ins k a ys) = omax (osucn k (ν a)) (la_ev ν ys).
Proof.
  induction ys as [| k' b r IH]; cbn; [ reflexivity |].
  destruct (ne_cmp a b) eqn:E; cbn.
  - apply ne_cmp_eq in E; subst; generalize (ν b) (la_ev ν r); intros; ord.
  - reflexivity.
  - rewrite IH; generalize (ν a) (ν b) (la_ev ν r); intros; ord.
Qed.

Lemma la_ev_sort : forall ν xs, la_ev ν (la_sort xs) = la_ev ν xs.
Proof. induction xs as [| k a r IH]; cbn; [ reflexivity | rewrite la_ev_ins, IH; reflexivity ]. Qed.

Lemma la_maxoff_le_ev : forall ν xs, ole (ofin (la_maxoff xs)) (la_ev ν xs).
Proof.
  induction xs as [| k a r IH]; cbn; [ ord |].
  revert IH; generalize (ν a) (la_ev ν r) (la_maxoff r); intros; ord.
Qed.

Lemma lvl_canon_ev : forall ν l, lvl_ev ν (lvl_canon l) = lvl_ev ν l.
Proof.
  intros ν [c xs]; unfold lvl_canon, lvl_ev; cbn.
  rewrite la_ev_sort.
  pose proof (la_maxoff_le_ev ν (la_sort xs)) as H; rewrite la_ev_sort in H.
  destruct (o2_dominated c (la_maxoff (la_sort xs))) eqn:E; [| reflexivity ].
  apply o2_dominated_spec in E.
  revert H E; generalize (la_ev ν xs) (la_maxoff (la_sort xs)); intros; ord.
Qed.

(** Strictly sorted: every later atom is greater. *)
Fixpoint la_In (k : nat) (a : ne) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => False
  | la_cons k' b r => (k = k' /\ a = b) \/ la_In k a r
  end.

Fixpoint la_sorted (ys : lvl_atoms) : Prop :=
  match ys with
  | la_nil => True
  | la_cons _ a r => (forall k b, la_In k b r -> ne_cmp a b = Lt) /\ la_sorted r
  end.

Lemma la_ins_atoms : forall k a ys k' b, la_In k' b (la_ins k a ys) -> b = a \/ exists k'', la_In k'' b ys.
Proof.
  induction ys as [| k0 c r IH]; cbn; intros k' b H.
  - destruct H as [[_ ->] | []]; auto.
  - destruct (ne_cmp a c) eqn:E; cbn in H.
    + destruct H as [[_ ->] | H]; [ right; eauto | right; eauto ].
    + destruct H as [[_ ->] | H]; [ auto | right; eauto ].
    + destruct H as [[_ ->] | H]; [ right; eauto |].
      destruct (IH _ _ H) as [-> | [k'' Hin]]; [ auto | right; eauto ].
Qed.

Lemma la_ins_sorted : forall k a ys, la_sorted ys -> la_sorted (la_ins k a ys).
Proof.
  induction ys as [| k0 c r IH]; cbn; intros Hs.
  - split; [ intros ? ? [] | exact I ].
  - destruct Hs as [Hc Hr].
    destruct (ne_cmp a c) eqn:E; cbn.
    + apply ne_cmp_eq in E; subst; auto.
    + split; [| split; auto ].
      intros k' b [[_ ->] | H]; [ exact E | eapply ne_cmp_trans; eauto ].
    + split; [| auto ].
      intros k' b H; destruct (la_ins_atoms _ _ _ _ _ H) as [-> | [k'' Hin]]; eauto.
      rewrite ne_cmp_opp, E; reflexivity.
Qed.

Lemma la_sort_sorted : forall xs, la_sorted (la_sort xs).
Proof. induction xs as [| k a r IH]; cbn; [ exact I | apply la_ins_sorted; exact IH ]. Qed.

Definition lvl_canonical (l : lvl) : Prop :=
  la_sorted (snd l) /\ (fst l = oz \/ olt (ofin (la_maxoff (snd l))) (fst l)).

Lemma lvl_canon_canonical : forall l, lvl_canonical (lvl_canon l).
Proof.
  intros [c xs]; unfold lvl_canon, lvl_canonical; cbn; split; [ apply la_sort_sorted |].
  destruct (o2_dominated c (la_maxoff (la_sort xs))) eqn:E; cbn; [ left; reflexivity | right ].
  assert (~ ole c (ofin (la_maxoff (la_sort xs)))) as Hn
    by (rewrite <- o2_dominated_spec, E; discriminate).
  revert Hn; generalize (la_maxoff (la_sort xs)); intros; ord.
Qed.

Fixpoint la_look (a : ne) (ys : lvl_atoms) : option nat :=
  match ys with
  | la_nil => None
  | la_cons k b r => match ne_cmp a b with Eq => Some k | _ => la_look a r end
  end.

Lemma la_look_In : forall a ys k, la_look a ys = Some k -> la_In k a ys.
Proof.
  induction ys as [| k0 b r IH]; cbn; intros k H; [ discriminate |].
  destruct (ne_cmp a b) eqn:E; [ apply ne_cmp_eq in E; subst; injection H as <-; auto | right; auto | right; auto ].
Qed.

Lemma la_sorted_unique : forall ys1 ys2, la_sorted ys1 -> la_sorted ys2 ->
    (forall a, la_look a ys1 = la_look a ys2) -> ys1 = ys2.
Proof.
  induction ys1 as [| k a r1 IH]; intros [| k' b r2] H1 H2 Hl.
  - reflexivity.
  - specialize (Hl b); cbn in Hl; rewrite ne_cmp_refl in Hl; discriminate.
  - specialize (Hl a); cbn in Hl; rewrite ne_cmp_refl in Hl; discriminate.
  - destruct H1 as [Ha1 Hr1], H2 as [Hb2 Hr2].
    destruct (ne_cmp a b) eqn:E.
    + apply ne_cmp_eq in E; subst b.
      pose proof (Hl a) as Hk; cbn in Hk; rewrite ne_cmp_refl in Hk; injection Hk as <-.
      f_equal; apply IH; auto.
      intros x; specialize (Hl x); cbn in Hl.
      destruct (ne_cmp x a) eqn:Ex; auto.
      apply ne_cmp_eq in Ex; subst x.
      destruct (la_look a r1) eqn:L1;
        [ apply la_look_In in L1; specialize (Ha1 _ _ L1); rewrite ne_cmp_refl in Ha1; discriminate |].
      destruct (la_look a r2) eqn:L2;
        [ apply la_look_In in L2; specialize (Hb2 _ _ L2); rewrite ne_cmp_refl in Hb2; discriminate |].
      reflexivity.
    + pose proof (Hl a) as Hk; cbn in Hk; rewrite ne_cmp_refl, E in Hk.
      symmetry in Hk; apply la_look_In in Hk; specialize (Hb2 _ _ Hk).
      rewrite ne_cmp_opp, E in Hb2; discriminate.
    + pose proof (Hl b) as Hk; cbn in Hk; rewrite ne_cmp_refl in Hk.
      assert (Eb : ne_cmp b a = Lt) by (rewrite ne_cmp_opp, E; reflexivity).
      rewrite Eb in Hk; apply la_look_In in Hk; specialize (Ha1 _ _ Hk).
      rewrite ne_cmp_opp, Eb in Ha1; discriminate.
Qed.

(** The assignment that separates one atom: it alone is large, at the limit
    [ω·N]. *)
Definition ν_at (a : ne) (N : nat) : ne -> o2 :=
  fun b => match ne_cmp a b with Eq => (N, 0) | _ => oz end.

Lemma la_ev_zero : forall ys, la_ev (fun _ => oz) ys = ofin (la_maxoff ys).
Proof. induction ys as [| k a r IH]; cbn; [ reflexivity | rewrite IH; ord ]. Qed.

Lemma la_ev_at_none : forall a N ys, la_look a ys = None -> la_ev (ν_at a N) ys = ofin (la_maxoff ys).
Proof.
  induction ys as [| k b r IH]; cbn; intros H; [ reflexivity |].
  unfold ν_at at 1; destruct (ne_cmp a b); try discriminate; rewrite IH by auto; ord.
Qed.

Lemma la_ev_at_some : forall a N ys k, 0 < N -> la_sorted ys -> la_look a ys = Some k ->
    la_ev (ν_at a N) ys = (N, k).
Proof.
  induction ys as [| k0 b r IH]; cbn; intros k HN Hs H; [ discriminate |].
  destruct Hs as [Hb Hr]; unfold ν_at at 1.
  destruct (ne_cmp a b) eqn:E.
  - apply ne_cmp_eq in E; subst b; injection H as <-.
    rewrite la_ev_at_none; [ ord |].
    destruct (la_look a r) eqn:L; auto.
    apply la_look_In in L; specialize (Hb _ _ L); rewrite ne_cmp_refl in Hb; discriminate.
  - rewrite (IH k HN Hr H); ord.
  - rewrite (IH k HN Hr H); ord.
Qed.

Theorem lvl_canonical_unique : forall l1 l2, lvl_canonical l1 -> lvl_canonical l2 ->
    (forall ν, lvl_ev ν l1 = lvl_ev ν l2) -> l1 = l2.
Proof.
  intros [c1 ys1] [c2 ys2] [S1 C1] [S2 C2] Hev; cbn in *.
  assert (Hys : ys1 = ys2).
  { apply la_sorted_unique; auto; intros a.
    set (N := S (fst c1 + fst c2)).
    assert (HN : 0 < N) by (subst N; lia).
    specialize (Hev (ν_at a N)); unfold lvl_ev in Hev; cbn in Hev.
    destruct (la_look a ys1) as [k1 |] eqn:L1, (la_look a ys2) as [k2 |] eqn:L2.
    - rewrite (la_ev_at_some _ _ _ _ HN S1 L1), (la_ev_at_some _ _ _ _ HN S2 L2) in Hev.
      f_equal; subst N; revert Hev; ord.
    - rewrite (la_ev_at_some _ _ _ _ HN S1 L1), (la_ev_at_none _ _ _ L2) in Hev; subst N; revert Hev; ord.
    - rewrite (la_ev_at_none _ _ _ L1), (la_ev_at_some _ _ _ _ HN S2 L2) in Hev; subst N; revert Hev; ord.
    - reflexivity. }
  subst ys2; f_equal.
  specialize (Hev (fun _ => oz)); unfold lvl_ev in Hev; cbn in Hev; rewrite la_ev_zero in Hev.
  revert Hev C1 C2; generalize (la_maxoff ys1); intros; ord.
Qed.

Theorem lvl_canon_iff : forall l l', lvl_canon l = lvl_canon l' <-> (forall ν, lvl_ev ν l = lvl_ev ν l').
Proof.
  split.
  - intros H ν; rewrite <- (lvl_canon_ev ν l), <- (lvl_canon_ev ν l'), H; reflexivity.
  - intros H; apply lvl_canonical_unique; try apply lvl_canon_canonical.
    intros ν; rewrite !lvl_canon_ev; apply H.
Qed.

Lemma lvl_canon_idem : forall l, lvl_canon (lvl_canon l) = lvl_canon l.
Proof. intros; apply lvl_canon_iff; intros; apply lvl_canon_ev. Qed.

Lemma lvl_canonical_canon : forall l, lvl_canonical l -> lvl_canon l = l.
Proof.
  intros l H; apply lvl_canonical_unique; [ apply lvl_canon_canonical | assumption |].
  intros; apply lvl_canon_ev.
Qed.

(** The level operations evaluate as the successor and the join. *)
Lemma la_ev_suc : forall ν xs,
    la_ev ν (la_suc xs) = match xs with la_nil => oz | _ => osuc (la_ev ν xs) end.
Proof.
  intros ν; induction xs as [| k a r IH]; cbn; [ reflexivity |]; rewrite IH.
  destruct r; cbn; [| generalize (la_ev ν (la_cons n n0 r)) ]; generalize (ν a); intros; ord.
Qed.

Lemma lvl_ev_suc : forall ν l, lvl_ev ν (lvl_suc l) = osuc (lvl_ev ν l).
Proof.
  intros ν [c xs]; unfold lvl_ev, lvl_suc; cbn; rewrite la_ev_suc.
  destruct xs; cbn; [| generalize (la_ev ν (la_cons n n0 xs)) ]; intros; ord.
Qed.

Lemma la_ev_app : forall ν xs ys, la_ev ν (la_app xs ys) = omax (la_ev ν xs) (la_ev ν ys).
Proof.
  induction xs as [| k a r IH]; intros; cbn; [ symmetry; apply omax_zero_l |].
  rewrite IH; symmetry; apply omax_assoc.
Qed.

Lemma lvl_ev_max : forall ν l l', lvl_ev ν (lvl_max l l') = omax (lvl_ev ν l) (lvl_ev ν l').
Proof.
  intros ν [c xs] [d ys]; unfold lvl_ev, lvl_max; cbn; rewrite la_ev_app.
  generalize (la_ev ν xs) (la_ev ν ys); intros; ord.
Qed.

(** Canonicalising a part of a level does not change its canonical form: this
    is what makes readback compositional, since the atoms of a level read back
    already canonical. *)
Lemma lvl_canon_max_l : forall l l', lvl_canon (lvl_max (lvl_canon l) l') = lvl_canon (lvl_max l l').
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_ev_max, !lvl_canon_ev; reflexivity. Qed.

Lemma lvl_canon_max_r : forall l l', lvl_canon (lvl_max l (lvl_canon l')) = lvl_canon (lvl_max l l').
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_ev_max, !lvl_canon_ev; reflexivity. Qed.

Lemma lvl_canon_suc : forall l, lvl_canon (lvl_suc (lvl_canon l)) = lvl_canon (lvl_suc l).
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_ev_suc, !lvl_canon_ev; reflexivity. Qed.

Lemma lvl_canon_max_cong : forall l1 l1' l2 l2',
    lvl_canon l1 = lvl_canon l1' -> lvl_canon l2 = lvl_canon l2' ->
    lvl_canon (lvl_max l1 l2) = lvl_canon (lvl_max l1' l2').
Proof.
  intros * H1 H2; rewrite lvl_canon_iff in H1, H2 |- *.
  intros; rewrite !lvl_ev_max, H1, H2; reflexivity.
Qed.

Lemma lvl_canon_suc_cong : forall l l',
    lvl_canon l = lvl_canon l' -> lvl_canon (lvl_suc l) = lvl_canon (lvl_suc l').
Proof.
  intros * H; rewrite lvl_canon_iff in H |- *.
  intros; rewrite !lvl_ev_suc, H; reflexivity.
Qed.

(** ** Properties of Every Atom

    Canonicalisation only reorders, merges and drops atoms, so a property of
    all the atoms of a level survives it.  [la_clean] and [la_stuck] are
    instances. *)
Fixpoint la_all (P : ne -> Prop) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ a r => P a /\ la_all P r
  end.

Lemma la_all_ins : forall P k a ys, P a -> la_all P ys -> la_all P (la_ins k a ys).
Proof.
  induction ys as [| k' b r IH]; cbn; intros Ha Hys; [ auto |].
  destruct Hys as [Hb Hr]; destruct (ne_cmp a b) eqn:E; cbn; auto.
Qed.

Lemma la_all_sort : forall P xs, la_all P xs -> la_all P (la_sort xs).
Proof.
  induction xs as [| k a r IH]; cbn; intros H; [ exact I |].
  destruct H; apply la_all_ins; auto.
Qed.

Lemma la_all_canon : forall P c xs, la_all P xs -> la_all P (snd (lvl_canon (c, xs))).
Proof. intros; unfold lvl_canon; cbn; apply la_all_sort; assumption. Qed.

Lemma la_all_app : forall P xs ys, la_all P xs -> la_all P ys -> la_all P (la_app xs ys).
Proof.
  intros P xs ys; induction xs as [| k a r IH]; cbn; [ intros _ H; exact H |].
  intros [Ha Hr] Hy; split; auto.
Qed.

Lemma la_all_suc : forall P xs, la_all P xs -> la_all P (la_suc xs).
Proof.
  intros P xs; induction xs as [| k a r IH]; cbn; [ intros; exact I |].
  intros [Ha Hr]; split; auto.
Qed.

Lemma la_clean_all : forall xs, la_clean xs <-> la_all ne_clean xs.
Proof. induction xs as [| k a r IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma la_clean_canon : forall c xs, la_clean xs -> la_clean (snd (lvl_canon (c, xs))).
Proof. intros * H; apply la_clean_all, la_all_canon, la_clean_all; assumption. Qed.

Lemma la_clean_sort : forall xs, la_clean xs -> la_clean (la_sort xs).
Proof. intros * H; apply la_clean_all, la_all_sort, la_clean_all; assumption. Qed.

(** ** The Order on Levels

    [lvl_le l l'] is the decidable order [l ⊔ l' = l'], which is the pointwise
    order at every assignment. *)
Definition lvl_le (l l' : lvl) : Prop := lvl_canon (lvl_max l l') = lvl_canon l'.

Theorem lvl_le_correct : forall l l', lvl_le l l' <-> (forall ν, ole (lvl_ev ν l) (lvl_ev ν l')).
Proof.
  intros l l'; unfold lvl_le; rewrite lvl_canon_iff; split; intros H ν; specialize (H ν);
    rewrite lvl_ev_max in *; revert H; generalize (lvl_ev ν l) (lvl_ev ν l'); intros; ord.
Qed.

Definition lvl_eq_dec : forall (l l' : lvl), ({l = l'} + {l <> l'})%type.
Proof.
  intros [c xs] [c' ys]; destruct (o2_eq_dec c c') as [-> |]; [| right; congruence ].
  destruct (la_eq_dec xs ys) as [-> |]; [ left; reflexivity | right; congruence ].
Defined.

Definition lvl_le_dec : forall l l', ({lvl_le l l'} + {~ lvl_le l l'})%type.
Proof. intros; unfold lvl_le; apply lvl_eq_dec. Defined.

Lemma lvl_le_refl : forall l, lvl_le l l.
Proof. intros; apply lvl_le_correct; intros; apply ole_refl. Qed.

Lemma lvl_le_trans : forall l1 l2 l3, lvl_le l1 l2 -> lvl_le l2 l3 -> lvl_le l1 l3.
Proof.
  intros * H1 H2; rewrite lvl_le_correct in H1, H2; apply lvl_le_correct; intros ν.
  eapply ole_trans; [ apply H1 | apply H2 ].
Qed.

Lemma lvl_le_canon : forall l l', lvl_canon l = lvl_canon l' -> lvl_le l l'.
Proof. intros * H; rewrite lvl_canon_iff in H; apply lvl_le_correct; intros; rewrite H; apply ole_refl. Qed.

Lemma lvl_le_antisym : forall l l', lvl_le l l' -> lvl_le l' l -> lvl_canon l = lvl_canon l'.
Proof.
  intros * H H'; rewrite lvl_le_correct in H, H'; apply lvl_canon_iff; intros ν.
  apply ole_antisym; [ apply H | apply H' ].
Qed.

Lemma lvl_le_max_left : forall l l', lvl_le l (lvl_max l l').
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_ev_max; apply ole_omax_l. Qed.

Lemma lvl_le_max_right : forall l l', lvl_le l' (lvl_max l l').
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_ev_max; apply ole_omax_r. Qed.

Lemma lvl_le_max_lub : forall l l' l'', lvl_le l l'' -> lvl_le l' l'' -> lvl_le (lvl_max l l') l''.
Proof.
  intros * H H'; rewrite lvl_le_correct in H, H'; apply lvl_le_correct; intros ν.
  rewrite lvl_ev_max; apply omax_lub; [ apply H | apply H' ].
Qed.

Lemma lvl_le_suc : forall l, lvl_le l (lvl_suc l).
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_ev_suc; apply ole_osuc. Qed.

(** The least level, and the literals. *)
Definition lvl_lit (o : o2) : lvl := (o, la_nil).

Lemma lvl_ev_lit : forall ν o, lvl_ev ν (lvl_lit o) = o.
Proof. intros; unfold lvl_ev, lvl_lit; cbn; apply omax_zero_r. Qed.

Lemma lvl_canon_lit : forall o, lvl_canon (lvl_lit o) = lvl_lit o.
Proof. intros; apply lvl_canonical_canon; split; cbn; [ exact I | destruct o as [[|] [|]]; [ left | right .. ]; ord ]. Qed.

Lemma lvl_le_lit : forall o o', ole o o' -> lvl_le (lvl_lit o) (lvl_lit o').
Proof. intros; apply lvl_le_correct; intros; rewrite !lvl_ev_lit; assumption. Qed.

Lemma lvl_le_zero : forall l, lvl_le lvl_zero l.
Proof. intros; apply lvl_le_correct; intros; unfold lvl_ev, lvl_zero; cbn; rewrite omax_zero_l; apply ole_zero. Qed.

(** ** The Realiser

    The realiser of a level is its value when every atom is [0].  It is the
    index of a small universe in the PER and gluing models: those are indexed
    by ordinals, and a level's canonical form depends on the length of the
    context, so no finer index would be stable.  The order on levels refines
    the order on realisers ([lvl_le_real]), which is what makes a subtyping
    between small universes hold in the model. *)
(** The constant is the base of the fold rather than an [omax] on top of it,
    so that the realiser of a literal level is that literal by computation. *)
Fixpoint la_max (c : o2) (xs : lvl_atoms) : o2 :=
  match xs with
  | la_nil => c
  | la_cons k _ r => omax (ofin k) (la_max c r)
  end.

Definition lvl_real (l : lvl) : o2 := la_max (fst l) (snd l).

Lemma lvl_real_ev : forall l, lvl_real l = lvl_ev (fun _ => oz) l.
Proof.
  intros [c xs]; unfold lvl_real, lvl_ev; cbn.
  induction xs as [| k a r IH]; cbn; [ symmetry; apply omax_zero_r |].
  rewrite IH; generalize (la_ev (fun _ => oz) r); intros; ord.
Qed.

Lemma lvl_real_canon : forall l, lvl_real (lvl_canon l) = lvl_real l.
Proof. intros; rewrite !lvl_real_ev; apply lvl_canon_ev. Qed.

Lemma lvl_le_real : forall l l', lvl_le l l' -> ole (lvl_real l) (lvl_real l').
Proof. intros * H; rewrite lvl_le_correct in H; rewrite !lvl_real_ev; apply H. Qed.

Lemma lvl_real_lit : forall o, lvl_real (lvl_lit o) = o.
Proof. reflexivity. Qed.

Lemma lvl_real_suc : forall l, lvl_real (lvl_suc l) = osuc (lvl_real l).
Proof. intros; rewrite !lvl_real_ev; apply lvl_ev_suc. Qed.

Lemma lvl_real_max : forall l l', lvl_real (lvl_max l l') = omax (lvl_real l) (lvl_real l').
Proof. intros; rewrite !lvl_real_ev; apply lvl_ev_max. Qed.

(** ** The Order on Universe Normal Forms

    The checker compares two universes by the canonical order of their levels
    in the small tier, by the order on levels in the large one, and a small
    universe is below every large one. *)
Definition unf_le (u v : unf) : Prop :=
  match u, v with
  | uns L, uns L' => lvl_le L L'
  | uns _, unl _ => True
  | unl _, uns _ => False
  | unl i, unl j => i <= j
  end.

Lemma unf_le_refl : forall u, unf_le u u.
Proof. intros []; cbn; [ apply lvl_le_refl | lia ]. Qed.

Lemma unf_le_trans : forall u v w, unf_le u v -> unf_le v w -> unf_le u w.
Proof.
  intros [] [] []; cbn; try contradiction; intros;
    first [ eapply lvl_le_trans; eassumption | exact I | lia ].
Qed.

(** The large universe a type at [u] also lives in. *)
Definition unf_large (u : unf) : nat := match u with uns _ => 0 | unl n => n end.

Lemma unf_le_large : forall u, unf_le u (unl (unf_large u)).
Proof. intros []; cbn; [ exact I | lia ]. Qed.

(** The semantic index of a universe normal form. *)
Definition unf_idx (u : unf) : uidx :=
  match u with uns L => us (lvl_real L) | unl i => ul i end.

Lemma unf_le_idx : forall u v, unf_le u v -> uidx_le (unf_idx u) (unf_idx v).
Proof. intros [] []; cbn; try contradiction; intros; [ apply lvl_le_real | exact I |]; assumption. Qed.

(** ** The Join of Two Universe Normal Forms

    The universe a [Π] is inferred at.  Two closed small levels join to the
    small universe at their maximum; with an open one the join would need the
    level of the codomain, which lives under the domain, to be strengthened
    out of that context, so it falls back to the least large universe. *)
Definition unf_max (u v : unf) : unf :=
  match u, v with
  | uns (c, la_nil), uns (d, la_nil) => uns (lvl_lit (omax c d))
  | uns _, uns _ => unl 0
  | uns _, unl j => unl j
  | unl i, uns _ => unl i
  | unl i, unl j => unl (Nat.max i j)
  end.

Lemma unf_le_max_left : forall u v, unf_le u (unf_max u v).
Proof.
  intros [[c []] |] [[d []] |]; cbn [unf_max unf_le];
    try solve [ exact I | lia | apply lvl_le_lit; apply ole_omax_l ].
Qed.

Lemma unf_le_max_right : forall u v, unf_le v (unf_max u v).
Proof.
  intros [[c []] |] [[d []] |]; cbn [unf_max unf_le];
    try solve [ exact I | lia | apply lvl_le_lit; apply ole_omax_r ].
Qed.

(** A level below a literal has no atom: an atom's assignment is arbitrary,
    so it would exceed the literal. *)
Lemma lvl_le_lit_closed : forall l o, lvl_le l (lvl_lit o) -> snd l = la_nil.
Proof.
  intros [c xs] o H; rewrite lvl_le_correct in H; destruct xs as [| k a r]; [ reflexivity |].
  specialize (H (fun _ => (S (fst o), 0))); unfold lvl_ev, lvl_lit in H; cbn in H.
  revert H; generalize (la_ev (fun _ => (S (fst o), 0)) r); intros; ord.
Qed.

(** A universe with no open level in the small tier; the join is a least upper
    bound below such a universe.  (Above an open small universe it is not: the
    fallback to the large tier overshoots.) *)
Definition unf_closed (u : unf) : Prop :=
  match u with uns (_, la_nil) => True | uns _ => False | unl _ => True end.

Lemma unf_closed_lit : forall o, unf_closed (uns (lvl_lit o)).
Proof. exact (fun _ => I). Qed.

Lemma unf_max_lub : forall u v w,
    unf_closed w ->
    unf_le u w ->
    unf_le v w ->
    unf_le (unf_max u v) w.
Proof.
  intros u v [[e zs] | i] Hw Hu Hv.
  - cbn in Hw; destruct zs; [| contradiction ].
    destruct u as [[c xs] |]; [| contradiction ].
    destruct v as [[d ys] |]; [| contradiction ].
    assert (xs = la_nil) as -> by exact (lvl_le_lit_closed (c, xs) e Hu).
    assert (ys = la_nil) as -> by exact (lvl_le_lit_closed (d, ys) e Hv).
    cbn [unf_max unf_le] in Hu, Hv |- *; rewrite lvl_le_correct in Hu, Hv |- *; intros ν.
    specialize (Hu ν); specialize (Hv ν).
    unfold lvl_ev, lvl_lit in *; cbn in *; ord.
  - destruct u as [[c xs] |]; destruct v as [[d ys] |];
      try destruct xs; try destruct ys;
      cbn [unf_max unf_le] in *; try solve [ exact I | lia ].
Qed.

(** The literal small universes. *)
Definition unf_lit (o : o2) : unf := uns (lvl_lit o).

Lemma unf_le_lit : forall o o', ole o o' -> unf_le (unf_lit o) (unf_lit o').
Proof. intros; apply lvl_le_lit; assumption. Qed.

(** Decides an identity between ordinals built from the values of levels:
    each value [lvl_ev ν l] is an opaque ordinal, and [ord] does the rest. *)
Ltac lvl_ord :=
  repeat match goal with
         | |- context [lvl_ev ?ν ?l] => let x := fresh "x" in generalize (lvl_ev ν l) as x
         end;
  ord.
