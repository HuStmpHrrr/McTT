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
  | nf_level n => lt_node 2 (lt_node n lt_nil lt_nil) t
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
  | la_cons k n m r => lt_node 1 (lt_node k (ne_code m lt_nil) (lt_node n lt_nil lt_nil)) (la_code r t)
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
    finite offsets, each atom with its sort.  An atom of sort [s] is a level
    of type [Level@s], so it ranges over the ordinals below ω·(s+1):
    [lvl_ev ν] evaluates a level at an assignment [ν] of ordinals to atoms,
    and the assignments that matter are the admissible ones ([lvl_adm]),
    which respect the sorts.  Two levels are equal exactly when they agree at
    every admissible assignment.  A constant [c] absorbs every atom of a sort
    below [fst c] ([max (ω, u + 5)] is [ω] for [u : Level@0]), and no other:
    an atom of sort [s ≥ fst c] can be [ω·s + N] for any [N].  The type
    [lvl] itself is in [Core.Syntactic.Syntax], with the normal forms it
    indexes. *)

(** The order on the atoms: by the neutral, then by the sort. *)
Definition at_cmp (a : ne) (s : nat) (b : ne) (t : nat) : comparison :=
  match ne_cmp a b with Eq => Nat.compare s t | c => c end.

Lemma at_cmp_eq : forall a s b t, at_cmp a s b t = Eq <-> a = b /\ s = t.
Proof.
  intros; unfold at_cmp; destruct (ne_cmp a b) eqn:E.
  - apply ne_cmp_eq in E as ->; rewrite Nat.compare_eq_iff; intuition.
  - split; [ discriminate | intros [-> _]; rewrite ne_cmp_refl in E; discriminate ].
  - split; [ discriminate | intros [-> _]; rewrite ne_cmp_refl in E; discriminate ].
Qed.

Lemma at_cmp_refl : forall a s, at_cmp a s a s = Eq.
Proof. intros; apply at_cmp_eq; split; reflexivity. Qed.

Lemma at_cmp_opp : forall a s b t, at_cmp b t a s = CompOpp (at_cmp a s b t).
Proof.
  intros; unfold at_cmp; rewrite (ne_cmp_opp a b).
  destruct (ne_cmp a b); cbn; [ apply Nat.compare_antisym | reflexivity .. ].
Qed.

Lemma at_cmp_trans : forall a s b t c u,
    at_cmp a s b t = Lt -> at_cmp b t c u = Lt -> at_cmp a s c u = Lt.
Proof.
  intros * H1 H2; unfold at_cmp in *.
  destruct (ne_cmp a b) eqn:E1, (ne_cmp b c) eqn:E2; try discriminate.
  - apply ne_cmp_eq in E1, E2; subst; rewrite ne_cmp_refl.
    apply Nat.compare_lt_iff in H1, H2; apply Nat.compare_lt_iff; lia.
  - apply ne_cmp_eq in E1; subst; rewrite E2; reflexivity.
  - apply ne_cmp_eq in E2; subst; rewrite E1; reflexivity.
  - rewrite (ne_cmp_trans _ _ _ E1 E2); reflexivity.
Qed.

Fixpoint la_ev (ν : ne -> nat -> o2) (xs : lvl_atoms) : o2 :=
  match xs with
  | la_nil => oz
  | la_cons k s a r => omax (osucn k (ν a s)) (la_ev ν r)
  end.

Definition lvl_ev (ν : ne -> nat -> o2) (l : lvl) : o2 := omax (fst l) (la_ev ν (snd l)).

(** An assignment is admissible when it respects the sorts. *)
Definition lvl_adm (ν : ne -> nat -> o2) : Prop := forall a s, fst (ν a s) <= s.

Lemma lvl_adm_zero : lvl_adm (fun _ _ => oz).
Proof. intros a s; cbn; lia. Qed.

Definition lvl_zero : lvl := (oz, la_nil).

Fixpoint la_suc (xs : lvl_atoms) : lvl_atoms :=
  match xs with
  | la_nil => la_nil
  | la_cons k s a r => la_cons (S k) s a (la_suc r)
  end.

Definition lvl_suc (l : lvl) : lvl := (osuc (fst l), la_suc (snd l)).

Fixpoint la_app (xs ys : lvl_atoms) : lvl_atoms :=
  match xs with
  | la_nil => ys
  | la_cons k s a r => la_cons k s a (la_app r ys)
  end.

Definition lvl_max (l l' : lvl) : lvl := (omax (fst l) (fst l'), la_app (snd l) (snd l')).

(** Insertion into a sorted list of atoms, merging at the larger offset. *)
Fixpoint la_ins (k s : nat) (a : ne) (ys : lvl_atoms) : lvl_atoms :=
  match ys with
  | la_nil => la_cons k s a la_nil
  | la_cons k' t b r =>
      match at_cmp a s b t with
      | Lt => la_cons k s a ys
      | Eq => la_cons (Nat.max k k') t b r
      | Gt => la_cons k' t b (la_ins k s a r)
      end
  end.

Fixpoint la_sort (xs : lvl_atoms) : lvl_atoms :=
  match xs with
  | la_nil => la_nil
  | la_cons k s a r => la_ins k s a (la_sort r)
  end.

Fixpoint la_maxoff (xs : lvl_atoms) : nat :=
  match xs with
  | la_nil => 0
  | la_cons k _ _ r => Nat.max k (la_maxoff r)
  end.

(** The atoms a constant does not absorb: those of a sort at least its
    tier. *)
Fixpoint la_keep (c : o2) (xs : lvl_atoms) : lvl_atoms :=
  match xs with
  | la_nil => la_nil
  | la_cons k s a r => if fst c <=? s then la_cons k s a (la_keep c r) else la_keep c r
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

(** The canonical form: sort and merge the atoms, drop the atoms the constant
    absorbs, then drop the constant if the atoms dominate it. *)
Definition lvl_canon (l : lvl) : lvl :=
  let ys := la_keep (fst l) (la_sort (snd l)) in
  (if o2_dominated (fst l) (la_maxoff ys) then oz else fst l, ys).

Lemma la_ev_ins : forall ν k s a ys, la_ev ν (la_ins k s a ys) = omax (osucn k (ν a s)) (la_ev ν ys).
Proof.
  induction ys as [| k' t b r IH]; cbn; [ reflexivity |].
  destruct (at_cmp a s b t) eqn:E; cbn.
  - apply at_cmp_eq in E as [-> ->]; generalize (ν b t) (la_ev ν r); intros; ord.
  - reflexivity.
  - rewrite IH; generalize (ν a s) (ν b t) (la_ev ν r); intros; ord.
Qed.

Lemma la_ev_sort : forall ν xs, la_ev ν (la_sort xs) = la_ev ν xs.
Proof. induction xs as [| k s a r IH]; cbn; [ reflexivity | rewrite la_ev_ins, IH; reflexivity ]. Qed.

(** The dropped atoms are absorbed by the constant. *)
Lemma la_ev_keep : forall ν c ys, lvl_adm ν -> omax c (la_ev ν (la_keep c ys)) = omax c (la_ev ν ys).
Proof.
  intros ν c ys Hadm; induction ys as [| k s a r IH]; cbn [la_keep la_ev]; [ reflexivity |].
  specialize (Hadm a s).
  destruct (Nat.leb_spec (fst c) s); cbn [la_ev].
  - revert IH; generalize (la_ev ν (la_keep c r)) (la_ev ν r); intros; ord.
  - revert IH Hadm; generalize (la_ev ν (la_keep c r)) (la_ev ν r) (ν a s); intros; ord.
Qed.

Lemma la_maxoff_le_ev : forall ν xs, ole (ofin (la_maxoff xs)) (la_ev ν xs).
Proof.
  induction xs as [| k s a r IH]; cbn; [ ord |].
  revert IH; generalize (ν a s) (la_ev ν r) (la_maxoff r); intros; ord.
Qed.

Lemma lvl_canon_ev : forall ν l, lvl_adm ν -> lvl_ev ν (lvl_canon l) = lvl_ev ν l.
Proof.
  intros ν [c xs] Hadm; unfold lvl_canon, lvl_ev; cbn [fst snd].
  rewrite <- (la_ev_sort ν xs), <- (la_ev_keep ν c _ Hadm).
  pose proof (la_maxoff_le_ev ν (la_keep c (la_sort xs))) as H.
  destruct (o2_dominated c (la_maxoff (la_keep c (la_sort xs)))) eqn:E; [| reflexivity ].
  apply o2_dominated_spec in E.
  revert H E; generalize (la_ev ν (la_keep c (la_sort xs))) (la_maxoff (la_keep c (la_sort xs))); intros; ord.
Qed.

(** Strictly sorted: every later atom is greater. *)
Fixpoint la_In (k s : nat) (a : ne) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => False
  | la_cons k' t b r => (k = k' /\ s = t /\ a = b) \/ la_In k s a r
  end.

Fixpoint la_sorted (ys : lvl_atoms) : Prop :=
  match ys with
  | la_nil => True
  | la_cons _ s a r => (forall k t b, la_In k t b r -> at_cmp a s b t = Lt) /\ la_sorted r
  end.

Lemma la_ins_atoms : forall k s a ys k' t b,
    la_In k' t b (la_ins k s a ys) -> (t = s /\ b = a) \/ exists k'', la_In k'' t b ys.
Proof.
  induction ys as [| k0 u c r IH]; cbn; intros k' t b H.
  - destruct H as [(_ & -> & ->) | []]; auto.
  - destruct (at_cmp a s c u) eqn:E; cbn in H.
    + destruct H as [(_ & -> & ->) | H]; [ right; eauto | right; eauto ].
    + destruct H as [(_ & -> & ->) | H]; [ auto | right; eauto ].
    + destruct H as [(_ & -> & ->) | H]; [ right; eauto |].
      destruct (IH _ _ _ H) as [[-> ->] | [k'' Hin]]; [ auto | right; eauto ].
Qed.

Lemma la_ins_sorted : forall k s a ys, la_sorted ys -> la_sorted (la_ins k s a ys).
Proof.
  induction ys as [| k0 u c r IH]; cbn; intros Hs.
  - split; [ intros ? ? ? [] | exact I ].
  - destruct Hs as [Hc Hr].
    destruct (at_cmp a s c u) eqn:E; cbn.
    + apply at_cmp_eq in E as [-> ->]; auto.
    + split; [| split; auto ].
      intros k' t b [(_ & -> & ->) | H]; [ exact E | eapply at_cmp_trans; eauto ].
    + split; [| auto ].
      intros k' t b H; destruct (la_ins_atoms _ _ _ _ _ _ _ H) as [[-> ->] | [k'' Hin]]; eauto.
      rewrite at_cmp_opp, E; reflexivity.
Qed.

Lemma la_sort_sorted : forall xs, la_sorted (la_sort xs).
Proof. induction xs as [| k s a r IH]; cbn; [ exact I | apply la_ins_sorted; exact IH ]. Qed.

Lemma la_keep_In : forall c ys k s a, la_In k s a (la_keep c ys) -> la_In k s a ys /\ fst c <= s.
Proof.
  intros c; induction ys as [| k0 t b r IH]; cbn [la_keep]; intros k s a H; [ destruct H |].
  destruct (Nat.leb_spec (fst c) t); cbn in H |- *.
  - destruct H as [(-> & -> & ->) | H]; [ auto |].
    apply IH in H as [? ?]; auto.
  - apply IH in H as [? ?]; auto.
Qed.

Lemma la_keep_sorted : forall c ys, la_sorted ys -> la_sorted (la_keep c ys).
Proof.
  intros c; induction ys as [| k t b r IH]; cbn [la_keep]; intros Hs; [ exact I |].
  destruct Hs as [Hb Hr].
  destruct (Nat.leb_spec (fst c) t); [| apply IH; exact Hr ].
  cbn [la_sorted]; split; [| apply IH; exact Hr ].
  intros k' t' b' Hin; apply la_keep_In in Hin as [Hin _]; eapply Hb; eauto.
Qed.

Definition lvl_canonical (l : lvl) : Prop :=
  la_sorted (snd l) /\
    (forall k s a, la_In k s a (snd l) -> fst (fst l) <= s) /\
    (fst l = oz \/ olt (ofin (la_maxoff (snd l))) (fst l)).

Lemma lvl_canon_canonical : forall l, lvl_canonical (lvl_canon l).
Proof.
  intros [c xs]; unfold lvl_canon, lvl_canonical; cbn [fst snd].
  split; [ apply la_keep_sorted, la_sort_sorted |].
  destruct (o2_dominated c (la_maxoff (la_keep c (la_sort xs)))) eqn:E; cbn [fst].
  - split; [ intros; cbn; lia | left; reflexivity ].
  - split; [ intros k s a H; apply la_keep_In in H as [_ H]; exact H | right ].
    assert (~ ole c (ofin (la_maxoff (la_keep c (la_sort xs))))) as Hn
      by (rewrite <- o2_dominated_spec, E; discriminate).
    revert Hn; generalize (la_maxoff (la_keep c (la_sort xs))); intros; ord.
Qed.

Fixpoint la_look (a : ne) (s : nat) (ys : lvl_atoms) : option nat :=
  match ys with
  | la_nil => None
  | la_cons k t b r => match at_cmp a s b t with Eq => Some k | _ => la_look a s r end
  end.

Lemma la_look_In : forall a s ys k, la_look a s ys = Some k -> la_In k s a ys.
Proof.
  induction ys as [| k0 t b r IH]; cbn; intros k H; [ discriminate |].
  destruct (at_cmp a s b t) eqn:E;
    [ apply at_cmp_eq in E as [-> ->]; injection H as <-; auto | right; auto | right; auto ].
Qed.

Lemma la_sorted_unique : forall ys1 ys2, la_sorted ys1 -> la_sorted ys2 ->
    (forall a s, la_look a s ys1 = la_look a s ys2) -> ys1 = ys2.
Proof.
  induction ys1 as [| k s a r1 IH]; intros [| k' t b r2] H1 H2 Hl.
  - reflexivity.
  - specialize (Hl b t); cbn in Hl; rewrite at_cmp_refl in Hl; discriminate.
  - specialize (Hl a s); cbn in Hl; rewrite at_cmp_refl in Hl; discriminate.
  - destruct H1 as [Ha1 Hr1], H2 as [Hb2 Hr2].
    destruct (at_cmp a s b t) eqn:E.
    + apply at_cmp_eq in E as [<- <-].
      pose proof (Hl a s) as Hk; cbn in Hk; rewrite at_cmp_refl in Hk; injection Hk as <-.
      f_equal; apply IH; auto.
      intros x u; specialize (Hl x u); cbn in Hl.
      destruct (at_cmp x u a s) eqn:Ex; auto.
      apply at_cmp_eq in Ex as [-> ->].
      destruct (la_look a s r1) eqn:L1;
        [ apply la_look_In in L1; specialize (Ha1 _ _ _ L1); rewrite at_cmp_refl in Ha1; discriminate |].
      destruct (la_look a s r2) eqn:L2;
        [ apply la_look_In in L2; specialize (Hb2 _ _ _ L2); rewrite at_cmp_refl in Hb2; discriminate |].
      reflexivity.
    + pose proof (Hl a s) as Hk; cbn in Hk; rewrite at_cmp_refl, E in Hk.
      symmetry in Hk; apply la_look_In in Hk; specialize (Hb2 _ _ _ Hk).
      rewrite at_cmp_opp, E in Hb2; discriminate.
    + pose proof (Hl b t) as Hk; cbn in Hk; rewrite at_cmp_refl in Hk.
      assert (Eb : at_cmp b t a s = Lt) by (rewrite at_cmp_opp, E; reflexivity).
      rewrite Eb in Hk; apply la_look_In in Hk; specialize (Ha1 _ _ _ Hk).
      rewrite at_cmp_opp, Eb in Ha1; discriminate.
Qed.

(** The assignment that separates one atom: it alone is large, at [ω·s + N],
    the largest region its sort [s] allows. *)
Definition ν_at (a : ne) (s N : nat) : ne -> nat -> o2 :=
  fun b t => match at_cmp a s b t with Eq => (s, N) | _ => oz end.

Lemma ν_at_adm : forall a s N, lvl_adm (ν_at a s N).
Proof.
  intros a s N b t; unfold ν_at; destruct (at_cmp a s b t) eqn:E; cbn; [| lia | lia ].
  apply at_cmp_eq in E as [_ ->]; lia.
Qed.

Lemma la_ev_zero : forall ys, la_ev (fun _ _ => oz) ys = ofin (la_maxoff ys).
Proof. induction ys as [| k s a r IH]; cbn; [ reflexivity | rewrite IH; ord ]. Qed.

Lemma la_ev_at_none : forall a s N ys, la_look a s ys = None -> la_ev (ν_at a s N) ys = ofin (la_maxoff ys).
Proof.
  induction ys as [| k t b r IH]; cbn; intros H; [ reflexivity |].
  unfold ν_at at 1; destruct (at_cmp a s b t); try discriminate; rewrite IH by auto; ord.
Qed.

Lemma la_ev_at_some : forall a s N ys k, la_maxoff ys < N -> la_sorted ys -> la_look a s ys = Some k ->
    la_ev (ν_at a s N) ys = (s, k + N).
Proof.
  induction ys as [| k0 t b r IH]; cbn; intros k HN Hs H; [ discriminate |].
  destruct Hs as [Hb Hr]; unfold ν_at at 1.
  destruct (at_cmp a s b t) eqn:E.
  - apply at_cmp_eq in E as [<- <-]; injection H as <-.
    rewrite la_ev_at_none; [ revert HN; ord |].
    destruct (la_look a s r) eqn:L; auto.
    apply la_look_In in L; specialize (Hb _ _ _ L); rewrite at_cmp_refl in Hb; discriminate.
  - rewrite (IH k ltac:(lia) Hr H); revert HN; ord.
  - rewrite (IH k ltac:(lia) Hr H); revert HN; ord.
Qed.

Theorem lvl_canonical_unique : forall l1 l2, lvl_canonical l1 -> lvl_canonical l2 ->
    (forall ν, lvl_adm ν -> lvl_ev ν l1 = lvl_ev ν l2) -> l1 = l2.
Proof.
  intros [c1 ys1] [c2 ys2] [S1 [K1 C1]] [S2 [K2 C2]] Hev; cbn [fst snd] in *.
  assert (Hys : ys1 = ys2).
  { apply la_sorted_unique; auto; intros a s.
    set (N := S (snd c1 + snd c2 + la_maxoff ys1 + la_maxoff ys2)).
    assert (HN1 : la_maxoff ys1 < N) by (subst N; lia).
    assert (HN2 : la_maxoff ys2 < N) by (subst N; lia).
    assert (Hc1 : snd c1 < N) by (subst N; lia).
    assert (Hc2 : snd c2 < N) by (subst N; lia).
    specialize (Hev (ν_at a s N) (ν_at_adm a s N)); unfold lvl_ev in Hev; cbn [fst snd] in Hev.
    destruct (la_look a s ys1) as [k1 |] eqn:L1, (la_look a s ys2) as [k2 |] eqn:L2.
    - pose proof (K1 _ _ _ (la_look_In _ _ _ _ L1)); pose proof (K2 _ _ _ (la_look_In _ _ _ _ L2)).
      rewrite (la_ev_at_some _ _ _ _ _ HN1 S1 L1), (la_ev_at_some _ _ _ _ _ HN2 S2 L2) in Hev.
      f_equal; clearbody N; revert Hc1 Hc2 H H0 Hev; ord.
    - pose proof (K1 _ _ _ (la_look_In _ _ _ _ L1)).
      rewrite (la_ev_at_some _ _ _ _ _ HN1 S1 L1), (la_ev_at_none _ _ _ _ L2) in Hev.
      exfalso; clearbody N; revert Hc1 Hc2 HN2 H Hev; ord.
    - pose proof (K2 _ _ _ (la_look_In _ _ _ _ L2)).
      rewrite (la_ev_at_none _ _ _ _ L1), (la_ev_at_some _ _ _ _ _ HN2 S2 L2) in Hev.
      exfalso; clearbody N; revert Hc1 Hc2 HN1 H Hev; ord.
    - reflexivity. }
  subst ys2; f_equal.
  specialize (Hev _ lvl_adm_zero); unfold lvl_ev in Hev; cbn [fst snd] in Hev; rewrite la_ev_zero in Hev.
  revert Hev C1 C2; generalize (la_maxoff ys1); intros; ord.
Qed.

Theorem lvl_canon_iff : forall l l',
    lvl_canon l = lvl_canon l' <-> (forall ν, lvl_adm ν -> lvl_ev ν l = lvl_ev ν l').
Proof.
  split.
  - intros H ν Hν; rewrite <- (lvl_canon_ev ν l Hν), <- (lvl_canon_ev ν l' Hν), H; reflexivity.
  - intros H; apply lvl_canonical_unique; try apply lvl_canon_canonical.
    intros ν Hν; rewrite !lvl_canon_ev by exact Hν; apply H, Hν.
Qed.

Lemma lvl_canon_idem : forall l, lvl_canon (lvl_canon l) = lvl_canon l.
Proof. intros; apply lvl_canon_iff; intros; apply lvl_canon_ev; assumption. Qed.

Lemma lvl_canonical_canon : forall l, lvl_canonical l -> lvl_canon l = l.
Proof.
  intros l H; apply lvl_canonical_unique; [ apply lvl_canon_canonical | assumption |].
  intros; apply lvl_canon_ev; assumption.
Qed.

(** The level operations evaluate as the successor and the join. *)
Lemma la_ev_suc : forall ν xs,
    la_ev ν (la_suc xs) = match xs with la_nil => oz | _ => osuc (la_ev ν xs) end.
Proof.
  intros ν; induction xs as [| k s a r IH]; cbn; [ reflexivity |]; rewrite IH.
  destruct r; cbn; [| generalize (la_ev ν (la_cons n n0 n1 r)) ]; generalize (ν a s); intros; ord.
Qed.

Lemma lvl_ev_suc : forall ν l, lvl_ev ν (lvl_suc l) = osuc (lvl_ev ν l).
Proof.
  intros ν [c xs]; unfold lvl_ev, lvl_suc; cbn; rewrite la_ev_suc.
  destruct xs; cbn; [| generalize (la_ev ν (la_cons n n0 n1 xs)) ]; intros; ord.
Qed.

Lemma la_ev_app : forall ν xs ys, la_ev ν (la_app xs ys) = omax (la_ev ν xs) (la_ev ν ys).
Proof.
  induction xs as [| k s a r IH]; intros; cbn; [ symmetry; apply omax_zero_l |].
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
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_ev_max, !lvl_canon_ev by assumption; reflexivity. Qed.

Lemma lvl_canon_max_r : forall l l', lvl_canon (lvl_max l (lvl_canon l')) = lvl_canon (lvl_max l l').
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_ev_max, !lvl_canon_ev by assumption; reflexivity. Qed.

Lemma lvl_canon_suc : forall l, lvl_canon (lvl_suc (lvl_canon l)) = lvl_canon (lvl_suc l).
Proof. intros; apply lvl_canon_iff; intros; rewrite !lvl_ev_suc, !lvl_canon_ev by assumption; reflexivity. Qed.

Lemma lvl_canon_max_cong : forall l1 l1' l2 l2',
    lvl_canon l1 = lvl_canon l1' -> lvl_canon l2 = lvl_canon l2' ->
    lvl_canon (lvl_max l1 l2) = lvl_canon (lvl_max l1' l2').
Proof.
  intros * H1 H2; rewrite lvl_canon_iff in H1, H2 |- *.
  intros; rewrite !lvl_ev_max, H1, H2 by assumption; reflexivity.
Qed.

Lemma lvl_canon_suc_cong : forall l l',
    lvl_canon l = lvl_canon l' -> lvl_canon (lvl_suc l) = lvl_canon (lvl_suc l').
Proof.
  intros * H; rewrite lvl_canon_iff in H |- *.
  intros; rewrite !lvl_ev_suc, H by assumption; reflexivity.
Qed.

(** ** Properties of Every Atom

    Canonicalisation only reorders, merges and drops atoms, so a property of
    all the atoms of a level survives it.  [la_clean] and [la_stuck] are
    instances. *)
Fixpoint la_all (P : ne -> Prop) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ _ a r => P a /\ la_all P r
  end.

Lemma la_all_ins : forall P k s a ys, P a -> la_all P ys -> la_all P (la_ins k s a ys).
Proof.
  induction ys as [| k' t b r IH]; cbn; intros Ha Hys; [ auto |].
  destruct Hys as [Hb Hr]; destruct (at_cmp a s b t) eqn:E; cbn; auto.
Qed.

Lemma la_all_sort : forall P xs, la_all P xs -> la_all P (la_sort xs).
Proof.
  induction xs as [| k s a r IH]; cbn; intros H; [ exact I |].
  destruct H; apply la_all_ins; auto.
Qed.

Lemma la_all_keep : forall P c xs, la_all P xs -> la_all P (la_keep c xs).
Proof.
  intros P c; induction xs as [| k s a r IH]; cbn [la_keep]; intros H; [ exact I |].
  destruct H as [Ha Hr]; destruct (fst c <=? s); cbn; auto.
Qed.

Lemma la_all_canon : forall P c xs, la_all P xs -> la_all P (snd (lvl_canon (c, xs))).
Proof. intros; unfold lvl_canon; cbn; apply la_all_keep, la_all_sort; assumption. Qed.

Lemma la_all_app : forall P xs ys, la_all P xs -> la_all P ys -> la_all P (la_app xs ys).
Proof.
  intros P xs ys; induction xs as [| k s a r IH]; cbn; [ intros _ H; exact H |].
  intros [Ha Hr] Hy; split; auto.
Qed.

Lemma la_all_suc : forall P xs, la_all P xs -> la_all P (la_suc xs).
Proof.
  intros P xs; induction xs as [| k s a r IH]; cbn; [ intros; exact I |].
  intros [Ha Hr]; split; auto.
Qed.

Lemma la_clean_all : forall xs, la_clean xs <-> la_all ne_clean xs.
Proof. induction xs as [| k s a r IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma la_clean_canon : forall c xs, la_clean xs -> la_clean (snd (lvl_canon (c, xs))).
Proof. intros * H; apply la_clean_all, la_all_canon, la_clean_all; assumption. Qed.

Lemma la_clean_sort : forall xs, la_clean xs -> la_clean (la_sort xs).
Proof. intros * H; apply la_clean_all, la_all_sort, la_clean_all; assumption. Qed.

(** ** The Order on Levels

    [lvl_le l l'] is the decidable order [l ⊔ l' = l'], which is the pointwise
    order at every admissible assignment. *)
Definition lvl_le (l l' : lvl) : Prop := lvl_canon (lvl_max l l') = lvl_canon l'.

Theorem lvl_le_correct : forall l l',
    lvl_le l l' <-> (forall ν, lvl_adm ν -> ole (lvl_ev ν l) (lvl_ev ν l')).
Proof.
  intros l l'; unfold lvl_le; rewrite lvl_canon_iff; split; intros H ν Hν; specialize (H ν Hν);
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
  intros * H1 H2; rewrite lvl_le_correct in H1, H2; apply lvl_le_correct; intros ν Hν.
  eapply ole_trans; [ apply H1, Hν | apply H2, Hν ].
Qed.

Lemma lvl_le_canon : forall l l', lvl_canon l = lvl_canon l' -> lvl_le l l'.
Proof.
  intros * H; rewrite lvl_canon_iff in H; apply lvl_le_correct; intros ν Hν; rewrite (H ν Hν); apply ole_refl.
Qed.

Lemma lvl_le_antisym : forall l l', lvl_le l l' -> lvl_le l' l -> lvl_canon l = lvl_canon l'.
Proof.
  intros * H H'; rewrite lvl_le_correct in H, H'; apply lvl_canon_iff; intros ν Hν.
  apply ole_antisym; [ apply H, Hν | apply H', Hν ].
Qed.

Lemma lvl_le_max_left : forall l l', lvl_le l (lvl_max l l').
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_ev_max; apply ole_omax_l. Qed.

Lemma lvl_le_max_right : forall l l', lvl_le l' (lvl_max l l').
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_ev_max; apply ole_omax_r. Qed.

Lemma lvl_le_max_lub : forall l l' l'', lvl_le l l'' -> lvl_le l' l'' -> lvl_le (lvl_max l l') l''.
Proof.
  intros * H H'; rewrite lvl_le_correct in H, H'; apply lvl_le_correct; intros ν Hν.
  rewrite lvl_ev_max; apply omax_lub; [ apply H, Hν | apply H', Hν ].
Qed.

Lemma lvl_le_suc : forall l, lvl_le l (lvl_suc l).
Proof. intros; apply lvl_le_correct; intros; rewrite lvl_ev_suc; apply ole_osuc. Qed.

(** The least level, and the literals. *)
Definition lvl_lit (o : o2) : lvl := (o, la_nil).

Lemma lvl_ev_lit : forall ν o, lvl_ev ν (lvl_lit o) = o.
Proof. intros; unfold lvl_ev, lvl_lit; cbn; apply omax_zero_r. Qed.

Lemma lvl_canon_lit : forall o, lvl_canon (lvl_lit o) = lvl_lit o.
Proof.
  intros; apply lvl_canonical_canon; split; [ exact I | split; [ intros ? ? ? [] |] ].
  cbn; destruct o as [[|] [|]]; [ left | right .. ]; ord.
Qed.

Lemma lvl_le_lit : forall o o', ole o o' -> lvl_le (lvl_lit o) (lvl_lit o').
Proof. intros; apply lvl_le_correct; intros; rewrite !lvl_ev_lit; assumption. Qed.

Lemma lvl_le_zero : forall l, lvl_le lvl_zero l.
Proof. intros; apply lvl_le_correct; intros; unfold lvl_ev, lvl_zero; cbn; rewrite omax_zero_l; apply ole_zero. Qed.

(** ** Levels of a Sort

    A level of sort [n] has a constant of a tier at most [n] and atoms of
    sorts at most [n]: at every admissible assignment it is below ω·(n+1),
    so the limit [ω·(n+1)] absorbs it. *)
Definition lvl_bnd (n : nat) (l : lvl) : Prop :=
  fst (fst l) <= n /\ forall k s a, la_In k s a (snd l) -> s <= n.

Lemma la_sort_In : forall xs k s a, la_In k s a (la_sort xs) -> exists k', la_In k' s a xs.
Proof.
  induction xs as [| j t b r IH]; cbn; intros k s a H; [ contradiction |].
  destruct (la_ins_atoms _ _ _ _ _ _ _ H) as [[-> ->] | [k'' Hin]]; [ eauto |].
  destruct (IH _ _ _ Hin) as [k' ?]; eauto.
Qed.

Lemma lvl_bnd_canon : forall n l, lvl_bnd n l -> lvl_bnd n (lvl_canon l).
Proof.
  intros n [c xs] [Hc Hxs]; unfold lvl_canon, lvl_bnd in *; cbn [fst snd] in *; split.
  - destruct (o2_dominated _ _); cbn; lia.
  - intros k s a Hin; apply la_keep_In in Hin as [Hin _].
    apply la_sort_In in Hin as [k' Hin]; eapply Hxs; exact Hin.
Qed.

Lemma la_suc_In : forall xs k s a, la_In k s a (la_suc xs) -> exists k', la_In k' s a xs.
Proof.
  induction xs as [| j t b r IH]; cbn; intros k s a H; [ contradiction |].
  destruct H as [(_ & -> & ->) | H]; [ eauto |].
  destruct (IH _ _ _ H) as [k' ?]; eauto.
Qed.

Lemma la_app_In : forall xs ys k s a, la_In k s a (la_app xs ys) -> la_In k s a xs \/ la_In k s a ys.
Proof.
  induction xs as [| j t b r IH]; cbn; intros ys k s a H; [ auto |].
  destruct H as [H | H]; [ auto |].
  destruct (IH _ _ _ _ H); auto.
Qed.

Lemma lvl_bnd_lit : forall n o, fst o <= n -> lvl_bnd n (lvl_lit o).
Proof. intros; split; [ assumption | intros ? ? ? [] ]. Qed.

Lemma lvl_bnd_suc : forall n l, lvl_bnd n l -> lvl_bnd n (lvl_suc l).
Proof.
  intros n [c xs] [Hc Ha]; split; [ exact Hc |].
  intros k s a Hin; apply la_suc_In in Hin as [k' Hin]; eapply Ha; exact Hin.
Qed.

Lemma lvl_bnd_max : forall n l l', lvl_bnd n l -> lvl_bnd n l' -> lvl_bnd n (lvl_max l l').
Proof.
  intros n [c xs] [d ys] [Hc Ha] [Hd Hb]; split; [ apply omax_fst_le; assumption |].
  intros k s a Hin; apply la_app_In in Hin as [Hin | Hin]; [ eapply Ha | eapply Hb ]; exact Hin.
Qed.

Lemma lvl_ev_bnd : forall ν n l, lvl_adm ν -> lvl_bnd n l -> fst (lvl_ev ν l) <= n.
Proof.
  intros ν n [c xs] Hν [Hc Hxs]; unfold lvl_ev; cbn [fst snd] in *.
  enough (fst (la_ev ν xs) <= n) by (revert Hc H; generalize (la_ev ν xs); intros; ord).
  induction xs as [| k s a r IH]; cbn; [ lia |].
  assert (Hs : s <= n) by (eapply Hxs; left; auto).
  assert (IH' : fst (la_ev ν r) <= n) by (apply IH; intros; eapply Hxs; right; eassumption).
  specialize (Hν a s); revert IH' Hs Hν; generalize (la_ev ν r) (ν a s); intros; ord.
Qed.

Lemma lvl_canon_absorb : forall n l, lvl_bnd n l ->
    lvl_canon (lvl_max l (lvl_lit (S n, 0))) = lvl_lit (S n, 0).
Proof.
  intros n l Hl; rewrite <- (lvl_canon_lit (S n, 0)) at 2; apply lvl_canon_iff; intros ν Hν.
  rewrite lvl_ev_max, lvl_ev_lit; pose proof (lvl_ev_bnd _ _ _ Hν Hl) as H.
  revert H; generalize (lvl_ev ν l); intros; ord.
Qed.

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
  | la_cons k _ _ r => omax (ofin k) (la_max c r)
  end.

Definition lvl_real (l : lvl) : o2 := la_max (fst l) (snd l).

Lemma lvl_real_ev : forall l, lvl_real l = lvl_ev (fun _ _ => oz) l.
Proof.
  intros [c xs]; unfold lvl_real, lvl_ev; cbn.
  induction xs as [| k s a r IH]; cbn; [ symmetry; apply omax_zero_r |].
  rewrite IH; generalize (la_ev (fun _ _ => oz) r); intros; ord.
Qed.

Lemma lvl_real_canon : forall l, lvl_real (lvl_canon l) = lvl_real l.
Proof. intros; rewrite !lvl_real_ev; apply lvl_canon_ev, lvl_adm_zero. Qed.

Lemma lvl_le_real : forall l l', lvl_le l l' -> ole (lvl_real l) (lvl_real l').
Proof. intros * H; rewrite lvl_le_correct in H; rewrite !lvl_real_ev; apply H, lvl_adm_zero. Qed.

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

    Two small universes join at the canonical join of their levels, a small
    and a large one at the large one, and two large ones at the larger.  (The
    universe a [Π] is inferred at is [Core.Syntactic.Fresh.unf_pi_tm]: its
    codomain's level lives under the domain, and is bounded first.) *)
Definition unf_max (u v : unf) : unf :=
  match u, v with
  | uns l, uns l' => uns (lvl_canon (lvl_max l l'))
  | uns _, unl j => unl j
  | unl i, uns _ => unl i
  | unl i, unl j => unl (Nat.max i j)
  end.

Lemma unf_le_max_left : forall u v, unf_le u (unf_max u v).
Proof.
  intros [l |] [l' |]; cbn [unf_max unf_le]; try solve [ exact I | lia ].
  apply lvl_le_correct; intros ν Hν; rewrite lvl_canon_ev, lvl_ev_max by exact Hν; apply ole_omax_l.
Qed.

Lemma unf_le_max_right : forall u v, unf_le v (unf_max u v).
Proof.
  intros [l |] [l' |]; cbn [unf_max unf_le]; try solve [ exact I | lia ].
  apply lvl_le_correct; intros ν Hν; rewrite lvl_canon_ev, lvl_ev_max by exact Hν; apply ole_omax_r.
Qed.

(** A level below a literal has no atom of a sort at least the literal's
    tier: such an atom can be assigned [ω·s + N] for any [N].  Below a finite
    literal, then, a level has no atom at all. *)
Lemma lvl_le_lit_sorts : forall l o, lvl_le l (lvl_lit o) ->
    forall k s a, la_In k s a (snd l) -> s < fst o.
Proof.
  intros [c xs] o H k s a Hin; rewrite lvl_le_correct in H; cbn [snd] in Hin.
  destruct (Nat.lt_ge_cases s (fst o)) as [| Hs]; [ assumption | exfalso ].
  specialize (H (ν_at a s (S (snd o))) (ν_at_adm _ _ _)); rewrite lvl_ev_lit in H.
  unfold lvl_ev in H; cbn [fst snd] in H.
  assert (Hge : ole (s, S (snd o)) (la_ev (ν_at a s (S (snd o))) xs)).
  { clear H; induction xs as [| k0 t b r IH]; cbn in Hin |- *; [ contradiction |].
    destruct Hin as [(<- & <- & <-) | Hin].
    - unfold ν_at at 1; rewrite at_cmp_refl.
      generalize (la_ev (ν_at a s (S (snd o))) r); intros; ord.
    - specialize (IH Hin); revert IH; generalize (la_ev (ν_at a s (S (snd o))) r) (ν_at a s (S (snd o)) b t); intros; ord. }
  revert H Hge Hs; generalize (la_ev (ν_at a s (S (snd o))) xs); intros; ord.
Qed.

Lemma lvl_le_lit_closed : forall l n, lvl_le l (lvl_lit (ofin n)) -> snd l = la_nil.
Proof.
  intros [c xs] n H; destruct xs as [| k s a r]; [ reflexivity | exfalso ].
  pose proof (lvl_le_lit_sorts _ _ H k s a ltac:(cbn; left; auto)) as Hs; cbn in Hs; lia.
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
