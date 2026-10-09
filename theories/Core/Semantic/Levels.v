From Stdlib Require Import Lia List PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER.
Import Domain_Notations Fixed_Notations.

(** * Levels in the Semantics

    Evaluation of [succl] and [maxl] only flattens: it adds to the offsets of
    the atoms, or joins the constants and concatenates the atoms.  Readback
    canonicalises, so two levels are related ([per_lvl]) exactly when their
    canonical forms agree, and the level equations hold in the model by the
    arithmetic of [lvl_canon] — [lvl_canon_iff] reduces each of them to an
    identity between maxima of ordinals.

    A value of type [Level] is flat, or a neutral, which is the single atom at
    offset [0]: that is its flat view ([dlvl_view]).  [dlvl_shape] says which of
    the two a value is; no other value is read back at [Level]. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Variant dlvl_shape : domain -> Prop :=
| dls_lvl : forall c xs, dlvl_shape (lvᵈ c xs)
| dls_neut : forall a m, dlvl_shape (⇑ a m).

Hint Constructors dlvl_shape : mctt.

Lemma dlvl_shape_suc : forall l, dlvl_shape (dlvl_suc l).
Proof. intros; unfold dlvl_suc; constructor. Qed.

Lemma dlvl_shape_max : forall l l', dlvl_shape (dlvl_max l l').
Proof. intros; unfold dlvl_max; constructor. Qed.

Lemma dlvl_shape_lit : forall n, dlvl_shape (dlvl_lit n).
Proof. intros; unfold dlvl_lit; constructor. Qed.

Hint Resolve dlvl_shape_suc dlvl_shape_max dlvl_shape_lit : mctt.

(** The flat view of each operation, as equations rather than by unfolding, so
    that [dlvl_cst] and [dlvl_atoms] stay abstract on a level that is not one
    of the operations. *)
Fact dlvl_cst_lit : forall n, dlvl_cst (dlvl_lit n) = n.
Proof. reflexivity. Qed.

Fact dlvl_atoms_lit : forall n, dlvl_atoms (dlvl_lit n) = nil.
Proof. reflexivity. Qed.

Fact dlvl_cst_suc : forall l, dlvl_cst (dlvl_suc l) = osuc (dlvl_cst l).
Proof. reflexivity. Qed.

Fact dlvl_atoms_suc : forall l,
    dlvl_atoms (dlvl_suc l) = List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) (dlvl_atoms l).
Proof. reflexivity. Qed.

Fact dlvl_cst_max : forall l l', dlvl_cst (dlvl_max l l') = omax (dlvl_cst l) (dlvl_cst l').
Proof. reflexivity. Qed.

Fact dlvl_atoms_max : forall l l', dlvl_atoms (dlvl_max l l') = dlvl_atoms l ++ dlvl_atoms l'.
Proof. reflexivity. Qed.

(** ** Readback of the Atoms *)

Lemma read_la_app : forall s xs ys xs' ys',
    Rla xs in s ↘ ys ->
    Rla xs' in s ↘ ys' ->
    Rla (xs ++ xs') in s ↘ la_app ys ys'.
Proof.
  intros * H H'; induction H; cbn; eauto with mctt.
Qed.

Lemma read_la_suc : forall s xs ys,
    Rla xs in s ↘ ys ->
    Rla (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs) in s ↘ la_suc ys.
Proof.
  intros * H; induction H; cbn; eauto with mctt.
Qed.

Hint Resolve read_la_app read_la_suc : mctt.

(** ** The Canonical Form of a Level at a Length

    [dlvl_canon s l L]: at length [s], the atoms of [l] read back and make the
    canonical level [L].  It is what [l] reads back as ([dlvl_canon_read]), it
    is unique, and it computes on the level operations — which is how the level
    equations are proved. *)
Definition dlvl_canon (s : nat) (l : domain) (L : lvl) : Prop :=
  exists ys, Rla (dlvl_atoms l) in s ↘ ys /\ L = lvl_canon (dlvl_cst l, ys).

Lemma dlvl_canon_read : forall s l L,
    dlvl_shape l ->
    dlvl_canon s l L ->
    Rnf ⇓ Levelᵈ l in s ↘ nf_lvl_of L.
Proof.
  intros * Hl [ys [Hys ->]]; destruct Hl; cbn in *.
  - constructor; assumption.
  - progressive_inversion.
    match goal with H : Rla nil in _ ↘ _ |- _ => inversion H end.
    constructor; assumption.
Qed.

Lemma dlvl_canon_of_read : forall s l L,
    Rnf ⇓ Levelᵈ l in s ↘ L ->
    dlvl_shape l /\ exists L', L = nf_lvl_of L' /\ dlvl_canon s l L'.
Proof.
  inversion 1; subst.
  - split; [ constructor |].
    eexists (lvl_canon (_, _)); split; [ reflexivity |].
    eexists; split; [ eassumption | reflexivity ].
  - split; [ constructor |].
    exists (oz, la_cons 0 (dsort a) M la_nil); split; [ reflexivity |].
    eexists; split; [ repeat constructor; eassumption | reflexivity ].
Qed.

Lemma dlvl_canon_functional : forall s l L L',
    dlvl_canon s l L ->
    dlvl_canon s l L' ->
    L = L'.
Proof.
  intros * [ys [Hys ->]] [ys' [Hys' ->]].
  assert (ys = ys') as -> by (eapply functional_read_la; eassumption).
  reflexivity.
Qed.

(** A canonical form from a reading of the atoms is canonical. *)
Lemma dlvl_canon_canonical : forall s l L,
    dlvl_canon s l L ->
    lvl_canon L = L.
Proof.
  intros * [ys [_ ->]]; apply lvl_canon_idem.
Qed.

Lemma dlvl_canon_lit : forall s n, dlvl_canon s (dlvl_lit n) (lvl_lit n).
Proof.
  intros; eexists; rewrite dlvl_atoms_lit, dlvl_cst_lit.
  split; [ constructor | symmetry; apply lvl_canon_lit ].
Qed.

Lemma dlvl_canon_suc : forall s l L,
    dlvl_canon s l L ->
    dlvl_canon s (dlvl_suc l) (lvl_canon (lvl_suc L)).
Proof.
  intros * [ys [Hys ->]]; eexists; rewrite dlvl_atoms_suc, dlvl_cst_suc.
  split; [ apply read_la_suc; eassumption |].
  rewrite lvl_canon_suc; reflexivity.
Qed.

Lemma dlvl_canon_max : forall s l L m M,
    dlvl_canon s l L ->
    dlvl_canon s m M ->
    dlvl_canon s (dlvl_max l m) (lvl_canon (lvl_max L M)).
Proof.
  intros * [ys [Hys ->]] [zs [Hzs ->]]; eexists; rewrite dlvl_atoms_max, dlvl_cst_max.
  split; [ apply read_la_app; eassumption |].
  rewrite lvl_canon_max_l, lvl_canon_max_r; reflexivity.
Qed.

Hint Resolve dlvl_canon_lit dlvl_canon_suc dlvl_canon_max : mctt.

(** ** The Level PER through Canonical Forms

    Two levels are related exactly when their canonical forms agree at every
    length.  These are the introduction and the elimination form; every
    equation below is an identity of canonical forms. *)
Lemma per_lvl_of : forall l l',
    dlvl_shape l ->
    dlvl_shape l' ->
    (forall s, exists L, dlvl_canon s l L) ->
    (forall s, exists L, dlvl_canon s l' L) ->
    (forall s L L', dlvl_canon s l L -> dlvl_canon s l' L' -> L = L') ->
    Dom l ≈ l' ∈ per_lvl.
Proof.
  intros * Hl Hl' Hex Hex' Heq s.
  destruct (Hex s) as [L HL]; destruct (Hex' s) as [L' HL'].
  exists (nf_lvl_of L); split; [ apply dlvl_canon_read; assumption |].
  rewrite (Heq _ _ _ HL HL'); apply dlvl_canon_read; assumption.
Qed.

Lemma per_lvl_shape : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    dlvl_shape l /\ dlvl_shape l'.
Proof.
  intros * H.
  destruct (H 0) as [L [HL HL']].
  apply dlvl_canon_of_read in HL as [? _]; apply dlvl_canon_of_read in HL' as [? _].
  split; assumption.
Qed.

Lemma per_lvl_ex : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    forall s, exists L, dlvl_canon s l L.
Proof.
  intros * H s.
  destruct (H s) as [L [HL _]]; apply dlvl_canon_of_read in HL as [_ [L' [_ ?]]]; eauto.
Qed.

Lemma per_lvl_ex_right : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    forall s, exists L, dlvl_canon s l' L.
Proof.
  intros * H; apply (per_lvl_ex l' l), per_lvl_sym; assumption.
Qed.

Lemma per_lvl_eq : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    forall s L L',
      dlvl_canon s l L ->
      dlvl_canon s l' L' ->
      L = L'.
Proof.
  intros * H * HL HL'.
  destruct (H s) as [W [HW HW']].
  apply dlvl_canon_of_read in HW as [_ [L1 [-> HL1]]].
  apply dlvl_canon_of_read in HW' as [_ [L2 [Heq HL2]]].
  assert (L1 = L) as <- by (eapply dlvl_canon_functional; eassumption).
  assert (L2 = L') as <- by (eapply dlvl_canon_functional; eassumption).
  apply nf_lvl_of_inj; exact Heq.
Qed.

(** ** The Level Operations Respect the PER

    Each proof reads the atoms of the levels at a length, computes the
    canonical form of each side by [dlvl_canon_suc] and [dlvl_canon_max], and
    compares the two by [lvl_canon_iff]. *)

Lemma per_lvl_suc : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom dlvl_suc l ≈ dlvl_suc l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    eexists; apply dlvl_canon_suc; exact HA.
  - intros s; destruct (per_lvl_ex_right _ _ H s) as [B HB].
    eexists; apply dlvl_canon_suc; exact HB.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA].
    destruct (per_lvl_ex_right _ _ H s) as [B HB].
    assert (A = B) as <- by (eapply per_lvl_eq; [ exact H | exact HA | exact HB ]).
    assert (L = lvl_canon (lvl_suc A)) as ->
      by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_suc; exact HA ]).
    assert (L' = lvl_canon (lvl_suc A)) as ->
      by (eapply dlvl_canon_functional; [ exact HL' | apply dlvl_canon_suc; exact HB ]).
    reflexivity.
Qed.

Lemma per_lvl_max : forall l l' m m',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom dlvl_max l m ≈ dlvl_max l' m' ∈ per_lvl.
Proof.
  intros * H H'.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  pose proof (per_lvl_shape _ _ H') as [Hm Hm'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA]; destruct (per_lvl_ex _ _ H' s) as [B HB].
    eexists; apply dlvl_canon_max; [ exact HA | exact HB ].
  - intros s; destruct (per_lvl_ex_right _ _ H s) as [A HA]; destruct (per_lvl_ex_right _ _ H' s) as [B HB].
    eexists; apply dlvl_canon_max; [ exact HA | exact HB ].
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA]; destruct (per_lvl_ex _ _ H' s) as [B HB].
    destruct (per_lvl_ex_right _ _ H s) as [A' HA']; destruct (per_lvl_ex_right _ _ H' s) as [B' HB'].
    assert (A = A') as <- by (eapply per_lvl_eq; [ exact H | exact HA | exact HA' ]).
    assert (B = B') as <- by (eapply per_lvl_eq; [ exact H' | exact HB | exact HB' ]).
    assert (L = lvl_canon (lvl_max A B)) as ->
      by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_max; [ exact HA | exact HB ] ]).
    assert (L' = lvl_canon (lvl_max A B)) as ->
      by (eapply dlvl_canon_functional; [ exact HL' | apply dlvl_canon_max; [ exact HA' | exact HB' ] ]).
    reflexivity.
Qed.

Hint Resolve per_lvl_suc per_lvl_max : mctt.

(** ** Levels of a Sort

    The elements of [Level@n] read back as canonical levels of sort [n]
    ([per_lvl_at]).  Readback keeps the sorts of the atoms, which are read off
    the types of the neutrals, and the level operations keep the bound. *)
Lemma per_lvl_at_canon_bnd : forall n l l' s L,
    Dom l ≈ l' ∈ per_lvl_at n ->
    dlvl_canon s l L ->
    lvl_bnd n L.
Proof.
  intros * H HL.
  destruct (H s) as (L' & HL' & _ & Hb).
  apply dlvl_canon_of_read in HL' as [_ [L'' [Heq HL'']]].
  apply nf_lvl_of_inj in Heq as <-.
  assert (L = L') as -> by (eapply dlvl_canon_functional; eassumption).
  exact Hb.
Qed.

(** A level related to one whose canonical forms are of sort [n] is an
    element of [Level@n]. *)
Lemma per_lvl_at_intro : forall n l l',
    Dom l ≈ l' ∈ per_lvl ->
    (forall s L, dlvl_canon s l L -> lvl_bnd n L) ->
    Dom l ≈ l' ∈ per_lvl_at n.
Proof.
  intros * H Hb s.
  destruct (H s) as (W & HW & HW').
  pose proof HW as HW0; apply dlvl_canon_of_read in HW0 as [_ [L [-> HL]]].
  exists L; split; [| split ]; [ exact HW | exact HW' | eapply Hb; exact HL ].
Qed.

Lemma per_lvl_at_of_lvl : forall n l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom l ≈ l ∈ per_lvl_at n ->
    Dom l ≈ l' ∈ per_lvl_at n.
Proof.
  intros * H Hb; apply per_lvl_at_intro; [ exact H |].
  intros; eapply per_lvl_at_canon_bnd; eassumption.
Qed.

Lemma per_lvl_at_lit : forall n o, fst o <= n -> Dom dlvl_lit o ≈ dlvl_lit o ∈ per_lvl_at n.
Proof.
  intros; apply per_lvl_at_intro; [ apply per_lvl_lit |].
  intros s L HL; assert (L = lvl_lit o) as -> by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_lit ]).
  apply lvl_bnd_lit; assumption.
Qed.

Lemma per_lvl_at_suc : forall n l l',
    Dom l ≈ l' ∈ per_lvl_at n -> Dom dlvl_suc l ≈ dlvl_suc l' ∈ per_lvl_at n.
Proof.
  intros * H; pose proof (per_lvl_at_lvl _ _ _ H) as Hl.
  apply per_lvl_at_intro; [ apply per_lvl_suc; exact Hl |].
  intros s L HL; destruct (per_lvl_ex _ _ Hl s) as [A HA].
  assert (L = lvl_canon (lvl_suc A)) as ->
    by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_suc; exact HA ]).
  apply lvl_bnd_canon, lvl_bnd_suc; eapply per_lvl_at_canon_bnd; eassumption.
Qed.

Lemma per_lvl_at_max : forall n l l' m m',
    Dom l ≈ l' ∈ per_lvl_at n -> Dom m ≈ m' ∈ per_lvl_at n ->
    Dom dlvl_max l m ≈ dlvl_max l' m' ∈ per_lvl_at n.
Proof.
  intros * H H'; pose proof (per_lvl_at_lvl _ _ _ H) as Hl; pose proof (per_lvl_at_lvl _ _ _ H') as Hm.
  apply per_lvl_at_intro; [ apply per_lvl_max; assumption |].
  intros s L HL; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
  assert (L = lvl_canon (lvl_max A B)) as ->
    by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_max; [ exact HA | exact HB ] ]).
  apply lvl_bnd_canon, lvl_bnd_max; [ exact (per_lvl_at_canon_bnd _ _ _ _ _ H HA) | exact (per_lvl_at_canon_bnd _ _ _ _ _ H' HB) ].
Qed.

Hint Resolve per_lvl_at_lit per_lvl_at_suc per_lvl_at_max : mctt.

(** The limit [ω·(n+1)] absorbs every level of sort [n]. *)
Lemma per_lvl_absorb : forall n l l',
    Dom l ≈ l' ∈ per_lvl_at n ->
    Dom dlvl_max l (dlvl_lit (S n, 0)) ≈ dlvl_lit (S n, 0) ∈ per_lvl.
Proof.
  intros * H; pose proof (per_lvl_at_lvl _ _ _ H) as Hl0.
  pose proof (per_lvl_shape _ _ Hl0) as [Hl _].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | eauto with mctt |].
  - intros s; destruct (per_lvl_ex _ _ Hl0 s) as [A HA].
    eexists; apply dlvl_canon_max; [ exact HA | apply dlvl_canon_lit ].
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl0 s) as [A HA].
    assert (L = lvl_canon (lvl_max A (lvl_lit (S n, 0)))) as ->
      by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_max; [ exact HA | apply dlvl_canon_lit ] ]).
    assert (L' = lvl_lit (S n, 0)) as ->
      by (eapply dlvl_canon_functional; [ exact HL' | apply dlvl_canon_lit ]).
    apply lvl_canon_absorb; eapply per_lvl_at_canon_bnd; eassumption.
Qed.

(** ** The Level Equations in the Model

    Each is the identity between the canonical forms of the two sides, which
    [lvl_canon_iff] turns into arithmetic of maxima. *)

Lemma per_lvl_llit_suc : forall a b,
    Dom dlvl_lit (a, S b) ≈ dlvl_suc (dlvl_lit (a, b)) ∈ per_lvl.
Proof.
  intros; apply per_lvl_of; [ mauto 3 | mauto 3 | eauto with mctt | eauto with mctt |].
  intros s L L' HL HL'.
  assert (L = lvl_lit (a, S b)) as ->
    by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_lit ]).
  assert (L' = lvl_canon (lvl_suc (lvl_lit (a, b)))) as ->
    by (eapply dlvl_canon_functional; [ exact HL' | apply dlvl_canon_suc, dlvl_canon_lit ]).
  rewrite <- (lvl_canon_lit (a, S b)); apply lvl_canon_iff; intros ν Hν.
  rewrite lvl_ev_suc, !lvl_ev_lit; reflexivity.
Qed.

Lemma per_lvl_max_zero : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom dlvl_max (dlvl_lit oz) l ≈ l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | assumption | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    eexists; apply dlvl_canon_max; [ apply dlvl_canon_lit | exact HA ].
  - intros s; exact (per_lvl_ex_right _ _ H s).
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA].
    assert (L = lvl_canon (lvl_max (lvl_lit oz) A)) as ->
      by (eapply dlvl_canon_functional;
          [ exact HL | apply dlvl_canon_max; [ apply dlvl_canon_lit | exact HA ] ]).
    assert (L' = A) as -> by (symmetry; eapply per_lvl_eq; [ exact H | exact HA | exact HL' ]).
    transitivity (lvl_canon A); [| exact (dlvl_canon_canonical _ _ _ HA) ].
    apply lvl_canon_iff; intros ν Hν; rewrite !lvl_ev_max, lvl_ev_lit; lvl_ord.
Qed.

Lemma per_lvl_max_assoc : forall l l' m m' n n',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom n ≈ n' ∈ per_lvl ->
    Dom dlvl_max (dlvl_max l m) n ≈ dlvl_max l' (dlvl_max m' n') ∈ per_lvl.
Proof.
  intros * Hl Hm Hn.
  pose proof (per_lvl_shape _ _ Hl) as [Hls Hls'].
  pose proof (per_lvl_shape _ _ Hm) as [Hms Hms'].
  pose proof (per_lvl_shape _ _ Hn) as [Hns Hns'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB];
      destruct (per_lvl_ex _ _ Hn s) as [C HC].
    eexists; repeat apply dlvl_canon_max; [ exact HA | exact HB | exact HC ].
  - intros s; destruct (per_lvl_ex_right _ _ Hl s) as [A HA]; destruct (per_lvl_ex_right _ _ Hm s) as [B HB];
      destruct (per_lvl_ex_right _ _ Hn s) as [C HC].
    eexists; repeat apply dlvl_canon_max; [ exact HA | exact HB | exact HC ].
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB];
      destruct (per_lvl_ex _ _ Hn s) as [C HC].
    destruct (per_lvl_ex_right _ _ Hl s) as [A' HA']; destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'];
      destruct (per_lvl_ex_right _ _ Hn s) as [C' HC'].
    assert (A = A') as <- by (eapply per_lvl_eq; [ exact Hl | exact HA | exact HA' ]).
    assert (B = B') as <- by (eapply per_lvl_eq; [ exact Hm | exact HB | exact HB' ]).
    assert (C = C') as <- by (eapply per_lvl_eq; [ exact Hn | exact HC | exact HC' ]).
    assert (L = lvl_canon (lvl_max (lvl_canon (lvl_max A B)) C)) as ->
      by (eapply dlvl_canon_functional;
          [ exact HL | repeat apply dlvl_canon_max; [ exact HA | exact HB | exact HC ] ]).
    assert (L' = lvl_canon (lvl_max A (lvl_canon (lvl_max B C)))) as ->
      by (eapply dlvl_canon_functional;
          [ exact HL' | repeat apply dlvl_canon_max; [ exact HA' | exact HB' | exact HC' ] ]).
    rewrite lvl_canon_max_l, lvl_canon_max_r.
    apply lvl_canon_iff; intros ν Hν; rewrite !lvl_ev_max; lvl_ord.
Qed.

Lemma per_lvl_max_comm : forall l l' m m',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom dlvl_max l m ≈ dlvl_max m' l' ∈ per_lvl.
Proof.
  intros * Hl Hm.
  pose proof (per_lvl_shape _ _ Hl) as [Hls Hls'].
  pose proof (per_lvl_shape _ _ Hm) as [Hms Hms'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    eexists; apply dlvl_canon_max; [ exact HA | exact HB ].
  - intros s; destruct (per_lvl_ex_right _ _ Hl s) as [A HA]; destruct (per_lvl_ex_right _ _ Hm s) as [B HB].
    eexists; apply dlvl_canon_max; [ exact HB | exact HA ].
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    destruct (per_lvl_ex_right _ _ Hl s) as [A' HA']; destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'].
    assert (A = A') as <- by (eapply per_lvl_eq; [ exact Hl | exact HA | exact HA' ]).
    assert (B = B') as <- by (eapply per_lvl_eq; [ exact Hm | exact HB | exact HB' ]).
    assert (L = lvl_canon (lvl_max A B)) as ->
      by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_max; [ exact HA | exact HB ] ]).
    assert (L' = lvl_canon (lvl_max B A)) as ->
      by (eapply dlvl_canon_functional; [ exact HL' | apply dlvl_canon_max; [ exact HB' | exact HA' ] ]).
    apply lvl_canon_iff; intros ν Hν; rewrite !lvl_ev_max; lvl_ord.
Qed.

Lemma per_lvl_max_idem : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom dlvl_max l l ≈ l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | assumption | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    eexists; apply dlvl_canon_max; [ exact HA | exact HA ].
  - intros s; exact (per_lvl_ex_right _ _ H s).
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA].
    assert (L = lvl_canon (lvl_max A A)) as ->
      by (eapply dlvl_canon_functional; [ exact HL | apply dlvl_canon_max; [ exact HA | exact HA ] ]).
    assert (L' = A) as -> by (symmetry; eapply per_lvl_eq; [ exact H | exact HA | exact HL' ]).
    transitivity (lvl_canon A); [| exact (dlvl_canon_canonical _ _ _ HA) ].
    apply lvl_canon_iff; intros ν Hν; rewrite !lvl_ev_max; lvl_ord.
Qed.

Lemma per_lvl_suc_max : forall l l' m m',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom dlvl_suc (dlvl_max l m) ≈ dlvl_max (dlvl_suc l') (dlvl_suc m') ∈ per_lvl.
Proof.
  intros * Hl Hm.
  pose proof (per_lvl_shape _ _ Hl) as [Hls Hls'].
  pose proof (per_lvl_shape _ _ Hm) as [Hms Hms'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    eexists; apply dlvl_canon_suc, dlvl_canon_max; [ exact HA | exact HB ].
  - intros s; destruct (per_lvl_ex_right _ _ Hl s) as [A HA]; destruct (per_lvl_ex_right _ _ Hm s) as [B HB].
    eexists; apply dlvl_canon_max; apply dlvl_canon_suc; [ exact HA | exact HB ].
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    destruct (per_lvl_ex_right _ _ Hl s) as [A' HA']; destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'].
    assert (A = A') as <- by (eapply per_lvl_eq; [ exact Hl | exact HA | exact HA' ]).
    assert (B = B') as <- by (eapply per_lvl_eq; [ exact Hm | exact HB | exact HB' ]).
    assert (L = lvl_canon (lvl_suc (lvl_canon (lvl_max A B)))) as ->
      by (eapply dlvl_canon_functional;
          [ exact HL | apply dlvl_canon_suc, dlvl_canon_max; [ exact HA | exact HB ] ]).
    assert (L' = lvl_canon (lvl_max (lvl_canon (lvl_suc A)) (lvl_canon (lvl_suc B)))) as ->
      by (eapply dlvl_canon_functional;
          [ exact HL' | apply dlvl_canon_max; apply dlvl_canon_suc; [ exact HA' | exact HB' ] ]).
    rewrite lvl_canon_suc, lvl_canon_max_l, lvl_canon_max_r.
    apply lvl_canon_iff; intros ν Hν; rewrite !lvl_ev_suc, !lvl_ev_max, !lvl_ev_suc; lvl_ord.
Qed.

Lemma per_lvl_max_suc : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom dlvl_max l (dlvl_suc l) ≈ dlvl_suc l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    eexists; apply dlvl_canon_max; [ exact HA | apply dlvl_canon_suc; exact HA ].
  - intros s; destruct (per_lvl_ex_right _ _ H s) as [B HB].
    eexists; apply dlvl_canon_suc; exact HB.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA]; destruct (per_lvl_ex_right _ _ H s) as [B HB].
    assert (A = B) as <- by (eapply per_lvl_eq; [ exact H | exact HA | exact HB ]).
    assert (L = lvl_canon (lvl_max A (lvl_canon (lvl_suc A)))) as ->
      by (eapply dlvl_canon_functional;
          [ exact HL | apply dlvl_canon_max; [ exact HA | apply dlvl_canon_suc; exact HA ] ]).
    assert (L' = lvl_canon (lvl_suc A)) as ->
      by (eapply dlvl_canon_functional; [ exact HL' | apply dlvl_canon_suc; exact HB ]).
    rewrite lvl_canon_max_r.
    apply lvl_canon_iff; intros ν Hν; rewrite !lvl_ev_max, !lvl_ev_suc; lvl_ord.
Qed.

(** ** The Order on Levels from a Join

    [maxl l m ≈ m'] with [m ≈ m'] says that [l] is below [m'] in the canonical
    order: at every length, the canonical form of the join is that of [m'],
    which is what [lvl_le] states.  This is the semantic content of the
    premise of [wf_subtyp_suniv]. *)
Lemma per_sublvl_of_max : forall l m m',
    Dom l ≈ l ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom dlvl_max l m ≈ m' ∈ per_lvl ->
    per_sublvl l m'.
Proof.
  intros * Hl Hm Hmax s.
  pose proof (per_lvl_shape _ _ Hl) as [Hls _].
  pose proof (per_lvl_shape _ _ Hm) as [_ Hms'].
  destruct (per_lvl_ex _ _ Hl s) as [A HA].
  destruct (per_lvl_ex _ _ Hm s) as [B HB].
  destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'].
  assert (B = B') as <- by (eapply per_lvl_eq; [ exact Hm | exact HB | exact HB' ]).
  assert (lvl_canon (lvl_max A B) = B) as Hj
    by (eapply per_lvl_eq; [ exact Hmax | apply dlvl_canon_max; [ exact HA | exact HB ] | exact HB' ]).
  exists A, B; repeat split;
    [ apply dlvl_canon_read; assumption | apply dlvl_canon_read; assumption |].
  unfold lvl_le; rewrite Hj; symmetry; exact (dlvl_canon_canonical _ _ _ HB').
Qed.

(** The same from readbacks: if [maxl l l'] and [l'] read back equally, the
    canonical forms of [l] and [l'] are in [lvl_le].  This is what the
    algorithmic subtyping of two small universes decides. *)
Lemma read_max_lvl_le : forall s n1 n2 n3 n4 l l' L L' W,
    Rnf ⇓ (Levelᵈ@n1) l in s ↘ nf_lvl_of L ->
    Rnf ⇓ (Levelᵈ@n2) l' in s ↘ nf_lvl_of L' ->
    Rnf ⇓ (Levelᵈ@n3) (dlvl_max l l') in s ↘ W ->
    Rnf ⇓ (Levelᵈ@n4) l' in s ↘ W ->
    lvl_le L L'.
Proof.
  intros * HL HL' Hmax Hmax'.
  apply (read_nf_level_sort _ _ 0 _ _) in HL, HL', Hmax, Hmax'.
  pose proof (functional_read_nf _ _ _ _ HL' Hmax') as <-.
  apply dlvl_canon_of_read in HL as [_ [L1 [Heq1 HL1]]].
  apply nf_lvl_of_inj in Heq1 as <-.
  apply dlvl_canon_of_read in HL' as [_ [L2 [Heq2 HL2]]].
  apply nf_lvl_of_inj in Heq2 as <-.
  apply dlvl_canon_of_read in Hmax as [_ [L3 [Heq3 HL3]]].
  apply nf_lvl_of_inj in Heq3.
  assert (L3 = lvl_canon (lvl_max L L')) as Hc
    by (eapply dlvl_canon_functional; [ exact HL3 | apply dlvl_canon_max; eassumption ]).
  unfold lvl_le; rewrite <- Hc, <- Heq3, (dlvl_canon_canonical _ _ _ HL2); reflexivity.
Qed.

End Fixed_GCtx.

#[export]
Hint Constructors dlvl_shape : mctt.
#[export]
Hint Resolve dlvl_shape_suc dlvl_shape_max dlvl_shape_lit : mctt.
#[export]
Hint Resolve read_la_app read_la_suc : mctt.
#[export]
Hint Resolve dlvl_canon_lit dlvl_canon_suc dlvl_canon_max : mctt.
#[export]
Hint Resolve per_lvl_suc per_lvl_max : mctt.
#[export]
Hint Resolve per_lvl_at_lit per_lvl_at_suc per_lvl_at_max : mctt.
