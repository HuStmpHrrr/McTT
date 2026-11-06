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
    offset [0]: that is its flat view ([domain_level_view]).  [domain_level_shape] says which of
    the two a value is; no other value is read back at [Level]. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Variant domain_level_shape : domain -> Prop :=
| domain_level_shape_lvl : forall c xs, domain_level_shape (lvᵈ c xs)
| domain_level_shape_neut : forall a m, domain_level_shape (⇑ a m).

Hint Constructors domain_level_shape : mctt.

Lemma domain_level_shape_suc : forall l, domain_level_shape (domain_level_suc l).
Proof. intros; unfold domain_level_suc; constructor. Qed.

Lemma domain_level_shape_max : forall l l', domain_level_shape (domain_level_max l l').
Proof. intros; unfold domain_level_max; constructor. Qed.

Lemma domain_level_shape_lit : forall n, domain_level_shape (domain_level_lit n).
Proof. intros; unfold domain_level_lit; constructor. Qed.

Hint Resolve domain_level_shape_suc domain_level_shape_max domain_level_shape_lit : mctt.

(** The flat view of each operation, as equations rather than by unfolding, so
    that [domain_level_const] and [domain_level_atoms] stay abstract on a level that is not one
    of the operations. *)
Fact domain_level_const_lit : forall n, domain_level_const (domain_level_lit n) = n.
Proof. reflexivity. Qed.

Fact domain_level_atoms_lit : forall n, domain_level_atoms (domain_level_lit n) = nil.
Proof. reflexivity. Qed.

Fact domain_level_const_suc : forall l, domain_level_const (domain_level_suc l) = ordinal_succ (domain_level_const l).
Proof. reflexivity. Qed.

Fact domain_level_atoms_suc : forall l,
    domain_level_atoms (domain_level_suc l) = List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) (domain_level_atoms l).
Proof. reflexivity. Qed.

Fact domain_level_const_max : forall l l', domain_level_const (domain_level_max l l') = ordinal_max (domain_level_const l) (domain_level_const l').
Proof. reflexivity. Qed.

Fact domain_level_atoms_max : forall l l', domain_level_atoms (domain_level_max l l') = domain_level_atoms l ++ domain_level_atoms l'.
Proof. reflexivity. Qed.

(** ** Readback of the Atoms *)

Lemma read_level_atoms_app : forall s xs ys xs' ys',
    Rla xs in s ↘ ys ->
    Rla xs' in s ↘ ys' ->
    Rla (xs ++ xs') in s ↘ (ys ++ ys').
Proof.
  intros * H H'; induction H; cbn; eauto with mctt.
Qed.

Lemma read_level_atoms_suc : forall s xs ys,
    Rla xs in s ↘ ys ->
    Rla (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs) in s ↘ level_atoms_suc ys.
Proof.
  intros * H; induction H; cbn; eauto with mctt.
Qed.

Hint Resolve read_level_atoms_app read_level_atoms_suc : mctt.

(** ** The Canonical Form of a Level at a Length

    [domain_level_canon s l L]: at length [s], the atoms of [l] read back and make the
    canonical level [L].  It is what [l] reads back as ([domain_level_canon_read]), it
    is unique, and it computes on the level operations — which is how the level
    equations are proved. *)
Definition domain_level_canon (s : nat) (l : domain) (L : lvl) : Prop :=
  exists ys, Rla (domain_level_atoms l) in s ↘ ys /\ L = lvl_canon (domain_level_const l, ys).

Lemma domain_level_canon_read : forall s l L,
    domain_level_shape l ->
    domain_level_canon s l L ->
    Rnf ⇓ Levelᵈ l in s ↘ nf_lvl_of L.
Proof.
  intros * Hl [ys [Hys ->]]; destruct Hl; cbn in *.
  - constructor; assumption.
  - progressive_inversion.
    match goal with H : Rla nil in _ ↘ _ |- _ => inversion H end.
    constructor; assumption.
Qed.

Lemma domain_level_canon_of_read : forall s l L,
    Rnf ⇓ Levelᵈ l in s ↘ L ->
    domain_level_shape l /\ exists L', L = nf_lvl_of L' /\ domain_level_canon s l L'.
Proof.
  inversion 1; subst; try solve [ exfalso; clear_wrong_kind ].
  - split; [ constructor |].
    eexists (lvl_canon (_, _)); split; [ reflexivity |].
    eexists; split; [ eassumption | reflexivity ].
  - split; [ constructor |].
    (** The atom is stored as read, as [lvl_canon] stores atoms. *)
    exists (lvl_canon (ordinal_zero, cons (mk_level_atom 0 (domain_level_sort a) M) nil)); split.
    + unfold lvl_canon, nf_lvl_of; cbn [fst snd level_atoms_sort level_atoms_insert].
      destruct (o2_dominated _ _); reflexivity.
    + eexists; split; [ repeat constructor; eassumption | reflexivity ].
Qed.

Lemma domain_level_canon_functional : forall s l L L',
    domain_level_canon s l L ->
    domain_level_canon s l L' ->
    L = L'.
Proof.
  intros * [ys [Hys ->]] [ys' [Hys' ->]].
  assert (ys = ys') as -> by (eapply functional_read_level_atoms; eassumption).
  reflexivity.
Qed.

(** A canonical form from a reading of the atoms is canonical. *)
Lemma domain_level_canon_canonical : forall s l L,
    domain_level_canon s l L ->
    lvl_canon L = L.
Proof.
  intros * [ys [_ ->]]; apply lvl_canon_idem.
Qed.

Lemma domain_level_canon_lit : forall s n, domain_level_canon s (domain_level_lit n) (lvl_lit n).
Proof.
  intros; eexists; rewrite domain_level_atoms_lit, domain_level_const_lit.
  split; [ constructor | symmetry; apply lvl_canon_lit ].
Qed.

(** The canonical form of a successor is, up to the proofs in its atoms,
    the canonical successor of the canonical form ([lvl_canon_suc]): the
    canonical form keeps one of two atoms equal up to proofs. *)
Lemma domain_level_canon_suc : forall s l L,
    domain_level_canon s l L ->
    exists L', domain_level_canon s (domain_level_suc l) L' /\ lvl_eq_upto_proofs L' (lvl_canon (lvl_suc L)).
Proof.
  intros * [ys [Hys ->]]; eexists; split.
  - eexists; rewrite domain_level_atoms_suc, domain_level_const_suc.
    split; [ apply read_level_atoms_suc; eassumption | reflexivity ].
  - symmetry; apply lvl_canon_suc.
Qed.

(** So is that of a join. *)
Lemma domain_level_canon_max : forall s l L m M,
    domain_level_canon s l L ->
    domain_level_canon s m M ->
    exists L', domain_level_canon s (domain_level_max l m) L' /\ lvl_eq_upto_proofs L' (lvl_canon (lvl_max L M)).
Proof.
  intros * [ys [Hys ->]] [zs [Hzs ->]]; eexists; split.
  - eexists; rewrite domain_level_atoms_max, domain_level_const_max.
    split; [ apply read_level_atoms_app; eassumption | reflexivity ].
  - symmetry; etransitivity; [ apply lvl_canon_max_l |]; apply lvl_canon_max_r.
Qed.

(** The two, at any canonical form of the operation's value. *)
Lemma domain_level_canon_suc_upto : forall s l L L',
    domain_level_canon s l L ->
    domain_level_canon s (domain_level_suc l) L' ->
    lvl_eq_upto_proofs L' (lvl_canon (lvl_suc L)).
Proof.
  intros * HL HL'; destruct (domain_level_canon_suc _ _ _ HL) as (L1 & HL1 & E).
  rewrite (domain_level_canon_functional _ _ _ _ HL' HL1); exact E.
Qed.

Lemma domain_level_canon_max_upto : forall s l L m M L',
    domain_level_canon s l L ->
    domain_level_canon s m M ->
    domain_level_canon s (domain_level_max l m) L' ->
    lvl_eq_upto_proofs L' (lvl_canon (lvl_max L M)).
Proof.
  intros * HL HM HL'; destruct (domain_level_canon_max _ _ _ _ _ HL HM) as (L1 & HL1 & E).
  rewrite (domain_level_canon_functional _ _ _ _ HL' HL1); exact E.
Qed.

Hint Resolve domain_level_canon_lit : mctt.

(** Closes [lvl_canon X ≈ lvl_canon Y] by [lvl_canon_iff]: the two agree
    under every admissible assignment, the levels related up to proofs in
    the context having equal values ([lvl_eval_upto]). *)
Ltac lvl_upto_eval :=
  apply lvl_canon_iff; let ν := fresh "ν" in let Hν := fresh "Hν" in intros ν Hν;
  repeat first
    [ rewrite lvl_eval_max | rewrite lvl_eval_suc | rewrite lvl_eval_lit
    | rewrite (lvl_canon_eval ν _ Hν)
    | match goal with H : lvl_eq_upto_proofs ?A ?B |- context [lvl_eval ν ?A] =>
        rewrite (lvl_eval_upto ν A B Hν H) end ];
  lvl_ordinal.

(** ** The Level PER through Canonical Forms

    Two levels are related exactly when their canonical forms agree, up to
    the proofs in their atoms, at every length.  These are the introduction
    and the elimination form; every equation below is an identity of
    canonical forms up to proofs. *)
Lemma per_lvl_of : forall l l',
    domain_level_shape l ->
    domain_level_shape l' ->
    (forall s, exists L, domain_level_canon s l L) ->
    (forall s, exists L, domain_level_canon s l' L) ->
    (forall s L L', domain_level_canon s l L -> domain_level_canon s l' L' -> lvl_eq_upto_proofs L L') ->
    Dom l ≈ l' ∈ per_lvl.
Proof.
  intros * Hl Hl' Hex Hex' Heq s.
  destruct (Hex s) as [L HL]; destruct (Hex' s) as [L' HL'].
  apply (mk_normal_reads_alike _ _ _ (nf_lvl_of L) (nf_lvl_of L')); [ apply domain_level_canon_read; assumption .. |].
  apply nf_lvl_of_upto_proofs, (Heq _ _ _ HL HL').
Qed.

Lemma per_lvl_shape : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    domain_level_shape l /\ domain_level_shape l'.
Proof.
  intros * H.
  destruct (H 0) as [L L' HL HL' _].
  apply domain_level_canon_of_read in HL as [? _]; apply domain_level_canon_of_read in HL' as [? _].
  split; assumption.
Qed.

Lemma per_lvl_ex : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    forall s, exists L, domain_level_canon s l L.
Proof.
  intros * H s.
  destruct (H s) as [L L1 HL _ _]; apply domain_level_canon_of_read in HL as [_ [L' [_ ?]]]; eauto.
Qed.

Lemma per_lvl_ex_right : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    forall s, exists L, domain_level_canon s l' L.
Proof.
  intros * H; apply (per_lvl_ex l' l), per_lvl_sym; assumption.
Qed.

Lemma per_lvl_eq : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    forall s L L',
      domain_level_canon s l L ->
      domain_level_canon s l' L' ->
      lvl_eq_upto_proofs L L'.
Proof.
  intros * H * HL HL'.
  destruct (H s) as [W W' HW HW' HE].
  apply domain_level_canon_of_read in HW as [_ [L1 [-> HL1]]].
  apply domain_level_canon_of_read in HW' as [_ [L2 [-> HL2]]].
  assert (L1 = L) as <- by (eapply domain_level_canon_functional; eassumption).
  assert (L2 = L') as <- by (eapply domain_level_canon_functional; eassumption).
  apply nf_lvl_of_upto_proofs_iff; exact HE.
Qed.

(** ** The Level Operations Respect the PER

    Each proof reads the atoms of the levels at a length, computes the
    canonical form of each side by [domain_level_canon_suc] and [domain_level_canon_max], and
    compares the two by [lvl_canon_iff]. *)

Lemma per_lvl_suc : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom domain_level_suc l ≈ domain_level_suc l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    destruct (domain_level_canon_suc _ _ _ HA) as (L & HL & _); eauto.
  - intros s; destruct (per_lvl_ex_right _ _ H s) as [B HB].
    destruct (domain_level_canon_suc _ _ _ HB) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA].
    destruct (per_lvl_ex_right _ _ H s) as [B HB].
    pose proof (per_lvl_eq _ _ H _ _ _ HA HB) as EAB.
    pose proof (domain_level_canon_suc_upto _ _ _ _ HA HL) as EL.
    pose proof (domain_level_canon_suc_upto _ _ _ _ HB HL') as EL'.
    etransitivity; [ exact EL |]; etransitivity; [| symmetry; exact EL' ]; lvl_upto_eval.
Qed.

Lemma per_lvl_max : forall l l' m m',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom domain_level_max l m ≈ domain_level_max l' m' ∈ per_lvl.
Proof.
  intros * H H'.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  pose proof (per_lvl_shape _ _ H') as [Hm Hm'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA]; destruct (per_lvl_ex _ _ H' s) as [B HB].
    destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (L & HL & _); eauto.
  - intros s; destruct (per_lvl_ex_right _ _ H s) as [A HA]; destruct (per_lvl_ex_right _ _ H' s) as [B HB].
    destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA]; destruct (per_lvl_ex _ _ H' s) as [B HB].
    destruct (per_lvl_ex_right _ _ H s) as [A' HA']; destruct (per_lvl_ex_right _ _ H' s) as [B' HB'].
    pose proof (per_lvl_eq _ _ H _ _ _ HA HA') as EA.
    pose proof (per_lvl_eq _ _ H' _ _ _ HB HB') as EB.
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HA HB HL) as EL.
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HA' HB' HL') as EL'.
    etransitivity; [ exact EL |]; etransitivity; [| symmetry; exact EL' ]; lvl_upto_eval.
Qed.

Hint Resolve per_lvl_suc per_lvl_max : mctt.

(** ** Levels of a Sort

    The elements of [Level@n] read back as canonical levels of sort [n]
    ([per_lvl_at]).  Readback keeps the sorts of the atoms, which are read off
    the types of the neutrals, and the level operations keep the bound. *)
Lemma per_lvl_at_canon_sort_bounded : forall n l l' s L,
    Dom l ≈ l' ∈ per_lvl_at n ->
    domain_level_canon s l L ->
    lvl_sort_bounded n L.
Proof.
  intros * H HL.
  destruct (H s) as [L' L1 HL' _ _ Hb _].
  apply domain_level_canon_of_read in HL' as [_ [L'' [Heq HL'']]].
  apply nf_lvl_of_inj in Heq as <-.
  assert (L = L') as -> by (eapply domain_level_canon_functional; eassumption).
  exact Hb.
Qed.

(** The canonical forms of an element of [Level@n] hold no proof. *)
Lemma per_lvl_at_canon_proof_free : forall n l l' s L,
    Dom l ≈ l' ∈ per_lvl_at n ->
    domain_level_canon s l L ->
    nf_proof_free (nf_lvl_of L).
Proof.
  intros * H HL.
  destruct (H s) as [L' L1 HL' _ _ _ Hp].
  apply domain_level_canon_of_read in HL' as [_ [L'' [Heq HL'']]].
  apply nf_lvl_of_inj in Heq as <-.
  assert (L = L') as -> by (eapply domain_level_canon_functional; eassumption).
  exact Hp.
Qed.

(** A canonical level holds no proof when its atoms' neutrals hold none
    ([level_atoms_all]). *)
Lemma lvl_proof_free_atoms : forall L, nf_proof_free (nf_lvl_of L) <-> level_atoms_all ne_proof_free (snd L).
Proof. intros [c xs]; cbn [nf_lvl_of nf_proof_free fst snd]; apply level_atoms_all_all_list. Qed.

(** A level equal up to proofs to one without proofs is that level. *)
Lemma lvl_proof_free_upto : forall L L', lvl_eq_upto_proofs L L' -> nf_proof_free (nf_lvl_of L') -> nf_proof_free (nf_lvl_of L).
Proof. intros * HE Hp; symmetry in HE; rewrite <- (lvl_proof_free_upto_proofs_eq _ _ Hp HE); exact Hp. Qed.

(** A level related to one whose canonical forms are of sort [n], and hold
    no proof, is an element of [Level@n]. *)
Lemma per_lvl_at_intro : forall n l l',
    Dom l ≈ l' ∈ per_lvl ->
    (forall s L, domain_level_canon s l L -> lvl_sort_bounded n L) ->
    (forall s L, domain_level_canon s l L -> nf_proof_free (nf_lvl_of L)) ->
    Dom l ≈ l' ∈ per_lvl_at n.
Proof.
  intros * H Hb Hp s.
  destruct (H s) as [W W' HW HW' HE].
  pose proof HW as HW0; apply domain_level_canon_of_read in HW0 as [_ [L [-> HL]]].
  pose proof HW' as HW1; apply domain_level_canon_of_read in HW1 as [_ [L' [-> HL']]].
  apply nf_lvl_of_upto_proofs_iff in HE.
  exists L L'; [ exact HW | exact HW' | exact HE | eapply Hb; exact HL | eapply Hp; exact HL ].
Qed.

Lemma per_lvl_at_of_lvl : forall n l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom l ≈ l ∈ per_lvl_at n ->
    Dom l ≈ l' ∈ per_lvl_at n.
Proof.
  intros * H Hb; apply per_lvl_at_intro; [ exact H | |].
  - intros; eapply per_lvl_at_canon_sort_bounded; eassumption.
  - intros; eapply per_lvl_at_canon_proof_free; eassumption.
Qed.

Lemma per_lvl_at_lit : forall n o, fst o <= n -> Dom domain_level_lit o ≈ domain_level_lit o ∈ per_lvl_at n.
Proof.
  intros; apply per_lvl_at_intro; [ apply per_lvl_lit | |];
    intros s L HL; assert (L = lvl_lit o) as -> by (eapply domain_level_canon_functional; [ exact HL | apply domain_level_canon_lit ]).
  - apply lvl_sort_bounded_lit; assumption.
  - exact I.
Qed.

Lemma per_lvl_at_suc : forall n l l',
    Dom l ≈ l' ∈ per_lvl_at n -> Dom domain_level_suc l ≈ domain_level_suc l' ∈ per_lvl_at n.
Proof.
  intros * H; pose proof (per_lvl_at_lvl _ _ _ H) as Hl.
  apply per_lvl_at_intro; [ apply per_lvl_suc; exact Hl | |];
    intros s L HL; destruct (per_lvl_ex _ _ Hl s) as [A HA].
  - eapply lvl_sort_bounded_upto_proofs; [ symmetry; exact (domain_level_canon_suc_upto _ _ _ _ HA HL) |].
    apply lvl_sort_bounded_canon, lvl_sort_bounded_suc; eapply per_lvl_at_canon_sort_bounded; eassumption.
  - eapply lvl_proof_free_upto; [ exact (domain_level_canon_suc_upto _ _ _ _ HA HL) |].
    pose proof (per_lvl_at_canon_proof_free _ _ _ _ _ H HA) as HpA; rewrite lvl_proof_free_atoms in HpA |- *.
    destruct A as [c xs]; apply level_atoms_all_canon, level_atoms_all_suc; exact HpA.
Qed.

Lemma per_lvl_at_max : forall n l l' m m',
    Dom l ≈ l' ∈ per_lvl_at n -> Dom m ≈ m' ∈ per_lvl_at n ->
    Dom domain_level_max l m ≈ domain_level_max l' m' ∈ per_lvl_at n.
Proof.
  intros * H H'; pose proof (per_lvl_at_lvl _ _ _ H) as Hl; pose proof (per_lvl_at_lvl _ _ _ H') as Hm.
  apply per_lvl_at_intro; [ apply per_lvl_max; assumption | |];
    intros s L HL; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
  - eapply lvl_sort_bounded_upto_proofs; [ symmetry; exact (domain_level_canon_max_upto _ _ _ _ _ _ HA HB HL) |].
    apply lvl_sort_bounded_canon, lvl_sort_bounded_max; [ exact (per_lvl_at_canon_sort_bounded _ _ _ _ _ H HA) | exact (per_lvl_at_canon_sort_bounded _ _ _ _ _ H' HB) ].
  - eapply lvl_proof_free_upto; [ exact (domain_level_canon_max_upto _ _ _ _ _ _ HA HB HL) |].
    pose proof (per_lvl_at_canon_proof_free _ _ _ _ _ H HA) as HpA; pose proof (per_lvl_at_canon_proof_free _ _ _ _ _ H' HB) as HpB.
    rewrite lvl_proof_free_atoms in HpA, HpB |- *.
    destruct A as [c xs], B as [d ys]; apply level_atoms_all_canon, level_atoms_all_app; assumption.
Qed.

Hint Resolve per_lvl_at_lit per_lvl_at_suc per_lvl_at_max : mctt.

(** The limit [ω·(n+1)] absorbs every level of sort [n]. *)
Lemma per_lvl_absorb : forall n l l',
    Dom l ≈ l' ∈ per_lvl_at n ->
    Dom domain_level_max l (domain_level_lit (S n, 0)) ≈ domain_level_lit (S n, 0) ∈ per_lvl.
Proof.
  intros * H; pose proof (per_lvl_at_lvl _ _ _ H) as Hl0.
  pose proof (per_lvl_shape _ _ Hl0) as [Hl _].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | eauto with mctt |].
  - intros s; destruct (per_lvl_ex _ _ Hl0 s) as [A HA].
    destruct (domain_level_canon_max _ _ _ _ _ HA (domain_level_canon_lit s (S n, 0))) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl0 s) as [A HA].
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HA (domain_level_canon_lit s (S n, 0)) HL) as EL.
    assert (L' = lvl_lit (S n, 0)) as ->
      by (eapply domain_level_canon_functional; [ exact HL' | apply domain_level_canon_lit ]).
    rewrite EL, lvl_canon_absorb; [ reflexivity |]; eapply per_lvl_at_canon_sort_bounded; eassumption.
Qed.

(** ** The Level Equations in the Model

    Each is the identity between the canonical forms of the two sides, which
    [lvl_canon_iff] turns into arithmetic of maxima. *)

Lemma per_lvl_llit_suc : forall a b,
    Dom domain_level_lit (a, S b) ≈ domain_level_suc (domain_level_lit (a, b)) ∈ per_lvl.
Proof.
  intros; apply per_lvl_of; [ mauto 3 | mauto 3 | eauto with mctt | |].
  - intros s; destruct (domain_level_canon_suc _ _ _ (domain_level_canon_lit s (a, b))) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    assert (L = lvl_lit (a, S b)) as ->
      by (eapply domain_level_canon_functional; [ exact HL | apply domain_level_canon_lit ]).
    pose proof (domain_level_canon_suc_upto _ _ _ _ (domain_level_canon_lit s (a, b)) HL') as EL'.
    etransitivity; [| symmetry; exact EL' ].
    rewrite <- (lvl_canon_lit (a, S b)); lvl_upto_eval.
Qed.

Lemma per_lvl_max_zero : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom domain_level_max (domain_level_lit ordinal_zero) l ≈ l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | assumption | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    destruct (domain_level_canon_max _ _ _ _ _ (domain_level_canon_lit s ordinal_zero) HA) as (L & HL & _); eauto.
  - intros s; exact (per_lvl_ex_right _ _ H s).
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA].
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ (domain_level_canon_lit s ordinal_zero) HA HL) as EL.
    pose proof (per_lvl_eq _ _ H _ _ _ HA HL') as EA.
    etransitivity; [ exact EL |]; etransitivity; [| exact EA ].
    rewrite <- (domain_level_canon_canonical _ _ _ HA) at 2; lvl_upto_eval.
Qed.

Lemma per_lvl_max_assoc : forall l l' m m' n n',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom n ≈ n' ∈ per_lvl ->
    Dom domain_level_max (domain_level_max l m) n ≈ domain_level_max l' (domain_level_max m' n') ∈ per_lvl.
Proof.
  intros * Hl Hm Hn.
  pose proof (per_lvl_shape _ _ Hl) as [Hls Hls'].
  pose proof (per_lvl_shape _ _ Hm) as [Hms Hms'].
  pose proof (per_lvl_shape _ _ Hn) as [Hns Hns'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB];
      destruct (per_lvl_ex _ _ Hn s) as [C HC].
    destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (D & HD & _).
    destruct (domain_level_canon_max _ _ _ _ _ HD HC) as (L & HL & _); eauto.
  - intros s; destruct (per_lvl_ex_right _ _ Hl s) as [A HA]; destruct (per_lvl_ex_right _ _ Hm s) as [B HB];
      destruct (per_lvl_ex_right _ _ Hn s) as [C HC].
    destruct (domain_level_canon_max _ _ _ _ _ HB HC) as (D & HD & _).
    destruct (domain_level_canon_max _ _ _ _ _ HA HD) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB];
      destruct (per_lvl_ex _ _ Hn s) as [C HC].
    destruct (per_lvl_ex_right _ _ Hl s) as [A' HA']; destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'];
      destruct (per_lvl_ex_right _ _ Hn s) as [C' HC'].
    pose proof (per_lvl_eq _ _ Hl _ _ _ HA HA') as EA.
    pose proof (per_lvl_eq _ _ Hm _ _ _ HB HB') as EB.
    pose proof (per_lvl_eq _ _ Hn _ _ _ HC HC') as EC.
    destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (D & HD & ED).
    destruct (domain_level_canon_max _ _ _ _ _ HB' HC') as (D' & HD' & ED').
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HD HC HL) as EL.
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HA' HD' HL') as EL'.
    etransitivity; [ exact EL |]; etransitivity; [| symmetry; exact EL' ]; lvl_upto_eval.
Qed.

Lemma per_lvl_max_comm : forall l l' m m',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom domain_level_max l m ≈ domain_level_max m' l' ∈ per_lvl.
Proof.
  intros * Hl Hm.
  pose proof (per_lvl_shape _ _ Hl) as [Hls Hls'].
  pose proof (per_lvl_shape _ _ Hm) as [Hms Hms'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (L & HL & _); eauto.
  - intros s; destruct (per_lvl_ex_right _ _ Hl s) as [A HA]; destruct (per_lvl_ex_right _ _ Hm s) as [B HB].
    destruct (domain_level_canon_max _ _ _ _ _ HB HA) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    destruct (per_lvl_ex_right _ _ Hl s) as [A' HA']; destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'].
    pose proof (per_lvl_eq _ _ Hl _ _ _ HA HA') as EA.
    pose proof (per_lvl_eq _ _ Hm _ _ _ HB HB') as EB.
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HA HB HL) as EL.
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HB' HA' HL') as EL'.
    etransitivity; [ exact EL |]; etransitivity; [| symmetry; exact EL' ]; lvl_upto_eval.
Qed.

Lemma per_lvl_max_idem : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom domain_level_max l l ≈ l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | assumption | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    destruct (domain_level_canon_max _ _ _ _ _ HA HA) as (L & HL & _); eauto.
  - intros s; exact (per_lvl_ex_right _ _ H s).
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA].
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HA HA HL) as EL.
    pose proof (per_lvl_eq _ _ H _ _ _ HA HL') as EA.
    etransitivity; [ exact EL |]; etransitivity; [| exact EA ].
    rewrite <- (domain_level_canon_canonical _ _ _ HA) at 3; lvl_upto_eval.
Qed.

Lemma per_lvl_suc_max : forall l l' m m',
    Dom l ≈ l' ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom domain_level_suc (domain_level_max l m) ≈ domain_level_max (domain_level_suc l') (domain_level_suc m') ∈ per_lvl.
Proof.
  intros * Hl Hm.
  pose proof (per_lvl_shape _ _ Hl) as [Hls Hls'].
  pose proof (per_lvl_shape _ _ Hm) as [Hms Hms'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (D & HD & _).
    destruct (domain_level_canon_suc _ _ _ HD) as (L & HL & _); eauto.
  - intros s; destruct (per_lvl_ex_right _ _ Hl s) as [A HA]; destruct (per_lvl_ex_right _ _ Hm s) as [B HB].
    destruct (domain_level_canon_suc _ _ _ HA) as (SA & HSA & _).
    destruct (domain_level_canon_suc _ _ _ HB) as (SB & HSB & _).
    destruct (domain_level_canon_max _ _ _ _ _ HSA HSB) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ Hl s) as [A HA]; destruct (per_lvl_ex _ _ Hm s) as [B HB].
    destruct (per_lvl_ex_right _ _ Hl s) as [A' HA']; destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'].
    pose proof (per_lvl_eq _ _ Hl _ _ _ HA HA') as EA.
    pose proof (per_lvl_eq _ _ Hm _ _ _ HB HB') as EB.
    destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (D & HD & ED).
    destruct (domain_level_canon_suc _ _ _ HA') as (SA & HSA & ESA).
    destruct (domain_level_canon_suc _ _ _ HB') as (SB & HSB & ESB).
    pose proof (domain_level_canon_suc_upto _ _ _ _ HD HL) as EL.
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HSA HSB HL') as EL'.
    etransitivity; [ exact EL |]; etransitivity; [| symmetry; exact EL' ]; lvl_upto_eval.
Qed.

Lemma per_lvl_max_suc : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    Dom domain_level_max l (domain_level_suc l) ≈ domain_level_suc l' ∈ per_lvl.
Proof.
  intros * H.
  pose proof (per_lvl_shape _ _ H) as [Hl Hl'].
  apply per_lvl_of; [ mauto 3 | mauto 3 | | |].
  - intros s; destruct (per_lvl_ex _ _ H s) as [A HA].
    destruct (domain_level_canon_suc _ _ _ HA) as (SA & HSA & _).
    destruct (domain_level_canon_max _ _ _ _ _ HA HSA) as (L & HL & _); eauto.
  - intros s; destruct (per_lvl_ex_right _ _ H s) as [B HB].
    destruct (domain_level_canon_suc _ _ _ HB) as (L & HL & _); eauto.
  - intros s L L' HL HL'.
    destruct (per_lvl_ex _ _ H s) as [A HA]; destruct (per_lvl_ex_right _ _ H s) as [B HB].
    pose proof (per_lvl_eq _ _ H _ _ _ HA HB) as EAB.
    destruct (domain_level_canon_suc _ _ _ HA) as (SA & HSA & ESA).
    pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HA HSA HL) as EL.
    pose proof (domain_level_canon_suc_upto _ _ _ _ HB HL') as EL'.
    etransitivity; [ exact EL |]; etransitivity; [| symmetry; exact EL' ]; lvl_upto_eval.
Qed.

(** ** The Order on Levels from a Join

    [maxl l m ≈ m'] with [m ≈ m'] says that [l] is below [m'] in the canonical
    order: at every length, the canonical form of the join is that of [m'],
    which is what [lvl_le] states.  This is the semantic content of the
    premise of [wf_subtyp_suniv]. *)
Lemma per_sublvl_of_max : forall l m m',
    Dom l ≈ l ∈ per_lvl ->
    Dom m ≈ m' ∈ per_lvl ->
    Dom domain_level_max l m ≈ m' ∈ per_lvl ->
    per_sublvl l m'.
Proof.
  intros * Hl Hm Hmax s.
  pose proof (per_lvl_shape _ _ Hl) as [Hls _].
  pose proof (per_lvl_shape _ _ Hm) as [_ Hms'].
  destruct (per_lvl_ex _ _ Hl s) as [A HA].
  destruct (per_lvl_ex _ _ Hm s) as [B HB].
  destruct (per_lvl_ex_right _ _ Hm s) as [B' HB'].
  pose proof (per_lvl_eq _ _ Hm _ _ _ HB HB') as EB.
  destruct (domain_level_canon_max _ _ _ _ _ HA HB) as (J & HJ & EJ).
  pose proof (per_lvl_eq _ _ Hmax _ _ _ HJ HB') as Hj.
  exists A B'; [ apply domain_level_canon_read; assumption | apply domain_level_canon_read; assumption |].
  (** [max A B' ≈ max A B ≈ J ≈ B'], which is canonical. *)
  unfold lvl_le; rewrite (domain_level_canon_canonical _ _ _ HB').
  etransitivity; [| exact Hj ]; etransitivity; [| symmetry; exact EJ ].
  symmetry in EB; lvl_upto_eval.
Qed.

(** The same from readbacks: if [maxl l l'] and [l'] read back equally, the
    canonical forms of [l] and [l'] are in [lvl_le].  This is what the
    algorithmic subtyping of two small universes decides. *)
Lemma read_max_lvl_le : forall s n1 n2 n3 n4 l l' L L' W,
    Rnf ⇓ (Levelᵈ@n1) l in s ↘ nf_lvl_of L ->
    Rnf ⇓ (Levelᵈ@n2) l' in s ↘ nf_lvl_of L' ->
    Rnf ⇓ (Levelᵈ@n3) (domain_level_max l l') in s ↘ W ->
    Rnf ⇓ (Levelᵈ@n4) l' in s ↘ W ->
    lvl_le L L'.
Proof.
  intros * HL HL' Hmax Hmax'.
  apply (read_nf_level_sort _ _ 0 _ _) in HL, HL', Hmax, Hmax'.
  pose proof (functional_read_nf _ _ _ _ HL' Hmax') as <-.
  apply domain_level_canon_of_read in HL as [_ [L1 [Heq1 HL1]]].
  apply nf_lvl_of_inj in Heq1 as <-.
  apply domain_level_canon_of_read in HL' as [_ [L2 [Heq2 HL2]]].
  apply nf_lvl_of_inj in Heq2 as <-.
  apply domain_level_canon_of_read in Hmax as [_ [L3 [Heq3 HL3]]].
  apply nf_lvl_of_inj in Heq3.
  pose proof (domain_level_canon_max_upto _ _ _ _ _ _ HL1 HL2 HL3) as Hc.
  unfold lvl_le; rewrite (domain_level_canon_canonical _ _ _ HL2).
  symmetry; rewrite Heq3 at 1; exact Hc.
Qed.

End Fixed_GCtx.

#[export]
Hint Constructors domain_level_shape : mctt.
#[export]
Hint Resolve domain_level_shape_suc domain_level_shape_max domain_level_shape_lit : mctt.
#[export]
Hint Resolve read_level_atoms_app read_level_atoms_suc : mctt.
#[export]
Hint Resolve domain_level_canon_lit : mctt.
#[export]
Hint Resolve per_lvl_suc per_lvl_max : mctt.
#[export]
Hint Resolve per_lvl_at_lit per_lvl_at_suc per_lvl_at_max : mctt.
