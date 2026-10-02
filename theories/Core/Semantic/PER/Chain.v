(** * Several Values Related by One PER

    The notation [{a₁, …, aₙ} ⊆ R] means consecutive relatedness:
    [a₁ ≈ a₂ ∈ R], …, [aₙ₋₁ ≈ aₙ ∈ R].  With two values, [{a, b} ⊆ R] is just
    [a ≈ b ∈ R].  Every semantic judgment of the completeness proof is built
    from the four-value pattern
<<
{⟦t[σ]⟧(ρ), ⟦t⟧(⟦σ⟧(ρ)), ⟦t'⟧(⟦σ'⟧(ρ')), ⟦t'[σ']⟧(ρ')} ⊆ 𝑅_T
>>
    Read left to right, its three conjuncts are a commutation obligation
    (evaluating a substituted term agrees with evaluating the substitution
    first), the relatedness of [t] and [t'], and the commutation obligation on
    the other side.  Substitution is an operation on syntax, so the
    commutation obligations have real content; stating them together with
    relatedness lets a single induction establish all three.

    A chain is a [list].  Consecutive relatedness needs an order, and
    repetition is harmless.  Order and repetition are immaterial because [R]
    is always a PER, which is the content of two lemmas:

    - [rel_chain_pairwise]: consecutive relatedness in a PER is relatedness of
      every pair, in either direction.  So any pair of members may be read
      off, and a chain may be reordered, reversed, thinned or padded
      ([rel_chain_incl]), as long as two members remain.
    - [rel_chain_merge]: two chains sharing a value join into one.

    Neither holds for a general relation.  Together they are all the
    completeness proof does with four-value patterns: it takes the ones it has
    apart with the first and assembles the one it wants with the second.

    Everything here is generic in the carrier and the relation, but is only
    used at PERs. *)

From Stdlib Require Import List Relation_Definitions RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.

(** Proves membership in a literal list, the side condition of the lemmas
    below. *)
Ltac solve_in :=
  simpl; solve [ repeat first [ solve [ left; reflexivity ] | right ] ].

(** Proves [forall x, In x L -> In x L'] for literal [L] and [L'], the side
    condition of [rel_chain_incl]. *)
Ltac solve_incl :=
  let Hin := fresh "Hin" in
  intros ? Hin;
  simpl in Hin;
  repeat
    match goal with
    | H : False |- _ => contradiction
    | H : _ \/ _ |- _ => destruct H
    | H : _ = _ |- _ => subst
    end;
  solve_in.

Section RelChain.
  Context {A : Type} (R : relation A).

  (** [{a₁, …, aₙ} ⊆ R] as a predicate on [[a₁; …; aₙ]].  Lists with fewer
      than two members are [False], so a chain hypothesis carries its own
      length bound and consuming lemmas can be stated at a plain [l].  The
      two-element case is exactly [R a b]. *)
  Fixpoint rel_chain (l : list A) : Prop :=
    match l with
    | [] | [_] => False
    | [a; b] => R a b
    | a :: (b :: _) as l' => R a b /\ rel_chain l'
    end.

  (** The length bound.  It needs nothing of [R]. *)
  Lemma rel_chain_shape : forall l,
      rel_chain l ->
      exists a b l', l = a :: b :: l'.
  Proof.
    intros [| a [| b l]] H; [ destruct H | destruct H | exists a, b, l; reflexivity ].
  Qed.

  (** The introduction principle for a chain of any length: if all pairs of
      members are related, so are consecutive ones.  It needs nothing of [R];
      its converse [rel_chain_pairwise] needs [R] to be a PER. *)
  Lemma rel_chain_intro : forall a b l,
      (forall x y, In x (a :: b :: l) -> In y (a :: b :: l) -> R x y) ->
      rel_chain (a :: b :: l).
  Proof.
    intros a b l; revert a b.
    induction l as [| c l IH]; intros * H; [ apply H; simpl; auto |].
    split; [ apply H; simpl; auto |].
    apply IH; intros; apply H; simpl; auto.
  Qed.

  (** Prefixing a chain with one more related value.  It needs nothing of [R].
      A chain is started with [rel_chain_of_pair], not by consing onto a
      singleton. *)
  Lemma rel_chain_cons : forall a b l,
      R a b ->
      rel_chain (b :: l) ->
      rel_chain (a :: b :: l).
  Proof.
    intros * ? ?.
    destruct l; [ assumption | split; assumption ].
  Qed.

  (** A related pair as a chain.  The two statements are definitionally equal;
      this lemma gives [merge_rel_chain] a syntactic [rel_chain], which its
      [exact] needs. *)
  Lemma rel_chain_of_pair : forall x y,
      R x y ->
      rel_chain ([x; y]).
  Proof.
    intros * H; exact H.
  Qed.

  Context {HR : PER R}.

  (** The head of a chain is related to every other member. *)
  Lemma rel_chain_head : forall l a,
      rel_chain (a :: l) ->
      forall x, In x l -> R a x.
  Proof.
    induction l as [| b l IH]; intros * Hchain * Hin; [ contradiction |].
    destruct Hin as [<- | Hin].
    - destruct l; [ assumption | destruct Hchain; assumption ].
    - destruct l as [| c l]; [ contradiction |].
      destruct Hchain as [Hab Hbl].
      etransitivity; [ eassumption | eapply IH; eassumption ].
  Qed.

  (** Every member is related to itself, via the second member that every chain
      has. *)
  Lemma rel_chain_refl : forall l x,
      rel_chain l ->
      In x l ->
      R x x.
  Proof.
    intros * Hchain Hin.
    destruct (rel_chain_shape _ Hchain) as [a [b [l' ->]]].
    assert (R a b) by (eapply rel_chain_head; [ eassumption | simpl; auto ]).
    destruct Hin as [<- | Hin].
    - etransitivity; [ eassumption | symmetry; eassumption ].
    - assert (R a x) by (eapply rel_chain_head; eassumption).
      etransitivity; [ symmetry; eassumption | eassumption ].
  Qed.

  (** ** Pairwise

      In a PER, consecutive relatedness implies relatedness of every pair.  The
      proof goes through the head: [R x a] by symmetry and [rel_chain_head],
      then [R a y] by [rel_chain_head]. *)
  Lemma rel_chain_pairwise : forall l x y,
      rel_chain l ->
      In x l ->
      In y l ->
      R x y.
  Proof.
    intros * Hchain Hx Hy.
    destruct (rel_chain_shape _ Hchain) as [a [b [l' ->]]].
    assert (R x a).
    { destruct Hx as [<- | Hin].
      - eapply rel_chain_refl; [ eassumption | simpl; auto ].
      - symmetry; eapply rel_chain_head; eassumption. }
    assert (R a y).
    { destruct Hy as [<- | Hin].
      - eapply rel_chain_refl; [ eassumption | simpl; auto ].
      - eapply rel_chain_head; eassumption. }
    etransitivity; eassumption.
  Qed.

  (** A list drawn from the members of a chain is a chain: order, repetition and
      omission do not matter, provided two members remain.  This is why the
      conclusion names two members. *)
  Corollary rel_chain_incl : forall l a b L,
      rel_chain l ->
      (forall x, In x (a :: b :: L) -> In x l) ->
      rel_chain (a :: b :: L).
  Proof.
    intros * ? ?.
    apply rel_chain_intro; intros.
    eapply rel_chain_pairwise; eauto.
  Qed.

  (** ** Merge

      Two chains sharing a value form one chain: every member of either is
      related to the shared value. *)
  Lemma rel_chain_merge : forall l l' c,
      rel_chain l ->
      rel_chain l' ->
      In c l ->
      In c l' ->
      rel_chain (l ++ l').
  Proof.
    intros * Hl Hl' ? ?.
    destruct (rel_chain_shape _ Hl) as [a [b [t ->]]].
    apply (rel_chain_intro a b (t ++ l')); intros x y Hx Hy.
    assert (Hx' : In x ((a :: b :: t) ++ l')) by exact Hx.
    assert (Hy' : In y ((a :: b :: t) ++ l')) by exact Hy.
    apply in_app_or in Hx'.
    apply in_app_or in Hy'.
    destruct Hx' as [Hx' | Hx'], Hy' as [Hy' | Hy'].
    - eapply (rel_chain_pairwise (a :: b :: t)); eassumption.
    - transitivity c;
        [ eapply (rel_chain_pairwise (a :: b :: t)) | eapply (rel_chain_pairwise l') ];
        eassumption.
    - transitivity c;
        [ eapply (rel_chain_pairwise l') | eapply (rel_chain_pairwise (a :: b :: t)) ];
        eassumption.
    - eapply (rel_chain_pairwise l'); eassumption.
  Qed.

  (** ** The Four-Value Pattern

      Its introduction and its projections, named after the obligations they
      discharge: the two commutations and the relatedness between them.  The
      outer pair, often the one wanted, is [rel_chain_4_outer]. *)
  Lemma rel_chain_4 : forall v1 v2 v3 v4,
      R v1 v2 ->
      R v2 v3 ->
      R v3 v4 ->
      rel_chain ([v1; v2; v3; v4]).
  Proof.
    intros; repeat split; assumption.
  Qed.

  Lemma rel_chain_4_commut_left : forall v1 v2 v3 v4,
      rel_chain ([v1; v2; v3; v4]) -> R v1 v2.
  Proof.
    intros * [] ; assumption.
  Qed.

  Lemma rel_chain_4_related : forall v1 v2 v3 v4,
      rel_chain ([v1; v2; v3; v4]) -> R v2 v3.
  Proof.
    intros * [? []]; assumption.
  Qed.

  Lemma rel_chain_4_commut_right : forall v1 v2 v3 v4,
      rel_chain ([v1; v2; v3; v4]) -> R v3 v4.
  Proof.
    intros * [? []]; assumption.
  Qed.

  Corollary rel_chain_4_outer : forall v1 v2 v3 v4,
      rel_chain ([v1; v2; v3; v4]) -> R v1 v4.
  Proof.
    intros * H.
    eapply rel_chain_pairwise; [ exact H | simpl; auto | simpl; auto ].
  Qed.

  (** The degenerate four-value pattern, in which both commutation obligations
      hold by equality.  This is the case for judgments about weakenings
      ([rel_sub_of_wk]) and for judgments at the identity substitution
      ([rel_exp_under_ctx_simple]). *)
  Corollary rel_chain_4_of_2 : forall v1 v2,
      R v1 v2 ->
      rel_chain ([v1; v1; v2; v2]).
  Proof.
    intros * H.
    eapply (rel_chain_incl ([v1; v2])); [ exact H | solve_incl ].
  Qed.

  (** Reversal.  This is all of the semantic symmetry lemma: the symmetric
      judgment has the same four values in the opposite order. *)
  Corollary rel_chain_4_sym : forall v1 v2 v3 v4,
      rel_chain ([v1; v2; v3; v4]) -> rel_chain ([v4; v3; v2; v1]).
  Proof.
    intros * H.
    eapply rel_chain_incl; [ exact H | solve_incl ].
  Qed.
End RelChain.

(** Weakening the relation.  A chain is a conjunction of links, so it is
    monotone in the relation, with no assumption on either.  This moves chains
    between [per_univ_elem i R] and [per_univ i], and gives the
    [relation_equivalence] morphism below. *)
Lemma rel_chain_mono : forall {A} (R R' : relation A),
    (forall x y, R x y -> R' x y) ->
    forall l, rel_chain R l -> rel_chain R' l.
Proof.
  intros * HR l.
  induction l as [| a l IH]; [ intros [] |].
  destruct l as [| b l]; [ intros [] |].
  destruct l as [| c l]; simpl.
  - apply HR.
  - intros [? ?]; split; [ apply HR | apply IH ]; assumption.
Qed.

(** Transporting a chain along a map that preserves relatedness.  The main
    case is [f = eval_wk φ], where the hypothesis is [rel_wk φ R R']: a chain
    of environments related in one context PER becomes a chain of weakened
    environments related in another. *)
Lemma rel_chain_map : forall {A B} (R : relation A) (R' : relation B) (f : A -> B),
    (forall x y, R x y -> R' (f x) (f y)) ->
    forall l, rel_chain R l -> rel_chain R' (map f l).
Proof.
  intros * Hf l.
  induction l as [| a l IH]; [ intros [] |].
  destruct l as [| b l]; [ intros [] |].
  destruct l as [| c l]; simpl.
  - apply Hf.
  - intros [? ?]; split; [ apply Hf | apply IH ]; assumption.
Qed.

#[export]
Instance rel_chain_Proper {A} :
  Proper (@relation_equivalence A ==> eq ==> iff) rel_chain.
Proof.
  intros R R' HR l l' <-.
  split; apply rel_chain_mono; apply HR.
Qed.

#[export]
Hint Resolve rel_chain_4 : mctt.

(** Discharges the [PER] instance argument of the lemmas above.  [apply] does
    not always resolve it: for context and element PERs the instances
    ([per_env_PER], [per_elem_PER]) are found from a hypothesis rather than
    from the goal. *)
Ltac solve_chain_PER := solve [ typeclasses eauto ].

(** Closes [R x y] from any [rel_chain] hypothesis about [R] that has [x] and
    [y] among its members.

    The relation is matched in the goal first, and otherwise left to [eapply]
    to unify: a goal produced by an [eapply] that could not yet fix the
    universe level or the element PER has a metavariable in place of [R], and
    then the hypothesis determines it.

    [unshelve] is needed because [eapply] shelves the [PER] instance argument
    when it cannot resolve it.  Without it, a chain at a relation not known to
    be a PER (say [per_pi] at a domain PER) would let the tactic succeed and
    leave the hole to be found at [Qed].  The remaining goals are closed with
    [first] rather than positionally, since the [PER] obligation may or may
    not remain. *)
Ltac pairwise_from H R :=
  unshelve (eapply (rel_chain_pairwise R _ _ _ H));
  first [ solve_in | solve_chain_PER ].

Ltac pairwise :=
  first
    [ match goal with
      | H : rel_chain ?R _ |- ?R _ _ => pairwise_from H R
      end
    | match goal with
      | H : rel_chain ?R _ |- _ => pairwise_from H R
      end ].

(** Closes a [rel_chain] goal whose members all occur in one hypothesis.  When
    they come from two, use [merge_rel_chain]. *)
Ltac solve_rel_chain :=
  first
    [ pairwise
    | match goal with
      | H : rel_chain ?R _ |- rel_chain ?R _ =>
          unshelve (eapply (rel_chain_incl R _ _ _ _ H));
          first [ solve_incl | solve_chain_PER ]
      end ].

(** Closes a [rel_chain] goal whose members are spread over two hypotheses
    [H1] and [H2] that share the value [c]: merge them along [c], then select.
    None of the arguments can be guessed.  [rel_chain_merge] leaves both chain
    premises with a metavariable list, so a search would use the same
    hypothesis twice and fail only at the inclusion, and the goal does not
    determine the shared value.  So every goal is addressed positionally,
    including the [PER] instance argument of [rel_chain_incl], which [eapply]
    does not resolve. *)
Ltac merge_rel_chain H1 H2 c :=
  eapply rel_chain_incl;
  [ solve_chain_PER
  | eapply (rel_chain_merge _ _ _ c);
    [ exact H1 | exact H2 | solve_in | solve_in ]
  | solve_incl ].
