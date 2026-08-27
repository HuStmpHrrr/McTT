(** * Several Values Related by One PER

    The set notation [{a₁, …, aₙ} ⊆ R] for "the [aᵢ] are related in [R]" means
    consecutive relatedness: [a₁ ≈ a₂ ∈ R] and … and [aₙ₋₁ ≈ aₙ ∈ R].  Two values is the degenerate case — [{a, b} ⊆
    R] is [a ≈ b ∈ R] and nothing more — and four values is the shape every
    semantic judgment of the completeness proof is built out of:

      {⟦t[σ]⟧(ρ), ⟦t⟧(⟦σ⟧(ρ)), ⟦t'⟧(⟦σ'⟧(ρ')), ⟦t'[σ']⟧(ρ')} ⊆ 𝑅_T

    Read left to right, the three conjuncts of this *four-value pattern* are the
    two commutation obligations — evaluating a substituted term agrees with
    evaluating the substitution first, on each side — and, between them, the
    relatedness obligation that [t] and [t'] are semantically equal.  With
    explicit substitutions the commutation conjuncts are reflexivity; with
    substitution as an operation they are the real content, and stating them
    alongside relatedness in one predicate is what lets a single induction
    establish all three.

    The collection is a [list] here, not a set.  The notation's meaning never
    depended on it being one: consecutive relatedness needs an
    order, and repetition is harmless.  What makes order and repetition
    *immaterial* is that [R] is always a PER, and that is the content of the two
    lemmas below:

    - [rel_chain_pairwise] — consecutive relatedness in a PER is relatedness of
      every pair, in either direction.  So any pair of members may be read off,
      and a chain may be reordered, reversed, thinned or padded
      ([rel_chain_incl]).
    - [rel_chain_merge] — two chains sharing a value join into one.

    Neither holds for a general relation, and together they are all the
    completeness proof ever does with a four-value pattern: take the ones it has
    apart with the first, put the one it wants together with the second.

    Everything here is generic in the carrier and the relation; it is filed under
    [PER] because a PER is the only thing it is ever used at. *)

From Stdlib Require Import List Relation_Definitions RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.

(** Membership in a literal list, which is what every side condition below
    is. *)
Ltac solve_in :=
  simpl; solve [ repeat first [ solve [ left; reflexivity ] | right ] ].

(** [forall x, In x L -> In x L'] for literal [L] and [L'], which is the side
    condition of [rel_chain_incl]: case on where in [L] the value is, then find
    it in [L']. *)
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

  (** [{a₁, …, aₙ} ⊆ R] as a predicate on [[a₁; …; aₙ]].  Lists of fewer than two
      elements carry no obligation; the two-element case is exactly [R a b], with
      no residual [True] to step over. *)
  Fixpoint rel_chain (l : list A) : Prop :=
    match l with
    | [] | [_] => True
    | [a; b] => R a b
    | a :: (b :: _) as l' => R a b /\ rel_chain l'
    end.

  (** Anything relating all pairs of members relates the consecutive ones, so
      this is the introduction principle for a chain of any length.  It needs no
      assumption on [R]; it is [rel_chain_pairwise], its converse, that does. *)
  Lemma rel_chain_intro : forall l,
      (forall x y, In x l -> In y l -> R x y) ->
      rel_chain l.
  Proof.
    induction l as [| a l IH]; [ intros; exact I |].
    intros H.
    destruct l as [| b l]; [ exact I |].
    assert (rel_chain (b :: l)) as Hbl by (apply IH; intros; apply H; simpl; auto).
    destruct l as [| c l].
    - apply H; simpl; auto.
    - split; [ apply H; simpl; auto | exact Hbl ].
  Qed.

  (** Prefixing a chain with one more related value.  Needs nothing of [R]
      either: it is the [cons] of the [Fixpoint], modulo the collapsed
      two-element case. *)
  Lemma rel_chain_cons : forall a b l,
      R a b ->
      rel_chain (b :: l) ->
      rel_chain (a :: b :: l).
  Proof.
    intros * ? ?.
    destruct l; [ assumption | split; assumption ].
  Qed.

  (** A single related pair, seen as a chain.  The two statements are
      definitionally equal; what this buys is a *syntactic* [rel_chain] to hand to
      [merge_rel_chain], whose [exact] would otherwise have to unify a
      metavariable list against a plain application. *)
  Lemma rel_chain_of_pair : forall x y,
      R x y ->
      rel_chain [x; y].
  Proof.
    intros * H; exact H.
  Qed.

  Context {HR : PER R}.

  (** The head of a chain is related to every other member: walk down the chain,
      composing as you go. *)
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

  (** Two members are enough for reflexivity at every member; with only one there
      is nothing to be symmetric and transitive against. *)
  Lemma rel_chain_refl : forall a b l x,
      rel_chain (a :: b :: l) ->
      In x (a :: b :: l) ->
      R x x.
  Proof.
    intros * Hchain Hin.
    assert (R a b) by (eapply rel_chain_head; [ eassumption | simpl; auto ]).
    destruct Hin as [<- | Hin].
    - etransitivity; [ eassumption | symmetry; eassumption ].
    - assert (R a x) by (eapply rel_chain_head; eassumption).
      etransitivity; [ symmetry; eassumption | eassumption ].
  Qed.

  (** ** Pairwise

      Consecutive relatedness in a PER is relatedness of every pair.  Both go
      through the head: [R x a] by symmetry on [rel_chain_head] and [R a y] by
      [rel_chain_head] again. *)
  Lemma rel_chain_pairwise : forall a b l x y,
      rel_chain (a :: b :: l) ->
      In x (a :: b :: l) ->
      In y (a :: b :: l) ->
      R x y.
  Proof.
    intros * Hchain Hx Hy.
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
      omission are all immaterial. *)
  Corollary rel_chain_incl : forall a b l L,
      rel_chain (a :: b :: l) ->
      (forall x, In x L -> In x (a :: b :: l)) ->
      rel_chain L.
  Proof.
    intros * ? ?.
    apply rel_chain_intro; intros.
    eapply rel_chain_pairwise; eauto.
  Qed.

  (** ** Merge

      Two chains sharing a value are one chain.  The shared value is what carries
      relatedness across: every member of the one is related to it, and it to
      every member of the other. *)
  Lemma rel_chain_merge : forall a b l a' b' l' c,
      rel_chain (a :: b :: l) ->
      rel_chain (a' :: b' :: l') ->
      In c (a :: b :: l) ->
      In c (a' :: b' :: l') ->
      rel_chain ((a :: b :: l) ++ a' :: b' :: l').
  Proof.
    intros * ? ? ? ?.
    apply rel_chain_intro; intros * Hx Hy.
    apply in_app_or in Hx.
    apply in_app_or in Hy.
    destruct Hx as [Hx | Hx], Hy as [Hy | Hy].
    - eapply (rel_chain_pairwise a b l); eassumption.
    - transitivity c;
        [ eapply (rel_chain_pairwise a b l) | eapply (rel_chain_pairwise a' b' l') ];
        eassumption.
    - transitivity c;
        [ eapply (rel_chain_pairwise a' b' l') | eapply (rel_chain_pairwise a b l) ];
        eassumption.
    - eapply (rel_chain_pairwise a' b' l'); eassumption.
  Qed.

  (** ** The Four-Value Pattern

      Its introduction and its three projections, named after the obligations
      they discharge: two *commutations* with the *relatedness*
      between them.  The pair actually wanted is often the outer one, which is
      none of the three. *)
  Lemma rel_chain_4 : forall v1 v2 v3 v4,
      R v1 v2 ->
      R v2 v3 ->
      R v3 v4 ->
      rel_chain [v1; v2; v3; v4].
  Proof.
    intros; repeat split; assumption.
  Qed.

  Lemma rel_chain_4_commut_left : forall v1 v2 v3 v4,
      rel_chain [v1; v2; v3; v4] -> R v1 v2.
  Proof.
    intros * [] ; assumption.
  Qed.

  Lemma rel_chain_4_related : forall v1 v2 v3 v4,
      rel_chain [v1; v2; v3; v4] -> R v2 v3.
  Proof.
    intros * [? []]; assumption.
  Qed.

  Lemma rel_chain_4_commut_right : forall v1 v2 v3 v4,
      rel_chain [v1; v2; v3; v4] -> R v3 v4.
  Proof.
    intros * [? []]; assumption.
  Qed.

  Corollary rel_chain_4_outer : forall v1 v2 v3 v4,
      rel_chain [v1; v2; v3; v4] -> R v1 v4.
  Proof.
    intros * H.
    eapply rel_chain_pairwise; [ exact H | simpl; auto | simpl; auto ].
  Qed.

  (** The degenerate four-value pattern, in which both commutation obligations
      hold by *equality* of the two values compared — the situation of every
      judgment about weakenings, where evaluation really does commute
      ([rel_sub_of_wk]), and of every instance of a judgment at the identity
      substitution ([rel_exp_under_ctx_simple]). *)
  Corollary rel_chain_4_of_2 : forall v1 v2,
      R v1 v2 ->
      rel_chain [v1; v1; v2; v2].
  Proof.
    intros * H.
    eapply (rel_chain_incl v1 v2 []); [ exact H | solve_incl ].
  Qed.

  (** Reversal, which is the whole of the semantic symmetry lemma: the four
      values of the symmetric judgment are the same four in the opposite
      order. *)
  Corollary rel_chain_4_sym : forall v1 v2 v3 v4,
      rel_chain [v1; v2; v3; v4] -> rel_chain [v4; v3; v2; v1].
  Proof.
    intros * H.
    eapply rel_chain_incl; [ exact H | solve_incl ].
  Qed.
End RelChain.

(** Weakening the relation.  No assumption on either relation: a chain is a
    conjunction of links, so it is monotone in whatever relates them.  This is
    what moves between [per_univ_elem i R] and [per_univ i], and it gives the
    [relation_equivalence] morphism below. *)
Lemma rel_chain_mono : forall {A} (R R' : relation A),
    (forall x y, R x y -> R' x y) ->
    forall l, rel_chain R l -> rel_chain R' l.
Proof.
  intros * HR l.
  induction l as [| a l IH]; [ trivial |].
  destruct l as [| b l]; [ trivial |].
  destruct l as [| c l]; simpl.
  - apply HR.
  - intros [? ?]; split; [ apply HR | apply IH ]; assumption.
Qed.

(** Transporting a chain along a map that preserves relatedness.  [rel_chain_mono]
    is the case [f = id]; the case that matters is [f = eval_wk φ], where the
    hypothesis is literally [rel_wk φ R R'] — so a chain of environments related
    in a context PER becomes a chain of weakened environments related in
    another. *)
Lemma rel_chain_map : forall {A B} (R : relation A) (R' : relation B) (f : A -> B),
    (forall x y, R x y -> R' (f x) (f y)) ->
    forall l, rel_chain R l -> rel_chain R' (map f l).
Proof.
  intros * Hf l.
  induction l as [| a l IH]; [ trivial |].
  destruct l as [| b l]; [ trivial |].
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

(** Every lemma above that needs [PER R] takes it as an instance argument, and
    [apply] does not always resolve it: the relations it is used at are context
    and element PERs, whose instances ([per_env_PER], [per_elem_PER]) are found
    from a hypothesis rather than from the goal, which the resolution [apply]
    runs will not do.  Discharging it explicitly is enough. *)
Ltac solve_chain_PER := solve [ typeclasses eauto ].

(** Closes [R x y] from any [rel_chain] hypothesis about [R], whichever two of
    its members [x] and [y] are.  [first] over the remaining goals rather than a
    positional [ | | ] because the [PER] obligation may or may not survive to
    become one. *)
Ltac pairwise :=
  match goal with
  | H : rel_chain ?R _ |- ?R _ _ =>
      eapply (rel_chain_pairwise R _ _ _ _ _ H); first [ solve_in | solve_chain_PER ]
  end.

(** Closes a [rel_chain] goal all of whose members occur in one hypothesis; when
    they come from two, merge those first with [merge_rel_chain]. *)
Ltac solve_rel_chain :=
  first
    [ pairwise
    | match goal with
      | H : rel_chain ?R _ |- rel_chain ?R _ =>
          eapply (rel_chain_incl R _ _ _ _ H); first [ solve_incl | solve_chain_PER ]
      end ].

(** Closes a [rel_chain] goal whose members are spread over *two* hypotheses:
    merge them along the value they share, then select.  None of the three can be
    guessed: [rel_chain_merge] leaves *both* its chain premises with a
    metavariable list, so a search tactic would put the same hypothesis in both
    and only fail later, at the inclusion; and the shared value is not determined
    by the goal at all.  So every goal is addressed positionally, including the
    [PER] instance argument of [rel_chain_incl], which unlike that of
    [rel_chain_merge] is not resolved by the [eapply] itself. *)
Ltac merge_rel_chain H1 H2 c :=
  eapply rel_chain_incl;
  [ solve_chain_PER
  | eapply (rel_chain_merge _ _ _ _ _ _ _ c);
    [ exact H1 | exact H2 | solve_in | solve_in ]
  | solve_incl ].
