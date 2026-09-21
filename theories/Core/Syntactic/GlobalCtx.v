From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

Generalizable All Variables.

(** * Global Contexts

    Two levels, spelled differently in the surface language and represented
    differently here.  [X::Y::Z] names a *unit* — a file — and units do not
    nest, so the [::] level is a trie of paths.  [X.W] names an internal module
    of one unit, and internal modules nest inside that unit's declarations, so
    the [.] level is a module. *)

(** ** Modules

    A module is a sequence of definitions, in declaration order, whose entries
    may themselves be modules.

    A member's type and body are stored fully generalized over the enclosing
    module's parameters, as the elaborator already emits them, so every [ge_def]
    is closed.  The telescope in [ge_mod] is therefore not needed to read a
    member; it is recorded so that a module application can be typed.

    In [ge_def b A B], [b] is transparency ([false] for [abstract]) and
    [B = None] is an axiom. *)
Inductive gentry : Set :=
| ge_def : bool -> typ -> option exp -> gentry
| ge_mod : ctx -> gmod -> gentry

with gmod : Set :=
| gm_nil : gmod
| gm_ext : gmod -> string -> gentry -> gmod.

(** ** Units

    A unit is a file: its parameter telescope and the module it declares. *)
Record gunit : Set :=
  { gu_params : ctx
  ; gu_mod : gmod }.

(** ** The Import Trie

    [gt_ext T x u T'] extends [T] with segment [x], carrying a unit iff a file
    exists at that path, and with [T'] beneath it.  [X::Y::Z] can be a file
    while [X::Y] is not, hence the [option]. *)
Inductive gtree : Set :=
| gt_nil : gtree
| gt_ext : gtree -> string -> option gunit -> gtree -> gtree.

(** ** The Definition Stack

    The modules still being elaborated, innermost first.  Entering a module
    pushes a frame; closing one pops it into its parent's [gmod] as a [ge_mod]
    entry.  A single [gmod] cannot express this: an open module is not yet an
    entry of anything, so the frames have to be held apart, and [qu_rel] indexes
    them.

    Each frame records the *whole* ambient telescope, not only the parameters it
    introduces, so a frame is well formed on its own and the stack needs no
    condition relating adjacent frames. *)
Definition gstack : Set := list gunit.

(** ** Global Contexts

    The imports in scope, and the definitions of the unit being elaborated. *)
Record gctx : Set :=
  { gc_imports : gtree
  ; gc_defs : gstack }.

Module GlobalCtx_Notations.
  Notation "⋄" := gm_nil : mctt_scope.
  Notation "Φ ⊳ x ↦ E" := (gm_ext Φ x E) (at level 50, left associativity, x at level 0) : mctt_scope.
  Notation "∅" := gt_nil : mctt_scope.
  Notation "T ▸ x ↦ u ⊲ T'" := (gt_ext T x u T') (at level 50, left associativity, x at level 0, u at level 0) : mctt_scope.
End GlobalCtx_Notations.

Import GlobalCtx_Notations.

(** ** Freshness

    Keys are single segments at both levels, so freshness is string inequality;
    no prefix relation on paths is needed. *)

Fixpoint gm_fresh (x : string) (Φ : gmod) : Prop :=
  match Φ with
  | ⋄ => True
  | Φ ⊳ y ↦ _ => x <> y /\ gm_fresh x Φ
  end.

Fixpoint gt_fresh (x : string) (T : gtree) : Prop :=
  match T with
  | ∅ => True
  | T ▸ y ↦ _ ⊲ _ => x <> y /\ gt_fresh x T
  end.

(** ** Canonicity

    A name is declared at most once per level, at either level.  Shadowing is
    not allowed, so resolution is deterministic without reference to declaration
    order. *)
Fixpoint gm_canon (Φ : gmod) : Prop :=
  match Φ with
  | ⋄ => True
  | Φ ⊳ x ↦ E =>
      gm_fresh x Φ
      /\ gm_canon Φ
      /\ match E with
         | ge_def _ _ _ => True
         | ge_mod _ Φ' => gm_canon Φ'
         end
  end.

(** In addition, an import set has exactly one representation: a leaf carries a
    module, since a segment with no file below it and no file of its own could
    not have been put there by any import. *)
Fixpoint gt_canon (T : gtree) : Prop :=
  match T with
  | ∅ => True
  | T ▸ x ↦ u ⊲ T' =>
      gt_fresh x T
      /\ gt_canon T
      /\ gt_canon T'
      /\ (T' = ∅ -> exists U, u = Some U)
      /\ match u with
         | None => True
         | Some U => gm_canon (gu_mod U)
         end
  end.

(** Frames are independent: a name declared in an enclosing module may be
    redeclared in a nested one, which is ordinary scoping.  [qu_rel] says which
    frame, so this costs nothing in determinism. *)
Definition gs_canon (Ξ : gstack) : Prop :=
  List.Forall (fun U => gm_canon (gu_mod U)) Ξ.

(** ** Resolution

    Both levels have the same three rules: the path ends here, the path descends
    into a module, or this entry is not the one we want. *)

Reserved Notation "Φ ∋ ip ⇒ E" (at level 70, ip at level 69, E at level 69).
Reserved Notation "T ∋ᵘ fp ⇒ U" (at level 70, fp at level 69, U at level 69).
Reserved Notation "Ψ ∋ᵍ p ⇒ E" (at level 70, p at level 69, E at level 69).

Inductive gm_lookup : gmod -> list string -> gentry -> Prop :=
| gml_last : `( Φ ⊳ x ↦ E ∋ x :: nil ⇒ E )
| gml_in   : `( Φ' ∋ ip ⇒ E ->
                ip <> nil ->
                Φ ⊳ x ↦ (ge_mod Δ Φ') ∋ x :: ip ⇒ E )
| gml_old  : `( Φ ∋ y :: ip ⇒ E ->
                y <> x ->
                Φ ⊳ x ↦ E' ∋ y :: ip ⇒ E )
where "Φ ∋ ip ⇒ E" := (gm_lookup Φ ip E) : type_scope.

Inductive gt_lookup : gtree -> list string -> gunit -> Prop :=
| gtl_last : `( T ▸ x ↦ (Some U) ⊲ T' ∋ᵘ x :: nil ⇒ U )
| gtl_in   : `( T' ∋ᵘ fp ⇒ U ->
                fp <> nil ->
                T ▸ x ↦ u ⊲ T' ∋ᵘ x :: fp ⇒ U )
| gtl_old  : `( T ∋ᵘ y :: fp ⇒ U ->
                y <> x ->
                T ▸ x ↦ u ⊲ T' ∋ᵘ y :: fp ⇒ U )
where "T ∋ᵘ fp ⇒ U" := (gt_lookup T fp U) : type_scope.

(** A whole reference.  The qualifier chooses the module — a frame of the stack,
    or an imported unit — and the members are then looked up in it, so the two
    rules are disjoint by constructor rather than by a side condition. *)
Inductive gc_lookup : gctx -> path -> gentry -> Prop :=
| gcl_rel : `( List.nth_error (gc_defs Ψ) n = Some U ->
               gu_mod U ∋ ip ⇒ E ->
               Ψ ∋ᵍ p_rel n ip ⇒ E )
| gcl_abs : `( gc_imports Ψ ∋ᵘ fp ⇒ U ->
               gu_mod U ∋ ip ⇒ E ->
               Ψ ∋ᵍ p_abs fp ip ⇒ E )
where "Ψ ∋ᵍ p ⇒ E" := (gc_lookup Ψ p E) : type_scope.

#[export] Hint Constructors gm_lookup gt_lookup gc_lookup : mctt.

(** Inverting [gc_lookup] leaves an equation between two [path] literals, which
    has to be taken apart field by field before [congruence] can use it or
    [discriminate] can rule the case out. *)
Ltac path_inj :=
  repeat match goal with
         | H : @eq path _ _ |- _ => inversion H; subst; try clear H
         | H : @eq qual _ _ |- _ => inversion H; subst; try clear H
         end.

(** A fresh name resolves nothing, which is what makes the third rule of each
    relation harmless. *)
Lemma gm_fresh_no_lookup : forall Φ x ip E,
    gm_fresh x Φ ->
    ~ Φ ∋ x :: ip ⇒ E.
Proof.
  induction Φ; simpl; intros x ip E Hfr Hlk; [inversion Hlk |].
  destruct Hfr as [Hne Hfr].
  inversion Hlk; subst; try congruence.
  eapply IHΦ; eassumption.
Qed.

Lemma gt_fresh_no_lookup : forall T x fp U,
    gt_fresh x T ->
    ~ T ∋ᵘ x :: fp ⇒ U.
Proof.
  induction T; simpl; intros x fp U Hfr Hlk; [inversion Hlk |].
  destruct Hfr as [Hne Hfr].
  inversion Hlk; subst; try congruence.
  eapply IHT1; eassumption.
Qed.

(** Every rule of both relations consumes a segment, so a resolvable path is
    nonempty — [path_valid] is a consequence of resolution, not a premise of it. *)
Lemma gm_lookup_nonnil : forall Φ ip E,
    Φ ∋ ip ⇒ E ->
    ip <> nil.
Proof.
  inversion 1; discriminate.
Qed.

Lemma gt_lookup_nonnil : forall T fp U,
    T ∋ᵘ fp ⇒ U ->
    fp <> nil.
Proof.
  inversion 1; discriminate.
Qed.

Lemma gc_lookup_valid : forall Ψ p E,
    Ψ ∋ᵍ p ⇒ E ->
    path_valid p.
Proof.
  inversion 1; subst; split; simpl;
    eauto using gm_lookup_nonnil, gt_lookup_nonnil.
Qed.

(** ** Determinism *)

Lemma gm_lookup_det : forall Φ ip E,
    Φ ∋ ip ⇒ E ->
    gm_canon Φ ->
    forall E', Φ ∋ ip ⇒ E' -> E = E'.
Proof.
  induction 1; simpl; intros Hc E'' Hlk; destruct_all;
    inversion Hlk; subst; try congruence; eauto.
Qed.

Lemma gt_lookup_det : forall T fp U,
    T ∋ᵘ fp ⇒ U ->
    gt_canon T ->
    forall U', T ∋ᵘ fp ⇒ U' -> U = U'.
Proof.
  induction 1; simpl; intros Hc U'' Hlk; destruct_all;
    inversion Hlk; subst; try congruence; eauto.
Qed.

Lemma gt_lookup_canon : forall T fp U,
    T ∋ᵘ fp ⇒ U ->
    gt_canon T ->
    gm_canon (gu_mod U).
Proof.
  induction 1; simpl; intros Hc; destruct_all; eauto.
Qed.

Lemma gs_canon_nth : forall Ξ n U,
    gs_canon Ξ ->
    List.nth_error Ξ n = Some U ->
    gm_canon (gu_mod U).
Proof.
  unfold gs_canon; intros Ξ n U HΞ Hn.
  rewrite List.Forall_forall in HΞ.
  eauto using List.nth_error_In.
Qed.

Corollary gc_lookup_det : forall Ψ p E E',
    gt_canon (gc_imports Ψ) ->
    gs_canon (gc_defs Ψ) ->
    Ψ ∋ᵍ p ⇒ E ->
    Ψ ∋ᵍ p ⇒ E' ->
    E = E'.
Proof.
  intros * Hct Hcs Hlk Hlk'.
  inversion Hlk; inversion Hlk'; subst; try congruence.
  all: path_inj.
  - replace U0 with U in * by congruence.
    eapply gm_lookup_det; try eassumption.
    eapply gs_canon_nth; eassumption.
  - assert (U = U0) by (eapply gt_lookup_det; eassumption); subst.
    eapply gm_lookup_det; try eassumption.
    eapply gt_lookup_canon; eassumption.
Qed.

(** ** Growth

    The metatheory never inspects the shape of a global context; it only needs
    that everything still resolves.  [⊑] is therefore lookup preservation, and
    it is the whole interface between the theory and the two containers above. *)
Definition gsub (Ψ Ψ' : gctx) : Prop :=
  forall p E, Ψ ∋ᵍ p ⇒ E -> Ψ' ∋ᵍ p ⇒ E.

Notation "Ψ ⊑ Ψ'" := (gsub Ψ Ψ') (at level 70) : type_scope.

Lemma gsub_refl : forall Ψ, Ψ ⊑ Ψ.
Proof.
  firstorder.
Qed.

Lemma gsub_trans : forall Ψ Ψ' Ψ'', Ψ ⊑ Ψ' -> Ψ' ⊑ Ψ'' -> Ψ ⊑ Ψ''.
Proof.
  firstorder.
Qed.

#[export] Hint Resolve gsub_refl : mctt.

(** ** Merging Imports

    A one-unit trie, for the path of a single import. *)
Fixpoint gt_singleton (fp : list string) (U : gunit) : gtree :=
  match fp with
  | nil => ∅
  | x :: nil => ∅ ▸ x ↦ (Some U) ⊲ ∅
  | x :: fp => ∅ ▸ x ↦ None ⊲ gt_singleton fp U
  end.

(** [gt_take x T] splits [T] at segment [x] into that segment's unit, its
    subtrie, and the rest of [T].  An absent segment yields [(None, ∅, T)],
    which canonicity makes unambiguous: no segment of a canonical trie carries
    neither a unit nor descendants.  Canonicity also makes the first match the
    only one. *)
Fixpoint gt_take (x : string) (T : gtree) : (option gunit * gtree * gtree)%type :=
  match T with
  | ∅ => (None, ∅, ∅)
  | T0 ▸ y ↦ u ⊲ T' =>
      if String.eqb x y
      then (u, T', T0)
      else let '(w, T1, T0') := gt_take x T0 in (w, T1, T0' ▸ y ↦ u ⊲ T')
  end.

(** A path may carry a unit on both sides of a merge; the join keeps the one
    already there, so no equality on [exp] is needed.  Stdlib has no such
    combinator for [option].

    Keeping the left one loses nothing under the standing assumption that a file
    path determines its unit: a path shared by two import sets carries the same
    [gunit] in both.  That is the import machinery's obligation, and the [T2]
    side of [gmerge_lookup_l] below waits on it. *)
Definition gu_join (u v : option gunit) : option gunit :=
  match u with
  | Some _ => u
  | None => v
  end.

(** The join of two import sets, structural on [T2]: each segment of [T2] is
    emitted once with its counterpart in [T1] joined into it, and whatever of
    [T1] is left over is carried over by the [∅] case.  Adding one unit is
    [gmerge T (gt_singleton fp U)]. *)
Fixpoint gmerge (T1 T2 : gtree) : gtree :=
  match T2 with
  | ∅ => T1
  | S0 ▸ y ↦ v ⊲ S1 =>
      let '(u, T', T1') := gt_take y T1 in
      gmerge T1' S0 ▸ y ↦ (gu_join u v) ⊲ gmerge T' S1
  end.

(** ** Merging Preserves Canonicity *)

Lemma gt_take_fresh : forall T x y u T' T0,
    gt_take y T = (u, T', T0) ->
    gt_fresh x T ->
    gt_fresh x T0.
Proof.
  induction T; simpl; intros x y u T' T0 Heq Hfr.
  - inversion Heq; subst; simpl; trivial.
  - destruct Hfr as [Hne Hfr].
    destruct (String.eqb y s) eqn:Hy.
    + inversion Heq; subst; assumption.
    + destruct (gt_take y T1) as [[w T1'] T0'] eqn:Ht.
      inversion Heq; subst; simpl.
      split; [assumption | eapply IHT1; eassumption].
Qed.

(** Removing a segment leaves it fresh, so a merged node is never duplicated. *)
Lemma gt_take_key_fresh : forall T y u T' T0,
    gt_take y T = (u, T', T0) ->
    gt_canon T ->
    gt_fresh y T0.
Proof.
  induction T; simpl; intros y u T' T0 Heq Hc.
  - inversion Heq; subst; simpl; trivial.
  - destruct_all.
    destruct (String.eqb y s) eqn:Hy.
    + apply String.eqb_eq in Hy; subst.
      inversion Heq; subst; assumption.
    + destruct (gt_take y T1) as [[w T1'] T0'] eqn:Ht.
      inversion Heq; subst; simpl.
      split; [now apply String.eqb_neq in Hy | eapply IHT1; eassumption].
Qed.

Lemma gt_take_canon : forall T y u T' T0,
    gt_take y T = (u, T', T0) ->
    gt_canon T ->
    gt_canon T' /\ gt_canon T0.
Proof.
  induction T; simpl; intros y u T' T0 Heq Hc.
  - inversion Heq; subst; simpl; split; trivial.
  - destruct_all.
    destruct (String.eqb y s) eqn:Hy.
    + inversion Heq; subst; split; assumption.
    + destruct (gt_take y T1) as [[w T1'] T0'] eqn:Ht.
      inversion Heq; subst; simpl.
      specialize (IHT1 _ _ _ _ Ht ltac:(eassumption)) as [? ?].
      split; [assumption |].
      repeat split; try assumption.
      eapply gt_take_fresh; eassumption.
Qed.

Lemma gt_take_unit_canon : forall T y u T' T0,
    gt_take y T = (u, T', T0) ->
    gt_canon T ->
    match u with
    | None => True
    | Some U => gm_canon (gu_mod U)
    end.
Proof.
  induction T; simpl; intros y u T' T0 Heq Hc.
  - inversion Heq; subst; trivial.
  - destruct_all.
    destruct (String.eqb y s) eqn:Hy.
    + inversion Heq; subst; assumption.
    + destruct (gt_take y T1) as [[w T1'] T0'] eqn:Ht.
      inversion Heq; subst.
      eapply IHT1; eassumption.
Qed.

Lemma gmerge_eq_nil : forall T1 T2,
    gmerge T1 T2 = ∅ ->
    T1 = ∅ /\ T2 = ∅.
Proof.
  intros T1 T2 Heq.
  destruct T2; simpl in Heq.
  - split; [assumption | reflexivity].
  - destruct (gt_take s T1) as [[u T'] T1'].
    discriminate.
Qed.

Lemma gt_fresh_gmerge : forall T2 T1 x,
    gt_fresh x T1 ->
    gt_fresh x T2 ->
    gt_fresh x (gmerge T1 T2).
Proof.
  induction T2; simpl; intros T1 x Hfr1 Hfr2.
  - assumption.
  - destruct Hfr2 as [Hne Hfr2].
    destruct (gt_take s T1) as [[u T'] T1'] eqn:Ht.
    simpl; split; [assumption |].
    apply IHT2_1; [| assumption].
    eapply gt_take_fresh; eassumption.
Qed.

Lemma gt_singleton_eq_nil : forall fp U,
    gt_singleton fp U = ∅ ->
    fp = nil.
Proof.
  destruct fp as [| x [| y fp]]; simpl; intros; try discriminate; reflexivity.
Qed.

Lemma gt_singleton_canon : forall fp U,
    gm_canon (gu_mod U) ->
    gt_canon (gt_singleton fp U).
Proof.
  induction fp as [| x fp IH]; intros U Hc; simpl; trivial.
  destruct fp as [| y fp]; repeat split; trivial;
    try (intros Hnil; destruct fp; discriminate); eauto.
Qed.

Theorem gmerge_canon : forall T2 T1,
    gt_canon T1 ->
    gt_canon T2 ->
    gt_canon (gmerge T1 T2).
Proof.
  induction T2; simpl; intros T1 Hc1 Hc2.
  - assumption.
  - destruct_all.
    destruct (gt_take s T1) as [[u T'] T1'] eqn:Ht.
    specialize (gt_take_canon _ _ _ _ _ Ht Hc1) as [Hc' Hc1'].
    specialize (gt_take_unit_canon _ _ _ _ _ Ht Hc1) as Hcu.
    simpl; repeat split.
    + apply gt_fresh_gmerge; [| assumption].
      eapply gt_take_key_fresh; eassumption.
    + now apply IHT2_1.
    + now apply IHT2_2.
    + intros Hnil.
      apply gmerge_eq_nil in Hnil as [_ Hnil].
      match goal with H : _ = ∅ -> _ |- _ => specialize (H Hnil) as [U ?] end.
      subst; unfold gu_join; destruct u; eauto.
    + unfold gu_join; destruct u; assumption.
Qed.

(** ** Merging Preserves Resolution

    Splitting a trie at a segment sends every resolution to exactly one of the
    three places the split produced. *)
Lemma gt_take_lookup : forall T y u T' T0 fp U,
    gt_take y T = (u, T', T0) ->
    gt_canon T ->
    T ∋ᵘ fp ⇒ U ->
    (fp = y :: nil /\ u = Some U)
    \/ (exists fp', fp = y :: fp' /\ fp' <> nil /\ T' ∋ᵘ fp' ⇒ U)
    \/ T0 ∋ᵘ fp ⇒ U.
Proof.
  induction T; simpl; intros y u T' T0 fp U Heq Hc Hlk; [inversion Hlk |].
  destruct_all.
  destruct (String.eqb y s) eqn:Hy.
  - apply String.eqb_eq in Hy; subst.
    inversion Heq; subst.
    inversion Hlk; subst; eauto 6.
  - apply String.eqb_neq in Hy.
    destruct (gt_take y T1) as [[w T1'] T0'] eqn:Ht.
    inversion Heq; subst.
    inversion Hlk; subst.
    + right; right; mauto.
    + right; right; mauto.
    + specialize (IHT1 _ _ _ _ _ _ Ht ltac:(eassumption) ltac:(eassumption))
        as [[? ?] | [[fp' [? [? ?]]] | ?]]; subst; mauto 6.
Qed.

Theorem gmerge_lookup_l : forall T2 T1 fp U,
    gt_canon T1 ->
    T1 ∋ᵘ fp ⇒ U ->
    gmerge T1 T2 ∋ᵘ fp ⇒ U.
Proof.
  induction T2; simpl; intros T1 fp U Hc Hlk; [assumption |].
  destruct (gt_take s T1) as [[u T'] T1'] eqn:Ht.
  specialize (gt_take_canon _ _ _ _ _ Ht Hc) as [Hc' Hc1'].
  specialize (gt_take_lookup _ _ _ _ _ _ _ Ht Hc Hlk)
    as [[? ?] | [[fp' [? [? ?]]] | ?]]; subst.
  - unfold gu_join; mauto.
  - apply gtl_in; [| assumption].
    now apply IHT2_2.
  - destruct fp as [| z fp]; [inversion Hlk |].
    assert (z <> s).
    { intros ?; subst.
      eapply gt_fresh_no_lookup; [| eassumption].
      eapply gt_take_key_fresh; eassumption. }
    apply gtl_old; [| assumption].
    now apply IHT2_1.
Qed.
