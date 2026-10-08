(** * Renaming Normal Forms

    A weakening [φ] acts on normal and neutral forms as it acts on terms: it
    renames the variables, and lifts itself under binders ([nf_wk]).  It
    commutes with [nf_to_exp] ([nf_wk_to_exp]).

    The point of this file is that an *order-preserving* renaming also
    commutes with the canonical form of a level ([lvl_canon_wk]): the order
    on atoms ([ne_cmp]) is lexicographic on a coding in which a variable is
    coded by its index, and an order-preserving renaming does not change the
    result of comparing two indices at the same binder depth
    ([ne_cmp_wk]).  So the renaming of a canonical level is canonical, and
    renaming a normal form gives a normal form.

    This is the syntactic half of the readback-shift lemma in
    [Core.Semantic.Rename]. *)
From Stdlib Require Import Arith Lia List PeanoNat.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Levels Fresh.
From Mctt.Core.Semantic Require Import Domain.
Import Syntax_Notations.

Fixpoint nf_wk (φ : wk) (W : nf) {struct W} : nf :=
  match W with
  | nf_typ i => nf_typ i
  | nf_univ c xs => nf_univ c (la_wk φ xs)
  | nf_level => nf_level
  | nf_lvl c xs => nf_lvl c (la_wk φ xs)
  | nf_nat => nf_nat
  | nf_zero => nf_zero
  | nf_succ W => nf_succ (nf_wk φ W)
  | nf_True => nf_True
  | nf_true => nf_true
  | nf_False => nf_False
  | nf_pi A B => nf_pi (nf_wk φ A) (nf_wk (wk_q φ) B)
  | nf_fn A M => nf_fn (nf_wk φ A) (nf_wk (wk_q φ) M)
  | nf_neut u => nf_neut (ne_wk φ u)
  end
with ne_wk (φ : wk) (u : ne) {struct u} : ne :=
  match u with
  | ne_natrec A MZ MS u =>
      ne_natrec (nf_wk (wk_q φ) A) (nf_wk φ MZ) (nf_wk (wk_q (wk_q φ)) MS) (ne_wk φ u)
  | ne_exfalso A u => ne_exfalso (nf_wk (wk_q φ) A) (ne_wk φ u)
  | ne_app u W => ne_app (ne_wk φ u) (nf_wk φ W)
  | ne_var x => ne_var (φ x)
  | ne_glob p => ne_glob p
  end
with la_wk (φ : wk) (xs : lvl_atoms) {struct xs} : lvl_atoms :=
  match xs with
  | la_nil => la_nil
  | la_cons j u r => la_cons j (ne_wk φ u) (la_wk φ r)
  end.

Definition lvl_wk (φ : wk) (l : lvl) : lvl := (fst l, la_wk φ (snd l)).

Lemma nf_lvl_of_wk : forall φ l, nf_wk φ (nf_lvl_of l) = nf_lvl_of (lvl_wk φ l).
Proof. reflexivity. Qed.

Lemma nf_univ_of_wk : forall φ l, nf_wk φ (nf_univ_of l) = nf_univ_of (lvl_wk φ l).
Proof. reflexivity. Qed.

(** ** The Renaming of the Term a Normal Form Denotes *)

Lemma nf_wk_to_exp :
  (forall W φ, nf_to_exp (nf_wk φ W) = (nf_to_exp W)[φ]ʷ) /\
  (forall u φ, ne_to_exp (ne_wk φ u) = (ne_to_exp u)[φ]ʷ) /\
  (forall xs φ, la_to_list (la_wk φ xs)
                = List.map (fun p => (fst p, (snd p)[φ]ʷ)) (la_to_list xs)).
Proof.
  apply nf_mut_ind; intros; cbn;
    try reflexivity;
    try solve [ f_equal; rewrite lvl_exp_of_wk; f_equal; eauto
              | rewrite lvl_exp_of_wk; f_equal; eauto
              | symmetry; apply qname_term_wk
              | f_equal; eauto
              | match goal with
                | Hu : forall φ, _ = _, Hr : forall φ, _ = _ |- _ => rewrite Hu, Hr; reflexivity
                end ].
Qed.

(** ** Order-Preserving Renamings Preserve the Order on Atoms

    The coding of a normal form is a node whose sibling is the continuation
    [t], so comparing two codings compares the forms first and the
    continuations only if the forms are equal ([nf_code_cmp]).  The
    continuation of [la_code] sits at the end of its list, with the same
    effect ([la_code_cmp]). *)
Definition cmp_then (c c' : comparison) : comparison :=
  match c with Eq => c' | _ => c end.

Definition nf_cmp (M N : nf) : comparison := lt_cmp (nf_code M lt_nil) (nf_code N lt_nil).
Definition la_cmp (xs ys : lvl_atoms) : comparison := lt_cmp (la_code xs lt_nil) (la_code ys lt_nil).

Lemma cmp_then_eq : forall c, cmp_then c Eq = c.
Proof. intros []; reflexivity. Qed.

Lemma lt_cmp_node : forall a c t b c' t',
    lt_cmp (lt_node a c t) (lt_node b c' t')
    = cmp_then (Nat.compare a b) (cmp_then (lt_cmp c c') (lt_cmp t t')).
Proof. intros; cbn; destruct (Nat.compare a b), (lt_cmp c c'); reflexivity. Qed.

Lemma lt_cmp_node_nil : forall a c t b c' t',
    lt_cmp (lt_node a c t) (lt_node b c' t')
    = cmp_then (lt_cmp (lt_node a c lt_nil) (lt_node b c' lt_nil)) (lt_cmp t t').
Proof.
  intros; rewrite !lt_cmp_node; cbn [lt_cmp].
  destruct (Nat.compare a b), (lt_cmp c c'); reflexivity.
Qed.

Lemma nf_code_node : forall M t, exists a c, nf_code M t = lt_node a c t /\ nf_code M lt_nil = lt_node a c lt_nil.
Proof. intros [] t; repeat match goal with p : o2 |- _ => destruct p end; cbn; eauto. Qed.

Lemma ne_code_node : forall m t, exists a c, ne_code m t = lt_node a c t /\ ne_code m lt_nil = lt_node a c lt_nil.
Proof. intros [] t; cbn; eauto. Qed.

Lemma nf_code_cmp : forall M N t t',
    lt_cmp (nf_code M t) (nf_code N t') = cmp_then (nf_cmp M N) (lt_cmp t t').
Proof.
  intros; unfold nf_cmp.
  destruct (nf_code_node M t) as (a & c & -> & ->), (nf_code_node N t') as (b & c' & -> & ->).
  apply lt_cmp_node_nil.
Qed.

Lemma ne_code_cmp : forall m n t t',
    lt_cmp (ne_code m t) (ne_code n t') = cmp_then (ne_cmp m n) (lt_cmp t t').
Proof.
  intros; unfold ne_cmp.
  destruct (ne_code_node m t) as (a & c & -> & ->), (ne_code_node n t') as (b & c' & -> & ->).
  apply lt_cmp_node_nil.
Qed.

Lemma cmp_then_assoc : forall a b c, cmp_then (cmp_then a b) c = cmp_then a (cmp_then b c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma la_code_cmp : forall xs ys t t',
    lt_cmp (la_code xs t) (la_code ys t') = cmp_then (la_cmp xs ys) (lt_cmp t t').
Proof.
  unfold la_cmp; induction xs as [| k m r IH]; intros [| k' m' r'] t t'; cbn [la_code];
    rewrite ?lt_cmp_node; cbn [Nat.compare lt_cmp cmp_then]; try reflexivity.
  rewrite (IH r' t t'), (IH r' lt_nil lt_nil); cbn [lt_cmp]; rewrite !cmp_then_eq, !cmp_then_assoc; reflexivity.
Qed.

(** Every coding is compared by [lt_cmp] of a node, so the comparisons
    reduce to [cmp_then] of the comparisons of the parts. *)
Ltac cmp_norm :=
  unfold nf_cmp, la_cmp, ne_cmp; cbn [nf_code ne_code la_code nf_wk ne_wk la_wk];
  rewrite ?lt_cmp_node; cbn [lt_cmp];
  repeat first [ rewrite nf_code_cmp | rewrite ne_code_cmp | rewrite la_code_cmp ]; cbn [lt_cmp];
  rewrite ?cmp_then_eq.

Lemma compare_mono : forall φ, wk_mono φ -> forall x y, Nat.compare (φ x) (φ y) = Nat.compare x y.
Proof.
  intros φ Hφ x y.
  destruct (Nat.compare_spec x y) as [-> | Hl | Hl];
    [ apply Nat.compare_refl | apply Nat.compare_lt_iff | apply Nat.compare_gt_iff ];
    apply Hφ; assumption.
Qed.

Lemma nf_cmp_wk :
  (forall M φ N, wk_mono φ -> nf_cmp (nf_wk φ M) (nf_wk φ N) = nf_cmp M N) /\
  (forall m φ n, wk_mono φ -> ne_cmp (ne_wk φ m) (ne_wk φ n) = ne_cmp m n) /\
  (forall xs φ ys, wk_mono φ -> la_cmp (la_wk φ xs) (la_wk φ ys) = la_cmp xs ys).
Proof.
  apply nf_mut_ind; intros;
    match goal with
    | |- nf_cmp _ (nf_wk _ ?N) = _ => destruct N
    | |- ne_cmp _ (ne_wk _ ?N) = _ => destruct N
    | |- la_cmp _ (la_wk _ ?N) = _ => destruct N
    end;
    repeat match goal with p : o2 |- _ => destruct p end;
    cmp_norm; try reflexivity.
  all: repeat match goal with
         | IH : forall φ N, wk_mono φ -> ?cmp (?wk φ ?M) (?wk φ N) = _ |- context [ ?cmp (?wk ?ψ ?M) (?wk ?ψ ?N') ] =>
             rewrite (IH ψ N') by (repeat apply wk_mono_q; assumption)
         end; try reflexivity.
  (** A variable: an order-preserving renaming preserves the comparison. *)
  match goal with H : wk_mono ?φ |- _ => rewrite (compare_mono φ H) end; reflexivity.
Qed.

Corollary ne_cmp_wk : forall φ m n, wk_mono φ -> ne_cmp (ne_wk φ m) (ne_wk φ n) = ne_cmp m n.
Proof. intros; apply (proj1 (proj2 nf_cmp_wk)); assumption. Qed.

(** ** Order-Preserving Renamings Commute with the Canonical Form *)

Lemma la_ins_wk : forall φ, wk_mono φ ->
    forall k a ys, la_wk φ (la_ins k a ys) = la_ins k (ne_wk φ a) (la_wk φ ys).
Proof.
  intros φ Hφ k a; induction ys as [| k' b r IH]; cbn [la_ins la_wk]; [ reflexivity |].
  rewrite ne_cmp_wk by assumption.
  destruct (ne_cmp a b); cbn [la_wk]; congruence.
Qed.

Lemma la_sort_wk : forall φ, wk_mono φ -> forall xs, la_wk φ (la_sort xs) = la_sort (la_wk φ xs).
Proof.
  intros φ Hφ; induction xs as [| k a r IH]; cbn [la_sort la_wk]; [ reflexivity |].
  rewrite la_ins_wk, IH by assumption; reflexivity.
Qed.

Lemma la_maxoff_wk : forall φ xs, la_maxoff (la_wk φ xs) = la_maxoff xs.
Proof. intros φ; induction xs; cbn; congruence. Qed.

Theorem lvl_canon_wk : forall φ, wk_mono φ -> forall l, lvl_canon (lvl_wk φ l) = lvl_wk φ (lvl_canon l).
Proof.
  intros φ Hφ [c xs]; unfold lvl_canon, lvl_wk; cbn [fst snd].
  rewrite <- la_sort_wk, la_maxoff_wk by assumption; reflexivity.
Qed.

(** ** Freshness

    A renaming that never hits [k] produces normal forms fresh at [k]. *)

Lemma nf_wk_fresh :
  (forall W k φ, wk_avoids k φ -> nf_fresh k (nf_wk φ W)) /\
  (forall u k φ, wk_avoids k φ -> ne_fresh k (ne_wk φ u)) /\
  (forall xs k φ, wk_avoids k φ -> la_fresh k (la_wk φ xs)).
Proof.
  apply nf_mut_ind; intros; cbn; repeat split; eauto 6 using wk_avoids_q.
Qed.

(** ** Injectivity

    An injective renaming is injective on normal forms. *)
Definition wk_inj (φ : wk) : Prop := forall x y, φ x = φ y -> x = y.

Lemma wk_inj_q : forall φ, wk_inj φ -> wk_inj (wk_q φ).
Proof. intros φ Hφ [| x] [| y]; cbn; intros H; try discriminate; [ reflexivity | f_equal; apply Hφ; lia ]. Qed.

Lemma wk_inj_shift : wk_inj wk_shift.
Proof. intros x y; cbn; lia. Qed.

Lemma nf_wk_inj :
  (forall W φ W', wk_inj φ -> nf_wk φ W = nf_wk φ W' -> W = W') /\
  (forall u φ u', wk_inj φ -> ne_wk φ u = ne_wk φ u' -> u = u') /\
  (forall xs φ xs', wk_inj φ -> la_wk φ xs = la_wk φ xs' -> xs = xs').
Proof.
  apply nf_mut_ind; intros;
    match goal with
    | H : nf_wk _ _ = nf_wk _ ?W' |- _ => destruct W'; cbn in H; inversion H; subst
    | H : ne_wk _ _ = ne_wk _ ?W' |- _ => destruct W'; cbn in H; inversion H; subst
    | H : la_wk _ _ = la_wk _ ?W' |- _ => destruct W'; cbn in H; inversion H; subst
    end;
    f_equal; eauto using wk_inj_q.
Qed.
