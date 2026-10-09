From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import CoreInversions Levels Fresh SystemOpt.
Import Syntax_Notations.

(** * Levels as Expressions: the Equations of a Canonical Form

    Readback canonicalises a level: it sorts the atoms, merges repetitions at
    the larger offset and drops a dominated constant
    ([Core.Syntactic.Levels.lvl_canon]).  Soundness needs that this is an
    equation of the theory, which is what this file proves:

<<
    la_wf Γ xs -> Γ ⊢ ⌈c, xs⌉ ≈ ⌈lvl_canon (c, xs)⌉ : Level@n
>>
    where [⌈c, xs⌉] is [lvl_exp_of c (la_to_list xs)], the expression a
    canonical level reads back as.  Each step of [lvl_canon] is an instance of
    the level equations: sorting is commutativity and associativity, merging is
    [maxl (k + a) (k' + a) ≈ max k k' + a], dropping an atom of a sort below
    the constant's tier is absorption, and dropping the constant is
    [c ≤ k -> maxl c (k + a) ≈ k + a].  Absorption needs every atom typed at
    its own sort ([la_ws]); the other steps only at the sort of the whole
    ([la_wf]).

    The proofs are easier on a right-nested fold with the constant innermost
    ([lvl_tm_from]) than on the left-nested fold readback produces, so the two
    are related first. *)

Section Fixed_GCtx.
  Context {Θ : gdeps} {Ξ : gstack}.

(** Every equation of this file is at one sort, the levels below [ω·(n+1)]:
    canonicalisation neither raises nor lowers the sort of a level, the
    atoms of a level of sort [n] are levels of sort [n], and so is its
    constant, a literal of a tier at most [n]. *)
  Context {n : nat}.

(** ** The Iterated Successor *)

Lemma wf_succl_n : forall {Γ M} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level@n.
Proof. intros ? ? k; induction k; cbn; mauto 3. Qed.

Hint Resolve wf_succl_n : mctt.

Lemma wf_exp_eq_succl_n_cong : forall {Γ M M'} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M ≈ succl_n k M' : Level@n.
Proof. intros ? ? ? k; induction k; cbn; mauto 3. Qed.

Hint Resolve wf_exp_eq_succl_n_cong : mctt.

Fact succl_n_add : forall k k' M, succl_n (k + k') M = succl_n k (succl_n k' M).
Proof. intros k; induction k; intros; cbn; [ reflexivity | rewrite IHk; reflexivity ]. Qed.

(** A literal [ω·a + b] is the [b]-th successor of the limit [ω·a]. *)
Lemma wf_exp_eq_llit_succl_n : forall {Γ} a b,
    a <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ(a, b) ≈ succl_n b (𝕃ᵒ(a, 0)) : Level@n.
Proof.
  intros ? a b Ha HΓ; induction b; cbn; [ mauto 3 |].
  transitivity (succl (𝕃ᵒ(a, b))); [ apply wf_exp_eq_llit_succl; assumption |].
  apply wf_exp_eq_succl_cong; exact IHb.
Qed.

(** The iterated distributivity of [succl] over [maxl]. *)
Lemma wf_exp_eq_succl_n_maxl : forall {Γ M N} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k (maxl M N) ≈ maxl (succl_n k M) (succl_n k N) : Level@n.
Proof.
  intros ? ? ? k HM HN; induction k; cbn; [ mauto 3 |].
  transitivity (succl (maxl (succl_n k M) (succl_n k N))); [ mauto 3 |].
  apply wf_exp_eq_succl_maxl; mauto 3.
Qed.

(** ** The Order on Levels

    [maxl M N ≈ N] is the order of the universe subtyping rule.  It is
    reflexive by idempotence, transitive by associativity, monotone under
    [succl] by distributivity, least at [𝕃@0] by the unit law, and
    inflationary by the subsumption law. *)
Definition lvl_sub (Γ : ctx) (M N : exp) : Prop := Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N ≈ N : Level@n.

Lemma lvl_sub_refl : forall {Γ M},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    lvl_sub Γ M M.
Proof. intros; apply wf_exp_eq_maxl_idem; assumption. Qed.

Lemma lvl_sub_trans : forall {Γ M N P},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Level@n ->
    lvl_sub Γ M N ->
    lvl_sub Γ N P ->
    lvl_sub Γ M P.
Proof.
  intros * HM HN HP HMN HNP; unfold lvl_sub in *.
  transitivity (maxl M (maxl N P));
    [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply wf_exp_eq_sym; exact HNP ] |].
  transitivity (maxl (maxl M N) P);
    [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
  transitivity (maxl N P); [ apply wf_exp_eq_maxl_cong; [ exact HMN | mauto 3 ] | exact HNP ].
Qed.

(** The join is the least upper bound. *)
Lemma lvl_sub_maxl_l : forall {Γ M N},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
    lvl_sub Γ M (maxl M N).
Proof.
  intros * HM HN; unfold lvl_sub.
  transitivity (maxl (maxl M M) N); [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
  apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_idem; assumption | mauto 3 ].
Qed.

Lemma lvl_sub_maxl_r : forall {Γ M N},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
    lvl_sub Γ N (maxl M N).
Proof.
  intros * HM HN; unfold lvl_sub.
  transitivity (maxl N (maxl N M)); [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply wf_exp_eq_maxl_comm; assumption ] |].
  transitivity (maxl (maxl N N) M); [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
  transitivity (maxl N M); [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_idem; assumption | mauto 3 ] |].
  apply wf_exp_eq_maxl_comm; assumption.
Qed.

Lemma lvl_sub_maxl_lub : forall {Γ M N P},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Level@n ->
    lvl_sub Γ M P ->
    lvl_sub Γ N P ->
    lvl_sub Γ (maxl M N) P.
Proof.
  intros * HM HN HP HMP HNP; unfold lvl_sub in *.
  transitivity (maxl M (maxl N P)); [ apply wf_exp_eq_maxl_assoc; assumption |].
  transitivity (maxl M P); [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HNP ] | exact HMP ].
Qed.

Lemma lvl_sub_succl : forall {Γ M N},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
    lvl_sub Γ M N ->
    lvl_sub Γ (succl M) (succl N).
Proof.
  intros * HM HN HMN; unfold lvl_sub in *.
  transitivity (succl (maxl M N)); [ apply wf_exp_eq_sym, wf_exp_eq_succl_maxl; assumption |].
  apply wf_exp_eq_succl_cong; assumption.
Qed.

Lemma lvl_sub_zero : forall {Γ M},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    lvl_sub Γ (𝕃@0) M.
Proof. intros; apply wf_exp_eq_maxl_zero; assumption. Qed.

Lemma lvl_sub_self_succl : forall {Γ M},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    lvl_sub Γ M (succl M).
Proof. intros; apply wf_exp_eq_maxl_succl; assumption. Qed.

Lemma lvl_sub_succl_n : forall {Γ M} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    lvl_sub Γ M (succl_n k M).
Proof.
  intros ? ? k HM; induction k; cbn; [ apply lvl_sub_refl; assumption |].
  assert (Hk : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level@n) by (apply (wf_succl_n k); exact HM).
  eapply lvl_sub_trans; [ exact HM | exact Hk | mauto 3 | exact IHk |].
  apply lvl_sub_self_succl; exact Hk.
Qed.

Lemma lvl_sub_succl_n_mono : forall {Γ M N} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
    lvl_sub Γ M N ->
    lvl_sub Γ (succl_n k M) (succl_n k N).
Proof.
  intros ? ? ? k HM HN HMN; induction k; cbn; [ exact HMN |].
  apply lvl_sub_succl; [ apply (wf_succl_n k); exact HM | apply (wf_succl_n k); exact HN | exact IHk ].
Qed.

(** The merge step: two offsets of the same atom join at the larger one. *)
Lemma wf_exp_eq_maxl_succl_n : forall {Γ M} k k',
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (succl_n k M) (succl_n k' M) ≈ succl_n (Nat.max k k') M : Level@n.
Proof.
  intros * HM.
  assert (Hle : forall d e, d <= e -> Θ ⍮ Ξ ⍮ Γ ⊢ maxl (succl_n d M) (succl_n e M) ≈ succl_n e M : Level@n).
  { intros d e Hde.
    replace e with (d + (e - d)) by lia.
    rewrite succl_n_add.
    apply lvl_sub_succl_n_mono;
      [ exact HM | apply (wf_succl_n (e - d)); exact HM | apply (lvl_sub_succl_n (e - d)); exact HM ]. }
  destruct (Nat.le_ge_cases k k') as [H | H].
  - rewrite (Nat.max_r _ _ H); apply Hle; exact H.
  - rewrite (Nat.max_l _ _ H).
    transitivity (maxl (succl_n k' M) (succl_n k M)); [ apply wf_exp_eq_maxl_comm; mauto 3 |].
    apply Hle; exact H.
Qed.

(** The drop step: a constant below an offset of an atom is absorbed. *)
Lemma wf_exp_eq_maxl_llit_succl_n : forall {Γ M} c k,
    c <= k ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃@c) (succl_n k M) ≈ succl_n k M : Level@n.
Proof.
  intros * Hck HM.
  assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
  (** [𝕃@c] is [succl^c 𝕃@0], and [succl^k M] is [succl^c (succl^(k-c) M)];
      the join distributes over the common prefix and [𝕃@0] is the unit. *)
  transitivity (maxl (succl_n c (𝕃@0)) (succl_n c (succl_n (k - c) M))).
  { apply wf_exp_eq_maxl_cong; [ apply (wf_exp_eq_llit_succl_n 0); [ apply le_0_n | mauto 2 ] |].
    rewrite <- succl_n_add; replace (c + (k - c)) with k by lia; mauto 3. }
  transitivity (succl_n c (maxl (𝕃@0) (succl_n (k - c) M)));
    [ apply wf_exp_eq_sym, wf_exp_eq_succl_n_maxl; mauto 3 |].
  transitivity (succl_n c (succl_n (k - c) M));
    [ apply wf_exp_eq_succl_n_cong, wf_exp_eq_maxl_zero; mauto 3 |].
  rewrite <- succl_n_add; replace (c + (k - c)) with k by lia; mauto 3.
Qed.

(** ** The Atoms of a Level, Well Typed *)

(** Every atom a level of the sort [n] of the whole. *)
Fixpoint la_wf (Γ : ctx) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ _ a r => Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level@n /\ la_wf Γ r
  end.

(** Every atom a level of its own sort, at most [n]: the atoms of a level
    readback produces are of this kind, their sorts read off their types. *)
Fixpoint la_ws (Γ : ctx) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ s a r => (s <= n /\ Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level@s) /\ la_ws Γ r
  end.

Lemma la_ws_wf : forall {Γ} xs, la_ws Γ xs -> la_wf Γ xs.
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros H; [ exact I |].
  destruct H as [[Hs Ha] Hr]; split; [| auto ].
  assert (⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
  eapply wf_exp_subtyp'; [ exact Ha | apply wf_subtyp_level; assumption ].
Qed.

Lemma la_wf_ins : forall {Γ} k s (a : ne) ys,
    Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level@n ->
    la_wf Γ ys ->
    la_wf Γ (la_ins k s a ys).
Proof.
  intros Γ k s a ys Ha; induction ys as [| k' t b r IH]; cbn; intros Hys; [ split; assumption |].
  destruct Hys as [Hb Hr]; destruct (at_cmp a s b t); cbn; split; auto.
Qed.

Lemma la_wf_sort : forall {Γ} xs,
    la_wf Γ xs ->
    la_wf Γ (la_sort xs).
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros H; [ exact I |].
  destruct H; apply la_wf_ins; auto.
Qed.

Lemma la_wf_keep : forall {Γ} c xs,
    la_wf Γ xs ->
    la_wf Γ (la_keep c xs).
Proof.
  intros Γ c xs; induction xs as [| k s a r IH]; cbn [la_keep]; intros H; [ exact I |].
  destruct H; destruct (fst c <=? s); cbn; auto.
Qed.

Lemma la_wf_app : forall {Γ} xs ys,
    la_wf Γ xs ->
    la_wf Γ ys ->
    la_wf Γ (la_app xs ys).
Proof.
  intros Γ xs ys; induction xs as [| k s a r IH]; cbn; intros Hxs Hys;
    [ exact Hys | destruct Hxs; split; auto ].
Qed.

Lemma la_wf_suc : forall {Γ} xs,
    la_wf Γ xs ->
    la_wf Γ (la_suc xs).
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros Hxs;
    [ exact I | destruct Hxs; split; auto ].
Qed.

Lemma la_ws_ins : forall {Γ} k s (a : ne) ys,
    s <= n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level@s ->
    la_ws Γ ys ->
    la_ws Γ (la_ins k s a ys).
Proof.
  intros Γ k s a ys Hs Ha; induction ys as [| k' t b r IH]; cbn; intros Hys; [ auto |].
  destruct Hys as [Hb Hr]; destruct (at_cmp a s b t); cbn; auto.
Qed.

Lemma la_ws_sort : forall {Γ} xs,
    la_ws Γ xs ->
    la_ws Γ (la_sort xs).
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros H; [ exact I |].
  destruct H as [[? ?] ?]; apply la_ws_ins; auto.
Qed.

Lemma la_ws_keep : forall {Γ} c xs,
    la_ws Γ xs ->
    la_ws Γ (la_keep c xs).
Proof.
  intros Γ c xs; induction xs as [| k s a r IH]; cbn [la_keep]; intros H; [ exact I |].
  destruct H; destruct (fst c <=? s); cbn; auto.
Qed.

Lemma la_ws_fresh_part : forall {Γ} k xs,
    la_ws Γ xs ->
    la_ws Γ (la_fresh_part k xs).
Proof.
  intros Γ k xs; induction xs as [| j s a r IH]; cbn [la_fresh_part]; intros H; [ exact I |].
  destruct H; destruct (ne_freshb k a); cbn; auto.
Qed.

Lemma la_ws_sorts : forall {Γ} xs, la_ws Γ xs -> forall j s a, la_In j s a xs -> s <= n.
Proof.
  intros Γ xs; induction xs as [| j0 t b r IH]; cbn; intros H j s a Hin; [ destruct Hin |].
  destruct H as [[Ht _] Hr]; destruct Hin as [(_ & -> & _) | Hin]; [ exact Ht | eapply IH; eassumption ].
Qed.

Lemma la_ws_app : forall {Γ} xs ys,
    la_ws Γ xs ->
    la_ws Γ ys ->
    la_ws Γ (la_app xs ys).
Proof.
  intros Γ xs ys; induction xs as [| k s a r IH]; cbn; intros Hxs Hys;
    [ exact Hys | destruct Hxs; split; auto ].
Qed.

Lemma la_ws_suc : forall {Γ} xs,
    la_ws Γ xs ->
    la_ws Γ (la_suc xs).
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros Hxs;
    [ exact I | destruct Hxs; split; auto ].
Qed.

(** ** The Two Folds

    [lvl_tm_from hd xs] is the right-nested fold, innermost [hd]; readback's
    [lvl_fold] is the left-nested one.  Up to the equations the two agree. *)
Fixpoint lvl_tm_from (hd : exp) (xs : lvl_atoms) : exp :=
  match xs with
  | la_nil => hd
  | la_cons k _ a r => maxl (succl_n k (a : exp)) (lvl_tm_from hd r)
  end.

Definition lvl_tm (c : o2) (xs : lvl_atoms) : exp := lvl_tm_from (𝕃ᵒ c) xs.

Lemma lvl_tm_from_wf : forall {Γ} hd xs,
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level@n ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from hd xs : Level@n.
Proof.
  intros Γ hd xs; revert hd; induction xs as [| k s a r IH]; cbn; intros hd Hhd Hxs;
    [ assumption |].
  destruct Hxs as [Ha Hr].
  apply wf_maxl; [ apply (wf_succl_n k); exact Ha | apply IH; assumption ].
Qed.

Hint Resolve lvl_tm_from_wf : mctt.

(** The fold at the least constant, the shape every step of the
    canonicalisation moves the atoms over. *)
Lemma lvl_tm_from_zero_wf : forall {Γ} xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) xs : Level@n.
Proof. intros; apply lvl_tm_from_wf; [ apply wf_llit; [ cbn; lia | assumption ] | assumption ]. Qed.

Hint Resolve lvl_tm_from_zero_wf : mctt.

Lemma lvl_tm_wf : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c xs : Level@n.
Proof. intros; unfold lvl_tm; apply lvl_tm_from_wf; [ apply wf_llit; assumption | assumption ]. Qed.

Hint Resolve lvl_tm_wf : mctt.

(** The innermost expression of the fold comes out. *)
Lemma lvl_tm_from_out : forall {Γ} hd xs,
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level@n ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from hd xs ≈ maxl hd (lvl_tm_from (𝕃@0) xs) : Level@n.
Proof.
  intros Γ hd xs; revert hd; induction xs as [| k s a r IH]; cbn; intros hd Hhd Hxs.
  - assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
    transitivity (maxl (𝕃@0) hd); [ apply wf_exp_eq_sym, wf_exp_eq_maxl_zero; assumption |].
    apply wf_exp_eq_maxl_comm; mauto 3.
  - destruct Hxs as [Ha Hr].
    assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
    transitivity (maxl (succl_n k a) (maxl hd (lvl_tm_from (𝕃@0) r)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; assumption ] |].
    (** The swap: [maxl x (maxl y z) ≈ maxl y (maxl x z)]. *)
    transitivity (maxl (maxl (succl_n k a) hd) (lvl_tm_from (𝕃@0) r));
      [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; mauto 3 |].
    transitivity (maxl (maxl hd (succl_n k a)) (lvl_tm_from (𝕃@0) r));
      [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_comm; mauto 3 | mauto 3 ] |].
    apply wf_exp_eq_maxl_assoc; mauto 3.
Qed.

Lemma lvl_fold_tm_from : forall {Γ} xs hd,
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level@n ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold hd (la_to_list xs) ≈ lvl_tm_from hd xs : Level@n.
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros hd Hhd Hxs; [ mauto 3 |].
  destruct Hxs as [Ha Hr].
  assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
  transitivity (lvl_tm_from (maxl hd (succl_n k a)) r); [ apply IH; mauto 3 |].
  transitivity (maxl (maxl hd (succl_n k a)) (lvl_tm_from (𝕃@0) r));
    [ apply lvl_tm_from_out; mauto 3 |].
  transitivity (maxl (succl_n k a) (maxl hd (lvl_tm_from (𝕃@0) r)));
    [| apply wf_exp_eq_maxl_cong; [ mauto 3 | apply wf_exp_eq_sym, lvl_tm_from_out; mauto 3 ] ].
  transitivity (maxl (maxl (succl_n k a) hd) (lvl_tm_from (𝕃@0) r));
    [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_comm; mauto 3 | mauto 3 ] |].
  apply wf_exp_eq_maxl_assoc; mauto 3.
Qed.

(** The expression a canonical level reads back as is the right-nested fold. *)
Lemma lvl_exp_of_tm : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) ≈ lvl_tm c xs : Level@n.
Proof.
  intros Γ c xs Hc HΓ Hxs; unfold lvl_tm.
  destruct xs as [| k s a r]; cbn; [ apply wf_exp_eq_llit_cong; assumption |].
  destruct Hxs as [Ha Hr].
  assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level@n) by (apply (wf_succl_n k); exact Ha).
  assert (Hz : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@0 : Level@n) by (apply wf_llit; [ cbn; lia | assumption ]).
  assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) r : Level@n) by (apply lvl_tm_from_wf; assumption).
  assert (Hct : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c : Level@n) by (apply wf_llit; assumption).
  assert (Hgen :
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold (maxl (𝕃ᵒ c) (succl_n k a)) (la_to_list r) ≈ lvl_tm_from (𝕃ᵒ c) (la_cons k s a r) : Level@n).
  { cbn [lvl_tm_from].
    assert (Hhd : Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ c) (succl_n k a) : Level@n)
      by (apply wf_maxl; [ exact Hct | exact Hka ]).
    transitivity (lvl_tm_from (maxl (𝕃ᵒ c) (succl_n k a)) r);
      [ apply lvl_fold_tm_from; [ exact Hhd | exact Hr ] |].
    transitivity (maxl (maxl (𝕃ᵒ c) (succl_n k a)) (lvl_tm_from (𝕃@0) r));
      [ apply lvl_tm_from_out; [ exact Hhd | exact Hr ] |].
    transitivity (maxl (maxl (succl_n k a) (𝕃ᵒ c)) (lvl_tm_from (𝕃@0) r));
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_maxl_comm; [ exact Hct | exact Hka ] | mauto 3 ] |].
    transitivity (maxl (succl_n k a) (maxl (𝕃ᵒ c) (lvl_tm_from (𝕃@0) r)));
      [ apply wf_exp_eq_maxl_assoc; assumption |].
    apply wf_exp_eq_maxl_cong;
      [ mauto 3 | apply wf_exp_eq_sym, lvl_tm_from_out; [ exact Hct | exact Hr ] ]. }
  destruct c as [[| c1] [| c2]]; try (apply Hgen).
  (** With atoms and no constant, the fold starts at the first atom. *)
  transitivity (lvl_tm_from (succl_n k a) r);
    [ apply lvl_fold_tm_from; [ exact Hka | exact Hr ] |].
  apply lvl_tm_from_out; [ exact Hka | exact Hr ].
Qed.

(** Two literals join at the larger one. *)
Lemma wf_exp_eq_maxl_llit : forall {Γ} c d,
    fst c <= n ->
    fst d <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ c) (𝕃ᵒ d) ≈ 𝕃ᵒ (omax c d) : Level@n.
Proof.
  intros Γ c d Hc Hd HΓ.
  destruct (ole_or_olt c d) as [Hle | Hlt].
  - rewrite omax_r by exact Hle; apply wf_exp_eq_maxl_llit_ole; assumption.
  - rewrite omax_l by (apply olt_ole; exact Hlt).
    transitivity (maxl (𝕃ᵒ d) (𝕃ᵒ c));
      [ apply wf_exp_eq_maxl_comm; apply wf_llit; assumption |].
    apply wf_exp_eq_maxl_llit_ole; [ apply olt_ole; exact Hlt | exact Hc | exact HΓ ].
Qed.

(** The two operations on the fold: the successor raises every offset and the
    constant, and the join concatenates the atoms and joins the constants.
    These are the equations soundness needs of a level operation. *)
Lemma lvl_tm_suc : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl (lvl_tm c xs) ≈ lvl_tm (osuc c) (la_suc xs) : Level@n.
Proof.
  intros Γ c xs Hc; revert c Hc; induction xs as [| k s a r IH]; cbn; intros c Hc HΓ Hxs;
    [ unfold lvl_tm; cbn; destruct c; apply wf_exp_eq_sym, wf_exp_eq_llit_succl; assumption |].
  destruct Hxs as [Ha Hr].
  assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level@n) by (apply (wf_succl_n k); exact Ha).
  assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c r : Level@n) by (apply lvl_tm_wf; assumption).
  unfold lvl_tm in *; cbn in *.
  transitivity (maxl (succl (succl_n k a)) (succl (lvl_tm_from (𝕃ᵒ c) r)));
    [ apply wf_exp_eq_succl_maxl; assumption |].
  apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; [ exact Hc | exact HΓ | exact Hr ] ].
Qed.

Lemma lvl_tm_max : forall {Γ} c xs d ys,
    fst c <= n ->
    fst d <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    la_wf Γ ys ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (lvl_tm c xs) (lvl_tm d ys) ≈ lvl_tm (omax c d) (la_app xs ys) : Level@n.
Proof.
  intros Γ c xs d ys Hc Hd; revert c Hc; induction xs as [| k s a r IH]; cbn; intros c Hc HΓ Hxs Hys.
  - (** No atom on the left: the two constants join in front of the right. *)
    assert (Hct : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c : Level@n) by (apply wf_llit; assumption).
    assert (Hdt : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ d : Level@n) by (apply wf_llit; assumption).
    assert (HT0 : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) ys : Level@n) by mauto 3.
    assert (Hcd : fst (omax c d) <= n) by (apply omax_fst_le; assumption).
    unfold lvl_tm; cbn.
    transitivity (maxl (𝕃ᵒ c) (maxl (𝕃ᵒ d) (lvl_tm_from (𝕃@0) ys)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply lvl_tm_from_out; [ exact Hdt | exact Hys ] ] |].
    transitivity (maxl (maxl (𝕃ᵒ c) (𝕃ᵒ d)) (lvl_tm_from (𝕃@0) ys));
      [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
    transitivity (maxl (𝕃ᵒ (omax c d)) (lvl_tm_from (𝕃@0) ys));
      [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_llit; assumption | mauto 3 ] |].
    apply wf_exp_eq_sym, lvl_tm_from_out; [ apply wf_llit; assumption | exact Hys ].
  - destruct Hxs as [Ha Hr].
    assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level@n) by (apply (wf_succl_n k); exact Ha).
    assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c r : Level@n) by (apply lvl_tm_wf; assumption).
    assert (Hyt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm d ys : Level@n) by (apply lvl_tm_wf; assumption).
    unfold lvl_tm in *; cbn in *.
    transitivity (maxl (succl_n k a) (maxl (lvl_tm_from (𝕃ᵒ c) r) (lvl_tm_from (𝕃ᵒ d) ys)));
      [ apply wf_exp_eq_maxl_assoc; assumption |].
    apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; assumption ].
Qed.

(** ** Sorting, Merging and Dropping *)

Lemma lvl_tm_ins : forall {Γ} c k s (a : ne) ys,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level@n ->
    la_wf Γ ys ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c (la_ins k s a ys) ≈ maxl (succl_n k a) (lvl_tm c ys) : Level@n.
Proof.
  intros Γ c k s a ys Hc HΓ Ha; induction ys as [| k' t b r IH]; cbn; intros Hys;
    [ unfold lvl_tm; cbn; apply wf_exp_eq_refl, wf_maxl; mauto 3 |].
  destruct Hys as [Hb Hr].
  assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level@n) by (apply (wf_succl_n k); exact Ha).
  assert (Hk'b : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k' b : Level@n) by (apply (wf_succl_n k'); exact Hb).
  assert (Hct : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c : Level@n) by (apply wf_llit; assumption).
  assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃ᵒ c) r : Level@n) by (apply lvl_tm_from_wf; assumption).
  destruct (at_cmp a s b t) eqn:E; cbn.
  - (** The same atom: the two offsets merge at the larger one. *)
    apply at_cmp_eq in E as [<- <-].
    unfold lvl_tm; cbn.
    transitivity (maxl (maxl (succl_n k a) (succl_n k' a)) (lvl_tm_from (𝕃ᵒ c) r));
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_sym, wf_exp_eq_maxl_succl_n; exact Ha
        | apply wf_exp_eq_refl; exact Hrt ] |].
    apply wf_exp_eq_maxl_assoc; [ exact Hka | exact Hk'b | exact Hrt ].
  - (** Below the head: the atom goes in front. *)
    unfold lvl_tm; cbn.
    apply wf_exp_eq_refl, wf_maxl; [ exact Hka | apply wf_maxl; [ exact Hk'b | exact Hrt ] ].
  - (** Above the head: the atom goes past it, by the swap. *)
    unfold lvl_tm in *; cbn.
    transitivity (maxl (succl_n k' b) (maxl (succl_n k a) (lvl_tm_from (𝕃ᵒ c) r)));
      [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_refl; exact Hk'b | apply IH; exact Hr ] |].
    transitivity (maxl (maxl (succl_n k' b) (succl_n k a)) (lvl_tm_from (𝕃ᵒ c) r));
      [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; [ exact Hk'b | exact Hka | exact Hrt ] |].
    transitivity (maxl (maxl (succl_n k a) (succl_n k' b)) (lvl_tm_from (𝕃ᵒ c) r));
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_maxl_comm; [ exact Hk'b | exact Hka ] | apply wf_exp_eq_refl; exact Hrt ] |].
    apply wf_exp_eq_maxl_assoc; [ exact Hka | exact Hk'b | exact Hrt ].
Qed.

Lemma lvl_tm_sort : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c (la_sort xs) ≈ lvl_tm c xs : Level@n.
Proof.
  intros Γ c xs Hc HΓ; induction xs as [| k s a r IH]; cbn; intros Hxs; [ mauto 3 |].
  destruct Hxs as [Ha Hr].
  transitivity (maxl (succl_n k a) (lvl_tm c (la_sort r)));
    [ apply lvl_tm_ins; [ assumption | assumption | assumption | apply la_wf_sort; assumption ] |].
  unfold lvl_tm; cbn.
  apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; assumption ].
Qed.

(** The absorption step: an atom of a sort below the tier of the constant
    is below the constant, which is above [ω·(s+1)]. *)
Lemma wf_exp_eq_maxl_succl_n_absorb : forall {Γ M} k s c,
    s < fst c ->
    fst c <= n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@s ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (succl_n k M) (𝕃ᵒ c) ≈ 𝕃ᵒ c : Level@n.
Proof.
  intros * Hsc Hc HM.
  assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
  assert (HkM : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level@n)
    by (apply (wf_succl_n k); eapply wf_exp_subtyp'; [ exact HM | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
  assert (HkMs : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level@s).
  { clear HkM; induction k; cbn; [ exact HM | apply wf_succl; exact IHk ]. }
  assert (Hl : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ(S s, 0) : Level@n) by (apply wf_llit; [ cbn; lia | exact HΓ ]).
  assert (Hct : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c : Level@n) by (apply wf_llit; assumption).
  assert (Hlc : Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ(S s, 0)) (𝕃ᵒ c) ≈ 𝕃ᵒ c : Level@n)
    by (apply wf_exp_eq_maxl_llit_ole; [ destruct c; unfold ole; cbn in *; lia | exact Hc | exact HΓ ]).
  assert (Habs : Θ ⍮ Ξ ⍮ Γ ⊢ maxl (succl_n k M) (𝕃ᵒ(S s, 0)) ≈ 𝕃ᵒ(S s, 0) : Level@n).
  { eapply wf_exp_eq_subtyp';
      [ apply wf_exp_eq_maxl_absorb; exact HkMs | apply wf_subtyp_level; [ lia | exact HΓ ] ]. }
  transitivity (maxl (succl_n k M) (maxl (𝕃ᵒ(S s, 0)) (𝕃ᵒ c)));
    [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply wf_exp_eq_sym; exact Hlc ] |].
  transitivity (maxl (maxl (succl_n k M) (𝕃ᵒ(S s, 0))) (𝕃ᵒ c));
    [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
  transitivity (maxl (𝕃ᵒ(S s, 0)) (𝕃ᵒ c)); [ apply wf_exp_eq_maxl_cong; [ exact Habs | mauto 3 ] |].
  exact Hlc.
Qed.

Lemma lvl_tm_keep : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_ws Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c (la_keep c xs) ≈ lvl_tm c xs : Level@n.
Proof.
  intros Γ c xs Hc HΓ; induction xs as [| k s a r IH]; cbn [la_keep]; intros Hxs; [ mauto 3 |].
  destruct Hxs as [[Hs Ha] Hr].
  pose proof (la_ws_wf _ Hr) as Hrw.
  assert (Han : Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level@n)
    by (eapply wf_exp_subtyp'; [ exact Ha | apply wf_subtyp_level; assumption ]).
  assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level@n) by (apply (wf_succl_n k); exact Han).
  assert (Hct : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c : Level@n) by (apply wf_llit; assumption).
  assert (HT0 : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) r : Level@n) by mauto 3.
  destruct (Nat.leb_spec (fst c) s); unfold lvl_tm in *; cbn [lvl_tm_from].
  - apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; exact Hr ].
  - (** The atom is absorbed by the constant. *)
    transitivity (lvl_tm_from (𝕃ᵒ c) r); [ apply IH; exact Hr |].
    apply wf_exp_eq_sym.
    transitivity (maxl (succl_n k a) (maxl (𝕃ᵒ c) (lvl_tm_from (𝕃@0) r)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply lvl_tm_from_out; assumption ] |].
    transitivity (maxl (maxl (succl_n k a) (𝕃ᵒ c)) (lvl_tm_from (𝕃@0) r));
      [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
    transitivity (maxl (𝕃ᵒ c) (lvl_tm_from (𝕃@0) r));
      [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_succl_n_absorb with (s := s); assumption | mauto 3 ] |].
    apply wf_exp_eq_sym, lvl_tm_from_out; assumption.
Qed.

(** The constant is dropped when some atom's offset dominates it; such a
    constant is finite. *)
Lemma lvl_tm_drop_fin : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    c <= la_maxoff xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm (ofin c) xs ≈ lvl_tm oz xs : Level@n.
Proof.
  intros Γ c xs HΓ; induction xs as [| k s a r IH]; cbn; intros Hxs Hle.
  - (** No atom: the constant is [0] already. *)
    assert (c = 0) as -> by lia; apply wf_exp_eq_llit_cong; [ cbn; lia | assumption ].
  - destruct Hxs as [Ha Hr].
    assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level@n) by (apply (wf_succl_n k); exact Ha).
    (** [𝕃@c] and [𝕃@0] are finite literals, levels of every sort. *)
    assert (Hc : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@c : Level@n) by (apply wf_llit; [ cbn; lia | assumption ]).
    assert (Hz : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@0 : Level@n) by (apply wf_llit; [ cbn; lia | assumption ]).
    assert (HT0 : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) r : Level@n) by (apply lvl_tm_from_wf; assumption).
    unfold lvl_tm; cbn.
    destruct (Nat.le_gt_cases c k) as [Hck | Hck].
    + (** The head atom dominates the constant, which the join absorbs. *)
      transitivity (maxl (succl_n k a) (maxl (𝕃@c) (lvl_tm_from (𝕃@0) r)));
        [ apply wf_exp_eq_maxl_cong;
          [ apply wf_exp_eq_refl; exact Hka | apply lvl_tm_from_out; [ exact Hc | exact Hr ] ] |].
      transitivity (maxl (maxl (succl_n k a) (𝕃@c)) (lvl_tm_from (𝕃@0) r));
        [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; [ exact Hka | exact Hc | exact HT0 ] |].
      apply wf_exp_eq_maxl_cong; [| apply wf_exp_eq_refl; exact HT0 ].
      transitivity (maxl (𝕃@c) (succl_n k a));
        [ apply wf_exp_eq_maxl_comm; [ exact Hka | exact Hc ] |].
      apply wf_exp_eq_maxl_llit_succl_n; [ exact Hck | exact Ha ].
    + (** Some atom of the tail does. *)
      assert (c <= la_maxoff r) by lia.
      apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_refl; exact Hka |].
      apply IH; assumption.
Qed.

Lemma lvl_tm_drop : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    ole c (ofin (la_maxoff xs)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c xs ≈ lvl_tm oz xs : Level@n.
Proof.
  intros Γ [a c] xs HΓ Hxs Hle.
  assert (a = 0) as -> by (unfold ole in Hle; cbn in Hle; lia).
  apply lvl_tm_drop_fin;
    [ assumption | assumption | unfold ole in Hle; cbn in Hle; lia ].
Qed.

(** ** The Canonical Form

    The equation soundness needs: a level is equal to its canonical form. *)
Lemma lvl_canon_cst_le : forall c xs, fst (fst (lvl_canon (c, xs))) <= fst c.
Proof.
  intros; unfold lvl_canon; cbn [fst snd].
  destruct (o2_dominated _ _); cbn; lia.
Qed.

Theorem lvl_tm_canon : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_ws Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c xs ≈ lvl_tm (fst (lvl_canon (c, xs))) (snd (lvl_canon (c, xs))) : Level@n.
Proof.
  intros Γ c xs Hc HΓ Hxs; unfold lvl_canon; cbn [fst snd].
  pose proof (la_ws_wf _ Hxs) as Hxw.
  assert (Hsk : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c (la_keep c (la_sort xs)) ≈ lvl_tm c xs : Level@n).
  { transitivity (lvl_tm c (la_sort xs));
      [ apply lvl_tm_keep; [ assumption | assumption | apply la_ws_sort; assumption ]
      | apply lvl_tm_sort; assumption ]. }
  destruct (o2_dominated c (la_maxoff (la_keep c (la_sort xs)))) eqn:Hle; cbn;
    [ apply o2_dominated_spec in Hle |].
  - transitivity (lvl_tm c (la_keep c (la_sort xs))); [ apply wf_exp_eq_sym; exact Hsk |].
    apply lvl_tm_drop; [ exact HΓ | apply la_wf_keep, la_wf_sort; exact Hxw | exact Hle ].
  - apply wf_exp_eq_sym; exact Hsk.
Qed.

Theorem lvl_exp_of_canon : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_ws Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs)
             ≈ nf_to_exp (nf_lvl_of (lvl_canon (c, xs))) : Level@n.
Proof.
  intros Γ c xs Hc HΓ Hxs.
  pose proof (la_ws_wf _ Hxs) as Hxw.
  assert (Hcanon : la_wf Γ (snd (lvl_canon (c, xs))))
    by (unfold lvl_canon; cbn; apply la_wf_keep, la_wf_sort; assumption).
  assert (Hcc : fst (fst (lvl_canon (c, xs))) <= n) by (eapply Nat.le_trans; [ apply lvl_canon_cst_le | exact Hc ]).
  transitivity (lvl_tm c xs); [ apply lvl_exp_of_tm; assumption |].
  transitivity (lvl_tm (fst (lvl_canon (c, xs))) (snd (lvl_canon (c, xs))));
    [ apply lvl_tm_canon; assumption |].
  apply wf_exp_eq_sym.
  unfold nf_lvl_of; cbn [nf_to_exp].
  apply lvl_exp_of_tm; assumption.
Qed.

(** ** The Atoms of a Well-Typed Level

    Soundness meets a level only as the readback of a value, so what it has is
    the typing of the whole expression; these recover the typing of each atom,
    which the equations above need. *)
(** The inversions give the argument at its own sort, which subsumption
    moves to the sort of the whole level. *)
Lemma wf_succl_n_inversion : forall {Γ M} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n.
Proof.
  intros Γ M k; revert M; induction k; cbn; intros M H; [ exact H |].
  apply wf_succl_inversion in H as (n0 & HM & Hsub).
  apply IHk; eapply wf_exp_subtyp'; [ exact HM | exact Hsub ].
Qed.

Lemma lvl_fold_hd_wf : forall {Γ} xs hd,
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold hd (la_to_list xs) : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level@n.
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros hd H; [ exact H |].
  apply IH in H; apply wf_maxl_inversion in H as (n0 & Hhd & _ & Hsub).
  eapply wf_exp_subtyp'; [ exact Hhd | exact Hsub ].
Qed.

Lemma lvl_fold_la_wf : forall {Γ} xs hd,
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold hd (la_to_list xs) : Level@n ->
    la_wf Γ xs.
Proof.
  intros Γ xs; induction xs as [| k s a r IH]; cbn; intros hd H; [ exact I |].
  split; [| eapply IH; exact H ].
  apply lvl_fold_hd_wf in H; apply wf_maxl_inversion in H as (n0 & _ & Ha & Hsub).
  apply (wf_succl_n_inversion k); eapply wf_exp_subtyp'; [ exact Ha | exact Hsub ].
Qed.

Lemma lvl_exp_of_la_wf : forall {Γ} c xs,
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) : Level@n ->
    la_wf Γ xs.
Proof.
  intros Γ c xs H; destruct xs as [| k s a r]; cbn in *; [ exact I |].
  destruct c as [[| c1] [| c2]];
    (split; [| eapply lvl_fold_la_wf; exact H ]);
    apply lvl_fold_hd_wf in H;
    try (apply wf_maxl_inversion in H as (n0 & _ & Ha & Hsub);
         assert (H : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level@n)
           by (eapply wf_exp_subtyp'; [ exact Ha | exact Hsub ]));
    apply (wf_succl_n_inversion k); exact H.
Qed.

(** ** The Order on Canonical Levels, Syntactically

    Subtyping between two small universes asks for [maxl t t' ≈ t'], which for
    two canonical levels is exactly the decidable order [lvl_le]: the
    canonicalisation equations turn the join into the canonical form of the
    join, and [lvl_le] says that is the canonical form of the right-hand
    side. *)
Lemma lvl_exp_of_wf : forall {Γ} c xs,
    fst c <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) : Level@n.
Proof.
  intros Γ c xs Hc HΓ Hxs.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) ≈ lvl_tm c xs : Level@n)
    by (apply lvl_exp_of_tm; assumption).
  gen_presups; assumption.
Qed.

Hint Resolve lvl_exp_of_wf : mctt.

Lemma lvl_exp_of_le : forall {Γ} c xs d ys,
    fst c <= n ->
    fst d <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_ws Γ xs ->
    la_ws Γ ys ->
    lvl_le (c, xs) (d, ys) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (lvl_exp_of c (la_to_list xs)) (lvl_exp_of d (la_to_list ys))
             ≈ lvl_exp_of d (la_to_list ys) : Level@n.
Proof.
  intros Γ c xs d ys Hc Hd HΓ Hxs Hys Hle.
  pose proof (la_ws_wf _ Hxs) as Hxw; pose proof (la_ws_wf _ Hys) as Hyw.
  assert (Hcd : fst (omax c d) <= n) by (apply omax_fst_le; assumption).
  transitivity (lvl_tm (fst (lvl_canon (lvl_max (c, xs) (d, ys))))
                       (snd (lvl_canon (lvl_max (c, xs) (d, ys))))).
  - transitivity (maxl (lvl_tm c xs) (lvl_tm d ys));
      [ apply wf_exp_eq_maxl_cong; apply lvl_exp_of_tm; assumption |].
    transitivity (lvl_tm (omax c d) (la_app xs ys));
      [ apply lvl_tm_max; assumption |].
    apply lvl_tm_canon; [ exact Hcd | exact HΓ | cbn; apply la_ws_app; assumption ].
  - unfold lvl_le in Hle; rewrite Hle.
    apply wf_exp_eq_sym.
    transitivity (lvl_tm d ys); [ apply lvl_exp_of_tm; assumption |].
    apply lvl_tm_canon; assumption.
Qed.

End Fixed_GCtx.

(** An atom typed at its own sort, at most [m], is at a sort at most every
    [n ≥ m]. *)
Lemma la_ws_mono : forall {Θ Ξ} m n Γ xs,
    m <= n ->
    @la_ws Θ Ξ m Γ xs ->
    @la_ws Θ Ξ n Γ xs.
Proof.
  intros * Hmn; induction xs as [| k s a r IH]; cbn; [ auto |].
  intros [[Hs Ha] Hr]; split; [ split; [ lia | exact Ha ] | auto ].
Qed.

#[export]
Hint Resolve wf_succl_n wf_exp_eq_succl_n_cong : mctt.
#[export]
Hint Resolve lvl_exp_of_wf : mctt.
