From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import CoreInversions Levels SystemOpt.
Import Syntax_Notations.

(** * Levels as Expressions: the Equations of a Canonical Form

    Readback canonicalises a level: it sorts the atoms, merges repetitions at
    the larger offset and drops a dominated constant
    ([Core.Syntactic.Levels.lvl_canon]).  Soundness needs that this is an
    equation of the theory, which is what this file proves:

<<
    la_wf Γ xs -> Γ ⊢ ⌈c, xs⌉ ≈ ⌈lvl_canon (c, xs)⌉ : Level
>>
    where [⌈c, xs⌉] is [lvl_exp_of c (la_to_list xs)], the expression a
    canonical level reads back as.  Each step of [lvl_canon] is an instance of
    the level equations: sorting is commutativity and associativity, merging is
    [maxl (k + a) (k' + a) ≈ max k k' + a], and dropping the constant is
    [c ≤ k -> maxl c (k + a) ≈ k + a].

    The proofs are easier on a right-nested fold with the constant innermost
    ([lvl_tm_from]) than on the left-nested fold readback produces, so the two
    are related first. *)

Section Fixed_GCtx.
  Context {Θ : gdeps} {Ξ : gstack}.

(** ** The Iterated Successor *)

Lemma wf_succl_n : forall {Γ M} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level.
Proof. intros ? ? k; induction k; cbn; mauto 3. Qed.

Hint Resolve wf_succl_n : mctt.

Lemma wf_exp_eq_succl_n_cong : forall {Γ M M'} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M ≈ succl_n k M' : Level.
Proof. intros ? ? ? k; induction k; cbn; mauto 3. Qed.

Hint Resolve wf_exp_eq_succl_n_cong : mctt.

Fact succl_n_add : forall k k' M, succl_n (k + k') M = succl_n k (succl_n k' M).
Proof. intros k; induction k; intros; cbn; [ reflexivity | rewrite IHk; reflexivity ]. Qed.

(** A literal [ω·a + n] is the [n]-th successor of the limit [ω·a]. *)
Lemma wf_exp_eq_llit_succl_n : forall {Γ} a n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ(a, n) ≈ succl_n n (𝕃ᵒ(a, 0)) : Level.
Proof.
  intros ? a n HΓ; induction n; cbn; [ mauto 3 |].
  transitivity (succl (𝕃ᵒ(a, n))); [ mauto 3 |].
  apply wf_exp_eq_succl_cong; exact IHn.
Qed.

(** The iterated distributivity of [succl] over [maxl]. *)
Lemma wf_exp_eq_succl_n_maxl : forall {Γ M N} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k (maxl M N) ≈ maxl (succl_n k M) (succl_n k N) : Level.
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
Definition lvl_sub (Γ : ctx) (M N : exp) : Prop := Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N ≈ N : Level.

Lemma lvl_sub_refl : forall {Γ M},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    lvl_sub Γ M M.
Proof. intros; apply wf_exp_eq_maxl_idem; assumption. Qed.

Lemma lvl_sub_trans : forall {Γ M N P},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Level ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level ->
    lvl_sub Γ M (maxl M N).
Proof.
  intros * HM HN; unfold lvl_sub.
  transitivity (maxl (maxl M M) N); [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
  apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_idem; assumption | mauto 3 ].
Qed.

Lemma lvl_sub_maxl_r : forall {Γ M N},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level ->
    lvl_sub Γ N (maxl M N).
Proof.
  intros * HM HN; unfold lvl_sub.
  transitivity (maxl N (maxl N M)); [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply wf_exp_eq_maxl_comm; assumption ] |].
  transitivity (maxl (maxl N N) M); [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
  transitivity (maxl N M); [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_idem; assumption | mauto 3 ] |].
  apply wf_exp_eq_maxl_comm; assumption.
Qed.

Lemma lvl_sub_maxl_lub : forall {Γ M N P},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Level ->
    lvl_sub Γ M P ->
    lvl_sub Γ N P ->
    lvl_sub Γ (maxl M N) P.
Proof.
  intros * HM HN HP HMP HNP; unfold lvl_sub in *.
  transitivity (maxl M (maxl N P)); [ apply wf_exp_eq_maxl_assoc; assumption |].
  transitivity (maxl M P); [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HNP ] | exact HMP ].
Qed.

Lemma lvl_sub_succl : forall {Γ M N},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level ->
    lvl_sub Γ M N ->
    lvl_sub Γ (succl M) (succl N).
Proof.
  intros * HM HN HMN; unfold lvl_sub in *.
  transitivity (succl (maxl M N)); [ apply wf_exp_eq_sym, wf_exp_eq_succl_maxl; assumption |].
  apply wf_exp_eq_succl_cong; assumption.
Qed.

Lemma lvl_sub_zero : forall {Γ M},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    lvl_sub Γ (𝕃@0) M.
Proof. intros; apply wf_exp_eq_maxl_zero; assumption. Qed.

Lemma lvl_sub_self_succl : forall {Γ M},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    lvl_sub Γ M (succl M).
Proof. intros; apply wf_exp_eq_maxl_succl; assumption. Qed.

Lemma lvl_sub_succl_n : forall {Γ M} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    lvl_sub Γ M (succl_n k M).
Proof.
  intros ? ? k HM; induction k; cbn; [ apply lvl_sub_refl; assumption |].
  assert (Hk : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level) by (apply (wf_succl_n k); exact HM).
  eapply lvl_sub_trans; [ exact HM | exact Hk | mauto 3 | exact IHk |].
  apply lvl_sub_self_succl; exact Hk.
Qed.

Lemma lvl_sub_succl_n_mono : forall {Γ M N} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : Level ->
    lvl_sub Γ M N ->
    lvl_sub Γ (succl_n k M) (succl_n k N).
Proof.
  intros ? ? ? k HM HN HMN; induction k; cbn; [ exact HMN |].
  apply lvl_sub_succl; [ apply (wf_succl_n k); exact HM | apply (wf_succl_n k); exact HN | exact IHk ].
Qed.

(** The merge step: two offsets of the same atom join at the larger one. *)
Lemma wf_exp_eq_maxl_succl_n : forall {Γ M} k k',
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (succl_n k M) (succl_n k' M) ≈ succl_n (Nat.max k k') M : Level.
Proof.
  intros * HM.
  assert (Hle : forall d e, d <= e -> Θ ⍮ Ξ ⍮ Γ ⊢ maxl (succl_n d M) (succl_n e M) ≈ succl_n e M : Level).
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
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃@c) (succl_n k M) ≈ succl_n k M : Level.
Proof.
  intros * Hck HM.
  assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
  (** [𝕃@c] is [succl^c 𝕃@0], and [succl^k M] is [succl^c (succl^(k-c) M)];
      the join distributes over the common prefix and [𝕃@0] is the unit. *)
  transitivity (maxl (succl_n c (𝕃@0)) (succl_n c (succl_n (k - c) M))).
  { apply wf_exp_eq_maxl_cong; [ apply (wf_exp_eq_llit_succl_n 0); assumption |].
    rewrite <- succl_n_add; replace (c + (k - c)) with k by lia; mauto 3. }
  transitivity (succl_n c (maxl (𝕃@0) (succl_n (k - c) M)));
    [ apply wf_exp_eq_sym, wf_exp_eq_succl_n_maxl; mauto 3 |].
  transitivity (succl_n c (succl_n (k - c) M));
    [ apply wf_exp_eq_succl_n_cong, wf_exp_eq_maxl_zero; mauto 3 |].
  rewrite <- succl_n_add; replace (c + (k - c)) with k by lia; mauto 3.
Qed.

(** ** The Atoms of a Level, Well Typed *)

Fixpoint la_wf (Γ : ctx) (xs : lvl_atoms) : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ a r => Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level /\ la_wf Γ r
  end.

Lemma la_wf_ins : forall {Γ} k (a : ne) ys,
    Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level ->
    la_wf Γ ys ->
    la_wf Γ (la_ins k a ys).
Proof.
  intros Γ k a ys Ha; induction ys as [| k' b r IH]; cbn; intros Hys; [ split; assumption |].
  destruct Hys as [Hb Hr]; destruct (ne_cmp a b); cbn; split; auto.
Qed.

Lemma la_wf_sort : forall {Γ} xs,
    la_wf Γ xs ->
    la_wf Γ (la_sort xs).
Proof.
  intros Γ xs; induction xs as [| k a r IH]; cbn; intros H; [ exact I |].
  destruct H; apply la_wf_ins; auto.
Qed.

Lemma la_wf_app : forall {Γ} xs ys,
    la_wf Γ xs ->
    la_wf Γ ys ->
    la_wf Γ (la_app xs ys).
Proof.
  intros Γ xs ys; induction xs as [| k a r IH]; cbn; intros Hxs Hys;
    [ exact Hys | destruct Hxs; split; auto ].
Qed.

Lemma la_wf_suc : forall {Γ} xs,
    la_wf Γ xs ->
    la_wf Γ (la_suc xs).
Proof.
  intros Γ xs; induction xs as [| k a r IH]; cbn; intros Hxs;
    [ exact I | destruct Hxs; split; auto ].
Qed.

(** ** The Two Folds

    [lvl_tm_from hd xs] is the right-nested fold, innermost [hd]; readback's
    [lvl_fold] is the left-nested one.  Up to the equations the two agree. *)
Fixpoint lvl_tm_from (hd : exp) (xs : lvl_atoms) : exp :=
  match xs with
  | la_nil => hd
  | la_cons k a r => maxl (succl_n k (a : exp)) (lvl_tm_from hd r)
  end.

Definition lvl_tm (c : o2) (xs : lvl_atoms) : exp := lvl_tm_from (𝕃ᵒ c) xs.

Lemma lvl_tm_from_wf : forall {Γ} hd xs,
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from hd xs : Level.
Proof.
  intros Γ hd xs; revert hd; induction xs as [| k a r IH]; cbn; intros hd Hhd Hxs;
    [ assumption |].
  destruct Hxs as [Ha Hr].
  apply wf_maxl; [ apply (wf_succl_n k); exact Ha | apply IH; assumption ].
Qed.

Hint Resolve lvl_tm_from_wf : mctt.

Lemma lvl_tm_wf : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c xs : Level.
Proof. intros; unfold lvl_tm; apply lvl_tm_from_wf; mauto 3. Qed.

Hint Resolve lvl_tm_wf : mctt.

(** The innermost expression of the fold comes out. *)
Lemma lvl_tm_from_out : forall {Γ} hd xs,
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from hd xs ≈ maxl hd (lvl_tm_from (𝕃@0) xs) : Level.
Proof.
  intros Γ hd xs; revert hd; induction xs as [| k a r IH]; cbn; intros hd Hhd Hxs.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold hd (la_to_list xs) ≈ lvl_tm_from hd xs : Level.
Proof.
  intros Γ xs; induction xs as [| k a r IH]; cbn; intros hd Hhd Hxs; [ mauto 3 |].
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
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) ≈ lvl_tm c xs : Level.
Proof.
  intros Γ c xs HΓ Hxs; unfold lvl_tm.
  destruct xs as [| k a r]; cbn; [ mauto 3 |].
  destruct Hxs as [Ha Hr].
  assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level) by (apply (wf_succl_n k); exact Ha).
  assert (Hz : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@0 : Level) by mauto 3.
  assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) r : Level) by (apply lvl_tm_from_wf; assumption).
  assert (Hgen : forall c', c' <> oz ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold (maxl (𝕃ᵒ c') (succl_n k a)) (la_to_list r) ≈ lvl_tm_from (𝕃ᵒ c') (la_cons k a r) : Level).
  { intros c' _; cbn [lvl_tm_from].
    assert (Hc : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c' : Level) by mauto 3.
    assert (Hhd : Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ c') (succl_n k a) : Level)
      by (apply wf_maxl; [ exact Hc | exact Hka ]).
    transitivity (lvl_tm_from (maxl (𝕃ᵒ c') (succl_n k a)) r);
      [ apply lvl_fold_tm_from; [ exact Hhd | exact Hr ] |].
    transitivity (maxl (maxl (𝕃ᵒ c') (succl_n k a)) (lvl_tm_from (𝕃@0) r));
      [ apply lvl_tm_from_out; [ exact Hhd | exact Hr ] |].
    transitivity (maxl (maxl (succl_n k a) (𝕃ᵒ c')) (lvl_tm_from (𝕃@0) r));
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_maxl_comm; [ exact Hc | exact Hka ] | mauto 3 ] |].
    transitivity (maxl (succl_n k a) (maxl (𝕃ᵒ c') (lvl_tm_from (𝕃@0) r)));
      [ apply wf_exp_eq_maxl_assoc; assumption |].
    apply wf_exp_eq_maxl_cong;
      [ mauto 3 | apply wf_exp_eq_sym, lvl_tm_from_out; [ exact Hc | exact Hr ] ]. }
  destruct c as [[| c1] [| c2]]; try (apply Hgen; discriminate).
  (** With atoms and no constant, the fold starts at the first atom. *)
  transitivity (lvl_tm_from (succl_n k a) r);
    [ apply lvl_fold_tm_from; [ exact Hka | exact Hr ] |].
  apply lvl_tm_from_out; [ exact Hka | exact Hr ].
Qed.

(** Two literals join at the larger one. *)
Lemma wf_exp_eq_maxl_llit : forall {Γ} c d,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ c) (𝕃ᵒ d) ≈ 𝕃ᵒ (omax c d) : Level.
Proof.
  intros Γ c d HΓ.
  destruct (ole_or_olt c d) as [Hle | Hlt].
  - rewrite omax_r by exact Hle; apply wf_exp_eq_maxl_llit_ole; assumption.
  - rewrite omax_l by (apply olt_ole; exact Hlt).
    transitivity (maxl (𝕃ᵒ d) (𝕃ᵒ c)); [ apply wf_exp_eq_maxl_comm; mauto 3 |].
    apply wf_exp_eq_maxl_llit_ole; [ assumption | apply olt_ole; exact Hlt ].
Qed.

(** The two operations on the fold: the successor raises every offset and the
    constant, and the join concatenates the atoms and joins the constants.
    These are the equations soundness needs of a level operation. *)
Lemma lvl_tm_suc : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ succl (lvl_tm c xs) ≈ lvl_tm (osuc c) (la_suc xs) : Level.
Proof.
  intros Γ c xs HΓ; revert c; induction xs as [| k a r IH]; cbn; intros c Hxs;
    [ unfold lvl_tm; cbn; destruct c; apply wf_exp_eq_sym, wf_exp_eq_llit_succl; assumption |].
  destruct Hxs as [Ha Hr].
  assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level) by (apply (wf_succl_n k); exact Ha).
  assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c r : Level) by (apply lvl_tm_wf; assumption).
  unfold lvl_tm in *; cbn in *.
  transitivity (maxl (succl (succl_n k a)) (succl (lvl_tm_from (𝕃ᵒ c) r)));
    [ apply wf_exp_eq_succl_maxl; assumption |].
  apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; exact Hr ].
Qed.

Lemma lvl_tm_max : forall {Γ} c xs d ys,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    la_wf Γ ys ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (lvl_tm c xs) (lvl_tm d ys) ≈ lvl_tm (omax c d) (la_app xs ys) : Level.
Proof.
  intros Γ c xs d ys HΓ; revert c; induction xs as [| k a r IH]; cbn; intros c Hxs Hys.
  - (** No atom on the left: the two constants join in front of the right. *)
    assert (Hc : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c : Level) by mauto 3.
    assert (Hd : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ d : Level) by mauto 3.
    assert (HT0 : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) ys : Level) by (apply lvl_tm_from_wf; mauto 3).
    unfold lvl_tm; cbn.
    transitivity (maxl (𝕃ᵒ c) (maxl (𝕃ᵒ d) (lvl_tm_from (𝕃@0) ys)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | apply lvl_tm_from_out; [ exact Hd | exact Hys ] ] |].
    transitivity (maxl (maxl (𝕃ᵒ c) (𝕃ᵒ d)) (lvl_tm_from (𝕃@0) ys));
      [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; assumption |].
    transitivity (maxl (𝕃ᵒ (omax c d)) (lvl_tm_from (𝕃@0) ys));
      [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_maxl_llit; assumption | mauto 3 ] |].
    apply wf_exp_eq_sym, lvl_tm_from_out; [ mauto 3 | exact Hys ].
  - destruct Hxs as [Ha Hr].
    assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level) by (apply (wf_succl_n k); exact Ha).
    assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c r : Level) by (apply lvl_tm_wf; assumption).
    assert (Hyt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm d ys : Level) by (apply lvl_tm_wf; assumption).
    unfold lvl_tm in *; cbn in *.
    transitivity (maxl (succl_n k a) (maxl (lvl_tm_from (𝕃ᵒ c) r) (lvl_tm_from (𝕃ᵒ d) ys)));
      [ apply wf_exp_eq_maxl_assoc; assumption |].
    apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; assumption ].
Qed.

(** ** Sorting, Merging and Dropping *)

Lemma lvl_tm_ins : forall {Γ} c k (a : ne) ys,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (a : exp) : Level ->
    la_wf Γ ys ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c (la_ins k a ys) ≈ maxl (succl_n k a) (lvl_tm c ys) : Level.
Proof.
  intros Γ c k a ys HΓ Ha; induction ys as [| k' b r IH]; cbn; intros Hys;
    [ unfold lvl_tm; cbn; apply wf_exp_eq_refl, wf_maxl; mauto 3 |].
  destruct Hys as [Hb Hr].
  assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level) by (apply (wf_succl_n k); exact Ha).
  assert (Hk'b : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k' b : Level) by (apply (wf_succl_n k'); exact Hb).
  assert (Hc : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ c : Level) by mauto 3.
  assert (Hrt : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃ᵒ c) r : Level) by (apply lvl_tm_from_wf; assumption).
  destruct (ne_cmp a b) eqn:E; cbn.
  - (** The same atom: the two offsets merge at the larger one. *)
    apply ne_cmp_eq in E; subst b.
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
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c (la_sort xs) ≈ lvl_tm c xs : Level.
Proof.
  intros Γ c xs HΓ; induction xs as [| k a r IH]; cbn; intros Hxs; [ mauto 3 |].
  destruct Hxs as [Ha Hr].
  transitivity (maxl (succl_n k a) (lvl_tm c (la_sort r)));
    [ apply lvl_tm_ins; [ assumption | assumption | apply la_wf_sort; assumption ] |].
  unfold lvl_tm; cbn.
  apply wf_exp_eq_maxl_cong; [ mauto 3 | apply IH; assumption ].
Qed.

(** The constant is dropped when some atom's offset dominates it; such a
    constant is finite. *)
Lemma lvl_tm_drop_fin : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    c <= la_maxoff xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm (ofin c) xs ≈ lvl_tm oz xs : Level.
Proof.
  intros Γ c xs HΓ; induction xs as [| k a r IH]; cbn; intros Hxs Hle.
  - (** No atom: the constant is [0] already. *)
    assert (c = 0) as -> by lia; apply wf_exp_eq_refl; mauto 3.
  - destruct Hxs as [Ha Hr].
    assert (Hka : Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k a : Level) by (apply (wf_succl_n k); exact Ha).
    assert (Hc : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@c : Level) by mauto 3.
    assert (Hz : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@0 : Level) by mauto 3.
    assert (HT0 : Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm_from (𝕃@0) r : Level) by (apply lvl_tm_from_wf; assumption).
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
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c xs ≈ lvl_tm oz xs : Level.
Proof.
  intros Γ [a c] xs HΓ Hxs Hle.
  assert (a = 0) as -> by (unfold ole in Hle; cbn in Hle; lia).
  apply lvl_tm_drop_fin; [ assumption | assumption | unfold ole in Hle; cbn in Hle; lia ].
Qed.

(** ** The Canonical Form

    The equation soundness needs: a level is equal to its canonical form. *)
Theorem lvl_tm_canon : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_tm c xs ≈ lvl_tm (fst (lvl_canon (c, xs))) (snd (lvl_canon (c, xs))) : Level.
Proof.
  intros Γ c xs HΓ Hxs; unfold lvl_canon; cbn.
  destruct (o2_dominated c (la_maxoff (la_sort xs))) eqn:Hle; cbn;
    [ apply o2_dominated_spec in Hle |].
  - transitivity (lvl_tm c (la_sort xs));
      [ apply wf_exp_eq_sym, lvl_tm_sort; assumption |].
    apply lvl_tm_drop; [ assumption | apply la_wf_sort; assumption | assumption ].
  - apply wf_exp_eq_sym, lvl_tm_sort; assumption.
Qed.

Theorem lvl_exp_of_canon : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs)
             ≈ nf_to_exp (nf_lvl_of (lvl_canon (c, xs))) : Level.
Proof.
  intros Γ c xs HΓ Hxs.
  assert (Hcanon : la_wf Γ (snd (lvl_canon (c, xs))))
    by (unfold lvl_canon; cbn; apply la_wf_sort; assumption).
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
Lemma wf_succl_n_inversion : forall {Γ M} k,
    Θ ⍮ Ξ ⍮ Γ ⊢ succl_n k M : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level.
Proof.
  intros Γ M k; revert M; induction k; cbn; intros M H; [ exact H |].
  apply wf_succl_inversion in H as [H _]; apply IHk; exact H.
Qed.

Lemma lvl_fold_hd_wf : forall {Γ} xs hd,
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold hd (la_to_list xs) : Level ->
    Θ ⍮ Ξ ⍮ Γ ⊢ hd : Level.
Proof.
  intros Γ xs; induction xs as [| k a r IH]; cbn; intros hd H; [ exact H |].
  apply IH in H; apply wf_maxl_inversion in H as (? & _ & _); assumption.
Qed.

Lemma lvl_fold_la_wf : forall {Γ} xs hd,
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_fold hd (la_to_list xs) : Level ->
    la_wf Γ xs.
Proof.
  intros Γ xs; induction xs as [| k a r IH]; cbn; intros hd H; [ exact I |].
  split; [| eapply IH; exact H ].
  apply lvl_fold_hd_wf in H; apply wf_maxl_inversion in H as (_ & H & _).
  apply (wf_succl_n_inversion k); exact H.
Qed.

Lemma lvl_exp_of_la_wf : forall {Γ} c xs,
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) : Level ->
    la_wf Γ xs.
Proof.
  intros Γ c xs H; destruct xs as [| k a r]; cbn in *; [ exact I |].
  destruct c as [[| c1] [| c2]];
    (split; [| eapply lvl_fold_la_wf; exact H ]);
    apply lvl_fold_hd_wf in H;
    try (apply wf_maxl_inversion in H as (_ & H & _));
    apply (wf_succl_n_inversion k); exact H.
Qed.

(** ** The Order on Canonical Levels, Syntactically

    Subtyping between two small universes asks for [maxl t t' ≈ t'], which for
    two canonical levels is exactly the decidable order [lvl_le]: the
    canonicalisation equations turn the join into the canonical form of the
    join, and [lvl_le] says that is the canonical form of the right-hand
    side. *)
Lemma lvl_exp_of_wf : forall {Γ} c xs,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) : Level.
Proof.
  intros Γ c xs HΓ Hxs.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ lvl_exp_of c (la_to_list xs) ≈ lvl_tm c xs : Level)
    by (apply lvl_exp_of_tm; assumption).
  gen_presups; assumption.
Qed.

Hint Resolve lvl_exp_of_wf : mctt.

Lemma lvl_exp_of_le : forall {Γ} c xs d ys,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    la_wf Γ xs ->
    la_wf Γ ys ->
    lvl_le (c, xs) (d, ys) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (lvl_exp_of c (la_to_list xs)) (lvl_exp_of d (la_to_list ys))
             ≈ lvl_exp_of d (la_to_list ys) : Level.
Proof.
  intros Γ c xs d ys HΓ Hxs Hys Hle.
  transitivity (lvl_tm (fst (lvl_canon (lvl_max (c, xs) (d, ys))))
                       (snd (lvl_canon (lvl_max (c, xs) (d, ys))))).
  - transitivity (maxl (lvl_tm c xs) (lvl_tm d ys));
      [ apply wf_exp_eq_maxl_cong; apply lvl_exp_of_tm; assumption |].
    transitivity (lvl_tm (omax c d) (la_app xs ys));
      [ apply lvl_tm_max; assumption |].
    apply lvl_tm_canon; [ assumption | cbn; apply la_wf_app; assumption ].
  - unfold lvl_le in Hle; rewrite Hle.
    apply wf_exp_eq_sym.
    transitivity (lvl_tm d ys); [ apply lvl_exp_of_tm; assumption |].
    apply lvl_tm_canon; assumption.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve wf_succl_n wf_exp_eq_succl_n_cong : mctt.
#[export]
Hint Resolve lvl_exp_of_wf : mctt.
