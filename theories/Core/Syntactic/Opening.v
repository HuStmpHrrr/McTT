(** * The Algebra of Path Opening

    Opening touches only the paths inside [a_glob], and weakening and
    substitution touch only variables, so the two commute outright.  What is
    specific to opening is how the three openings resolution uses compose: a
    shift by [n] frames, reading out through a nested module [p_rel 0 [x]], and
    reading out of a filed unit [p_abs fp []].  Everything here is stated in the
    notation, so that it rewrites the goals [cbn] leaves. *)

From Stdlib Require Import Lia List Morphisms PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

(** ** Paths

    Each equation is a case split on the qualifier and a little arithmetic on
    truncated subtraction. *)

Ltac path_open_solve :=
  intros; repeat match goal with r : path |- _ => destruct r as [[? | ?] ?] end;
  cbn; rewrite ?Nat.sub_0_r, ?Nat.add_0_r;
  try reflexivity; try (do 2 f_equal; lia);
  try (replace (1 - S _) with 0 by lia; cbn; do 2 f_equal; lia).

Lemma path_open_here : forall r : path, r[p_rel 0 nil]p = r.
Proof. path_open_solve. Qed.

(** Pushing a frame after shifting by [n] shifts by [1 + n]. *)
Lemma path_open_shift_shift : forall n (r : path), r[p_rel n nil]p[p_rel 1 nil]p = r[p_rel (S n) nil]p.
Proof. path_open_solve. Qed.

(** Reading out through a nested module undoes pushing a frame. *)
Lemma path_open_shift_in : forall x (r : path), r[p_rel 1 nil]p[p_rel 0 (x :: nil)]p = r.
Proof. path_open_solve. Qed.

Lemma path_open_shift_succ_in : forall n x (r : path),
    r[p_rel (S n) nil]p[p_rel 0 (x :: nil)]p = r[p_rel n nil]p.
Proof. path_open_solve. Qed.

(** What comes out of a filed unit is absolute, so no further opening moves it. *)
Lemma path_open_abs_absorb : forall fp t (r : path), r[p_abs fp nil]p[t]p = r[p_abs fp nil]p.
Proof. path_open_solve. Qed.

(** ** Lifting Path Equations *)

Lemma exp_open_ext_comp : forall a b c,
    (forall r : path, r[a]p[b]p = r[c]p) ->
    forall M : exp, M[a]p[b]p = M[c]p.
Proof.
  intros a b c H M; induction M; cbn; congruence.
Qed.

Lemma exp_open_ext_id : forall a,
    (forall r : path, r[a]p = r) ->
    forall M : exp, M[a]p = M.
Proof.
  intros a H M; induction M; cbn; congruence.
Qed.

Lemma list_open_ext_comp : forall {A : Type} {HA : POpen A} a b c,
    (forall X : A, X[a]p[b]p = X[c]p) ->
    forall l : list A, l[a]p[b]p = l[c]p.
Proof.
  intros * H' l; induction l; cbn in *; congruence.
Qed.

Lemma list_open_ext_id : forall {A : Type} {HA : POpen A} a,
    (forall X : A, X[a]p = X) ->
    forall l : list A, l[a]p = l.
Proof.
  intros * H' l; induction l; cbn in *; congruence.
Qed.

Lemma option_open_ext_comp : forall {A : Type} {HA : POpen A} a b c,
    (forall X : A, X[a]p[b]p = X[c]p) ->
    forall o : option A, o[a]p[b]p = o[c]p.
Proof.
  intros * H' [|]; cbn; congruence.
Qed.

Lemma option_open_ext_id : forall {A : Type} {HA : POpen A} a,
    (forall X : A, X[a]p = X) ->
    forall o : option A, o[a]p = o.
Proof.
  intros * H' [|]; cbn; congruence.
Qed.

(** ** Containers *)

Lemma list_open_app : forall {A : Type} {HA : POpen A} a (l l' : list A),
    (l ++ l')[a]p = l[a]p ++ l'[a]p.
Proof.
  intros; apply List.map_app.
Qed.

Lemma list_open_length : forall {A : Type} {HA : POpen A} a (l : list A), length l[a]p = length l.
Proof.
  intros; apply List.length_map.
Qed.

Lemma list_open_nil : forall {A : Type} {HA : POpen A} a, (@nil A)[a]p = nil.
Proof. reflexivity. Qed.

Lemma list_open_cons : forall {A : Type} {HA : POpen A} a (X : A) l, (X :: l)[a]p = X[a]p :: l[a]p.
Proof. reflexivity. Qed.

(** ** Commuting with Weakening and Substitution *)

Lemma exp_open_wk : forall a M φ, M[φ]w[a]p = M[a]p[φ]w.
Proof.
  intros a M; induction M; intros; cbn; congruence.
Qed.

(** A substitution opened pointwise. *)
Definition sb_open (a : path) (σ : sub) : sub := fun x => (σ x)[a]p.

Lemma sb_open_q : forall a σ, sb_eq (sb_open a (q σ)) (q (sb_open a σ)).
Proof.
  intros a σ [|x]; unfold sb_open; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  apply exp_open_wk.
Qed.

Lemma exp_open_sub : forall a M σ, M[σ][a]p = M[a]p[sb_open a σ].
Proof.
  intros a M; induction M; intros; cbn; rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4;
    try reflexivity.
  (* the binders: opening and lifting commute, once or twice *)
  all: f_equal; apply exp_sub_sb_eq;
    first [ apply sb_open_q
          | etransitivity; [ apply sb_open_q | apply sb_q_cong, sb_open_q ] ].
Qed.

Lemma sb_open_id : forall a, sb_eq (sb_open a Id) Id.
Proof. intros a x; reflexivity. Qed.

Lemma sb_open_extend : forall a σ M, sb_eq (sb_open a (σ,,M)) (sb_open a σ ,, M[a]p).
Proof. intros a σ M [|x]; reflexivity. Qed.

Lemma sb_open_of_wk : forall a φ, sb_eq (sb_open a (ι φ)) (ι φ).
Proof. intros a φ x; reflexivity. Qed.

Lemma sb_open_shift : forall a, sb_eq (sb_open a Wk) Wk.
Proof. intros a x; reflexivity. Qed.

Lemma sb_open_compose : forall a σ τ, sb_eq (sb_open a (σ ⨟ τ)) (sb_open a σ ⨟ sb_open a τ).
Proof. intros a σ τ x; unfold sb_open, sb_compose; apply exp_open_sub. Qed.

(** The instances the rules use, in the form they appear. *)

Lemma exp_open_sub1 : forall a A M, A[Id,,M][a]p = A[a]p[Id,,M[a]p].
Proof. intros; rewrite exp_open_sub; apply exp_sub_sb_eq; intros [|x]; reflexivity. Qed.

Lemma exp_open_sub2 : forall a A M N, A[Id,,M,,N][a]p = A[a]p[Id,,M[a]p,,N[a]p].
Proof. intros; rewrite exp_open_sub; apply exp_sub_sb_eq; intros [|[|x]]; reflexivity. Qed.

Lemma exp_open_sub_succ : forall a A, A[Wk⨟Wk,,succ #1][a]p = A[a]p[Wk⨟Wk,,succ #1].
Proof. intros; rewrite exp_open_sub; apply exp_sub_sb_eq; intros [|x]; reflexivity. Qed.

(** ** Telescopes *)

Lemma ctx_pi_open : forall a Δ A, (ctx_pi Δ A)[a]p = ctx_pi Δ[a]p A[a]p.
Proof.
  intros a Δ; induction Δ; intros; cbn; [ reflexivity |].
  rewrite IHΔ; reflexivity.
Qed.

Lemma ctx_fn_open : forall a Δ M, (ctx_fn Δ M)[a]p = ctx_fn Δ[a]p M[a]p.
Proof.
  intros a Δ; induction Δ; intros; cbn; [ reflexivity |].
  rewrite IHΔ; reflexivity.
Qed.

(** Generalizing over [Δ ++ Δ'] is generalizing over the inner [Δ] first. *)
Lemma ctx_pi_app : forall Δ Δ' A, ctx_pi (Δ ++ Δ') A = ctx_pi Δ' (ctx_pi Δ A).
Proof.
  induction Δ; intros; cbn; [ reflexivity |]. apply IHΔ.
Qed.

Lemma ctx_fn_app : forall Δ Δ' M, ctx_fn (Δ ++ Δ') M = ctx_fn Δ' (ctx_fn Δ M).
Proof.
  induction Δ; intros; cbn; [ reflexivity |]. apply IHΔ.
Qed.

Lemma ctx_lookup_open : forall a Γ x A, Γ ∋ #x : A -> Γ[a]p ∋ #x : A[a]p.
Proof.
  intros a Γ x A; induction 1; cbn; rewrite exp_open_wk; constructor; assumption.
Qed.

Lemma ctx_lookup_open_inv : forall a Γ x A,
    Γ[a]p ∋ #x : A -> exists A0, Γ ∋ #x : A0 /\ A = A0[a]p.
Proof.
  intros a Γ; induction Γ as [| B Γ IH]; intros * H; cbn in H; inversion H; subst.
  - eexists; split; [ constructor | symmetry; apply exp_open_wk ].
  - destruct (IH _ _ ltac:(eassumption)) as [A1 [HA ->]].
    eexists; split; [ constructor; eassumption | symmetry; apply exp_open_wk ].
Qed.

#[export]
Hint Resolve ctx_lookup_open : mctt.

(** ** The Stack's Telescope *)

Lemma gs_tele_nil : gs_tele nil = nil.
Proof. reflexivity. Qed.

Lemma gs_tele_cons : forall U Ξ,
    gs_tele (U :: Ξ) = (gu_params U ++ gs_tele Ξ)[p_rel 1 nil]p.
Proof. reflexivity. Qed.

(** Reading an already relative path out of a filed unit is reading it out. *)
Lemma path_open_rel_abs : forall n fp (r : path), r[p_rel n nil]p[p_abs fp nil]p = r[p_abs fp nil]p.
Proof. path_open_solve. Qed.

Lemma path_open_in_rel : forall x ip, (p_rel 0 ip)[p_rel 0 (x :: nil)]p = p_rel 0 (x :: ip).
Proof. reflexivity. Qed.

Lemma path_open_in_succ : forall x m ip, (p_rel (S m) ip)[p_rel 0 (x :: nil)]p = p_rel m ip.
Proof. intros; cbn; rewrite Nat.sub_0_r; reflexivity. Qed.

Lemma path_open_shift_rel : forall n ip, (p_rel n ip)[p_rel 1 nil]p = p_rel (S n) ip.
Proof. intros; cbn; rewrite Nat.sub_0_r; reflexivity. Qed.

Lemma exp_open_ext_cancel : forall a b,
    (forall r : path, r[a]p[b]p = r) ->
    forall M : exp, M[a]p[b]p = M.
Proof.
  intros a b H M; induction M; cbn; congruence.
Qed.

Lemma list_open_ext_cancel : forall {A : Type} {HA : POpen A} a b,
    (forall X : A, X[a]p[b]p = X) ->
    forall l : list A, l[a]p[b]p = l.
Proof.
  intros * H' l; induction l; cbn in *; congruence.
Qed.

Lemma option_open_ext_cancel : forall {A : Type} {HA : POpen A} a b,
    (forall X : A, X[a]p[b]p = X) ->
    forall o : option A, o[a]p[b]p = o.
Proof.
  intros * H' [|]; cbn; congruence.
Qed.

(** Rewriting with a path equation in the three carriers resolution hands back:
    [open_comp] takes [r[a]p[b]p = r[c]p] or [r[a]p[b]p = r], [open_id] takes
    [r[a]p = r]. *)
Ltac open_comp_tac H :=
  repeat first [ rewrite (list_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ H))
               | rewrite (exp_open_ext_comp _ _ _ H)
               | rewrite (option_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ H))
               | rewrite (list_open_ext_cancel _ _ (exp_open_ext_cancel _ _ H))
               | rewrite (exp_open_ext_cancel _ _ H)
               | rewrite (option_open_ext_cancel _ _ (exp_open_ext_cancel _ _ H)) ].

Ltac open_comp_in_tac H H' :=
  repeat first [ rewrite (list_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ H)) in H'
               | rewrite (exp_open_ext_comp _ _ _ H) in H'
               | rewrite (option_open_ext_comp _ _ _ (exp_open_ext_comp _ _ _ H)) in H'
               | rewrite (list_open_ext_cancel _ _ (exp_open_ext_cancel _ _ H)) in H'
               | rewrite (exp_open_ext_cancel _ _ H) in H'
               | rewrite (option_open_ext_cancel _ _ (exp_open_ext_cancel _ _ H)) in H' ].

Ltac open_id_tac H :=
  repeat first [ rewrite (list_open_ext_id _ (exp_open_ext_id _ H))
               | rewrite (exp_open_ext_id _ H)
               | rewrite (option_open_ext_id _ (exp_open_ext_id _ H)) ].

Ltac open_id_in_tac H H' :=
  repeat first [ rewrite (list_open_ext_id _ (exp_open_ext_id _ H)) in H'
               | rewrite (exp_open_ext_id _ H) in H'
               | rewrite (option_open_ext_id _ (exp_open_ext_id _ H)) in H' ].

Tactic Notation "open_comp" constr(H) := open_comp_tac H.
Tactic Notation "open_comp" constr(H) "in" hyp(H') := open_comp_in_tac H H'.
Tactic Notation "open_id" constr(H) := open_id_tac H.
Tactic Notation "open_id" constr(H) "in" hyp(H') := open_id_in_tac H H'.
