(** * Builtin Bindings

    [builtin natural ≔ X] binds the inductive type [X] as the natural
    numbers.  The bindings are a record, [builtins], apart from the filed
    units and the stack: no typing judgment reads it.  Each unit runs from
    the empty record; it gains the bindings of its own [builtin] commands
    and the records of the units it imports, merged ([bt_merge]), but never
    those of the unit importing it.  The command semantics threads the
    record of the unit being run, and keeps the record each filed unit ended
    with ([Core.Syntactic.System.Command]).

    Where a binding is made, a numeral ([a_nlit]) stands for the chain of
    the bound type's constructors and the token [ℕ] ([a_ntok]) for its type
    former ([nat_view], [nat_chain]): when a command runs, its literals are
    filled from the binding ([Core.TypedElab.Fill]).  Without a binding a
    literal has no fill.  A literal has no typing, evaluation or readback
    rule. *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Export Inductives.
From Mctt.Core.Syntactic Require Export Members Command.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** The kind of the binding, as the command names it. *)
Definition nat_kind : string := "natural".

(** The shape of the natural numbers: a group of one declared member and
    no view, no parameter, and two constructors, one without arguments,
    [z], and one with a single recursive argument, [s], in either order. *)
Definition nat_cons_shape (cs : list (string * list carg)) : option (string * string) :=
  match cs with
  | (c1, nil) :: (c2, ca_rec (pt_self 0 nil) :: nil) :: nil => Some (c1, c2)
  | (c2, ca_rec (pt_self 0 nil) :: nil) :: (c1, nil) :: nil => Some (c1, c2)
  | _ => None
  end.

(** The names of the zero and successor constructors of a group of the
    shape of the natural numbers, if [D] is one. *)
Definition nat_shape (D : ind_decl) : option (string * string) :=
  match ind_uparams D, ind_members D with
  | nil, mk_imember (mh_decl _) nil cs :: nil => nat_cons_shape cs
  | _, _ => None
  end.

(** The sort the natural numbers are declared in: [Type@0]. *)
Definition nat_sort : typ := a_univ (a_llit (0, 0)).

(** ** The Configuration *)

(** The builtin bindings of a run: the path of the type bound as the
    natural numbers, if one is. *)
Record builtins : Set := mk_builtins { bt_nat : option qname }.

Definition bt_empty : builtins := mk_builtins None.

(** A binding is well formed where its type is an inductive type of the
    shape of the natural numbers, in [Type@0], filed or on the stack.  This
    is a condition on its own, not part of typing. *)
#[warnings="-cannot-define-projection"]
Record nat_binding_ok (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop := mk_nat_binding_ok
  { nbo_decl : ind_decl
  ; nbo_zero : string
  ; nbo_succ : string
  ; nbo_lookup : ind_lookup Θ Ξ p = Some nbo_decl
  ; nbo_shape : nat_shape nbo_decl = Some (nbo_zero, nbo_succ)
  ; nbo_sort : ind_sort nbo_decl = nat_sort }.

Definition builtins_wf (Θ : gdeps) (Ξ : gstack) (B : builtins) : Prop :=
  forall p, bt_nat B = Some p -> nat_binding_ok Θ Ξ p.

(** What a literal stands for at a state: the bound type and its
    constructors, the one without arguments first. *)
Definition nat_view (Θ : gdeps) (Ξ : gstack) (B : builtins) : option (qname * string * string) :=
  match bt_nat B with
  | Some p =>
      match ind_lookup Θ Ξ p with
      | Some D =>
          match nat_shape D with
          | Some (z, s) => Some (p, z, s)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

(** The numeral [n] as the chain of the constructors [z] and [s] of [p]. *)
Fixpoint nat_chain (p : qname) (z s : string) (n : nat) : exp :=
  match n with
  | 0 => a_con p 0 z
  | S n' => a_app (a_con p 0 s) (nat_chain p z s n')
  end.

(** Why a literal has no fill: a numeral, or the token [ℕ], with no
    natural-number type bound. *)
Inductive lerr : Set :=
(** The numeral [n] *)
| le_num : nat -> lerr
(** The token [ℕ] *)
| le_tok : lerr.

(** ** Merging

    Two records merge field by field: a field bound on one side only keeps
    that binding, and one bound on both sides must be bound to the same
    type.  A unit merges the record of each unit it imports into its own,
    and a [builtin] command merges the binding it makes. *)
Definition bt_merge (B1 B2 : builtins) : option builtins :=
  match bt_nat B1, bt_nat B2 with
  | None, o | o, None => Some (mk_builtins o)
  | Some p1, Some p2 => if qname_eq_dec p1 p2 then Some (mk_builtins (Some p1)) else None
  end.

Lemma bt_eta : forall B, mk_builtins (bt_nat B) = B.
Proof. intros []; reflexivity. Qed.

Lemma bt_merge_empty_l : forall B, bt_merge bt_empty B = Some B.
Proof. intros [o]; reflexivity. Qed.

Lemma bt_merge_empty_r : forall B, bt_merge B bt_empty = Some B.
Proof. intros [[p |]]; reflexivity. Qed.

Lemma bt_merge_comm : forall B1 B2, bt_merge B1 B2 = bt_merge B2 B1.
Proof.
  intros [[p1 |]] [[p2 |]]; unfold bt_merge; cbn; try reflexivity.
  destruct (qname_eq_dec p1 p2) as [<- | Hne];
    [ destruct (qname_eq_dec p1 p1); congruence | destruct (qname_eq_dec p2 p1); congruence ].
Qed.

Lemma bt_merge_idem : forall B, bt_merge B B = Some B.
Proof. intros [[p |]]; unfold bt_merge; cbn; [ destruct (qname_eq_dec p p); [ reflexivity | contradiction ] | reflexivity ]. Qed.

(** Associativity, where failure is a value of its own. *)
Lemma bt_merge_assoc : forall B1 B2 B3,
    match bt_merge B1 B2 with Some B12 => bt_merge B12 B3 | None => None end =
    match bt_merge B2 B3 with Some B23 => bt_merge B1 B23 | None => None end.
Proof.
  intros [[p1 |]] [[p2 |]] [[p3 |]]; unfold bt_merge; cbn;
    repeat (match goal with |- context [qname_eq_dec ?a ?b] => destruct (qname_eq_dec a b); try subst end; cbn);
    congruence.
Qed.

(** What a merge has: the bindings of both sides. *)
Lemma bt_merge_inv : forall B1 B2 B p,
    bt_merge B1 B2 = Some B -> bt_nat B = Some p -> bt_nat B1 = Some p \/ bt_nat B2 = Some p.
Proof.
  intros [[p1 |]] [[p2 |]] B p H Hp; unfold bt_merge in H; cbn in H;
    try (destruct (qname_eq_dec p1 p2)); try discriminate; injection H as <-; cbn in Hp; auto.
Qed.

(** A merge of well-formed records is well formed. *)
Lemma bt_merge_wf : forall Θ Ξ B1 B2 B,
    builtins_wf Θ Ξ B1 -> builtins_wf Θ Ξ B2 -> bt_merge B1 B2 = Some B -> builtins_wf Θ Ξ B.
Proof. intros * H1 H2 Hm p Hp; destruct (bt_merge_inv _ _ _ _ Hm Hp) as [E | E]; [ exact (H1 _ E) | exact (H2 _ E) ]. Qed.

(** The binding a [builtin natural ≔ X] command makes, from the bindings
    before it: [X] names the inductive type [p], with the shape of the
    natural numbers, in [Type@0]; it merges the binding of [p] alone. *)
Definition bt_bind_nat (B : builtins) (p : qname) : option builtins := bt_merge B (mk_builtins (Some p)).

(** ** Bindings Only Grow

    A record only gains bindings ([bt_merge_le]): those of an earlier point
    of a run are below those of a later one ([bt_le]). *)

Definition bt_le (B1 B2 : builtins) : Prop := bt_nat B1 = None \/ B1 = B2.

Lemma bt_le_refl : forall B, bt_le B B.
Proof. right; reflexivity. Qed.

Lemma bt_le_trans : forall B1 B2 B3, bt_le B1 B2 -> bt_le B2 B3 -> bt_le B1 B3.
Proof. intros * [H | <-] H2; [ left; exact H | exact H2 ]. Qed.

Lemma bt_merge_le : forall B1 B2 B, bt_merge B1 B2 = Some B -> bt_le B1 B /\ bt_le B2 B.
Proof.
  intros [[p1 |]] [[p2 |]] B H; unfold bt_merge in H; cbn in H;
    try (destruct (qname_eq_dec p1 p2) as [<- |]); try discriminate; injection H as <-;
    split; solve [ left; reflexivity | right; reflexivity ].
Qed.

Lemma bt_bind_nat_le : forall B p B', bt_bind_nat B p = Some B' -> bt_le B B'.
Proof. intros * H; exact (proj1 (bt_merge_le _ _ _ H)). Qed.

(** Whether a sort is [nat_sort]. *)
Definition is_nat_sort (A : exp) : bool :=
  match A with
  | a_univ (a_llit (0, 0)) => true
  | _ => false
  end.

Lemma is_nat_sort_spec : forall A, is_nat_sort A = true <-> A = nat_sort.
Proof.
  intros A; split; [| intros ->; reflexivity ].
  destruct A; try discriminate; cbn.
  destruct A; try discriminate.
  destruct o as [[| a] [| b]]; try discriminate; reflexivity.
Qed.
