(** * Builtin Bindings

    [builtin natural ≔ X] binds the inductive type [X] as the natural
    numbers.  A numeral ([a_nlit]) then stands for the chain of [X]'s
    constructors, wherever the binding is visible: expansion
    ([Core.Syntactic.Imports]) replaces it.

    The binding is filed as a member of the unit that makes it, under the
    name [#natural], which no source can write: a transparent definition
    whose body is the type former, [a_ind p].  So it is part of the unit,
    and visible exactly where the unit is filed, which is where the unit is
    imported, directly or not ([gds_natbinds]); in the unit itself, it is a
    member of the unit's frame, the bottom of the stack ([gs_natbinds]).
    The command ([rc_builtin]) checks the shape of [X]: no parameter, one
    constructor without arguments and one with a single recursive argument
    ([nat_shape]). *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Inductives.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** The name a binding of the natural numbers is filed under. *)
Definition nat_name : string := "#natural".

(** The kind of the binding, as the command names it. *)
Definition nat_kind : string := "natural".

(** The shape of the natural numbers: no parameter, and two constructors,
    one without arguments, [z], and one with a single recursive argument,
    [s], in either order. *)
Definition nat_shape (D : ind_decl) : option (string * string) :=
  match ind_nu D, ind_params D, ind_cons D with
  | 0, nil, (c1, nil) :: (c2, ca_rec (pt_self 0 nil) :: nil) :: nil => Some (c1, c2)
  | 0, nil, (c2, ca_rec (pt_self 0 nil) :: nil) :: (c1, nil) :: nil => Some (c1, c2)
  | _, _, _ => None
  end.

(** The binding filed in a body: its last [#natural] definition. *)
Fixpoint gm_natbind (Φ : gmod) : option qname :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' x E =>
      if String.eqb x nat_name then
        match E with
        | ge_def _ _ _ (Some (a_ind p)) => Some p
        | _ => gm_natbind Φ'
        end
      else gm_natbind Φ'
  | gm_open Φ' _ _ => gm_natbind Φ'
  end.

Definition gu_natbind (U : gunit) : option qname :=
  match gu_def U with
  | md_body Φ => gm_natbind Φ
  | md_alias _ => None
  end.

Definition opt_list {A} (o : option A) : list A :=
  match o with
  | Some a => a :: nil
  | None => nil
  end.

(** The bindings of the filed units, each unit as it is filed. *)
Definition gds_natbinds (Θ : gdeps) : list qname :=
  flat_map (fun e => match gds_lookup Θ (fst e) with
                     | Some U => opt_list (gu_natbind U)
                     | None => nil
                     end) Θ.

(** The binding of the unit being run: a member of its frame, the bottom
    of the stack. *)
Definition gs_natbinds (Ξ : gstack) : list qname :=
  match List.rev Ξ with
  | (_, U) :: _ => opt_list (gu_natbind U)
  | nil => nil
  end.

(** All the bindings visible. *)
Definition nat_binds (Θ : gdeps) (Ξ : gstack) : list qname := gs_natbinds Ξ ++ gds_natbinds Θ.

(** What a numeral stands for: no binding, one binding (all the visible
    ones agree), with the constructors of its shape, or bindings that
    disagree. *)
Inductive nbind : Set :=
| nb_none : nbind
| nb_one : qname -> string -> string -> nbind
| nb_many : nbind.

Definition qname_beq (p r1 : qname) : bool := path_beq (q_unit p) (q_unit r1) && path_beq (q_chain p) (q_chain r1).

Lemma qname_beq_true : forall p r1, qname_beq p r1 = true -> p = r1.
Proof.
  intros [fp cp] [fq cq] H; unfold qname_beq in H; cbn in H; apply andb_prop in H as [H1 H2].
  apply path_beq_true in H1, H2; subst; reflexivity.
Qed.

Lemma qname_beq_refl : forall p, qname_beq p p = true.
Proof. intros [fp cp]; unfold qname_beq; cbn; rewrite !path_beq_refl; reflexivity. Qed.

Definition nb_classify (Θ : gdeps) (Ξ : gstack) (l : list qname) : nbind :=
  match l with
  | nil => nb_none
  | p :: l' =>
      if forallb (qname_beq p) l' then
        match ind_lookup Θ Ξ p with
        | Some D => match nat_shape D with
                    | Some (z, s) => nb_one p z s
                    | None => nb_many
                    end
        | None => nb_many
        end
      else nb_many
  end.

Definition nat_binding (Θ : gdeps) (Ξ : gstack) : nbind := nb_classify Θ Ξ (nat_binds Θ Ξ).

(** The numeral [n] as the chain of the constructors [z] and [s] of [p]. *)
Fixpoint nat_chain (p : qname) (z s : string) (n : nat) : exp :=
  match n with
  | 0 => a_con p z
  | S n' => a_app (a_con p s) (nat_chain p z s n')
  end.

(** ** The Bindings Depend on the Filed Units Only *)

Lemma gds_natbinds_in : forall Θ r1,
    In r1 (gds_natbinds Θ) <-> exists fp U, gds_lookup Θ fp = Some U /\ gu_natbind U = Some r1.
Proof.
  intros Θ r1; unfold gds_natbinds; rewrite in_flat_map; split.
  - intros ([fp V] & _ & Hq); cbn in Hq.
    destruct (gds_lookup Θ fp) as [U |] eqn:E; [| destruct Hq ].
    destruct (gu_natbind U) eqn:E'; cbn in Hq; [| destruct Hq ].
    destruct Hq as [<- | []]; eauto.
  - intros (fp & U & HU & Hq).
    exists (fp, U); split; [ apply gds_lookup_in, HU |]; cbn; rewrite HU, Hq; left; reflexivity.
Qed.

Lemma nat_binds_in_equiv : forall Θ Θ' Ξ,
    (forall fp, gds_lookup Θ fp = gds_lookup Θ' fp) ->
    forall r1, In r1 (nat_binds Θ Ξ) <-> In r1 (nat_binds Θ' Ξ).
Proof.
  intros * Heq r1; unfold nat_binds; rewrite !in_app_iff, !gds_natbinds_in.
  split; intros [H | (fp & U & HU & Hq)]; auto; right; exists fp, U; rewrite ?Heq in *; rewrite <- ?Heq in *; auto.
Qed.

(** The classification depends only on which bindings are visible. *)
Lemma nb_classify_in : forall Θ Ξ l l',
    (forall r1, In r1 l <-> In r1 l') -> nb_classify Θ Ξ l = nb_classify Θ Ξ l'.
Proof.
  intros Θ Ξ [| p l] [| p' l'] Hin; cbn; try reflexivity.
  - exfalso; apply (proj2 (Hin p')); left; reflexivity.
  - exfalso; apply (proj1 (Hin p)); left; reflexivity.
  - destruct (forallb (qname_beq p) l) eqn:E; destruct (forallb (qname_beq p') l') eqn:E'.
    + (* all agree on both sides: on the same binding *)
      assert (Hp : p' = p).
      { destruct (proj2 (Hin p') (or_introl eq_refl)) as [-> | Hp']; [ reflexivity |].
        symmetry; apply qname_beq_true; exact (proj1 (forallb_forall _ _) E _ Hp'). }
      subst p'; reflexivity.
    + exfalso; apply Bool.not_true_iff_false in E'; apply E', forallb_forall; intros r1 Hq.
      assert (Hp : In p' (p :: l)) by (apply Hin; left; reflexivity).
      assert (Hq' : In r1 (p :: l)) by (apply Hin; right; exact Hq).
      assert (Hall : forall r, In r (p :: l) -> r = p).
      { intros r [<- | Hr]; [ reflexivity |]; symmetry; apply qname_beq_true; exact (proj1 (forallb_forall _ _) E _ Hr). }
      rewrite (Hall _ Hp), (Hall _ Hq'); apply qname_beq_refl.
    + exfalso; apply Bool.not_true_iff_false in E; apply E, forallb_forall; intros r1 Hq.
      assert (Hp : In p (p' :: l')) by (apply Hin; left; reflexivity).
      assert (Hq' : In r1 (p' :: l')) by (apply Hin; right; exact Hq).
      assert (Hall : forall r, In r (p' :: l') -> r = p').
      { intros r [<- | Hr]; [ reflexivity |]; symmetry; apply qname_beq_true; exact (proj1 (forallb_forall _ _) E' _ Hr). }
      rewrite (Hall _ Hp), (Hall _ Hq'); apply qname_beq_refl.
    + reflexivity.
Qed.

Lemma nb_classify_ext : forall Θ Θ' Ξ l,
    (forall p, ind_lookup Θ Ξ p = ind_lookup Θ' Ξ p) -> nb_classify Θ Ξ l = nb_classify Θ' Ξ l.
Proof. intros * Heq; destruct l as [| p l]; cbn; [ reflexivity |]; rewrite Heq; reflexivity. Qed.
