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
    former: when a command runs, its literals are generated from the
    binding ([cmd_lits]).  Without a binding a literal is an error.  A
    literal has no typing, evaluation or readback rule. *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Inductives Members Command.
Import Syntax_Notations.
#[local] Open Scope list_scope.

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
Definition builtins_wf (Θ : gdeps) (Ξ : gstack) (B : builtins) : Prop :=
  forall p, bt_nat B = Some p ->
    exists D z s, ind_lookup Θ Ξ p = Some D /\ nat_shape D = Some (z, s) /\ ind_sort D = nat_sort.

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
  | 0 => a_con p z
  | S n' => a_app (a_con p s) (nat_chain p z s n')
  end.

(** ** Literals *)

(** Why the literals of a command cannot be generated: a numeral, or the
    token [ℕ], with no natural-number type bound. *)
Inductive lerr : Set :=
| le_num : nat -> lerr
| le_tok : lerr.

Inductive lres (A : Type) : Type :=
| lok : A -> lres A
| lfail : lerr -> lres A.

Arguments lok {A}.
Arguments lfail {A}.

Definition lbind {A B} (m : lres A) (f : A -> lres B) : lres B :=
  match m with
  | lok a => f a
  | lfail e => lfail e
  end.

#[local] Notation "'let%' x ':=' m 'in' f" := (lbind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Definition lopt {A} (f : A -> lres A) (o : option A) : lres (option A) :=
  match o with
  | Some a => let% a' := f a in lok (Some a')
  | None => lok None
  end.

Fixpoint lmap {A B} (f : A -> lres B) (l : list A) : lres (list B) :=
  match l with
  | nil => lok nil
  | a :: l' => let% b := f a in let% bs := lmap f l' in lok (b :: bs)
  end.

Section Literals.
  (** The bound type and its constructors, if any. *)
  Variable nv : option (qname * string * string).

  Fixpoint exp_lits (M : exp) {struct M} : lres exp :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False | a_var _ | a_ind _ | a_con _ _ => lok M
    | a_ntok =>
        match nv with
        | Some (p, _, _) => lok (a_ind p)
        | None => lfail le_tok
        end
    | a_nlit n =>
        match nv with
        | Some (p, z, s) => lok (nat_chain p z s n)
        | None => lfail (le_num n)
        end
    | a_univ M => let% M' := exp_lits M in lok (a_univ M')
    | a_succl M => let% M' := exp_lits M in lok (a_succl M')
    | a_maxl M N => let% M' := exp_lits M in let% N' := exp_lits N in lok (a_maxl M' N')
    | a_exfalso A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (a_exfalso A' M')
    | a_elim nm A Bs M =>
        let% A' := exp_lits A in
        let% Bs' := (fix brs_lits (Bs : list (String.string * nat * exp)) : lres (list (String.string * nat * exp)) :=
                       match Bs with
                       | nil => lok nil
                       | b :: Bs0 =>
                           let% B' := exp_lits (snd b) in
                           let% Bs0' := brs_lits Bs0 in
                           lok ((fst b, B') :: Bs0')
                       end) Bs in
        let% M' := exp_lits M in
        lok (a_elim nm A' Bs' M')
    | a_pi A B => let% A' := exp_lits A in let% B' := exp_lits B in lok (a_pi A' B')
    | a_fn A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (a_fn A' M')
    | a_app M N => let% M' := exp_lits M in let% N' := exp_lits N in lok (a_app M' N')
    | a_let b B => let% b' := bnd_lits b in let% B' := exp_lits B in lok (a_let b' B')
    | a_mem H x => let% H' := modexp_lits H in lok (a_mem H' x)
    end
  with modexp_lits (H : modexp) {struct H} : lres modexp :=
    match H with
    | me_unit _ | me_var _ => lok H
    | me_mem H y => let% H' := modexp_lits H in lok (me_mem H' y)
    | me_app H N => let% H' := modexp_lits H in let% N' := exp_lits N in lok (me_app H' N')
    | me_lit U => let% U' := gunit_lits U in lok (me_lit U')
    end
  with bnd_lits (b : bnd) {struct b} : lres bnd :=
    match b with
    | b_def oA M => let% oA' := lopt exp_lits oA in let% M' := exp_lits M in lok (b_def oA' M')
    | b_mod U => let% U' := gunit_lits U in lok (b_mod U')
    end
  with gunit_lits (U : gunit) {struct U} : lres gunit :=
    match U with
    | gu_mk Δ D =>
        let% Δ' := (fix tele_lits (Δ : list centry) : lres ctx :=
                      match Δ with
                      | nil => lok nil
                      | e :: Δ0 => let% e' := centry_lits e in let% Δ0' := tele_lits Δ0 in lok (e' :: Δ0')
                      end) Δ in
        let% D' := moddef_lits D in
        lok (gu_mk Δ' D')
    end
  with moddef_lits (D : moddef) {struct D} : lres moddef :=
    match D with
    | md_body sm Φ => let% Φ' := gmod_lits Φ in lok (md_body sm Φ')
    | md_alias E => let% E' := modexp_lits E in lok (md_alias E')
    end
  with gmod_lits (Φ : gmod) {struct Φ} : lres gmod :=
    match Φ with
    | gm_nil => lok gm_nil
    | gm_ext Φ x E => let% Φ' := gmod_lits Φ in let% E' := gentry_lits E in lok (gm_ext Φ' x E')
    | gm_open Φ H its => let% Φ' := gmod_lits Φ in let% H' := modexp_lits H in lok (gm_open Φ' H' its)
    end
  with gentry_lits (E : gentry) {struct E} : lres gentry :=
    match E with
    | ge_def b pv A B => let% A' := exp_lits A in let% B' := lopt exp_lits B in lok (ge_def b pv A' B')
    | ge_mod pv U => let% U' := gunit_lits U in lok (ge_mod pv U')
    | ge_ind _ _ _ _ | ge_ind_alias _ _ _ _ => lok E
    end
  with centry_lits (e : centry) {struct e} : lres centry :=
    match e with
    | ce_ass A => let% A' := exp_lits A in lok (ce_ass A')
    | ce_def A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (ce_def A' M')
    | ce_mod U => let% U' := gunit_lits U in lok (ce_mod U')
    end.

  Definition tele_lits (Δ : ctx) : lres ctx := lmap centry_lits Δ.

  (** A declaration as written. *)
  Definition decl_lits (R : raw_decl) : lres raw_decl :=
    let% Δ' := tele_lits (rd_params R) in
    let% A' := exp_lits (rd_sort R) in
    let% cs' := lmap (fun cg => let% args := lmap (fun yT => let% T' := exp_lits (snd yT) in lok (fst yT, T')) (snd cg) in
                                lok (fst cg, args)) (rd_cons R) in
    lok (mk_raw (rd_nu R) Δ' A' cs').

  (** A command's own terms: the nested commands of a module get their
      literals when they run. *)
  Definition cmd_lits (c : ccmd) : lres ccmd :=
    match c with
    | cc_def x b pv A M => let% A' := exp_lits A in let% M' := lopt exp_lits M in lok (cc_def x b pv A' M')
    | cc_mod x pv Δ cs => let% Δ' := tele_lits Δ in lok (cc_mod x pv Δ' cs)
    | cc_alias x pv Δ E => let% Δ' := tele_lits Δ in let% E' := modexp_lits E in lok (cc_alias x pv Δ' E')
    | cc_load fp => lok (cc_load fp)
    | cc_open E its => let% E' := modexp_lits E in lok (cc_open E' its)
    | cc_eval M oA => let% M' := exp_lits M in let% oA' := lopt exp_lits oA in lok (cc_eval M' oA')
    | cc_ind x pv D => let% D' := decl_lits D in lok (cc_ind x pv D')
    | cc_builtin k H => let% H' := modexp_lits H in lok (cc_builtin k H')
    | cc_ind_alias x pv Δ H => let% Δ' := tele_lits Δ in let% H' := modexp_lits H in lok (cc_ind_alias x pv Δ' H')
    end.
End Literals.

(** The literals of a command at a state. *)
Definition cmd_lits_ok (Θ : gdeps) (Ξ : gstack) (B : builtins) (c c' : ccmd) : Prop :=
  cmd_lits (nat_view Θ Ξ B) c = lok c'.

Definition tele_lits_ok (Θ : gdeps) (Ξ : gstack) (B : builtins) (Δ Δ' : ctx) : Prop :=
  tele_lits (nat_view Θ Ξ B) Δ = lok Δ'.

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

(** A successful step of a literal pass. *)
Lemma lbind_lok_inv : forall {A B} (m : lres A) (k : A -> lres B) r, lbind m k = lok r -> exists a, m = lok a /\ k a = lok r.
Proof. intros * H; destruct m; cbn in H; [ eauto | discriminate ]. Qed.

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
