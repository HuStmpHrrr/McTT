From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations Wk_Notations.

Generalizable All Variables.

(** * Global Contexts

    Names have two levels, spelled differently in the surface language and
    represented differently here.  [X::Y::Z] names a unit; units are not
    declared inside one another, so the [::] level is flat.  [X.W] names a
    member of one unit, reached by selection.

    The global context is a flat list, newest first, of the units filed so
    far and of the constants their [abstract] definitions became.  Each is
    checked against the part of the list below it, which rules out cycles.
    A unit is closed: it is read in the empty context.  A constant is
    closed too: its type and body are generalized over the context it was
    declared in. *)

Module GlobalCtx_Notations.

  Notation "⋄" := gm_nil.
  Notation "Φ ⊳ x ↦ E" := (gm_ext Φ x E) (at level 50, x at level 0).

End GlobalCtx_Notations.

Import GlobalCtx_Notations.

(** ** Names in a Body *)

(** The name an open item declares. *)
Definition iitem_name (it : iitem) : string := let '(_, d, _) := it in d.

(** The names an open declares, in order: its alias, then its items. *)
Definition open_names (oz : option string) (its : list iitem) : list string :=
  match oz with
  | Some z => z :: map iitem_name its
  | None => map iitem_name its
  end.

(** The names [Φ] declares, newest first, and a name not among them. *)
Fixpoint gm_names (Φ : gmod) : list string :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' x _ => x :: gm_names Φ'
  | gm_open Φ' _ oz its => rev (open_names oz its) ++ gm_names Φ'
  end.

Definition gm_fresh (x : string) (Φ : gmod) : Prop :=
  ~ List.In x (gm_names Φ).

Lemma gm_fresh_ext : forall x Φ y E,
    gm_fresh x (gm_ext Φ y E) <-> x <> y /\ gm_fresh x Φ.
Proof.
  unfold gm_fresh; simpl; intros *; split; [ intuition | intuition congruence ].
Qed.

(** The body up to and including the newest entry named [x]. *)
Fixpoint gm_prefix_upto (Φ : gmod) (x : string) : option gmod :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' y _ => if String.eqb x y then Some Φ else gm_prefix_upto Φ' x
  | gm_open Φ' _ _ _ => gm_prefix_upto Φ' x
  end.

Lemma gm_prefix_upto_ext : forall Φ x Φx, gm_prefix_upto Φ x = Some Φx ->
    exists Φ' E, Φx = gm_ext Φ' x E.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H oz its]; intros * Hp; cbn in Hp; [ discriminate | | eauto ].
  destruct (String.eqb_spec x y) as [-> |]; [ injection Hp as <-; eauto | eauto ].
Qed.

(** An entry with a fresh name shadows nothing. *)
Lemma gm_prefix_upto_fresh : forall Φ x y E Φx,
    gm_fresh y Φ -> gm_prefix_upto Φ x = Some Φx -> gm_prefix_upto (Φ ⊳ y ↦ E) x = Some Φx.
Proof.
  intros * Hf Hp; cbn.
  destruct (String.eqb_spec x y) as [-> |]; [| exact Hp ].
  exfalso; apply Hf; clear Hf.
  induction Φ as [| Φ IH z E' | Φ IH H its]; cbn in Hp |- *; [ discriminate | |].
  - destruct (String.eqb_spec y z) as [-> |]; auto.
  - apply in_or_app; auto.
Qed.

(** ** Paths *)

Definition path_eq_dec := List.list_eq_dec String.string_dec.

Definition path_beq (fp fq : list string) : bool :=
  if path_eq_dec fp fq then true else false.

Lemma path_beq_refl : forall fp, path_beq fp fp = true.
Proof. intros; unfold path_beq; destruct (path_eq_dec fp fp); congruence. Qed.

Lemma path_beq_true : forall fp fq, path_beq fp fq = true -> fp = fq.
Proof. intros * H; unfold path_beq in H; destruct (path_eq_dec fp fq); congruence. Qed.

Lemma path_beq_false : forall fp fq, fp <> fq -> path_beq fp fq = false.
Proof. intros * H; unfold path_beq; destruct (path_eq_dec fp fq); congruence. Qed.

Definition qname_eq_dec (p1 p2 : qname) : sumbool (p1 = p2) (p1 <> p2).
Proof. decide equality; apply path_eq_dec. Defined.

Definition qname_beq (p1 p2 : qname) : bool := if qname_eq_dec p1 p2 then true else false.

Lemma qname_beq_refl : forall p, qname_beq p p = true.
Proof. intros; unfold qname_beq; destruct (qname_eq_dec p p); congruence. Qed.

Lemma qname_beq_true : forall p1 p2, qname_beq p1 p2 = true -> p1 = p2.
Proof. intros * H; unfold qname_beq in H; destruct (qname_eq_dec p1 p2); congruence. Qed.

(** ** The Global Context *)

Inductive gdecl : Set :=
(** A filed unit, by its path *)
| gd_unit : path -> gunit -> gdecl
(** A constant: its name, type and body, and whether it is unsealed.
    Without a body, it is an axiom. *)
| gd_const : qname -> typ -> option exp -> bool -> gdecl.

Definition gctx : Set := list gdecl.

Fixpoint gc_unit (Θ : gctx) (fp : path) : option gunit :=
  match Θ with
  | nil => None
  | gd_unit fq U :: Θ' => if path_beq fp fq then Some U else gc_unit Θ' fp
  | gd_const _ _ _ _ :: Θ' => gc_unit Θ' fp
  end.

Fixpoint gc_const (Θ : gctx) (qn : qname) : option (typ * option exp * bool) :=
  match Θ with
  | nil => None
  | gd_unit _ _ :: Θ' => gc_const Θ' qn
  | gd_const p A M b :: Θ' => if qname_beq qn p then Some (A, M, b) else gc_const Θ' qn
  end.

(** The part of [Θ] below the unit [fp], where it was checked. *)
Fixpoint gc_unit_below (Θ : gctx) (fp : path) : option (gunit * gctx) :=
  match Θ with
  | nil => None
  | gd_unit fq U :: Θ' => if path_beq fp fq then Some (U, Θ') else gc_unit_below Θ' fp
  | gd_const _ _ _ _ :: Θ' => gc_unit_below Θ' fp
  end.

Lemma gc_unit_below_unit : forall Θ fp U Θ',
    gc_unit_below Θ fp = Some (U, Θ') -> gc_unit Θ fp = Some U.
Proof.
  induction Θ as [| [fq V | p A M b] Θ IH]; intros * H; cbn in *; [ discriminate | | eauto ].
  destruct (path_beq fp fq); [ congruence | eauto ].
Qed.

Lemma gc_unit_below_some : forall Θ fp U,
    gc_unit Θ fp = Some U -> exists Θ', gc_unit_below Θ fp = Some (U, Θ').
Proof.
  induction Θ as [| [fq V | p A M b] Θ IH]; intros * H; cbn in *; [ discriminate | | eauto ].
  destruct (path_beq fp fq); [ injection H as ->; eauto | eauto ].
Qed.

(** One global context is below another when everything filed in it is
    filed, the same, in the other: what filing more preserves. *)
Definition gc_sub (Θ Θ' : gctx) : Prop :=
  (forall fp U, gc_unit Θ fp = Some U -> gc_unit Θ' fp = Some U) /\
  (forall qn c, gc_const Θ qn = Some c -> gc_const Θ' qn = Some c).

Notation "Θ ⊑ Θ'" := (gc_sub Θ Θ') (at level 70) : type_scope.

Lemma gc_sub_refl : forall Θ, Θ ⊑ Θ.
Proof. split; auto. Qed.

Lemma gc_sub_trans : forall Θ1 Θ2 Θ3, Θ1 ⊑ Θ2 -> Θ2 ⊑ Θ3 -> Θ1 ⊑ Θ3.
Proof. intros * [H1 H2] [H3 H4]; split; auto. Qed.

Lemma gc_sub_unit : forall Θ Θ' fp U, Θ ⊑ Θ' -> gc_unit Θ fp = Some U -> gc_unit Θ' fp = Some U.
Proof. intros * [H _]; apply H. Qed.

Lemma gc_sub_const : forall Θ Θ' qn c, Θ ⊑ Θ' -> gc_const Θ qn = Some c -> gc_const Θ' qn = Some c.
Proof. intros * [_ H]; apply H. Qed.

(** Filing a fresh unit or a fresh constant. *)
Lemma gc_sub_cons_unit : forall Θ fp U, gc_unit Θ fp = None -> Θ ⊑ gd_unit fp U :: Θ.
Proof.
  intros * Hn; split; cbn; [| auto ].
  intros fq V H; destruct (path_beq fq fp) eqn:E; [ apply path_beq_true in E; congruence | exact H ].
Qed.

Lemma gc_sub_cons_const : forall Θ qn A M b, gc_const Θ qn = None -> Θ ⊑ gd_const qn A M b :: Θ.
Proof.
  intros * Hn; split; cbn; [ auto |].
  intros p c H; destruct (qname_beq p qn) eqn:E; [ apply qname_beq_true in E; congruence | exact H ].
Qed.

#[export]
Hint Resolve gc_sub_refl gc_sub_unit gc_sub_const : mctt.

(** ** Transparent Global Contexts

    Every constant is unsealed and has a body: then nothing evaluates to a
    neutral but a variable, which is what canonicity and consistency need. *)
Definition gc_transparent (Θ : gctx) : Prop :=
  forall qn A oM b, gc_const Θ qn = Some (A, oM, b) -> b = true /\ oM <> None.

(** No constant is an axiom. *)
Definition gc_no_axioms (Θ : gctx) : Prop :=
  forall qn A oM b, gc_const Θ qn = Some (A, oM, b) -> oM <> None.

(** ** A Fixed Global Context

    The semantic model and the two metatheorems about NbE are stated for one
    global context at a time.  Found by instance resolution, it keeps their
    judgments in the short forms of [Core.Semantic.Fixed]. *)
Class GCtx : Set := gc_mk
  { gc_ctx : gctx }.
