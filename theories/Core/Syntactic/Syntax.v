From Stdlib Require Import List Morphisms Relation_Definitions RelationClasses Setoid String.

From Mctt.Core Require Import Base.

(** * Concrete Syntax Tree *)
Module Cst.
Inductive obj : Set :=
| typ : nat -> obj
| nat : obj
| zero : obj
| succ : obj -> obj
| natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
| pi : string -> obj -> obj -> obj
| fn : string -> obj -> obj -> obj
| app : obj -> obj -> obj
| var : string -> obj.
End Cst.

(** * Abstract Syntax Tree

    Note that, unlike a calculus of explicit substitutions, there is no
    constructor for substitution application and no syntactic category of
    substitutions.  Weakenings and substitutions are meta-level operations
    (recursive functions on [exp]) defined further down in this file, and their
    algebraic laws are theorems (in [Core.Syntactic.Substitution]) rather than
    definitional equalities of the object theory.
 *)
Inductive exp : Set :=
(** Universe *)
| a_typ : nat -> exp
(** Natural numbers *)
| a_nat : exp
| a_zero : exp
| a_succ : exp -> exp
| a_natrec : exp -> exp -> exp -> exp -> exp
(** Functions *)
| a_pi : exp -> exp -> exp
| a_fn : exp -> exp -> exp
| a_app : exp -> exp -> exp
(** Variable *)
| a_var : nat -> exp.

Abbreviation ctx := (list exp).
Abbreviation typ := exp.

Fixpoint nat_to_exp n : exp :=
  match n with
  | 0 => a_zero
  | S m => a_succ (nat_to_exp m)
  end.
Definition num_to_exp n := nat_to_exp (Nat.of_num_uint n).

Fixpoint exp_to_nat e : option nat :=
  match e with
  | a_zero => Some 0
  | a_succ e' =>
      match exp_to_nat e' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.
Definition exp_to_num e :=
  match exp_to_nat e with
  | Some n => Some (Nat.to_num_uint n)
  | None => None
  end.

(** ** Syntactic Normal/Neutral Form *)
Inductive nf : Set :=
| nf_typ : nat -> nf
| nf_nat : nf
| nf_zero : nf
| nf_succ : nf -> nf
| nf_pi : nf -> nf -> nf
| nf_fn : nf -> nf -> nf
| nf_neut : ne -> nf
with ne : Set :=
| ne_natrec : nf -> nf -> nf -> ne -> ne
| ne_app : ne -> nf -> ne
| ne_var : nat -> ne
.

Fixpoint nf_to_exp (M : nf) : exp :=
  match M with
  | nf_typ i => a_typ i
  | nf_nat => a_nat
  | nf_zero => a_zero
  | nf_succ M => a_succ (nf_to_exp M)
  | nf_pi A B => a_pi (nf_to_exp A) (nf_to_exp B)
  | nf_fn A M => a_fn (nf_to_exp A) (nf_to_exp M)
  | nf_neut M => ne_to_exp M
  end
with ne_to_exp (M : ne) : exp :=
  match M with
  | ne_natrec A MZ MS M => a_natrec (nf_to_exp A) (nf_to_exp MZ) (nf_to_exp MS) (ne_to_exp M)
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_var x => a_var x
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

Fact nf_eq_dec : forall (M M' : nf),
    ({M = M'} + {M <> M'})%type
with ne_eq_dec : forall (M M' : ne),
    ({M = M'} + {M <> M'})%type.
Proof.
  all: intros; decide equality;
    apply PeanoNat.Nat.eq_dec.
Defined.

(** * Weakenings

    Weakenings are meta-level functions on de Bruijn indices.  They form the
    first of the two tiers of the substitution machinery: lifting a
    substitution under a binder ([sb_q] below) has to weaken the results of
    that substitution by one, so weakening application must already be
    available before substitution application can be defined by structural
    recursion on expressions.
 *)

Definition wk : Set := nat -> nat.

Definition wk_id : wk := fun x => x.
Arguments wk_id _ /.

(** The shift [⇑], which increments every index by one. *)
Definition wk_shift : wk := fun x => S x.
Arguments wk_shift _ /.

(** [wk_q φ] extends [φ] under one binder: it fixes index [0] and shifts the
    image of every other index by one. *)
Definition wk_q (φ : wk) : wk :=
  fun x =>
    match x with
    | 0 => 0
    | S y => S (φ y)
    end.
Arguments wk_q _ _ /.

(** Composition of weakenings is *diagrammatic*: [wk_compose φ ψ] applies [φ]
    first and then [ψ].  This is the orientation of the paper, and the one for
    which [M⟨φ⟩⟨ψ⟩ = M⟨φ ⊙ ψ⟩] holds without a flip.  It is the *opposite* of
    the orientation of [a_compose] in the explicit-substitution presentation
    this development used previously. *)
Definition wk_compose (φ ψ : wk) : wk := fun x => ψ (φ x).
Arguments wk_compose _ _ _ /.

(** [wk_qn n φ] is the paper's [q^n(φ)]: [φ] lifted under [n] binders. *)
Fixpoint wk_qn (n : nat) (φ : wk) : wk :=
  match n with
  | 0 => φ
  | S m => wk_q (wk_qn m φ)
  end.

(** [wk_shiftn n] is the paper's [⇑^n], the [n]-fold shift. *)
Definition wk_shiftn (n : nat) : wk := fun x => x + n.
Arguments wk_shiftn _ _ /.

(** Application of a weakening to an expression.  Whenever we pass under a
    binder, the weakening is lifted with [wk_q]; the successor branch of the
    eliminator binds two variables, hence two lifts. *)
Fixpoint exp_wk (M : exp) (φ : wk) : exp :=
  match M with
  | a_typ i => a_typ i
  | a_nat => a_nat
  | a_zero => a_zero
  | a_succ M => a_succ (exp_wk M φ)
  | a_natrec A MZ MS M =>
      a_natrec (exp_wk A (wk_q φ))
               (exp_wk MZ φ)
               (exp_wk MS (wk_q (wk_q φ)))
               (exp_wk M φ)
  | a_pi A B => a_pi (exp_wk A φ) (exp_wk B (wk_q φ))
  | a_fn A M => a_fn (exp_wk A φ) (exp_wk M (wk_q φ))
  | a_app M N => a_app (exp_wk M φ) (exp_wk N φ)
  | a_var x => a_var (φ x)
  end.

(** * Substitutions

    A substitution maps each de Bruijn index to an expression.  Like
    weakenings, substitutions are not part of the object syntax: applying one
    is a meta-level recursion on the expression.
 *)

Definition sub : Set := nat -> exp.

Definition sb_id : sub := fun x => a_var x.
Arguments sb_id _ /.

(** Extension (cons).  [sb_extend σ M] sends index [0] to [M] and index
    [S y] to [σ y]; the paper writes it [σ, M/x₀]. *)
Definition sb_extend (σ : sub) (M : exp) : sub :=
  fun x =>
    match x with
    | 0 => M
    | S y => σ y
    end.
Arguments sb_extend _ _ _ /.

(** Postcomposition of a substitution with a weakening, pointwise. *)
Definition sb_wk (σ : sub) (φ : wk) : sub := fun x => exp_wk (σ x) φ.
Arguments sb_wk _ _ _ /.

(** The embedding [ι] of weakenings into substitutions. *)
Definition sb_of_wk (φ : wk) : sub := fun x => a_var (φ x).
Arguments sb_of_wk _ _ /.

(** [⇑] regarded as a substitution. *)
Definition sb_shift : sub := sb_of_wk wk_shift.
Arguments sb_shift _ /.

(** Lifting a substitution under a binder: [q(σ) := σ[⇑], x₀/x₀].

    Unlike the other operations, [sb_q] is deliberately *never* unfolded by
    [simpl]: keeping it folded is what makes goals mentioning [q σ] readable,
    and it is what lets [simpl] normalise the body of [exp_sub] without
    exposing the encoding of lifting.  Use [sb_q_zero] and [sb_q_succ] to
    compute with it. *)
Definition sb_q (σ : sub) : sub := sb_extend (sb_wk σ wk_shift) (a_var 0).
Arguments sb_q : simpl never.

(** Application of a substitution to an expression. *)
Fixpoint exp_sub (M : exp) (σ : sub) : exp :=
  match M with
  | a_typ i => a_typ i
  | a_nat => a_nat
  | a_zero => a_zero
  | a_succ M => a_succ (exp_sub M σ)
  | a_natrec A MZ MS M =>
      a_natrec (exp_sub A (sb_q σ))
               (exp_sub MZ σ)
               (exp_sub MS (sb_q (sb_q σ)))
               (exp_sub M σ)
  | a_pi A B => a_pi (exp_sub A σ) (exp_sub B (sb_q σ))
  | a_fn A M => a_fn (exp_sub A σ) (exp_sub M (sb_q σ))
  | a_app M N => a_app (exp_sub M σ) (exp_sub N σ)
  | a_var x => σ x
  end.

(** Composition of substitutions, again *diagrammatic*: [sb_compose σ τ]
    applies [σ] first and then [τ]. *)
Definition sb_compose (σ τ : sub) : sub := fun x => exp_sub (σ x) τ.
Arguments sb_compose _ _ _ /.

(** [sb_qn n σ] is the paper's [q^n(σ)]. *)
Fixpoint sb_qn (n : nat) (σ : sub) : sub :=
  match n with
  | 0 => σ
  | S m => sb_q (sb_qn m σ)
  end.

(** ** Equality of Weakenings and Substitutions

    Weakenings and substitutions are functions, so the algebraic laws that the
    paper states as equalities of weakenings or of substitutions (for instance
    [q(id) = id]) are function equalities.  Rather than assume functional
    extensionality — this development is otherwise axiom-free — we use
    pointwise equality throughout, and lift it through the two application
    operations with the congruence lemmas [exp_wk_wk_eq] and [exp_sub_sb_eq]
    below.  The [Proper] instances registered for those lemmas make ordinary
    [rewrite] work with pointwise hypotheses.
 *)

Definition wk_eq : relation wk := pointwise_relation nat eq.
Definition sb_eq : relation sub := pointwise_relation nat eq.

#[export]
Instance wk_eq_Equivalence : Equivalence wk_eq := _.
#[export]
Instance sb_eq_Equivalence : Equivalence sb_eq := _.

#[global] Declare Custom Entry exp.
#[global] Declare Custom Entry nf.

#[global] Bind Scope mctt_scope with exp.
#[global] Bind Scope mctt_scope with sub.
#[global] Bind Scope mctt_scope with nf.
#[global] Bind Scope mctt_scope with ne.
Open Scope mctt_scope.

(** ** Syntactic Notations *)
Module Syntax_Notations.
  Notation "{{{ x }}}" := x (at level 0, x custom exp at level 99, format "'{{{'  x  '}}}'") : mctt_scope.
  (** We need to define the substitution notations first to assert
      [left associativity] of level 1.  Level 0 is for *closed* notations —
      those beginning and ending in a terminal — so everything else that used to
      sit there is one level up. *)
  Notation "e [ s ]" := (exp_sub e s) (in custom exp at level 1, e custom exp, s custom exp at level 60, left associativity, format "e [ s ]") : mctt_scope.
  Notation "e ⟨ φ ⟩" := (exp_wk e φ) (in custom exp at level 1, e custom exp, φ constr at level 60, left associativity, format "e ⟨ φ ⟩") : mctt_scope.
  Notation "( x )" := x (in custom exp at level 0, x custom exp at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom exp at level 1, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom exp at level 0, x ident) : mctt_scope.
  Notation "'λ' A e" := (a_fn A e) (in custom exp at level 2, A custom exp at level 1, e custom exp at level 60) : mctt_scope.
  Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom exp at level 40, f custom exp, x custom exp at next level, y custom exp at next level) : mctt_scope.
  Notation "'ℕ'" := a_nat (in custom exp) : mctt_scope.
  Notation "'Type' @ n" := (a_typ n) (in custom exp at level 1, n constr at level 0, format "'Type' @ n") : mctt_scope.
  Notation "'Π' A B" := (a_pi A B) (in custom exp at level 2, A custom exp at level 1, B custom exp at level 60) : mctt_scope.
  Notation "'zero'" := a_zero (in custom exp at level 0) : mctt_scope.
  Notation "'succ' e" := (a_succ e) (in custom exp at level 2, e custom exp at level 1) : mctt_scope.
  Notation "'rec' e 'return' A | 'zero' -> ez | 'succ' -> es 'end'" := (a_natrec A ez es e) (in custom exp at level 0, A custom exp at level 60, ez custom exp at level 60, es custom exp at level 60, e custom exp at level 60) : mctt_scope.
  Notation "'#' n" := (a_var n) (in custom exp at level 1, n constr at level 0, format "'#' n") : mctt_scope.

  (** *** Substitutions

      Note that [σ ⨟ τ] is *diagrammatic* composition — [σ] first, then [τ] —
      unlike the [σ ∘ τ] of the explicit-substitution presentation.  The
      spelling is deliberately different so that no old occurrence parses
      silently under the new orientation. *)
  Notation "'Id'" := sb_id (in custom exp at level 0) : mctt_scope.
  Notation "'Wk'" := sb_shift (in custom exp at level 0) : mctt_scope.
  Notation "σ ⨟ τ" := (sb_compose σ τ) (in custom exp at level 40, right associativity, format "σ ⨟ τ") : mctt_scope.
  Notation "σ ,, e" := (sb_extend σ e) (in custom exp at level 50, left associativity, format "σ ,, e") : mctt_scope.
  Notation "'q' σ" := (sb_q σ) (in custom exp at level 30) : mctt_scope.

  Notation "⋅" := nil (in custom exp at level 0) : mctt_scope.
  Notation "x , y" := (cons y x) (in custom exp at level 50, left associativity, format "x ,  y") : mctt_scope.

  Notation "n{{{ x }}}" := x (at level 0, x custom nf at level 99, format "'n{{{'  x  '}}}'") : mctt_scope.
  Notation "( x )" := x (in custom nf at level 0, x custom nf at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom nf at level 1, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom nf at level 0, x ident) : mctt_scope.
  Notation "'λ' A e" := (nf_fn A e) (in custom nf at level 2, A custom nf at level 1, e custom nf at level 60) : mctt_scope.
  Notation "f x .. y" := (ne_app .. (ne_app f x) .. y) (in custom nf at level 40, f custom nf, x custom nf at next level, y custom nf at next level) : mctt_scope.
  Notation "'ℕ'" := nf_nat (in custom nf) : mctt_scope.
  Notation "'Type' @ n" := (nf_typ n) (in custom nf at level 1, n constr at level 0, format "'Type' @ n") : mctt_scope.
  Notation "'Π' A B" := (nf_pi A B) (in custom nf at level 2, A custom nf at level 1, B custom nf at level 60) : mctt_scope.
  Notation "'zero'" := nf_zero (in custom nf at level 0) : mctt_scope.
  Notation "'succ' M" := (nf_succ M) (in custom nf at level 2, M custom nf at level 1) : mctt_scope.
  Notation "'rec' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (ne_natrec A MZ MS M) (in custom nf at level 0, A custom nf at level 60, MZ custom nf at level 60, MS custom nf at level 60, M custom nf at level 60) : mctt_scope.
  Notation "'#' n" := (ne_var n) (in custom nf at level 1, n constr at level 0, format "'#' n") : mctt_scope.
  Notation "'⇑' M" := (nf_neut M) (in custom nf at level 1, M custom nf at level 99, format "'⇑'  M") : mctt_scope.
End Syntax_Notations.

(** ** Notations for Weakenings

    Weakenings live outside the [exp] custom entry: they are a separate sort,
    and after [Substitution.v] establishes that the embedding [ι] is faithful
    the development speaks almost exclusively of substitutions. *)
Module Wk_Notations.
  (** [↑] is the paper's [⇑] *as a weakening*.  The glyph differs because [⇑] is
      already the neutral-form embedding in the [nf] entry, and because the
      development needs to keep the shift weakening apart from the shift
      substitution [Wk = ι ↑]. *)
  Notation "↑" := wk_shift : mctt_scope.
  Notation "φ ⊙ ψ" := (wk_compose φ ψ) (at level 40, left associativity) : mctt_scope.
  Notation "'ι' φ" := (sb_of_wk φ) (at level 30) : mctt_scope.
End Wk_Notations.
