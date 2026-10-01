From Stdlib Require Import List Morphisms Relation_Definitions RelationClasses Setoid String.

From Mctt.Core Require Import Base.

(** * Concrete Syntax Tree *)
Module Cst.

(** ** Modifiers

    [private] hides a definition from importers, [abstract] makes its body
    opaque.  The two are orthogonal, hence a record rather than a variant. *)
Record mods : Set :=
  { md_private : bool
  ; md_abstract : bool }.

Definition md_pub : mods := {| md_private := false; md_abstract := false |}.
Definition md_priv : mods := {| md_private := true; md_abstract := false |}.
Definition md_abs : mods := {| md_private := false; md_abstract := true |}.
Definition md_priv_abs : mods := {| md_private := true; md_abstract := true |}.

(** ** Objects and Declarations

    The two levels of naming are spelled differently.  [::] separates the
    segments of a *file* path — the name of a compilation unit, which is what
    [glob] holds — and [.] selects a member of whatever precedes it, be that an
    internal module, a unit, or a local module binding.

    [proj] is that *postfix dot*: [X::Y::Z.W.foo] is a chain of [proj]s over
    [glob ["X"; "Y"; "Z"]], and [A.foo] for an internal module [A] is one over
    [var "A"].  Module arguments arrive as ordinary [app] nodes, so
    [(X::Y.Z a b).foo] needs no syntax of its own.  Whether a given [proj] or
    [app] is a module operation or a term operation is decided by name
    resolution, not by the parser; see [Frontend.Resolve].

    [letb] binds one declaration at a time; the parser folds a run of them into
    nested [letb]s.  Keeping the recursion out of a [list] is what lets [obj]
    and [decl] stay an ordinary mutual pair, so [Functional Scheme] still
    applies to functions defined over them. *)
Inductive obj : Set :=
| typ : nat -> obj
| nat : obj
| zero : obj
| succ : obj -> obj
| natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
| pi : string -> obj -> obj -> obj
| fn : string -> obj -> obj -> obj
| app : obj -> obj -> obj
| var : string -> obj
(** A [::] path, hence at least two segments after a [var] *)
| glob : list string -> obj
| proj : obj -> string -> obj
| letb : decl -> obj -> obj

with decl : Set :=
(** [x : A := M], carrying its modifiers *)
| d_def : mods -> string -> obj -> obj -> decl
(** [module M := E] *)
| d_mod : string -> obj -> decl.

(** ** Commands

    What an [import] brings into scope.  [i_open] makes the module reachable
    under its full path, [i_as] additionally binds a short alias, and [i_use]
    binds the listed members directly.  All three are name-resolution
    operations: none of them elaborates to anything. *)
Inductive ispec : Set :=
| i_open : ispec
| i_as : string -> ispec
| i_use : list string -> ispec.

(** A module declaration carries the *internal* path it introduces ([module A.B]
    nests two levels at once) and its parameter telescope; a unit's own name is
    declared by [prog] below, not here. *)
Inductive cmd : Set :=
| c_mod : list string -> list (string * obj) -> list cmd -> cmd
| c_def : mods -> string -> obj -> obj -> cmd
(** [c_import fp ip] imports the module at internal path [ip] of the unit at
    file path [fp].  An empty [fp] is this unit, so [import A.B] is
    [c_import nil ["A"; "B"]] and [import X::Y] is [c_import ["X"; "Y"] nil]. *)
| c_import : list string -> list string -> ispec -> cmd
(** [eval M] normalizes [M] and prints the result; [eval M : A] additionally
    checks [M] against [A] rather than inferring its type. *)
| c_eval : obj -> option obj -> cmd.

(** A compilation unit: its imports, and the one module declaration everything
    else it contains lives in.  That declaration names the unit, so its path is a
    [::] one, and carries the unit's parameters.  Only imports may precede it, so
    no definition is ever made outside a module.  The imports are [c_import]s;
    the grammar admits nothing else there. *)
Definition prog : Set := (list cmd * (list string * list (string * obj) * list cmd))%type.

End Cst.

(** * Abstract Syntax Tree

    Note that, unlike a calculus of explicit substitutions, there is no
    constructor for substitution application and no syntactic category of
    substitutions.  Weakenings and substitutions are meta-level operations
    (recursive functions on [exp]) defined further down in this file, and their
    algebraic laws are theorems (in [Core.Syntactic.Substitution]) rather than
    definitional equalities of the object theory.
 *)

(** ** Qualified Names

    A reference to a global is [X::Y::Z.a.b.c]: a qualifier selecting a module,
    then a nonempty chain of member selections inside it.  The two halves are
    spelled differently in the surface language and are different kinds of thing
    here — the qualifier indexes the ambient structure, the members index one
    module — so they are separate fields rather than one path.

    Both qualifiers are *absolute*: neither changes when a frame is pushed
    around the point where the name is written.  That is what lets resolution
    hand an entry back exactly as it is stored. *)
Inductive qual : Set :=
(** [X::Y::Z]: a unit, named absolutely.  Units do not nest, so this is a path
    into the import trie. *)
| qu_abs : list string -> qual
(** A *de Bruijn level* into the frames open around the point of use: [0] is the
    outermost (the unit being elaborated), and a frame keeps its level while
    frames are pushed inside it.  The module being elaborated is not yet an
    entry of anything, so its members cannot be named by a [qu_abs] path; its
    level is its absolute name for as long as it is open. *)
| qu_rel : nat -> qual.

Record path : Set :=
  { p_qual : qual
  ; p_mems : list string }.

(** Abbreviations, not definitions: a rule keyed on [p_abs]/[p_rel] then has a
    record literal in its conclusion, so inverting it yields equations that
    [discriminate] and [injection] see through. *)
Notation p_abs fp ip := {| p_qual := qu_abs fp; p_mems := ip |}.
Notation p_rel n ip := {| p_qual := qu_rel n; p_mems := ip |}.

(** An absolute qualifier is nonempty, so it never denotes "this unit" — that is
    [qu_rel]'s job, and a name with two readings would resolve two ways.  The
    members are nonempty, so a path never denotes a module: a module is not an
    [exp] and has no type. *)
Definition qual_valid (q : qual) : Prop :=
  match q with
  | qu_abs fp => fp <> nil
  | qu_rel _ => True
  end.

Definition path_valid (p : path) : Prop :=
  qual_valid (p_qual p) /\ p_mems p <> nil.

(** The member [ip] of the module [mp]: what a member of a frame becomes once
    that frame is closed and filed as [mp]. *)
Definition p_app (mp : path) (ip : list string) : path :=
  {| p_qual := p_qual mp ; p_mems := p_mems mp ++ ip |}.

(** A module parameter: the [lp_param]-th parameter of the frame at level
    [lp_mod], both counted from the outside ([0] is the outermost frame, and the
    first parameter of a telescope).  Module parameters are not λ-bound: they
    are in scope because their module is open, so they are not de Bruijn indices
    of the local context, and weakening and substitution leave them alone.  Like
    a [qu_rel] path, a parameter keeps its name while frames are pushed. *)
Record lpath : Set := lp_mk
  { lp_mod : nat
  ; lp_param : nat }.

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
| a_var : nat -> exp
(** Module parameter *)
| a_param : lpath -> exp
(** Globals.  [X::Y::Z.W.bar] is [a_glob (p_abs ["X"; "Y"; "Z"] ["W"; "bar"])];
    a reference into the unit being elaborated instead names an enclosing module
    by index, [a_glob (p_rel 0 ["W"; "bar"])].

    There is no projection constructor: a projection is not an operation on
    expressions but part of a name, resolved by the elaborator, so
    [(X::Y.Z x y).bar] elaborates to
    [a_glob (p_abs ["X"; "Y"] ["Z"; "bar"]) $ x $ y]. *)
| a_glob : path -> exp.

Abbreviation ctx := (list exp).
Abbreviation typ := exp.

(** ** Telescopes

    A member of a parameterized module is stored open in the telescope of
    parameters it lives under, and generalized when it is resolved; these two
    folds are what generalize it.  They are the [exp]-level counterparts of the
    elaborator's [tele_pi]/[tele_fn], which work on [Cst.obj] and so cannot
    appear in a judgment.

    A [ctx] is innermost-first, so the head of [Δ] is the parameter bound *last*
    and must become the *innermost* binder: the recursion wraps the head first
    and works outward.  Folding the other way reverses the telescope, and the
    result is still a well-formed [exp], so nothing catches it early.

    No shifting arises.  If [B] is well formed in [Δ'] and [A] in [Δ' ▹ B], then
    [Π B A] is well formed in [Δ'] — exactly the invariant [a_pi] wants — so the
    indices already point at the right parameters. *)
Fixpoint ctx_pi (Δ : ctx) (A : typ) : typ :=
  match Δ with
  | nil => A
  | cons B Δ' => ctx_pi Δ' (a_pi B A)
  end.

Fixpoint ctx_fn (Δ : ctx) (M : exp) : exp :=
  match Δ with
  | nil => M
  | cons B Δ' => ctx_fn Δ' (a_fn B M)
  end.

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
| ne_param : lpath -> ne
(** An opaque definition or an axiom: it does not unfold. *)
| ne_glob : path -> ne
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
  | ne_param lp => a_param lp
  | ne_glob p => a_glob p
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

(** A normal form with no global and no parameter at the head of a neutral. *)

Fixpoint nf_clean (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_nat | nf_zero => True
  | nf_succ W => nf_clean W
  | nf_pi A B | nf_fn A B => nf_clean A /\ nf_clean B
  | nf_neut M => ne_clean M
  end
with ne_clean (M : ne) : Prop :=
  match M with
  | ne_natrec A MZ MS M => nf_clean A /\ nf_clean MZ /\ nf_clean MS /\ ne_clean M
  | ne_app M N => ne_clean M /\ nf_clean N
  | ne_var _ => True
  | ne_param _ | ne_glob _ => False
  end.

Fact nf_eq_dec : forall (M M' : nf),
    ({M = M'} + {M <> M'})%type
with ne_eq_dec : forall (M M' : ne),
    ({M = M'} + {M <> M'})%type.
Proof.
  all: intros; decide equality;
    repeat (apply PeanoNat.Nat.eq_dec || decide equality || apply String.string_dec).
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
    which [M[φ]ʷ[ψ]ʷ = M[φ ⊙ ψ]ʷ] holds without a flip.  It is the *opposite* of
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
  | a_param lp => a_param lp
  | a_glob p => a_glob p
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
    [S y] to [σ y]; the paper writes it [σ ▹ M/x₀]. *)
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
  | a_param lp => a_param lp
  | a_glob p => a_glob p
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

(** * Module Substitutions

    The third operation, next to weakening and substitution: [μ] says what each
    module parameter and each global becomes, and what it puts in is weakened
    past the binders it lands under, exactly as [q σ] does.  λ-variables are
    left alone.  Only the *judgments* use one: closing a frame ([ms_close]) when
    a nested module ends or a unit is filed, which is done once, to the stored
    entries.  Resolution and evaluation never apply one. *)
Record msub : Set := ms_mk
  { ms_param : lpath -> exp
  ; ms_glob : path -> exp }.

Definition ms_q (μ : msub) : msub :=
  ms_mk (fun lp => exp_wk (ms_param μ lp) wk_shift) (fun p => exp_wk (ms_glob μ p) wk_shift).

Fixpoint ms_qn (n : nat) (μ : msub) : msub :=
  match n with
  | 0 => μ
  | S m => ms_q (ms_qn m μ)
  end.

(** One notation for every carrier; compute with [cbn]. *)
Class MSub (A : Type) := msubst : msub -> A -> A.

Fixpoint exp_msub (μ : msub) (M : exp) : exp :=
  match M with
  | a_typ i => a_typ i
  | a_nat => a_nat
  | a_zero => a_zero
  | a_succ M => a_succ (exp_msub μ M)
  | a_natrec A MZ MS M =>
      a_natrec (exp_msub (ms_q μ) A)
               (exp_msub μ MZ)
               (exp_msub (ms_q (ms_q μ)) MS)
               (exp_msub μ M)
  | a_pi A B => a_pi (exp_msub μ A) (exp_msub (ms_q μ) B)
  | a_fn A M => a_fn (exp_msub μ A) (exp_msub (ms_q μ) M)
  | a_app M N => a_app (exp_msub μ M) (exp_msub μ N)
  | a_var x => a_var x
  | a_param lp => ms_param μ lp
  | a_glob p => ms_glob μ p
  end.

#[export]
Instance MSub_exp : MSub exp := exp_msub.

#[export]
Instance MSub_option {A} `{MSub A} : MSub (option A) := fun μ => option_map (msubst μ).

(** A telescope: each binding lies under the bindings below it. *)
Fixpoint ctx_msub (μ : msub) (Δ : ctx) : ctx :=
  match Δ with
  | nil => nil
  | A :: Δ' => exp_msub (ms_qn (List.length Δ') μ) A :: ctx_msub μ Δ'
  end.

#[export]
Instance MSub_ctx : MSub ctx := ctx_msub.

(** [M $ #(d + c - 1) $ … $ #d]: [M] applied to [c] variables past [d], the
    outermost first. *)
Fixpoint app_vars (M : exp) (d c : nat) : exp :=
  match c with
  | 0 => M
  | S c' => app_vars (a_app M (a_var (d + c'))) d c'
  end.

(** Closing the frame at level [L], filed from now on as the module [mp], with
    [c] parameters, [d] binders in: its parameters become the λ-variables past
    [d] (parameter [0], the outermost, the furthest out), its members are read
    out of [mp] and applied to them, and everything else stays as it is — no
    other frame changes its level. *)
Definition ms_close (L : nat) (mp : path) (c d : nat) : msub :=
  ms_mk (fun lp =>
           if Nat.eqb (lp_mod lp) L then a_var (d + (c - S (lp_param lp))) else a_param lp)
        (fun p =>
           match p_qual p with
           | qu_rel m => if Nat.eqb m L then app_vars (a_glob (p_app mp (p_mems p))) d c else a_glob p
           | qu_abs _ => a_glob p
           end).

(** Reading the first [j] bindings of the telescope of the frame at level [L] as
    its parameters: the variable [#i] under them is the parameter [j - 1 - i]. *)
Definition sb_params (L j : nat) : sub := fun i => a_param (lp_mk L (j - S i)).
Arguments sb_params _ _ _ /.

(** The types of a telescope's parameters, at their own names: the [j]-th, read
    with its [j] predecessors as parameters.  Indexed by parameter, i.e. the
    outermost first — so a telescope truncated to its outer bindings has a
    prefix of these. *)
Fixpoint ctx_ptys (L : nat) (Δ : ctx) : list typ :=
  match Δ with
  | nil => nil
  | A :: Δ' => ctx_ptys L Δ' ++ (exp_sub A (sb_params L (List.length Δ')) :: nil)
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

#[global] Bind Scope mctt_scope with exp.
#[global] Bind Scope mctt_scope with sub.
#[global] Bind Scope mctt_scope with nf.
#[global] Bind Scope mctt_scope with ne.
Open Scope mctt_scope.

(** ** Syntactic Notations

    Every notation below lives in ordinary [constr]: there is no custom entry
    and hence no delimiter to write.  The price is that a spelling can denote
    only one sort, so the normal forms — which mirror the expressions
    constructor for constructor — carry a superscript [ⁿ].  Values carry a
    superscript [ᵈ]; see [Domain_Notations]. *)
Module Syntax_Notations.
  (** Substitution and weakening application come first, so that level 1 is
      created *left* associative; everything else that reads as an atom is at
      level 0, and the constructor forms with a recursive last argument are at
      level 2. *)
  Notation "M [ σ ]" := (exp_sub M σ) (at level 1, left associativity, σ at level 60, format "M [ σ ]") : mctt_scope.
  Notation "M [ φ ]ʷ" := (exp_wk M φ) (at level 1, left associativity, φ at level 60, format "M [ φ ]ʷ") : mctt_scope.
  Notation "'Type' @ n" := (a_typ n) (at level 1, n at level 0, format "'Type' @ n") : mctt_scope.
  Notation "M [ μ ]ᵐ" := (msubst μ M) (at level 1, left associativity, μ at level 60, format "M [ μ ]ᵐ") : mctt_scope.
  Notation "'#' n" := (a_var n) (at level 1, n at level 0, format "'#' n") : mctt_scope.
  Notation "'$[' n , k ']'" := (a_param (lp_mk n k)) (at level 0, n at level 60, k at level 60) : mctt_scope.
  Notation "'close' L mp c" := (ms_close L mp c 0) (at level 2, L at level 1, mp at level 1, c at level 1) : mctt_scope.
  Notation "'ℕ'" := a_nat : mctt_scope.
  Notation "'zero'" := a_zero : mctt_scope.
  Notation "'succ' M" := (a_succ M) (at level 2, M at level 1) : mctt_scope.
  Notation "'λ' A M" := (a_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Π' A B" := (a_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'rec' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (a_natrec A MZ MS M) (at level 0, M at level 60, A at level 60, MZ at level 60, MS at level 60) : mctt_scope.
  (** Application needs an explicit operator: a [constr] notation may not be
      pure juxtaposition, which is Rocq's own application. *)
  Notation "M $ N" := (a_app M N) (at level 10, left associativity) : mctt_scope.

  (** *** Substitutions

      Note that [σ ⨟ τ] is *diagrammatic* composition — [σ] first, then [τ] —
      unlike the [σ ∘ τ] of the explicit-substitution presentation.  The
      spelling is deliberately different so that no old occurrence parses
      silently under the new orientation. *)
  Notation "'Id'" := sb_id : mctt_scope.
  Notation "'Wk'" := sb_shift : mctt_scope.
  Notation "σ ⨟ τ" := (sb_compose σ τ) (at level 45, right associativity, format "σ ⨟ τ") : mctt_scope.
  Notation "σ ,, M" := (sb_extend σ M) (at level 50, left associativity, format "σ ,, M") : mctt_scope.
  Notation "'q' σ" := (sb_q σ) (at level 30, σ at level 2) : mctt_scope.

  (** *** Contexts

      Extension is [▹] rather than the paper's comma: a parsing [,] in [constr]
      would steal Rocq's pair notation.  Both are restricted to [exp] so that
      an unrelated [list] does not print as a context. *)
  Notation "⋅" := (@nil exp) : mctt_scope.
  Notation "Γ ▹ A" := (@cons exp A Γ) (at level 50, left associativity) : mctt_scope.

  (** *** Normal and Neutral Forms *)
  Notation "'ℕⁿ'" := nf_nat : mctt_scope.
  Notation "'zeroⁿ'" := nf_zero : mctt_scope.
  Notation "'succⁿ' M" := (nf_succ M) (at level 2, M at level 1) : mctt_scope.
  Notation "'Typeⁿ' @ n" := (nf_typ n) (at level 1, n at level 0, format "'Typeⁿ' @ n") : mctt_scope.
  Notation "'λⁿ' A M" := (nf_fn A M) (at level 2, A at level 1, M at level 60) : mctt_scope.
  Notation "'Πⁿ' A B" := (nf_pi A B) (at level 2, A at level 1, B at level 60) : mctt_scope.
  Notation "'⇑ⁿ' M" := (nf_neut M) (at level 2, M at level 1, format "'⇑ⁿ'  M") : mctt_scope.
  Notation "'#ⁿ' n" := (ne_var n) (at level 1, n at level 0, format "'#ⁿ' n") : mctt_scope.
  Notation "M '$ⁿ' N" := (ne_app M N) (at level 10, left associativity, format "M  $ⁿ  N") : mctt_scope.
  Notation "'recⁿ' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (ne_natrec A MZ MS M) (at level 0, M at level 60, A at level 60, MZ at level 60, MS at level 60) : mctt_scope.
End Syntax_Notations.

(** ** Notations for Weakenings

    Weakenings are their own sort, in their own module: after [Substitution.v]
    establishes that the embedding [ι] is faithful the development speaks almost
    exclusively of substitutions. *)
Module Wk_Notations.
  (** [↑] is the paper's [⇑] *as a weakening*.  The glyph differs because [⇑] is
      already the neutral-value embedding of [Domain_Notations], and because the
      development needs to keep the shift weakening apart from the shift
      substitution [Wk = ι ↑]. *)
  Notation "↑" := wk_shift : mctt_scope.
  Notation "φ ⊙ ψ" := (wk_compose φ ψ) (at level 40, left associativity) : mctt_scope.
  Notation "'ι' φ" := (sb_of_wk φ) (at level 30) : mctt_scope.
End Wk_Notations.
