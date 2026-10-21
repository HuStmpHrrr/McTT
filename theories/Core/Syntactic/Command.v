(** * Commands

    The core commands a unit is elaborated into: names are resolved, and an
    import is a load and the declaration of its items.  Their meaning, as steps of
    the global state, is given in [Core.Syntactic.System.Command]. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** A group of inductive declarations as written ([cc_ind]): one type, or
    the types of a mutual block, in order.  The group's own uniform
    parameters [rd_uparams] (innermost first, over the enclosing frames'
    parameters) are shared; each member has its name, its non-uniform
    parameters (innermost first, over the uniform ones), its sort (over the
    uniform ones; the members' sorts are one) and its constructors, each
    with its named arguments, outermost first.  An argument's type is over
    the arguments before it, all of them binders, then the member's
    parameters, then the declared types themselves, [Self_0] (outermost) …
    [Self_(n-1)], variables of types [Π (params). S] bound outside the
    parameters (but inside those of the enclosing frames): a recursive
    occurrence of the [j]-th type is [Self_j] at all its own parameters.
    The command classifies the arguments of each constructor on the normal
    forms of their types, and so finds the group's views, into the
    structural declaration it files. *)
Record raw_member : Set := mk_rmem
  { (** The member's name *)
    rm_name : string
    (** Its non-uniform parameters, innermost first *)
  ; rm_nparams : ctx
    (** Its sort, over the uniform parameters *)
  ; rm_sort : exp
    (** Its constructors, each with its named arguments, outermost
        first *)
  ; rm_cons : list (string * list (string * exp)) }.

(** A group as written: see [raw_member]. *)
Record raw_decl : Set := mk_raw
  { (** The group's own uniform parameters, innermost first *)
    rd_uparams : ctx
    (** The declared members, in order *)
  ; rd_members : list raw_member }.

(** A function of a [mutual def] as written ([cc_mdef]): its name, its
    non-uniform parameters [ys] (innermost first, over the block's
    parameters [Δ]), the type of its scrutinee (over [ys]), its result type
    (over the scrutinee and [ys]) and its clauses, one per constructor of
    its member in order, each binding the non-uniform parameters, the
    arguments and the recursive results (over [Δ]). *)
Record raw_fun : Set := mk_rfun
  { (** The function's name *)
    rf_name : string
    (** Its non-uniform parameters [ys], innermost first *)
  ; rf_nparams : ctx
    (** The scrutinee's type, over [ys] *)
  ; rf_scrut : exp
    (** The result type, over the scrutinee and [ys] *)
  ; rf_res : exp
    (** The clauses: constructor name, number of binders, body *)
  ; rf_clauses : list (string * nat * exp) }.


(** The core commands. *)
Inductive ccmd : Set :=
(** [def x : A := M] and [axiom x : A]: transparency, privacy, type and
    body.  An axiom has no body; an [abstract] [def] is opaque, not
    bodiless. *)
| cc_def : string -> bool -> bool -> typ -> option exp -> ccmd
(** [module x (Δ) where cs end], private or not *)
| cc_mod : string -> bool -> ctx -> list ccmd -> ccmd
(** [module x (Δ) := E]: an alias, under its own parameters, private or not. *)
| cc_alias : string -> bool -> ctx -> modexp -> ccmd
(** [cc_load fp]: load the unit [fp] if it is not filed yet. *)
| cc_load : path -> ccmd
(** [cc_open E items]: check that [E] is a module, and declare the items,
    as definitions and aliases of this frame. *)
| cc_open : modexp -> list iitem -> ccmd
(** [eval M], or [eval M : A] *)
| cc_eval : exp -> option typ -> ccmd
(** [inductive x (Δ) : S where | c … with y : T where | … end], private or
    not: the group as written, its parameters over those of the enclosing
    frames.  It makes an entry per declared type, each the module, over the
    uniform parameters, of the type's constructors (and the recursor). *)
| cc_ind : bool -> raw_decl -> ccmd
(** [mutual def (Δ) f (ys) (z : Z) : A | … with g … end], abstract and
    private or not: one function per member of a group, in any order,
    each filed as the definition [λ Δ ys z. a_elim (Some pq) m Bks z] of
    the group's eliminator at its member [m]. *)
| cc_mdef : bool -> bool -> ctx -> list raw_fun -> ccmd
(** [builtin k := X]: the module [X], as written, is bound as the builtin
    [k]; the command resolves it to the inductive type it names. *)
| cc_builtin : string -> modexp -> ccmd
(** [inductive x := X]: the inductive alias [x] of the inductive type the
    module [X], as written, names. *)
| cc_ind_alias : string -> bool -> ctx -> modexp -> ccmd.

(** A unit: its leading imports, its parameters, its body. *)
Definition cunit : Set := (list ccmd * ctx * list ccmd)%type.

Definition prog_path (prg : Cst.prog) : path :=
  let '(_, (fp, _, _)) := prg in fp.
