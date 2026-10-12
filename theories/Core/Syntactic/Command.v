(** * Commands

    The core commands a unit is elaborated into: names are resolved, and an
    import is a load and the declaration of its items.  Their meaning, as steps of
    the global state, is given in [Core.Syntactic.System.Command]. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** An inductive declaration as written ([cc_ind]): the number of uniform
    parameters, the parameters (innermost first, the non-uniform ones
    inside), the sort over the uniform ones, and the constructors, each with
    its named arguments, outermost first.  An argument's type is over the
    arguments before it, all of them binders, then the parameters, then the
    declared type itself, [Self], a variable of type [Π Δ. S] bound outside
    the parameters (but inside those of the enclosing frames): a recursive
    occurrence is [Self] at all the declaration's own parameters.  The
    command classifies the arguments ([cls_args]) into the structural
    declaration it files. *)
Record raw_decl : Set := mk_raw
  { rd_nu : nat
  ; rd_params : ctx
  ; rd_sort : exp
  ; rd_cons : list (string * list (string * exp)) }.

(** The uniform parameters, the outermost [rd_nu R]: the parameters of the
    module the declaration makes. *)
Definition rd_uparams (R : raw_decl) : ctx :=
  List.skipn (List.length (rd_params R) - rd_nu R) (rd_params R).

(** A declaration is filed in the module it makes, under this name, which
    no source can write.  The module's other members are the
    constructors. *)
Definition ind_name : string := "#".

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
(** [inductive x (Δ) : S where | c : … end], private or not: the declaration
    as written, its parameters over those of the enclosing frames.  It
    makes the module [x], over the uniform parameters, of the declaration
    and the constructors. *)
| cc_ind : string -> bool -> raw_decl -> ccmd.

(** A unit: its leading imports, its parameters, its body. *)
Definition cunit : Set := (list ccmd * ctx * list ccmd)%type.

Definition prog_path (prg : Cst.prog) : path :=
  let '(_, (fp, _, _)) := prg in fp.
