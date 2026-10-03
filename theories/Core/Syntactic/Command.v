(** * Commands

    The core commands a unit is elaborated into: names are resolved, and [use]
    and [as] have been handled by the elaborator.  Their meaning, as steps of
    the global state, is given in [Core.Syntactic.System.Command]. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** A unit's absolute path, [X::Y]. *)
Abbreviation fpath := (list string).

Inductive ccmd : Set :=
(** [def x : A := M]: transparency, privacy, type and body.  A [def] always
    has a body; an [abstract] one is opaque, not bodiless. *)
| cc_def : string -> bool -> bool -> typ -> exp -> ccmd
(** [module x (Δ) where cs end] *)
| cc_mod : string -> ctx -> list ccmd -> ccmd
(** [module x (Δ) := E]: an alias, under its own parameters. *)
| cc_alias : string -> ctx -> modexp -> ccmd
(** [import E], whatever its [use]/[as]: the unit to load first, if [E] is in
    another unit; the imported module; and the names it [use]s, each of which
    must be a public member or a submodule of [E]. *)
| cc_import : option fpath -> modexp -> list string -> ccmd
(** [eval M], or [eval M : A] *)
| cc_eval : exp -> option typ -> ccmd.

(** A unit: its leading imports, its parameters, its body. *)
Definition cunit : Set := (list ccmd * ctx * list ccmd)%type.

Definition prog_path (prg : Cst.prog) : fpath :=
  let '(_, (fp, _, _)) := prg in fp.
