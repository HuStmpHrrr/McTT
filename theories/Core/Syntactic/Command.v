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
Notation fpath := (list string).

Inductive ccmd : Set :=
(** [def x : A := M]: transparency, privacy, type and body.  A [def] always
    has a body; an [abstract] one is opaque, not bodiless. *)
| cc_def : string -> bool -> bool -> typ -> exp -> ccmd
(** [module x (Δ) where cs end] *)
| cc_mod : string -> ctx -> list ccmd -> ccmd
(** [import X::Y.M], whatever its [use]/[as]: the unit, and the member path
    of the imported module (empty for the unit itself). *)
| cc_import : fpath -> list string -> ccmd
(** [eval M], or [eval M : A] *)
| cc_eval : exp -> option typ -> ccmd.

(** A unit: its leading imports, its parameters, its body. *)
Definition cunit : Set := (list ccmd * ctx * list ccmd)%type.

Definition prog_path (prg : Cst.prog) : fpath :=
  let '(_, (fp, _, _)) := prg in fp.
