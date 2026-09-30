(** * Commands

    The *core* commands a unit is elaborated into: names resolved, and [use]
    and [as] gone, being the elaborator's business.  Their meaning, as moves of
    the global state, is [Core.Syntactic.System.Command]. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** A unit's absolute path, [X::Y]. *)
Notation fpath := (list string).

Inductive ccmd : Set :=
(** [def x : A := M]: transparency, privacy, type, body.  A [def] always has
    one; an [abstract] one is opaque, not bodiless. *)
| cc_def : string -> bool -> bool -> typ -> exp -> ccmd
(** [module x (Δ) where cs end] *)
| cc_mod : string -> ctx -> list ccmd -> ccmd
(** [import X::Y.M], whatever the [use]/[as]: the unit and the member path to
    the module imported, empty for the unit itself *)
| cc_import : fpath -> list string -> ccmd
(** [eval M], or [eval M : A] *)
| cc_eval : exp -> option typ -> ccmd.

(** A unit: its leading imports, its parameters, its body. *)
Definition cunit : Set := (list ccmd * ctx * list ccmd)%type.

Definition prog_path (prg : Cst.prog) : fpath :=
  let '(_, (fp, _, _)) := prg in fp.
