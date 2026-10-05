(** * Commands

    The core commands a unit is elaborated into: names are resolved, and an
    import is a load and the declaration of its items.  Their meaning, as steps of
    the global state, is given in [Core.Syntactic.System.Command]. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

Inductive ccmd : Set :=
(** [def x : A := M]: transparency, privacy, type and body.  A [def] always
    has a body; an [abstract] one is opaque, not bodiless. *)
| cc_def : string -> bool -> bool -> typ -> exp -> ccmd
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
| cc_eval : exp -> option typ -> ccmd.

(** A unit: its leading imports, its parameters, its body. *)
Definition cunit : Set := (list ccmd * ctx * list ccmd)%type.

Definition prog_path (prg : Cst.prog) : path :=
  let '(_, (fp, _, _)) := prg in fp.
