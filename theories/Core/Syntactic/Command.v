(** * Commands

    The core commands a unit is elaborated into: names are resolved, an
    import is a load, and an open the declaration of its items.  Their meaning, as steps of
    the global state, is given in [Core.Syntactic.System.Command]. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

Inductive ccmd : Set :=
(** [def x : A := M]: transparency, privacy, type and body.  An [abstract]
    one ([b = false]) is filed as a constant, and the member is defined as
    that constant; so is one without a body, an axiom. *)
| cc_def : string -> bool -> bool -> typ -> option exp -> ccmd
(** [module x (Δ) where cs end], private or not *)
| cc_mod : string -> bool -> ctx -> list ccmd -> ccmd
(** [module x (Δ) := E]: an alias, under its own parameters, private or not. *)
| cc_alias : string -> bool -> ctx -> modexp -> ccmd
(** [cc_load fp]: load the unit [fp] if it is not filed yet. *)
| cc_load : path -> ccmd
(** [cc_open E oZ items]: check that [E] is a module, and declare the private
    alias [Z] of it when [oZ = Some Z], then the items, as definitions and
    aliases of this frame. *)
| cc_open : modexp -> option string -> list iitem -> ccmd
(** [eval M], or [eval M : A] *)
| cc_eval : exp -> option typ -> ccmd.

(** A unit: its leading loads and opens, its parameters, its body. *)
Definition cunit : Set := (list ccmd * ctx * list ccmd)%type.

Definition prog_path (prg : Cst.prog) : path :=
  let '(_, (fp, _, _)) := prg in fp.

(** ** Frames

    While a unit is checked, the modules open around the command being
    checked are its frames, innermost first: the chain of the module from
    the unit's root, its parameters, and its body so far.  A command is
    checked in [fctx Γimp F]: each frame contributes its self slot, holding
    its body so far, over its parameters, and the unit's leading opens [Γimp]
    are outermost. *)
Record frame : Set := fr_mk
  { fr_chain : list string
  ; fr_params : ctx
  ; fr_body : gmod }.

Fixpoint fctx (Γimp : ctx) (F : list frame) : ctx :=
  match F with
  | nil => Γimp
  | f :: F' => self_ent (fr_body f) :: fr_params f ++ fctx Γimp F'
  end.
