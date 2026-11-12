(** * The Values of the Set Model

    What a term, a variable, a member and a module denote: a term denotes a
    set together with the code of its inferred type ([set_meaning]); a
    variable or a member is a term, a module, or both ([set_entry]); a
    module is a function of its parameters' values, a table of members,
    or a global module at arguments ([set_module]).  An environment gives
    every variable an entry ([set_env]). *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Interpretation Require Export Codes.
From Mctt.Core.Syntactic Require Import Syntax.

(** What a variable or a member denotes. *)
Inductive set_entry : Type :=
(** A term of the kind [kind]: its value and the code of its type.  The
    kind is the one the syntax stores ([ce_ass], [ge_def]); it tells a
    member closure over a module's parameters whether it is a proof *)
| set_entry_term (kind : abs_kind) (value type : aczel_set)
(** A module *)
| set_entry_module (m : set_module)
(** A definition with a module part: its term, relevant, and its module *)
| set_entry_both (value type : aczel_set) (m : set_module)
with set_module : Type :=
(** A unit's parameter of the type code [domain]: a function of the
    parameter's value *)
| set_module_params (domain : aczel_set) (f : aczel_set -> set_module)
(** A body: its members by name, in order *)
| set_module_members (members : list (string * set_entry))
(** The global module at the path [p], at the arguments [args],
    outermost first *)
| set_module_global (p : qname) (args : list aczel_set).

(** A term's value and the code of its inferred type. *)
Record set_meaning : Type := mk_set_meaning
  { (** The value *)
    meaning_value : aczel_set
    (** The code of the type the term infers to *)
  ; meaning_type : aczel_set }.

(** An environment: an entry for every variable. *)
Definition set_env : Type := nat -> set_entry.

(** The entry of no binding: never read by a scoped term. *)
Definition absent_set_entry : set_entry := set_entry_term ak_relevant empty_set empty_set.

(** The environment of the empty context. *)
Definition empty_set_env : set_env := fun _ => absent_set_entry.

(** [ρ] extended by the entry [e] at the variable [#0]. *)
Definition set_env_extend (ρ : set_env) (e : set_entry) : set_env :=
  fun x => match x with 0 => e | S y => ρ y end.

(** The universe [Type@0], the type of [Prop]. *)
Definition universe_zero_code (T : universe_tower) : aczel_set :=
  universe_code (pair_ordinal_set (0, 0)) (small_universe_set T (pair_ordinal_set (0, 0))).

(** What an entry gives a term variable: its term, or at a module what
    the substitution's [se_mod] gives one, [Prop] at [Type@0]
    ([sentry_exp]), so that interpretation commutes with substitution. *)
Definition set_entry_meaning (T : universe_tower) (e : set_entry) : set_meaning :=
  match e with
  | set_entry_term _ v t | set_entry_both v t _ => mk_set_meaning v t
  | set_entry_module _ => mk_set_meaning prop_universe_code (universe_zero_code T)
  end.

(** What an entry gives a module variable: its module, or at a term what
    the substitution's [se_exp] gives one, the empty unit at the empty path
    ([sentry_modexp]). *)
Definition set_entry_module_part (e : set_entry) : set_module :=
  match e with
  | set_entry_module m | set_entry_both _ _ m => m
  | set_entry_term _ _ _ => set_module_global (q_abs nil nil) nil
  end.
