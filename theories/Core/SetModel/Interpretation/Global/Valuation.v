(** * The Valuation of a Global Context

    What the globals of a global context denote, as semantic data only:
    the value of each term entry, the module of each module entry, and the
    semantics of each group of inductive types and of each record type.
    The interpretation of terms reads globals only through a valuation;
    [Judgments.v] states when a valuation is one of a global context
    ([set_gctx_ok]). *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Interpretation Require Export Values Codes.
From Mctt.Core.Syntactic Require Import Syntax.

(** ** Groups of Inductive Types *)

(** A constructor argument, its types read off the values of the
    parameters (uniform, then non-uniform) and of the arguments before it,
    outermost first. *)
Inductive set_argument : Type :=
(** A non-recursive argument of the kind [κ] and the type code [type] *)
| set_argument_plain (κ : abs_kind) (type : list aczel_set -> aczel_set)
(** A recursive argument of the type code [type]: a function over the
    [domains] (each read off the values before it and the earlier domains'
    points) into the member [target] at the parameters [target_params].
    The eliminator reads its recursive results off the declaration, as
    evaluation does ([eval_ih]) *)
| set_argument_recursive (type : list aczel_set -> aczel_set) (domains : list (list aczel_set -> aczel_set))
    (target : nat) (target_params : list aczel_set -> list aczel_set).

(** A constructor: its name and its arguments, in order. *)
Record set_constructor : Type := mk_set_constructor
  { (** The constructor's name *)
    set_constructor_name : string
    (** Its arguments, outermost first *)
  ; set_constructor_arguments : list set_argument }.

(** A member of a group. *)
Record set_member : Type := mk_set_member
  { (** The types of its non-uniform parameters, each read off the uniform
        parameters and the non-uniform ones before it *)
    set_member_nparam_types : list (list aczel_set -> aczel_set)
    (** Its constructors, in order *)
  ; set_member_constructors : list set_constructor
    (** At a record view, the record's field names: its one constructor is
        the tuple of the fields *)
  ; set_member_record_fields : option (list string) }.

(** A group of inductive types. *)
Record set_group : Type := mk_set_group
  { (** The types of the uniform parameters, each read off those before it *)
    set_group_uniform_types : list (list aczel_set -> aczel_set)
    (** The members, the declared types then the views *)
  ; set_group_members : list set_member
    (** The carrier of the member [k] at the values of all its parameters,
        uniform then non-uniform *)
  ; set_group_carrier : nat -> list aczel_set -> aczel_set }.

(** ** Record Types *)

(** A record type. *)
Record set_record : Type := mk_set_record
  { (** The types of its parameters, each read off those before it *)
    set_record_param_types : list (list aczel_set -> aczel_set)
    (** Its field names, in order *)
  ; set_record_field_names : list string
    (** The type of each field, read off the parameters and the fields
        before it *)
  ; set_record_field_types : list (list aczel_set -> aczel_set)
    (** The carrier at the values of the parameters *)
  ; set_record_carrier : list aczel_set -> aczel_set }.

(** ** Valuations *)

(** What the globals denote. *)
Record global_valuation : Type := mk_global_valuation
  { (** The closed value of the term entry at a path, over the parameters
        of the modules enclosing it, and its kind *)
    global_term : qname -> abs_kind * aczel_set
    (** The closed module of the module entry at a path: a body is the
        global module at its path, an alias its target's module *)
  ; global_module : qname -> set_module
    (** The type former of the member [k] of the group at [p] *)
  ; global_former : qname -> nat -> aczel_set
    (** The constructor [c] of the member [k] of the group at [p] *)
  ; global_constructor : qname -> nat -> string -> aczel_set
    (** The semantics of the group at [p] *)
  ; global_group : qname -> set_group
    (** The type former of the record type at [p] *)
  ; global_record_former : qname -> aczel_set
    (** The semantics of the record type at [p] *)
  ; global_record : qname -> set_record
    (** Whether the member [x] of the module at the path [q] is a proof:
        what a global module's table reads at its term members, fixed
        once for the whole context *)
  ; global_proofs : qname -> string -> bool }.
