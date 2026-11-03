(** * The User Syntax

    The syntax after name resolution (level-1 elaboration), before the typed
    pass (level-2 elaboration, [TypedElab]) fills it into the core syntax
    ([Syntax]).  It holds what a user writes and nothing else: names are
    resolved to de Bruijn indices and paths, but no relevance tag, no
    eliminator group, no inferred annotation is present.  Where a user may
    omit an annotation the syntax has a hole ([u_hole]), which the typed
    pass fills; a term followed by a field name ([u_proj_term]) is resolved
    there too, once the term's type is known.

    The core syntax keeps every annotation explicit; the typed pass maps
    each user term to exactly one core term. *)

From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax.

(** ** Terms, Module Expressions and Units *)

Inductive uexp : Set :=
(** A large universe [Typeω@n] *)
| u_typ : nat -> uexp
(** A small universe at a level, [Type@{t}] *)
| u_univ : uexp -> uexp
(** The type of levels [Level@n] *)
| u_level : nat -> uexp
(** A level literal [ω·a + b] *)
| u_llit : o2 -> uexp
(** The successor of a level *)
| u_succl : uexp -> uexp
(** The join of two levels *)
| u_maxl : uexp -> uexp -> uexp
(** The token [ℕ], the type bound by [builtin natural]; the typed pass
    replaces it by the bound type's former *)
| u_ntok : uexp
(** A numeral; the typed pass replaces it by the chain of the bound type's
    constructors *)
| u_nlit : nat -> uexp
(** [Prop] *)
| u_prop : uexp
(** [⊤] *)
| u_True : uexp
(** The introduction of [⊤] *)
| u_tt : uexp
(** [⊥] *)
| u_False : uexp
(** [u_absurd C M]: ex falso, the proof [M] of [⊥] into [C] *)
| u_absurd : uexp -> uexp -> uexp
(** [u_and P Q]: the conjunction, [Q] binding a proof of [P] *)
| u_and : uexp -> uexp -> uexp
(** [u_conj P Q M N]: the proof of the conjunction of [P] and [Q] (under
    a binder of [P]) from [M] and [N]; [Q] is [u_hole] when omitted, as in
    [conj (m : P) n] *)
| u_conj : uexp -> uexp -> uexp -> uexp -> uexp
(** The first component of a proof of a conjunction *)
| u_left : uexp -> uexp
(** Its second component *)
| u_right : uexp -> uexp
(** [u_pi A B], [B] binding the argument; its sort is not written *)
| u_pi : uexp -> uexp -> uexp
(** [u_fn A M], [M] binding the argument *)
| u_fn : uexp -> uexp -> uexp
(** Application *)
| u_app : uexp -> uexp -> uexp
(** A variable *)
| u_var : nat -> uexp
(** [u_let b B]: [B] under the local binding [b] *)
| u_let : ubinding -> uexp -> uexp
(** The member [x] of the module [H] *)
| u_mem : umodexp -> string -> uexp
(** [t.x] for a term [t]: the field or member [x] of [t]'s record type,
    resolved by the typed pass once [t]'s type is inferred *)
| u_proj_term : uexp -> string -> uexp
(** [u_elim m Bks M]: the eliminator of [M], of the member [m] of its
    group, by the blocks [Bks], one per member in order; the group, its
    uniform parameters and the motives' sort are not written *)
| u_elim : nat -> list ublock -> uexp -> uexp
(** [u_tuple T fs]: the element of the record type [T] with the fields
    [fs], by name *)
| u_tuple : uexp -> list (string * uexp) -> uexp
(** An omitted annotation, which the typed pass fills *)
| u_hole : uexp
with ublock : Set :=
(** [u_eb_mk nm Z A Bs]: an eliminator block whose motive [A] binds [nm]
    variables (the non-uniform parameters and the scrutinee), the
    scrutinee's type [Z] as written ([u_hole] if omitted), and the
    branches, each a constructor, its number of binders and its body *)
| u_eb_mk : nat -> uexp -> uexp -> list (string * nat * uexp) -> ublock
with umodexp : Set :=
(** A unit, by its path *)
| u_me_unit : path -> umodexp
(** A local module slot *)
| u_me_var : nat -> umodexp
(** A submodule *)
| u_me_mem : umodexp -> string -> umodexp
(** A module applied to an argument *)
| u_me_app : umodexp -> uexp -> umodexp
with ubinding : Set :=
(** [u_b_def A M]: a local definition of [M], at [A] ([u_hole] when the
    type is not written) *)
| u_b_def : uexp -> uexp -> ubinding
(** [u_b_mod U]: a local module *)
| u_b_mod : uunit -> ubinding
with uunit : Set :=
(** [u_gu_mk Δ D]: the parameters, assumptions, innermost first, and the
    definition under them *)
| u_gu_mk : list uexp -> umoddef -> uunit
with umoddef : Set :=
(** A body *)
| u_md_body : ubody -> umoddef
(** An alias of a module expression *)
| u_md_alias : umodexp -> umoddef
with ubody : Set :=
(** The empty body *)
| u_gm_nil : ubody
(** A named entry after the body before it *)
| u_gm_ext : ubody -> string -> uentry -> ubody
(** [u_gm_open Φ H its]: an open of [H] declaring the items [its]; the
    core's open phase expands it *)
| u_gm_open : ubody -> umodexp -> list import_item -> ubody
with uentry : Set :=
(** [u_ge_def b pv A oM]: a definition, transparent when [b], private when
    [pv], of the type [A], with the body [oM] ([None] for an axiom); its
    sort is not written *)
| u_ge_def : bool -> bool -> uexp -> option uexp -> uentry
(** [u_ge_mod pv U]: a submodule *)
| u_ge_mod : bool -> uunit -> uentry.

(** ** Commands *)

(** A member of a group of inductive types as written: its name, its
    non-uniform parameters (assumptions, innermost first), its sort, and
    its constructors, each with its named arguments, outermost first. *)
Record uraw_member : Set := mk_urmem
  { (** The member's name *)
    uraw_member_name : string
    (** Its non-uniform parameters, innermost first *)
  ; uraw_member_nparams : list uexp
    (** Its sort, over the uniform parameters *)
  ; uraw_member_sort : uexp
    (** Its constructors, each with its named arguments *)
  ; uraw_member_cons : list (string * list (string * uexp)) }.

(** A group as written. *)
Record uraw_decl : Set := mk_uraw
  { (** The group's own uniform parameters, innermost first *)
    uraw_decl_uparams : list uexp
    (** The declared members, in order *)
  ; uraw_decl_members : list uraw_member
    (** Whether the group files its recursor module [Rec] *)
  ; uraw_decl_rec_field : bool }.

(** A function of a [mutual def] as written. *)
Record uraw_fun : Set := mk_urfun
  { (** The function's name *)
    uraw_fun_name : string
    (** Its non-uniform parameters, innermost first *)
  ; uraw_fun_nparams : list uexp
    (** The scrutinee's type *)
  ; uraw_fun_scrut : uexp
    (** The result type *)
  ; uraw_fun_res : uexp
    (** The clauses: constructor name, number of binders, body *)
  ; uraw_fun_clauses : list (string * nat * uexp) }.

Inductive ucmd : Set :=
(** [def x : A := M] or [axiom x : A]: transparency, privacy, type, body *)
| u_cmd_def : string -> bool -> bool -> uexp -> option uexp -> ucmd
(** [module x (Δ) where cs end] *)
| u_cmd_mod : string -> bool -> list uexp -> list ucmd -> ucmd
(** [module x (Δ) := E] *)
| u_cmd_alias : string -> bool -> list uexp -> umodexp -> ucmd
(** [import fp]: load the unit [fp] *)
| u_cmd_load : path -> ucmd
(** [open E its] *)
| u_cmd_open : umodexp -> list import_item -> ucmd
(** [eval M : A], [A] being [u_hole] when not written *)
| u_cmd_eval : uexp -> uexp -> ucmd
(** [inductive …] *)
| u_cmd_inductive : bool -> uraw_decl -> ucmd
(** [mutual def (Δ) f … with g … end], abstract and private or not *)
| u_cmd_mdef : bool -> bool -> list uexp -> list uraw_fun -> ucmd
(** [builtin k := X] *)
| u_cmd_builtin : string -> umodexp -> ucmd
(** [inductive x (Δ) := X] *)
| u_cmd_inductive_alias : string -> bool -> list uexp -> umodexp -> ucmd
(** [record x (Δ) := X] *)
| u_cmd_record_alias : string -> bool -> list uexp -> umodexp -> ucmd
(** [record x (Δ) : S where f : T ; … with cs end] *)
| u_cmd_record : string -> bool -> list uexp -> uexp -> list (string * uexp) -> list ucmd -> ucmd.

(** A unit as written: its leading imports, its parameters (innermost
    first), its body. *)
Definition user_unit : Set := (list ucmd * list uexp * list ucmd)%type.
