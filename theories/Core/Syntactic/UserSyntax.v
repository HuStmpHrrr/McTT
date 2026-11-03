(** * The User Syntax

    The syntax after name resolution (level-1 elaboration), before the typed
    pass (level-2 elaboration, [TypedElab]) fills it into the core syntax
    ([Syntax]).  It holds what a user writes and nothing else: names are
    resolved to de Bruijn indices and paths, but no relevance tag, no
    eliminator group, no inferred annotation is present.  Where a user may
    omit an annotation the syntax has a hole ([surface_hole]), which the typed
    pass fills; a term followed by a field name ([surface_proj_term]) is resolved
    there too, once the term's type is known.

    The core syntax keeps every annotation explicit; the typed pass maps
    each user term to exactly one core term. *)

From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax.

(** ** Terms, Module Expressions and Units *)

Inductive surface_exp : Set :=
(** A large universe [Typeω@n] *)
| surface_typ : nat -> surface_exp
(** A small universe at a level, [Type@{t}] *)
| surface_univ : surface_exp -> surface_exp
(** The type of levels [Level@n] *)
| surface_level : nat -> surface_exp
(** A level literal [ω·a + b] *)
| surface_llit : o2 -> surface_exp
(** The successor of a level *)
| surface_succl : surface_exp -> surface_exp
(** The join of two levels *)
| surface_maxl : surface_exp -> surface_exp -> surface_exp
(** The token [ℕ], the type bound by [builtin natural]; the typed pass
    replaces it by the bound type's former *)
| surface_ntok : surface_exp
(** A numeral; the typed pass replaces it by the chain of the bound type's
    constructors *)
| surface_nlit : nat -> surface_exp
(** [Prop] *)
| surface_prop : surface_exp
(** [⊤] *)
| surface_True : surface_exp
(** The introduction of [⊤] *)
| surface_tt : surface_exp
(** [⊥] *)
| surface_False : surface_exp
(** [surface_absurd C M]: ex falso, the proof [M] of [⊥] into [C] *)
| surface_absurd : surface_exp -> surface_exp -> surface_exp
(** [surface_and P Q]: the conjunction, [Q] binding a proof of [P] *)
| surface_and : surface_exp -> surface_exp -> surface_exp
(** [surface_conj P Q M N]: the proof of the conjunction of [P] and [Q] (under
    a binder of [P]) from [M] and [N]; [Q] is [surface_hole] when omitted, as in
    [conj (m : P) n] *)
| surface_conj : surface_exp -> surface_exp -> surface_exp -> surface_exp -> surface_exp
(** The first component of a proof of a conjunction *)
| surface_left : surface_exp -> surface_exp
(** Its second component *)
| surface_right : surface_exp -> surface_exp
(** [surface_pi A B], [B] binding the argument; its sort is not written *)
| surface_pi : surface_exp -> surface_exp -> surface_exp
(** [surface_fn A M], [M] binding the argument *)
| surface_fn : surface_exp -> surface_exp -> surface_exp
(** Application *)
| surface_app : surface_exp -> surface_exp -> surface_exp
(** A variable *)
| surface_var : nat -> surface_exp
(** [surface_let b B]: [B] under the local binding [b] *)
| surface_let : surface_binding -> surface_exp -> surface_exp
(** The member [x] of the module [H] *)
| surface_mem : surface_modexp -> string -> surface_exp
(** [t.x] for a term [t]: the field or member [x] of [t]'s record type,
    resolved by the typed pass once [t]'s type is inferred *)
| surface_proj_term : surface_exp -> string -> surface_exp
(** [surface_elim m Bks M]: the eliminator of [M], of the member [m] of its
    group, by the blocks [Bks], one per member in order; the group, its
    uniform parameters and the motives' sort are not written *)
| surface_elim : nat -> list surface_block -> surface_exp -> surface_exp
(** [surface_tuple T fs]: the element of the record type [T] with the fields
    [fs], by name *)
| surface_tuple : surface_exp -> list (string * surface_exp) -> surface_exp
(** An omitted annotation, which the typed pass fills *)
| surface_hole : surface_exp
with surface_block : Set :=
(** [surface_eb_mk nm Z A Bs]: an eliminator block whose motive [A] binds [nm]
    variables (the non-uniform parameters and the scrutinee), the
    scrutinee's type [Z] as written ([surface_hole] if omitted), and the
    branches, each a constructor, its number of binders and its body *)
| surface_eb_mk : nat -> surface_exp -> surface_exp -> list (string * nat * surface_exp) -> surface_block
with surface_modexp : Set :=
(** A unit, by its path *)
| surface_me_unit : path -> surface_modexp
(** A local module slot *)
| surface_me_var : nat -> surface_modexp
(** A submodule *)
| surface_me_mem : surface_modexp -> string -> surface_modexp
(** A module applied to an argument *)
| surface_me_app : surface_modexp -> surface_exp -> surface_modexp
with surface_binding : Set :=
(** [surface_b_def A M]: a local definition of [M], at [A] ([surface_hole] when the
    type is not written) *)
| surface_b_def : surface_exp -> surface_exp -> surface_binding
(** [surface_b_mod U]: a local module *)
| surface_b_mod : surface_unit -> surface_binding
with surface_unit : Set :=
(** [surface_gu_mk Δ D]: the parameters, assumptions, innermost first, and the
    definition under them *)
| surface_gu_mk : list surface_exp -> surface_moddef -> surface_unit
with surface_moddef : Set :=
(** A body *)
| surface_md_body : surface_body -> surface_moddef
(** An alias of a module expression *)
| surface_md_alias : surface_modexp -> surface_moddef
with surface_body : Set :=
(** The empty body *)
| surface_gm_nil : surface_body
(** A named entry after the body before it *)
| surface_gm_ext : surface_body -> string -> surface_entry -> surface_body
(** [surface_gm_open Φ H its]: an open of [H] declaring the items [its]; the
    core's open phase expands it *)
| surface_gm_open : surface_body -> surface_modexp -> list import_item -> surface_body
with surface_entry : Set :=
(** [surface_ge_def b pv A oM]: a definition, transparent when [b], private when
    [pv], of the type [A], with the body [oM] ([None] for an axiom); its
    sort is not written *)
| surface_ge_def : bool -> bool -> surface_exp -> option surface_exp -> surface_entry
(** [surface_ge_mod pv U]: a submodule *)
| surface_ge_mod : bool -> surface_unit -> surface_entry.

(** ** Commands *)

(** A member of a group of inductive types as written: its name, its
    non-uniform parameters (assumptions, innermost first), its sort, and
    its constructors, each with its named arguments, outermost first. *)
Record surface_raw_member : Set := mk_surface_raw_member
  { (** The member's name *)
    surface_raw_member_name : string
    (** Its non-uniform parameters, innermost first *)
  ; surface_raw_member_nparams : list surface_exp
    (** Its sort, over the uniform parameters *)
  ; surface_raw_member_sort : surface_exp
    (** Its constructors, each with its named arguments *)
  ; surface_raw_member_cons : list (string * list (string * surface_exp)) }.

(** A group as written. *)
Record surface_raw_decl : Set := mk_surface_raw_decl
  { (** The group's own uniform parameters, innermost first *)
    surface_raw_decl_uparams : list surface_exp
    (** The declared members, in order *)
  ; surface_raw_decl_members : list surface_raw_member
    (** Whether the group files its recursor module [Rec] *)
  ; surface_raw_decl_rec_field : bool }.

(** A function of a [mutual def] as written. *)
Record surface_raw_fun : Set := mk_surface_raw_fun
  { (** The function's name *)
    surface_raw_fun_name : string
    (** Its non-uniform parameters, innermost first *)
  ; surface_raw_fun_nparams : list surface_exp
    (** The scrutinee's type *)
  ; surface_raw_fun_scrut : surface_exp
    (** The result type *)
  ; surface_raw_fun_res : surface_exp
    (** The clauses: constructor name, number of binders, body *)
  ; surface_raw_fun_clauses : list (string * nat * surface_exp) }.

Inductive surface_cmd : Set :=
(** [def x : A := M] or [axiom x : A]: transparency, privacy, type, body *)
| surface_cmd_def : string -> bool -> bool -> surface_exp -> option surface_exp -> surface_cmd
(** [module x (Δ) where cs end] *)
| surface_cmd_mod : string -> bool -> list surface_exp -> list surface_cmd -> surface_cmd
(** [module x (Δ) := E] *)
| surface_cmd_alias : string -> bool -> list surface_exp -> surface_modexp -> surface_cmd
(** [import fp]: load the unit [fp] *)
| surface_cmd_load : path -> surface_cmd
(** [open E its] *)
| surface_cmd_open : surface_modexp -> list import_item -> surface_cmd
(** [eval M : A], [A] being [surface_hole] when not written *)
| surface_cmd_eval : surface_exp -> surface_exp -> surface_cmd
(** [inductive …] *)
| surface_cmd_inductive : bool -> surface_raw_decl -> surface_cmd
(** [mutual def (Δ) f … with g … end], abstract and private or not *)
| surface_cmd_mdef : bool -> bool -> list surface_exp -> list surface_raw_fun -> surface_cmd
(** [builtin k := X] *)
| surface_cmd_builtin : string -> surface_modexp -> surface_cmd
(** [inductive x (Δ) := X] *)
| surface_cmd_inductive_alias : string -> bool -> list surface_exp -> surface_modexp -> surface_cmd
(** [record x (Δ) := X] *)
| surface_cmd_record_alias : string -> bool -> list surface_exp -> surface_modexp -> surface_cmd
(** [record x (Δ) : S where f : T ; … with cs end] *)
| surface_cmd_record : string -> bool -> list surface_exp -> surface_exp -> list (string * surface_exp) -> list surface_cmd -> surface_cmd.

(** A unit as written: its leading imports, its parameters (innermost
    first), its body. *)
Definition surface_compilation_unit : Set := (list surface_cmd * list surface_exp * list surface_cmd)%type.
