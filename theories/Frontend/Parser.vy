%{

From Stdlib Require Import List Arith.PeanoNat String.

From Mctt Require Import Syntax.

Parameter loc : Type.

(** Fold a reversed parameter telescope into a binder chain.  [params]
    accumulates left-recursively, so [fold_left] restores declaration order. *)
Definition fold_params (b : string -> Cst.obj -> Cst.obj -> Cst.obj)
                       (ps : list (string * Cst.obj)) (body : Cst.obj) : Cst.obj :=
  List.fold_left (fun acc p => b (fst p) (snd p) acc) ps body.

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE ZERO LET IN (* keywords *)
%token <loc> TRUE_TY TRUE FALSE_TY EXFALSO (* unit and empty type keywords *)
%token <loc> MODULE WHERE DEF IMPORT AS USE PRIVATE ABSTRACT EVAL (* module keywords *)
%token <loc> ARROW "->" AT "@" BAR "|" COLON ":" COLONCOLON "::" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" DOT "." EQ ":=" SEMI ";" EOF (* symbols *)

%start <Cst.prog> prog
%type <Cst.obj> obj app_obj atomic_obj
%type <string * Cst.obj> param
%type <list (string * Cst.obj)> params params_opt
%type <string -> Cst.obj -> Cst.obj -> Cst.obj> fnbinder
%type <(string * Cst.obj) * Cst.obj> legacy_defn
%type <list ((string * Cst.obj) * Cst.obj)> legacy_defns
%type <Cst.decl> let_defn
%type <list Cst.decl> let_defns
%type <Cst.mods> mods
%type <list string> path fpath names
%type <(list string * list string)%type> qpath
%type <Cst.ispec> ispec
%type <Cst.cmd> cmd import_cmd
%type <list Cst.cmd> cmds imports

%on_error_reduce obj params params_opt app_obj atomic_obj cmds imports mods path fpath

%%

(* A unit is its imports and its module declaration, so definitions cannot
   appear at the top level. *)
let prog :=
  is = imports; MODULE; p = fpath; ps = params_opt; WHERE; cs = cmds; END; EOF;
    { (List.rev is, (List.rev p, List.rev ps, List.rev cs)) }

(* Reversed list of imports, possibly empty *)
let imports :=
  | { @nil Cst.cmd }
  | ~ = imports; ~ = import_cmd; { import_cmd :: imports }

(* Reversed list of commands, possibly empty *)
let cmds :=
  | { @nil Cst.cmd }
  | ~ = cmds; ~ = cmd; { cmd :: cmds }

let cmd :=
  | MODULE; p = path; ps = params_opt; WHERE; cs = cmds; END;
      { Cst.c_mod (List.rev p) (List.rev ps) (List.rev cs) }
  | m = mods; DEF; x = VAR; ps = params_opt; ":"; a = obj; ":="; b = obj; END;
      { Cst.c_def m (snd x) (fold_params Cst.pi ps a) (fold_params Cst.fn ps b) }
  | ~ = import_cmd; <>
  | EVAL; ~ = obj; { Cst.c_eval obj None }
  | EVAL; e = obj; ":"; t = obj; { Cst.c_eval e (Some t) }

let import_cmd :=
  | IMPORT; ~ = qpath; ~ = ispec; { Cst.c_import (fst qpath) (snd qpath) ispec }

let mods :=
  | { Cst.md_pub }
  | PRIVATE; { Cst.md_priv }
  | ABSTRACT; { Cst.md_abs }
  | PRIVATE; ABSTRACT; { Cst.md_priv_abs }

let ispec :=
  | { Cst.i_open }
  | AS; x = VAR; { Cst.i_as (snd x) }
  | USE; "("; ns = names; ")"; { Cst.i_use (List.rev ns) }

(* Reversed nonempty list of member names *)
let names :=
  | x = VAR; { [snd x] }
  | ~ = names; ";"; x = VAR; { snd x :: names }

(* Reversed nonempty dotted path: internal modules *)
let path :=
  | x = VAR; { [snd x] }
  | ~ = path; "."; x = VAR; { snd x :: path }

(* Reversed nonempty [::] path: a compilation unit *)
let fpath :=
  | x = VAR; { [snd x] }
  | ~ = fpath; "::"; x = VAR; { snd x :: fpath }

(* What an [import] names: an internal module, a unit, or a module of one *)
let qpath :=
  | ~ = path; { (@nil string, List.rev path) }
  | ~ = fpath; "::"; x = VAR; { (List.rev (snd x :: fpath), @nil string) }
  | ~ = fpath; "::"; x = VAR; "."; ~ = path;
      { (List.rev (snd x :: fpath), List.rev path) }

let fnbinder :=
  | PI; { Cst.pi }
  | LAMBDA; { Cst.fn }

let obj :=
  | ~ = fnbinder; ~ = params; "->"; ~ = obj; { fold_params fnbinder params obj }
  | ~ = app_obj; <>

  | REC; escr = obj; RETURN; mx = VAR; "."; em = obj;
    "|"; ZERO; "=>"; ez = obj;
    "|"; SUCC; sx = VAR; ","; sr = VAR; "=>"; ms = obj;
    END; { Cst.natrec escr (snd mx) em ez (snd sx) (snd sr) ms }
  | SUCC; ~ = obj; { Cst.succ obj }

  | EXFALSO; escr = obj; RETURN; mx = VAR; "."; em = obj;
    { Cst.exfalso escr (snd mx) em }

  (* A let of parenthesised bindings, which desugars to an application of a
     function. *)
  | LET; ds = legacy_defns; IN; body = obj; { List.fold_left (fun acc arg => Cst.app acc (snd arg)) (List.rev ds) (List.fold_left (fun acc arg => Cst.fn (fst (fst arg)) (snd (fst arg)) acc) ds body) }

  (* A let of declarations, each starting with DEF or MODULE, closed by END. *)
  | LET; ds = let_defns; IN; body = obj; END; { List.fold_left (fun acc d => Cst.letb d acc) ds body }


let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { Cst.app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  | TYPE; "@"; n = INT; { Cst.typ (snd n) }

  | NAT; { Cst.nat }
  | ZERO; { Cst.zero }
  | n = INT; { nat_rect (fun _ => Cst.obj) Cst.zero (fun _ => Cst.succ) (snd n) }

  | TRUE_TY; { Cst.true_ty }
  | TRUE; { Cst.true_tm }
  | FALSE_TY; { Cst.false_ty }

  | x = VAR; { Cst.var (snd x) }

  (* A unit, named by its [::] path.  Only the [.] level can be selected from,
     so the [::] segments are all consumed here. *)
  | ~ = fpath; "::"; x = VAR; { Cst.glob (List.rev (snd x :: fpath)) }

  (* Dot access binds tighter than application, so [X::Y.Z.foo] is one name
     and module arguments are parenthesised, as in [(X::Y.Z a b).foo]. *)
  | ~ = atomic_obj; "."; x = VAR; { Cst.proj atomic_obj (snd x) }

  | "("; ~ = obj; ")"; <>

(* Reversed nonempty list of parameters *)
let params :=
  | ~ = params; ~ = param; { param :: params }
  | ~ = param; { [param] }

let params_opt :=
  | { @nil (string * Cst.obj) }
  | ~ = params; <>

(* (x : A) *)
let param :=
  | "("; x = VAR; ":"; ~ = obj; ")"; { (snd x, obj) }

(* Reversed nonempty list of parenthesised definitions *)
let legacy_defns :=
  | ~ = legacy_defns; ~ = legacy_defn; { legacy_defn :: legacy_defns }
  | ~ = legacy_defn; { [legacy_defn] }

(* ((x : A) := t) *)
let legacy_defn :=
  | "("; ~ = param; ":="; ~ = obj; ")"; { (param, obj) }

(* Reversed nonempty list of declarations *)
let let_defns :=
  | ~ = let_defns; ~ = let_defn; { let_defn :: let_defns }
  | ~ = let_defn; { [let_defn] }

let let_defn :=
  | DEF; x = VAR; ps = params_opt; ":"; a = obj; ":="; b = obj;
      { Cst.d_def Cst.md_pub (snd x) (fold_params Cst.pi ps a) (fold_params Cst.fn ps b) }
  | MODULE; x = VAR; ":="; ~ = obj; { Cst.d_mod (snd x) obj }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
