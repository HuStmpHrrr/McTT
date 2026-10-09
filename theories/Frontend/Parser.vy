%{

From Stdlib Require Import List Arith.PeanoNat String.

From Mctt Require Import Syntax.

Parameter loc : Type.

(** Fold a reversed parameter telescope into a binder chain.  [params]
    accumulates left-recursively, so [fold_left] restores declaration order. *)
Definition fold_params (b : string -> Cst.obj -> Cst.obj -> Cst.obj)
                       (ps : list (string * Cst.obj)) (body : Cst.obj) : Cst.obj :=
  List.fold_left (fun acc p => b (fst p) (snd p) acc) ps body.

(** A dotted path as a list, in order. *)
Definition path_list (p : string * list string) : list string := List.rev (fst p :: snd p).

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE ZERO LET IN (* keywords *)
%token <loc> LEVEL SUCCL MAXL (* universe levels *)
%token <loc*nat> LLIT (* a level literal, [<n>l] *)
%token <loc*nat> LLITL (* a level literal, [<n>L] for [ω+n] *)
%token <loc> OMEGA (* the ordinal ω, written [ω] or [omega] *)
%token <loc> OMEGA2 (* [ω^2], written [ω^2] or [omega^2]; not a level *)
%token <loc> TRUE_TY TRUE FALSE_TY EXFALSO (* unit and empty type keywords *)
%token <loc> MODULE WHERE DEF IMPORT OPEN AS USE EXPORT PRIVATE ABSTRACT EVAL (* module keywords *)
%token <loc> THEOREM LEMMA FACT REMARK GIVEN AXIOM (* definition keywords; [let] is [LET] *)
%token <loc> ARROW "->" AT "@" BAR "|" COLON ":" COLONCOLON "::" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}" PLUS "+" STAR "*" DOT "." EQ ":=" SEMI ";" EOF (* symbols *)

%start <Cst.prog> prog
%type <Cst.obj> obj app_obj atomic_obj
%type <string * Cst.obj> param
%type <list (string * Cst.obj)> params params_opt
%type <string -> Cst.obj -> Cst.obj -> Cst.obj> fnbinder
%type <Cst.decl> let_defn
%type <list Cst.decl> let_defns
%type <Cst.mods> mods
%type <Cst.dkw> dkw
%type <(string * list string)%type> path
%type <list string> fpath upath mpath_opt
%type <string * string> item
%type <list (string * string)> items
%type <list Cst.obj> iargs
%type <(list string * list string)%type> qpath
%type <option string> as_opt
%type <list iitem> ilists ilist
%type <list Cst.cmd> cmd lead_cmd import_cmd open_cmd
%type <(list (string * Cst.obj) * Cst.mdef)%type> mdecl
%type <Cst.mdef> mdef
%type <list Cst.cmd> cmds leads

%on_error_reduce obj params params_opt app_obj atomic_obj cmds leads mods path fpath

%%

(* A unit is its leading imports and opens and its module declaration, so
   definitions cannot appear at the top level. *)
let prog :=
  is = leads; MODULE; p = fpath; ps = params_opt; WHERE; cs = cmds; END; EOF;
    { (List.rev is, (List.rev p, List.rev ps, List.rev cs)) }

(* Reversed list of leading imports and opens, possibly empty *)
let leads :=
  | { @nil Cst.cmd }
  | ~ = leads; ~ = lead_cmd; { List.rev_append lead_cmd leads }

(* Before the header, a list may only [use]: [Cst.lead_cmds] rejects an
   [export]. *)
let lead_cmd :=
  | ~ = import_cmd; { Cst.lead_cmds import_cmd }
  | ~ = open_cmd; { Cst.lead_cmds open_cmd }

(* Reversed list of commands, possibly empty.  A command may stand for
   several: the long form of [import] is an [import] and an [open]. *)
let cmds :=
  | { @nil Cst.cmd }
  | ~ = cmds; ~ = cmd; { List.rev_append cmd cmds }

let cmd :=
  | MODULE; p = path; md = mdecl; { [Cst.c_mod_dotted false (fst p) (snd p) (fst md) (snd md)] }
  | PRIVATE; MODULE; p = path; md = mdecl; { [Cst.c_mod_dotted true (fst p) (snd p) (fst md) (snd md)] }
  (* [def] and its shorthands share one production, so they take the same
     parameters, type and body; the keyword decides which modifiers it takes. *)
  | m = mods; k = dkw; x = VAR; ps = params_opt; ":"; a = obj; ":="; b = obj; END;
      { [Cst.def_cmd k m (snd x) (fold_params Cst.pi ps a) (fold_params Cst.fn ps b)] }
  (* An axiom has [def]'s parameters and type, and no body. *)
  | m = mods; AXIOM; x = VAR; ps = params_opt; ":"; a = obj;
      { [Cst.axiom_cmd m (snd x) (fold_params Cst.pi ps a)] }
  | ~ = import_cmd; <>
  | ~ = open_cmd; <>
  | EVAL; ~ = obj; { [Cst.c_eval obj None] }
  | EVAL; e = obj; ":"; t = obj; { [Cst.c_eval e (Some t)] }

(* A module declaration, at the top level or in a [let]: its parameters, and
   a body or an alias. *)
let mdecl :=
  | ps = params_opt; d = mdef; { (List.rev ps, d) }

let mdef :=
  | WHERE; cs = cmds; END; { Cst.md_where (List.rev cs) }
  | ":="; ~ = obj; { Cst.md_alias obj }

(* The definition keywords.  At command level, [let] is one of them. *)
let dkw :=
  | DEF; { Cst.dk_def }
  | THEOREM; { Cst.dk_theorem }
  | LEMMA; { Cst.dk_lemma }
  | FACT; { Cst.dk_fact }
  | REMARK; { Cst.dk_remark }
  | LET; { Cst.dk_let }
  | GIVEN; { Cst.dk_given }

(* [import X::Y] loads a unit.  Anything after the unit's path makes it the
   long form, [import X::Y] then [open X::Y.ip a1 .. ak as W items]. *)
let import_cmd :=
  | IMPORT; u = upath; m = mpath_opt; xs = iargs; w = as_opt; ls = ilists;
      { Cst.import_cmds u m (List.rev xs) w (List.rev ls) }

(* [open E as W items]: a module in scope or of an imported unit, applied to
   atomic arguments, then an alias and any number of item lists, all
   optional. *)
let open_cmd :=
  | OPEN; q = qpath; xs = iargs; w = as_opt; ls = ilists;
      { Cst.open_cmds (fst q) (snd q) (List.rev xs) w (List.rev ls) }

(* Reversed list of the arguments of an import or open, possibly empty *)
let iargs :=
  | { @nil Cst.obj }
  | ~ = iargs; ~ = atomic_obj; { atomic_obj :: iargs }

let mods :=
  | { Cst.md_pub }
  | PRIVATE; { Cst.md_priv }
  | ABSTRACT; { Cst.md_abs }
  | PRIVATE; ABSTRACT; { Cst.md_priv_abs }
  | ABSTRACT; PRIVATE; { Cst.md_priv_abs }

let as_opt :=
  | { None }
  | AS; x = VAR; { Some (snd x) }

(* Reversed list of the items of the [use] and [export] lists so far, in any
   order *)
let ilists :=
  | { @nil iitem }
  | ls = ilists; l = ilist; { l ++ ls }

(* One list, its items reversed: private for [use], public for [export] *)
let ilist :=
  | USE; "("; us = items; ")"; { List.map (fun p => (Some (fst p), snd p, true)) us }
  | EXPORT; "("; es = items; ")"; { List.map (fun p => (Some (fst p), snd p, false)) es }

(* Reversed nonempty list of items: a member, and the name it is declared as *)
let items :=
  | ~ = item; { [item] }
  | ~ = items; ";"; ~ = item; { item :: items }

let item :=
  | x = VAR; { (snd x, snd x) }
  | x = VAR; AS; y = VAR; { (snd x, snd y) }

(* Nonempty dotted path: internal modules.  Its last segment, and the
   segments before it reversed. *)
let path :=
  | x = VAR; { (snd x, @nil string) }
  | ~ = path; "."; x = VAR; { (snd x, fst path :: snd path) }

(* Reversed nonempty [::] path: a compilation unit *)
let fpath :=
  | x = VAR; { [snd x] }
  | ~ = fpath; "::"; x = VAR; { snd x :: fpath }

(* The unit an [import] names, in order *)
let upath :=
  | ~ = fpath; "::"; x = VAR; { List.rev (snd x :: fpath) }

(* The member path after it, possibly empty, in order *)
let mpath_opt :=
  | { @nil string }
  | "."; ~ = path; { path_list path }

(* What an [open] names: a module in scope, a unit, or a module of one *)
let qpath :=
  | ~ = path; { (@nil string, path_list path) }
  | ~ = upath; ~ = mpath_opt; { (upath, mpath_opt) }

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

  (* The level operations take atomic arguments, so that [maxl u v] is their
     join and not [maxl (u v)]. *)
  | SUCCL; m = atomic_obj; { Cst.succl m }
  | MAXL; m = atomic_obj; n = atomic_obj; { Cst.maxl m n }

  | EXFALSO; escr = obj; RETURN; mx = VAR; "."; em = obj;
    { Cst.exfalso escr (snd mx) em }

  (* [let x : A := a; y := b in body end].  The bindings fold into nested
     [letb]s, so each one sees the earlier ones. *)
  | LET; ds = let_defns; IN; body = obj; END; { List.fold_left (fun acc d => Cst.letb d acc) ds body }


let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { Cst.app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  (* A universe is written [Type@] its level: any level term in braces, or
     one of the short forms, a numeral [n] or [<n>l] for the finite level
     [n], [ω] (also spelled [omega]) for [ω], and [<n>L] for [ω+n].  Only
     the braced form admits an ordinal literal with [+] or [*]. *)
  | TYPE; "@"; n = INT; { Cst.suniv (Cst.llit (0, snd n)) }
  | TYPE; "@"; n = LLIT; { Cst.suniv (Cst.llit (0, snd n)) }
  | TYPE; "@"; "{"; m = obj; "}"; { Cst.suniv m }
  | TYPE; "@"; n = LLITL; { Cst.suniv (Cst.llit (1, snd n)) }
  | TYPE; "@"; OMEGA; { Cst.suniv (Cst.llit (1, 0)) }
  (* The large universes, above every small one: [Type@{ω^2}] and
     [Type@{ω^2+i}], the universe at [ω²+i].  [ω^2] is not a level (every
     level is below it), so it is written only here, in braces. *)
  | TYPE; "@"; "{"; OMEGA2; "}"; { Cst.typ 0 }
  | TYPE; "@"; "{"; OMEGA2; "+"; i = INT; "}"; { Cst.typ (snd i) }

  (* [Level@n] is the type of the levels below [ω·(n+1)], and [Level] is
     [Level@0], the finite levels. *)
  | LEVEL; { Cst.level 0 }
  | LEVEL; "@"; n = INT; { Cst.level (snd n) }
  | n = LLIT; { Cst.llit (0, snd n) }
  (* [<n>L] is the level [ω+n], the same literal as [ω + n]. *)
  | n = LLITL; { Cst.llit (1, snd n) }
  (* An ordinal level literal [ω·a + b]: [ω], [ω + b], [ω * a] and
     [ω * a + b] ([·] is the Unicode spelling of [*]). *)
  | OMEGA; { Cst.llit (1, 0) }
  | OMEGA; "+"; b = INT; { Cst.llit (1, snd b) }
  | OMEGA; "*"; a = INT; { Cst.llit (snd a, 0) }
  | OMEGA; "*"; a = INT; "+"; b = INT; { Cst.llit (snd a, snd b) }

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

(* Reversed nonempty list of [;]-separated bindings *)
let let_defns :=
  | ~ = let_defns; ";"; ~ = let_defn; { let_defn :: let_defns }
  | ~ = let_defn; { [let_defn] }

(* [x : A := a] or [x := a], or a local module [module X (ps) where … end] or
   [module X (ps) := E] *)
let let_defn :=
  | x = VAR; ":"; a = obj; ":="; b = obj; { Cst.d_def (snd x) (Some a) b }
  | x = VAR; ":="; b = obj; { Cst.d_def (snd x) None b }
  | MODULE; x = VAR; md = mdecl; { Cst.d_mod (snd x) (fst md) (snd md) }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
