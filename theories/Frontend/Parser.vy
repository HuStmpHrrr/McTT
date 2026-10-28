%{

From Stdlib Require Import List Arith.PeanoNat String.

From Mctt.Core.Syntactic Require Import Syntax.

Parameter loc : Type.

(** Fold a reversed parameter telescope into a binder chain.  [params]
    accumulates left-recursively, so [fold_left] restores declaration order. *)
Definition fold_params (b : string -> Cst.expression -> Cst.expression -> Cst.expression)
                       (ps : list (string * Cst.expression)) (body : Cst.expression) : Cst.expression :=
  List.fold_left (fun acc p => b (fst p) (snd p) acc) ps body.

(** A dotted path as a list, in order. *)
Definition path_list (p : string * list string) : list string := List.rev (fst p :: snd p).

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI RETURN TYPE LET IN (* keywords *)
%token <loc> LEVEL SUCCL MAXL (* universe levels *)
%token <loc*nat> LLIT (* a level literal, [<n>l] *)
%token <loc*nat> LLITL (* a level literal, [<n>L] for [ω+n] *)
%token <loc> OMEGA (* the ordinal ω, written [ω] or [omega] *)
%token <loc> OMEGA2 (* [ω^2], written [ω^2] or [omega^2]; not a level *)
%token <loc> TRUE_TY TRUE FALSE_TY EXFALSO (* unit and empty type keywords *)
%token <loc> MODULE WHERE DEF IMPORT OPEN AS USE EXPORT PRIVATE ABSTRACT EVAL (* module keywords *)
%token <loc> INDUCTIVE ELIM BUILTIN (* inductive types *)
%token <loc> RECORD (* record types and their values *)
%token <loc> MUTUAL WITH BLOCK_AT (* groups: [mutual], [with], and [at], which marks the scrutinee's block *)
%token <loc> THEOREM LEMMA FACT REMARK GIVEN AXIOM (* definition keywords; [let] is [LET] *)
%token <loc> ARROW "->" AT "@" BAR "|" COLON ":" COLONCOLON "::" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}" PLUS "+" STAR "*" DOT "." EQ ":=" SEMI ";" EOF (* symbols *)

%start <Cst.prog> prog
%type <Cst.expression> expression app_expression atomic_expression
%type <string * Cst.expression> param
%type <list (string * Cst.expression)> params params_opt
%type <Cst.decl> let_defn
%type <list Cst.decl> let_defns
%type <Cst.mods> mods
%type <Cst.dkw> dkw
%type <(string * list string)%type> path
%type <list string> fpath ipath upath mpath_opt
%type <string * string> item
%type <list (string * string)> items
%type <list Cst.expression> iargs
%type <(list string * list string)%type> qpath
%type <option string> as_opt
%type <list iitem> ilists ilist
%type <list Cst.cmd> cmd lead_cmd import_cmd open_cmd
%type <(list (string * Cst.expression) * Cst.mdef)%type> mdecl
%type <Cst.mdef> mdef
%type <list Cst.cmd> cmds leads
%type <list (string * list (string * Cst.expression))> ctors
%type <list string> vars vars_opt ihs_opt
%type <list (string * list string * Cst.expression)> brs
%type <string * Cst.expression * list (string * list (string * Cst.expression))> imember
%type <list (string * Cst.expression * list (string * list (string * Cst.expression)))> imembers
%type <string * option Cst.expression> ebinder
%type <list (string * option Cst.expression)> ebinders
%type <bool> block_kw
%type <bool * list (string * option Cst.expression) * Cst.expression * list (string * list string * Cst.expression)> eblock
%type <list (bool * list (string * option Cst.expression) * Cst.expression * list (string * list string * Cst.expression))> eblocks
%type <string * list (string * Cst.expression) * Cst.expression * list (string * list string * Cst.expression)> mfun
%type <list (string * list (string * Cst.expression) * Cst.expression * list (string * list string * Cst.expression))> mfuns
%type <list (string * Cst.expression)> rfields rfields1 tfields tfields1
%type <list Cst.cmd> rwith

%on_error_reduce expression params params_opt app_expression atomic_expression cmds leads mods path fpath

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
  | m = mods; k = dkw; x = VAR; ps = params_opt; ":"; a = expression; ":="; b = expression; END;
      { [Cst.def_cmd k m (snd x) (fold_params Cst.pi ps a) (fold_params Cst.fn ps b)] }
  (* An axiom has [def]'s parameters and type, and no body. *)
  | m = mods; AXIOM; x = VAR; ps = params_opt; ":"; a = expression;
      { [Cst.axiom_cmd m (snd x) (fold_params Cst.pi ps a)] }
  | ~ = import_cmd; <>
  | ~ = open_cmd; <>
  | EVAL; ~ = expression; { [Cst.c_eval expression None] }
  | EVAL; e = expression; ":"; t = expression; { [Cst.c_eval e (Some t)] }
  (* [inductive x (ps) : forall (n : A) -> S where | c (args) … with y : U
     where … end]: the group's uniform parameters, then its members, each
     with its type, which binds its non-uniform parameters. *)
  | INDUCTIVE; x = VAR; ps = params_opt; ":"; t = expression; WHERE; cs = ctors; ms = imembers; END;
      { [Cst.c_ind false false (List.rev ps) ((snd x, t, List.rev cs) :: List.rev ms)] }
  | PRIVATE; INDUCTIVE; x = VAR; ps = params_opt; ":"; t = expression; WHERE; cs = ctors; ms = imembers; END;
      { [Cst.c_ind true false (List.rev ps) ((snd x, t, List.rev cs) :: List.rev ms)] }
  (* [mutual T (ps) where inductive x : S where … with y : U where … end
     end]: the group in the module [T], its members [T.x], [T.y]. *)
  | m = mods; MUTUAL; g = VAR; ps = params_opt; WHERE; INDUCTIVE; x = VAR; ":"; t = expression; WHERE; cs = ctors; ms = imembers; END; END;
      { [Cst.mutual_cmd m (snd g) (List.rev ps) ((snd x, t, List.rev cs) :: List.rev ms)] }
  (* [mutual def (Δ) f (ys) (z : Z) : A := | c xs ⇒ B … with g … end]: the
     common parameters, then the functions, with the modifiers of a
     definition.  Any definition keyword may follow [mutual], and decides
     which modifiers it takes, as for a single definition. *)
  | m = mods; MUTUAL; k = dkw; ps = params_opt; fs = mfuns; END;
      { [Cst.mdef_cmd k m (List.rev ps) (List.rev fs)] }
  (* [inductive x (ps) := X Ms]: an inductive alias, the inductive type [X]
     at the arguments [Ms], under the parameters. *)
  | INDUCTIVE; x = VAR; ps = params_opt; ":="; e = expression;
      { [Cst.c_ind_alias false (snd x) (List.rev ps) e] }
  | PRIVATE; INDUCTIVE; x = VAR; ps = params_opt; ":="; e = expression;
      { [Cst.c_ind_alias true (snd x) (List.rev ps) e] }
  (* [builtin natural := X]: the inductive type [X] is the natural numbers. *)
  | BUILTIN; k = VAR; ":="; x = atomic_expression; { [Cst.c_builtin (snd k) x] }
  (* [record x (ps) : S where f : A ; … with cs end]: a record type, its
     parameters, its sort, its fields in order, and its with-area, the
     commands of its module after the fields. One [end] closes the record,
     with or without a with-area. *)
  | RECORD; x = VAR; ps = params_opt; ":"; t = expression; WHERE; fs = rfields; cs = rwith;
      { [Cst.c_record false (snd x) (List.rev ps) t (List.rev fs) cs] }
  | PRIVATE; RECORD; x = VAR; ps = params_opt; ":"; t = expression; WHERE; fs = rfields; cs = rwith;
      { [Cst.c_record true (snd x) (List.rev ps) t (List.rev fs) cs] }
  (* [record x (ps) := X Ms]: a record alias, the record type [X] at the
     arguments [Ms], under the parameters. *)
  | RECORD; x = VAR; ps = params_opt; ":="; e = expression;
      { [Cst.c_record_alias false (snd x) (List.rev ps) e] }
  | PRIVATE; RECORD; x = VAR; ps = params_opt; ":="; e = expression;
      { [Cst.c_record_alias true (snd x) (List.rev ps) e] }

(* Reversed list of the fields of a record type, possibly empty, separated
   by [;]: [f : A] *)
let rfields :=
  | { @nil (string * Cst.expression) }
  | ~ = rfields1; <>

let rfields1 :=
  | f = VAR; ":"; a = expression; { [(snd f, a)] }
  | ~ = rfields1; ";"; f = VAR; ":"; a = expression; { (snd f, a) :: rfields1 }

(* The end of a record type, with its with-area in order: [with cs end], or
   just [end] for an empty with-area. The one [end] closes the with-area and
   the record together. *)
let rwith :=
  | END; { @nil Cst.cmd }
  | WITH; cs = cmds; END; { List.rev cs }

(* Reversed list of the fields of a record value, possibly empty, separated
   by [;]: [f := M] *)
let tfields :=
  | { @nil (string * Cst.expression) }
  | ~ = tfields1; <>

let tfields1 :=
  | f = VAR; ":="; m = expression; { [(snd f, m)] }
  | ~ = tfields1; ";"; f = VAR; ":="; m = expression; { (snd f, m) :: tfields1 }

(* Reversed list of constructors, possibly empty: [| c (x : A) …] *)
let ctors :=
  | { @nil (string * list (string * Cst.expression)) }
  | ~ = ctors; "|"; x = VAR; ps = params_opt; { (snd x, List.rev ps) :: ctors }

(* A member after the first: [with y : U where | c (args) …] *)
let imember :=
  | WITH; x = VAR; ":"; t = expression; WHERE; cs = ctors; { (snd x, t, List.rev cs) }

(* Reversed list of the members after the first, possibly empty *)
let imembers :=
  | { @nil (string * Cst.expression * list (string * list (string * Cst.expression))) }
  | ~ = imembers; ~ = imember; { imember :: imembers }

(* A function of a [mutual def]: [f (ys) (z : Z) : A := | c xs ⇒ B …] *)
let mfun :=
  | f = VAR; ps = params; ":"; a = expression; ":="; bs = brs; { (snd f, List.rev ps, a, List.rev bs) }

(* Reversed nonempty list of the functions, separated by [with] *)
let mfuns :=
  | ~ = mfun; { [mfun] }
  | ~ = mfuns; WITH; ~ = mfun; { mfun :: mfuns }

(* A module declaration, at the top level or in a [let]: its parameters, and
   a body or an alias. *)
let mdecl :=
  | ps = params_opt; d = mdef; { (List.rev ps, d) }

let mdef :=
  | WHERE; cs = cmds; END; { Cst.md_where (List.rev cs) }
  | ":="; ~ = expression; { Cst.md_alias expression }

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
  | IMPORT; u = ipath; m = mpath_opt; xs = iargs; w = as_opt; ls = ilists;
      { Cst.import_cmds u m (List.rev xs) w (List.rev ls) }

(* [open E as W items]: a module in scope or of an imported unit, applied to
   atomic arguments, then an alias and any number of item lists, all
   optional. *)
let open_cmd :=
  | OPEN; q = qpath; xs = iargs; w = as_opt; ls = ilists;
      { Cst.open_cmds (fst q) (snd q) (List.rev xs) w (List.rev ls) }

(* Reversed list of the arguments of an import or open, possibly empty *)
let iargs :=
  | { @nil Cst.expression }
  | ~ = iargs; ~ = atomic_expression; { atomic_expression :: iargs }

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

(* The unit an [import] names, in order: a path of one segment or more *)
let ipath :=
  | ~ = fpath; { List.rev fpath }

(* A unit named where a name in scope may stand, in order: two segments or
   more, a one-segment unit being read as a name ([Elaborator]) *)
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

let expression :=
  (* The two binders are separate productions, so that an error after
     either one is reported in a state of its own, naming it. *)
  | PI; ~ = params; "->"; ~ = expression; { fold_params Cst.pi params expression }
  | LAMBDA; ~ = params; "->"; ~ = expression; { fold_params Cst.fn params expression }
  | ~ = app_expression; <>

  (* The level operations take atomic arguments, so that [maxl u v] is their
     join and not [maxl (u v)]. *)
  | SUCCL; m = atomic_expression; { Cst.succl m }
  | MAXL; m = atomic_expression; n = atomic_expression; { Cst.maxl m n }

  | EXFALSO; escr = expression; RETURN; mx = VAR; "."; em = expression;
    { Cst.exfalso escr (snd mx) em }

  (* [elim M at ys (z : Z) -> A | c xs, hs ⇒ B … with … end]: one block
     per member of the group, in member order, the one marked [at] the
     scrutinee's; a block's binders, the non-uniform parameters and the
     scrutinee, then its motive; a branch, the non-uniform parameters and
     the constructor's arguments, then after a comma its induction
     hypotheses. *)
  | ELIM; escr = expression; bks = eblocks; END;
    { Cst.elim escr (List.rev bks) }

  (* [let x : A := a; y := b in body end].  The bindings fold into nested
     [letb]s, so each one sees the earlier ones. *)
  | LET; ds = let_defns; IN; body = expression; END; { List.fold_left (fun acc d => Cst.letb d acc) ds body }

  (* [record T where f := M ; … end]: a value of the record type [T], its
     fields in order.  Not atomic, as a command may follow an object with
     no separator: an argument or a selection takes it in parentheses. *)
  | RECORD; t = app_expression; WHERE; fs = tfields; END; { Cst.tuple t (List.rev fs) }


let app_expression :=
  | ~ = app_expression; ~ = atomic_expression; { Cst.app app_expression atomic_expression }
  | ~ = atomic_expression; <>

let atomic_expression :=
  (* A universe is written [Type@] its level: any level term in braces, or
     one of the short forms, a numeral [n] or [<n>l] for the finite level
     [n], [ω] (also spelled [omega]) for [ω], and [<n>L] for [ω+n].  Only
     the braced form admits an ordinal literal with [+] or [*]. *)
  | TYPE; "@"; n = INT; { Cst.suniv (Cst.llit (0, snd n)) }
  | TYPE; "@"; n = LLIT; { Cst.suniv (Cst.llit (0, snd n)) }
  | TYPE; "@"; "{"; m = expression; "}"; { Cst.suniv m }
  | TYPE; "@"; n = LLITL; { Cst.suniv (Cst.llit (1, snd n)) }
  | TYPE; "@"; OMEGA; { Cst.suniv (Cst.llit (1, 0)) }
  (* The large universes, above every small one: [Type@{ω^2}] and
     [Type@{ω^2+i}], the universe at [ω²+i].  [ω^2] is not a level (every
     level is below it), so it is written only here, in braces. *)
  | TYPE; "@"; "{"; OMEGA2; "}"; { Cst.typ 0 }
  | TYPE; "@"; "{"; OMEGA2; "+"; i = INT; "}"; { Cst.typ (snd i) }

  (* [Level@n], also written [Level@{n}], is the type of the levels below
     [ω·(n+1)], and [Level] is [Level@0], the finite levels. *)
  | LEVEL; { Cst.level 0 }
  | LEVEL; "@"; n = INT; { Cst.level (snd n) }
  | LEVEL; "@"; "{"; n = INT; "}"; { Cst.level (snd n) }
  | n = LLIT; { Cst.llit (0, snd n) }
  (* [<n>L] is the level [ω+n], the same literal as [ω + n]. *)
  | n = LLITL; { Cst.llit (1, snd n) }
  (* An ordinal level literal [ω·a + b]: [ω], [ω + b], [ω * a] and
     [ω * a + b] ([·] is the Unicode spelling of [*]). *)
  | OMEGA; { Cst.llit (1, 0) }
  | OMEGA; "+"; b = INT; { Cst.llit (1, snd b) }
  | OMEGA; "*"; a = INT; { Cst.llit (snd a, 0) }
  | OMEGA; "*"; a = INT; "+"; b = INT; { Cst.llit (snd a, snd b) }

  (* The type bound as [builtin natural], and a numeral of it. *)
  | NAT; { Cst.nat }
  | n = INT; { Cst.num (snd n) }

  | TRUE_TY; { Cst.true_ty }
  | TRUE; { Cst.true_tm }
  | FALSE_TY; { Cst.false_ty }

  | x = VAR; { Cst.var (snd x) }

  (* A unit, named by its [::] path.  Only the [.] level can be selected from,
     so the [::] segments are all consumed here. *)
  | ~ = fpath; "::"; x = VAR; { Cst.glob (List.rev (snd x :: fpath)) }

  (* Dot access binds tighter than application, so [X::Y.Z.foo] is one name
     and module arguments are parenthesised, as in [(X::Y.Z a b).foo]. *)
  | ~ = atomic_expression; "."; x = VAR; { Cst.proj atomic_expression (snd x) }

  | "("; ~ = expression; ")"; <>

(* Reversed nonempty list of names *)
let vars :=
  | x = VAR; { [snd x] }
  | ~ = vars; x = VAR; { snd x :: vars }

let vars_opt :=
  | { @nil string }
  | ~ = vars; <>

(* The induction hypotheses of a branch, in order *)
let ihs_opt :=
  | { @nil string }
  | ","; ~ = vars; { List.rev vars }

(* A binder of a block: a name, or a name and its type *)
let ebinder :=
  | x = VAR; { (snd x, None) }
  | "("; x = VAR; ":"; ~ = expression; ")"; { (snd x, Some expression) }

(* Reversed nonempty list of the binders of a block *)
let ebinders :=
  | ~ = ebinder; { [ebinder] }
  | ~ = ebinders; ~ = ebinder; { ebinder :: ebinders }

(* [at] marks the scrutinee's block, [with] any other *)
let block_kw :=
  | BLOCK_AT; { true }
  | WITH; { false }

(* A block of an eliminator: [at ys (z : Z) -> A | c xs ⇒ B …] *)
let eblock :=
  | k = block_kw; xs = ebinders; "->"; a = expression; bs = brs; { (k, List.rev xs, a, List.rev bs) }

(* Reversed nonempty list of the blocks of an eliminator *)
let eblocks :=
  | ~ = eblock; { [eblock] }
  | ~ = eblocks; ~ = eblock; { eblock :: eblocks }

(* Reversed list of the branches of an eliminator, possibly empty *)
let brs :=
  | { @nil (string * list string * Cst.expression) }
  | ~ = brs; "|"; c = VAR; ys = vars_opt; zs = ihs_opt; "=>"; b = expression;
      { (snd c, List.rev ys ++ zs, b) :: brs }

(* Reversed nonempty list of parameters *)
let params :=
  | ~ = params; ~ = param; { param :: params }
  | ~ = param; { [param] }

let params_opt :=
  | { @nil (string * Cst.expression) }
  | ~ = params; <>

(* (x : A) *)
let param :=
  | "("; x = VAR; ":"; ~ = expression; ")"; { (snd x, expression) }

(* Reversed nonempty list of [;]-separated bindings *)
let let_defns :=
  | ~ = let_defns; ";"; ~ = let_defn; { let_defn :: let_defns }
  | ~ = let_defn; { [let_defn] }

(* [x : A := a] or [x := a], or a local module [module X (ps) where … end] or
   [module X (ps) := E] *)
let let_defn :=
  | x = VAR; ":"; a = expression; ":="; b = expression; { Cst.d_def (snd x) (Some a) b }
  | x = VAR; ":="; b = expression; { Cst.d_def (snd x) None b }
  | MODULE; x = VAR; md = mdecl; { Cst.d_mod (snd x) (fst md) (snd md) }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
