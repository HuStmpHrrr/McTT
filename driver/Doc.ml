(* Documentation pages for McTT units: highlighted source, every use of a
   name linked to its definition.

   Nothing here decides what a name means:
   - the lexer, the verified parser and its [Cst] are the checker's own;
   - a bare name, or the head of [X.y], is resolved by the elaborator's own
     [lookup] (Frontend/Elaborator.v), on the elaborator's own scope: at a
     command the frame's entries are those [elab_cmd] returns, and the walk
     below only adds the entries the elaborator adds for binders, the same
     way and in the same order;
   - a member chain, [M.x] or [A.B.x], through aliases, opens and applied
     modules and across units, is resolved by the core's [def_site]
     (Extraction/Privacy.v), over the global context the checker built;
   - the token [ℕ] is the type bound as the natural numbers in the
     checker's run of the unit ([check_units]), a member resolved by
     [def_site] as any other;
   - a member selected from a term, [p.y], is a member of the record the
     core's typed fill found [p]'s type to be, read off the unit as the
     checker filed it ([record_selections]), then resolved by [def_site].

   The [Cst] has no positions.  The walk visits the names of a [Cst] in
   source order and pairs each with the next VAR token, checking that the
   strings agree ([next]); a mismatch is an error, never a wrong link.  A
   [def]'s parameters occur twice in the [Cst], in its type and in its body
   ([fold_params] in Parser.vy), and the long forms of [import] and [open]
   repeat the module they name ([Cst.import_cmds], [Cst.open_cmds]); the
   walk reads both cases off the tokens.

   Below each [eval] goes its output: the checker's log entry for it,
   printed as [mctt] prints it ([PrettyPrinter.eval_outputs]), from a run
   of the unit as its own program. *)

module C = McttExtracted.Syntax.Cst
module S = McttExtracted.Syntax
module P = McttExtracted.Parser
module E = McttExtracted.ElabSpec
module El = McttExtracted.Elaborator
module Pr = McttExtracted.Privacy0
module Ep = McttExtracted.Entrypoint

(* ------------------------------------------------------------------ *)
(* Tokens and comments *)

type tok = { t : P.token; s : int; e : int (* byte offsets *) }

let lex (src : string) : tok array =
  let lb = Lexing.from_string src in
  let rec go acc =
    let t = Lexer.read lb in
    let a, b = Lexer.get_range_of_token t in
    let acc = { t; s = a.Lexing.pos_cnum; e = b.Lexing.pos_cnum } :: acc in
    match t with P.EOF _ -> List.rev acc | _ -> go acc
  in
  Array.of_list (go [])

(* The comments, as byte spans with their delimiters: everything between
   two tokens that is not blank.  Comments do not nest, as in the lexer. *)
let comments (src : string) (ts : tok array) : (int * int) list =
  let acc = ref [] in
  let scan a b =
    let i = ref a in
    while !i + 1 < b do
      if src.[!i] = '(' && src.[!i + 1] = '*' then begin
        let j = ref (!i + 2) in
        while !j + 1 < b && not (src.[!j] = '*' && src.[!j + 1] = ')') do incr j done;
        acc := (!i, !j + 2) :: !acc;
        i := !j + 2
      end else incr i
    done
  in
  let prev = ref 0 in
  Array.iter (fun t -> scan !prev t.s; prev := t.e) ts;
  List.rev !acc

let rec buf_of (ts : tok array) (i : int) : P.MenhirLibParser.Inter.buffer =
  lazy (P.MenhirLibParser.Inter.Buf_cons (ts.(min i (Array.length ts - 1)).t, buf_of ts (i + 1)))

(* ------------------------------------------------------------------ *)
(* Occurrences *)

(* A place to link to: a unit's page and an anchor in it ("" is the top). *)
type site = { s_unit : string list; s_anchor : string }

type kind = Local | Def | Mod | Unit

(* What a use links to, before resolution: a place, or the member [ch] of
   the module [H], to be resolved by [def_site] in the global context of
   the unit [u]. *)
type link =
  | Site of site
  | Member of string list * S.modexp * string list

(* [bare]: a name that names nothing by itself, the constructor of an
   eliminator's branch, which is the scrutinee's type's.  [extra]: the
   anchors of what the declaration of the name generates besides it, each
   with its kind: the recursor module [Rec] of a group at the group's
   name for [mutual T], at its first member's otherwise, and its function
   [rec_x] at the member [x]'s. *)
type occ = { mutable link : link option; mutable anchor : string option; mutable kind : kind option;
             mutable bare : bool; mutable extra : (string * kind) list }

(* Every anchor a name declares, with its kind: its own, then the extra
   ones. *)
let occ_anchors (o : occ) : (string * kind) list =
  (match o.anchor, o.kind with Some a, Some k -> [ (a, k) ] | Some a, None -> [ (a, Def) ] | None, _ -> [])
  @ o.extra

exception Misaligned of string

(* What a module object denotes, as far as links need: a module of the
   global context, as a member chain of a module expression; the entries
   of a local body, by name; or nothing known (a term variable). *)
type mden =
  | MGlobal of S.modexp * string list
  | MLocal of (string * (link * mden)) list
  | MNone

(* A core binder in scope: what a use links to (its binding occurrence, or
   for an open's item the member it names) and, for a local module, what it
   denotes.  [vs] lists one per binder entry ([en_var], [en_tvar]) of [sc], in order. *)
type vb = { v_link : link; v_mod : mden }

type env = { sc : E.ent list; vs : vb list }

(* An entry of a unit's contents: a declaration of the unit's body, at any
   depth of its modules, with the anchor its name declares.  [te_depth] is
   the length of the member chain it is declared in; [te_kw] is the
   keyword shown in front of it. *)
type toc_entry = { te_depth : int; te_name : string; te_anchor : string; te_kw : string; te_kind : kind }

let push x v env = { sc = E.Coq_en_var x :: env.sc; vs = v :: env.vs }

(* A member selected from something that may be a term, [h.y] with [h]
   not a local module: the VAR of [y], [y], and the link the walk gives
   it, if any.  If [h] is a term, [y] is a member of the module of the
   record [h]'s type, which only the core's typed fill knows
   ([record_selections]). *)
type sel = { sl_var : int; sl_name : string; sl_link : link option }

(* Where the checked unit files what a command declares, for the
   selections of the command ([cmd_rec]).  What a frame declares is filed
   over the frame's parameters, those of the frames around it too, and for
   a record's with-area the record's parameters and the value the record's
   module is at: [k] counts them, as the source does not repeat them.
   - [L_def (ch, x, k, n)]: the definition [x] of the frame [ch], with its
     [n] parameters, which occur in the source once and in the core twice,
     in its type and in its body;
   - [L_mod (ch, x)]: the module [x], its parameters and, for an alias,
     its target (its body's commands are commands of their own);
   - [L_record (ch, x, k)]: the record [x], its parameters, sort and fields
     (its with-area's commands are commands of their own);
   - [L_mdef (ch, k, n, gs)]: a mutual definition with [n] common
     parameters, and its functions [gs], each its name, its number of
     parameters, and its clauses' constructors, in order;
   - [L_ind (ch, x, k)]: the group of inductive types filed at its member
     [x] of the frame [ch], its parameters and its members' parameters
     and constructors' arguments;
   - [L_alias (ch, x, k, n)]: the inductive or record alias [x], with its
     [n] parameters, filed as a definition with a module part, which
     repeats the definition;
   - [L_open (ch, k, ds)]: an open or import declaring the items [ds],
     each filed with the module opened;
   - [L_eval (k, a)]: the [k]-th eval of the unit, which is in the log of
     the run, not in the unit, and whether it has a type annotation [a],
     which the log holds as its type;
   - [L_params]: the unit's parameters;
   - [L_none]: none of these (an open declaring nothing, an import, a
     builtin binding). *)
type cmd_loc =
  | L_def of string list * string * int * int
  | L_mod of string list * string
  | L_record of string list * string * int
  | L_mdef of string list * int * int * (string * int * string list) list
  | L_ind of string list * string * int
  | L_alias of string list * string * int * int
  | L_open of string list * int * string list
  | L_eval of int * bool
  | L_params
  | L_none

(* A command's selections, in source order, and where what it declares
   is filed. *)
type cmd_rec = { cr_loc : cmd_loc; cr_sels : sel list }

type st = {
  unit : string list;          (* the unit's declared path *)
  toks : tok array;
  vars : int array;            (* token index of the i-th VAR *)
  occ : occ array;             (* indexed like [vars] *)
  mutable cur : int;           (* the next VAR to pair *)
  items : (string list * string list, link) Hashtbl.t;  (* open items, see [items] below *)
  mutable toc : toc_entry list;  (* the unit's declarations at every depth, last first *)
  mutable notes : string list;
  mutable evals : (C.obj * C.obj option) list;  (* the evals walked, last first *)
  mutable recs : rec_site list;  (* the groups walked, last first *)
  mutable sels : sel list;       (* the current command's selections, last first *)
  mutable cmd_recs : cmd_rec list;  (* the commands walked, last first *)
  mutable frame_ps : int;        (* what the current frame's declarations are filed over ([cmd_loc]) *)
}

(* A group, which files a recursor module [Rec]: [T.Rec] for one declared
   by [mutual T (ps) where …], otherwise [X.Rec] in its first member [X]'s
   module.  [r_chain]: the member chain of the module [Rec] is in;
   [r_group]: that of the frame the members are declared in; [r_name]: the
   VAR the anchor of [Rec] is at, [T]'s or [X]'s; [r_members]: the
   declared members' names, in order.  The views' functions of [Rec] are
   known only once the group is filed ([rec_view_anchors]). *)
and rec_site = { r_chain : string list; r_group : string list; r_name : int; r_members : string list }

let next st x =
  let i = st.cur in
  if i >= Array.length st.vars then raise (Misaligned ("no token left for " ^ x));
  (match st.toks.(st.vars.(i)).t with
   | P.VAR (_, y) when y = x -> ()
   | P.VAR (_, y) -> raise (Misaligned (Printf.sprintf "name %s, token %s at byte %d" x y st.toks.(st.vars.(i)).s))
   | _ -> assert false);
  st.cur <- i + 1; i

let tok_after_var st i = st.toks.(st.vars.(i) + 1).t

let local st i = { s_unit = st.unit; s_anchor = "l" ^ string_of_int i }

let refer st i l = st.occ.(i).link <- Some l
let declare st i a k = st.occ.(i).anchor <- Some a; st.occ.(i).kind <- Some k

let bind st x : vb =
  let i = next st x in
  let s = local st i in
  declare st i s.s_anchor Local; { v_link = Site s; v_mod = MNone }

(* The parameters [(x : A)] right after the VAR [i]. *)
let count_params st i =
  let ts = st.toks in
  let j = ref (st.vars.(i) + 1) and n = ref 0 in
  while (match ts.(!j).t with P.LPAREN _ -> true | _ -> false) do
    let depth = ref 0 and stop = ref false in
    while not !stop do
      (match ts.(!j).t with
       | P.LPAREN _ -> incr depth
       | P.RPAREN _ -> decr depth; if !depth = 0 then stop := true
       | _ -> ());
      incr j
    done;
    incr n
  done;
  !n

(* Is the open at the current position the continuation of the previous
   command, [import X::Y …] or [open E as W …], rather than a command of
   its own?  Only an [open] of its own has the OPEN keyword between the last
   name paired and the next. *)
let continues st =
  let a = if st.cur = 0 then 0 else st.vars.(st.cur - 1) + 1 in
  let b = if st.cur < Array.length st.vars then st.vars.(st.cur) else Array.length st.toks in
  let r = ref true in
  for j = a to b - 1 do (match st.toks.(j).t with P.OPEN _ -> r := false | _ -> ()) done;
  !r

(* ------------------------------------------------------------------ *)
(* Names *)

let lookup env x : (E.ent * vb option) option =
  match El.lookup x env.sc with
  | None -> None
  | Some ((k, e), _) ->
      (match e with
       | E.Coq_en_var _ | E.Coq_en_tvar _ ->
           if E.binders env.sc <> List.length env.vs then
             raise (Misaligned "scope out of step with its binders");
           Some (e, Some (List.nth env.vs k))
       | _ -> Some (e, None))

let opt_list = function Some c -> [ c ] | None -> []

let qname_mden (p : S.qname) = MGlobal (S.Coq_me_unit p.S.q_unit, p.S.q_chain)

(* A head name, in term or module position; a name no binding has is the
   imported unit of that one-segment path, as [Elaborator.unit_mod]. *)
let head st env i x : mden =
  match lookup env x with
  | None when El.unit_in_b [ x ] env.sc ->
      refer st i (Site { s_unit = [ x ]; s_anchor = "" }); MGlobal (S.Coq_me_unit [ x ], [])
  | None -> MNone
  | Some (_, Some v) -> refer st i v.v_link; v.v_mod
  | Some (E.Coq_en_mem (_, p), _) ->
      refer st i (Member (st.unit, S.Coq_me_unit p.S.q_unit, p.S.q_chain)); qname_mden p
  | Some (E.Coq_en_open (d, h, oc), _) ->
      (match oc with
       | Some c -> refer st i (Member (st.unit, h, [ c ]))
       | None -> refer st i (Site { s_unit = st.unit; s_anchor = d }));
      MGlobal (h, opt_list oc)
  | Some _ -> MNone

let member_link st m y =
  match m with
  | MGlobal (h, ch) -> Some (Member (st.unit, h, ch @ [ y ]))
  | MLocal tbl -> Option.map fst (List.assoc_opt y tbl)
  | MNone -> None

let member_mden m y =
  match m with
  | MGlobal (h, ch) -> MGlobal (h, ch @ [ y ])
  | MLocal tbl -> (match List.assoc_opt y tbl with Some (_, m) -> m | None -> MNone)
  | MNone -> MNone

let select st m y =
  let i = next st y in
  let l = member_link st m y in
  Option.iter (refer st i) l;
  (match m with
   | MNone | MGlobal _ -> st.sels <- { sl_var = i; sl_name = y; sl_link = l } :: st.sels
   | MLocal _ -> ());
  member_mden m y

let unit_path st fq =
  List.iter (fun x -> let i = next st x in refer st i (Site { s_unit = fq; s_anchor = "" })) fq

(* ------------------------------------------------------------------ *)
(* Objects: the binders of [Elaborator.elab], clause by clause. *)

let rec term st env (o : C.obj) : unit =
  match o with
  | C.Coq_typ _ | C.Coq_level _ | C.Coq_llit _
  | C.Coq_nat | C.Coq_num _ | C.Coq_true_ty | C.Coq_true_tm | C.Coq_false_ty -> ()
  | C.Coq_suniv o | C.Coq_succl o -> term st env o
  | C.Coq_maxl (o1, o2) -> term st env o1; term st env o2
  | C.Coq_exfalso (m, x, a) -> term st env m; let v = bind st x in term st (push x v env) a
  | C.Coq_pi (x, a, b) | C.Coq_fn (x, a, b) ->
      let v = bind st x in term st env a; term st (push x v env) b
  | C.Coq_app (f, a) -> term st env f; term st env a
  | C.Coq_var x -> ignore (head st env (next st x) x)
  | C.Coq_glob _ -> ignore (modv st env o)
  | C.Coq_proj (h, x) -> ignore (select st (modv st env h) x)
  | C.Coq_letb (C.Coq_d_def (x, a, m), b) ->
      let v = bind st x in
      Option.iter (term st env) a; term st env m; term st (push x v env) b
  | C.Coq_letb (C.Coq_d_mod (x, ps, md), b) ->
      let v = bind st x in
      let env' = fst (params st env ps) in
      let m = mdef st env' md in
      term st (push x { v with v_mod = m } env) b
  (* An eliminator: each block's binders, the scrutinee's type after its
     name, then its motive, then each branch's constructor, which names no
     global here, and its names. *)
  | C.Coq_elim (m, bks) ->
      term st env m;
      let binds env ys = List.fold_left (fun env y -> let v = bind st y in push y v env) env ys in
      List.iter (fun (((_, xs), a), bs) ->
          let envx = List.fold_left (fun env' (x, oz) ->
              let v = bind st x in Option.iter (term st env') oz; push x v env') env xs in
          term st envx a;
          List.iter (fun ((c, ys), b) -> st.occ.(next st c).bare <- true; term st (binds env ys) b) bs) bks
  (* A record value: its type, then each field's name, which names no
     global here, and its value. *)
  | C.Coq_tuple (t, fs) ->
      term st env t;
      List.iter (fun (y, m) -> st.occ.(next st y).bare <- true; term st env m) fs

(* Module position: [Elaborator.elab_mod]. *)
and modv st env (o : C.obj) : mden =
  match o with
  | C.Coq_var x -> head st env (next st x) x
  | C.Coq_glob fq -> unit_path st fq; MGlobal (S.Coq_me_unit fq, [])
  | C.Coq_proj (h, y) -> select st (modv st env h) y
  | C.Coq_app (h, a) -> let m = modv st env h in term st env a; m
  | _ -> term st env o; MNone

(* A parameter telescope, each type seeing the earlier parameters; the
   extended scope and the parameters' binders, in order. *)
and params st env ps : env * vb list =
  List.fold_left (fun (env, vbs) (x, a) ->
      let v = bind st x in term st env a; (push x v env, vbs @ [ v ])) (env, []) ps

(* A [def]'s type and body: its [n] parameters occur once in the source. *)
and def_parts st env i ty body =
  let n = count_params st i in
  let rec pis k env ty =
    if k = 0 then (env, ty) else
      match ty with
      | C.Coq_pi (y, a, b) -> let v = bind st y in term st env a; pis (k - 1) (push y v env) b
      | _ -> raise (Misaligned "def parameters")
  in
  let rec fns k b = if k = 0 then b else
      match b with C.Coq_fn (_, _, b) -> fns (k - 1) b | _ -> raise (Misaligned "def body") in
  let env', a = pis n env ty in
  term st env' a; term st env' (fns n body)

(* What an open names: its head, unless the previous command named it,
   then its chain and arguments. *)
and target st env fq ip args : mden =
  let cont = continues st in
  let m, ip =
    match fq, ip with
    | [], x :: ip' when cont ->
        (match lookup env x with
         | Some (_, Some v) -> (v.v_mod, ip')
         | Some (E.Coq_en_mem (_, p), _) -> (qname_mden p, ip')
         | Some (E.Coq_en_open (_, h, oc), _) -> (MGlobal (h, opt_list oc), ip')
         | None when El.unit_in_b [ x ] env.sc -> (MGlobal (S.Coq_me_unit [ x ], []), ip')
         | _ -> (MNone, ip'))
    | [], x :: ip' -> (head st env (next st x) x, ip')
    | [], [] -> raise (Misaligned "nothing to open")
    | _, _ -> if not cont then unit_path st fq; (MGlobal (S.Coq_me_unit fq, []), ip)
  in
  let m = List.fold_left (select st) m ip in
  List.iter (term st env) args; m

(* The items of an open of [m]: the name declared, its occurrence, what it
   denotes and where its source is. *)
and items st m (its : S.iitem list) : (string * int * mden * link option) list =
  List.map (fun ((on, d), _) ->
      match on with
      | None -> let i = next st d in (d, i, m, None)
      | Some n ->
          let i = next st n in
          let l = member_link st m n in
          Option.iter (refer st i) l;
          let j = (match tok_after_var st i with
              | P.AS _ ->
                  (* The member renamed: of the opened module, or, if that
                     is a term's, of its record ([record_selections]). *)
                  (match m with
                   | MNone | MGlobal _ -> st.sels <- { sl_var = i; sl_name = n; sl_link = l } :: st.sels
                   | MLocal _ -> ());
                  next st d
              | _ -> i) in
          (d, j, member_mden m n, l)) its

(* A local module: [Elaborator.elab_mdef]. *)
and mdef st env (md : C.mdef) : mden =
  match md with
  | C.Coq_md_alias e -> modv st env e
  | C.Coq_md_where cs ->
      let tbl = ref [] in
      ignore (List.fold_left (fun env c ->
          match c with
          | C.Coq_c_def (_, x, a, b) ->
              let v = bind st x in
              def_parts st env (st.cur - 1) a b;
              tbl := (x, (v.v_link, MNone)) :: !tbl; push x v env
          | C.Coq_c_mod (_, x, ps, md') ->
              let v = bind st x in
              let m = mdef st (fst (params st env ps)) md' in
              tbl := (x, (v.v_link, m)) :: !tbl; push x { v with v_mod = m } env
          | C.Coq_c_open (fq, ip, args, its) ->
              let m = target st env fq ip args in
              List.fold_left (fun env (d, i, dm, l) ->
                  let s = local st i in declare st i s.s_anchor Local;
                  let l = Option.value l ~default:(Site s) in
                  tbl := (d, (l, dm)) :: !tbl; push d { v_link = l; v_mod = dm } env)
                env (items st m its)
          | _ -> raise (Misaligned "a command a local body does not have")) env cs);
      MLocal !tbl

(* ------------------------------------------------------------------ *)
(* Commands *)

let anchor_of ch x = String.concat "." (ch @ [ x ])

(* The keyword of the definition whose name is the VAR [i]: the token in
   front of the name. *)
let def_kw st i =
  match st.toks.(st.vars.(i) - 1).t with
  | P.THEOREM _ -> "theorem" | P.LEMMA _ -> "lemma" | P.FACT _ -> "fact" | P.REMARK _ -> "remark"
  | P.LET _ -> "let" | P.GIVEN _ -> "given" | _ -> "def"

(* [cmd st fp ch o ov f fv c]: the command [c] in the frame at member chain
   [ch], whose entries are [f] inside the scope [o]; [fv] and [ov] are the
   binders of [f] and [o].  The frame's next entries are [elab_cmd]'s.  Each
   declaration of the body is an entry of the unit's contents. *)
let rec cmd st fp ch (o, ov) (f, fv) (c : C.cmd) : E.ent list =
  let env = { sc = f @ o; vs = fv @ ov } in
  (* The selections of an enclosing command, set aside while this one's
     are gathered. *)
  let outer = st.sels in
  st.sels <- [];
  (* An entry of the contents, declared in the member chain [ch']. *)
  let entry ch' x kw k =
    st.toc <- { te_depth = List.length ch'; te_name = x; te_anchor = anchor_of ch' x; te_kw = kw; te_kind = k }
              :: st.toc in
  let decl kw x k =
    let i = next st x in
    declare st i (anchor_of ch x) k;
    entry ch x (match kw with Some kw -> kw | None -> def_kw st i) k;
    i
  in
  (* A group of inductive types in the frame [ch]: its members' names, each
     a module, and, when [ps_first] (the group of a [mutual T (ps)]), its
     uniform parameters before them, otherwise after the first member's
     name; each member's type, binding its non-uniform parameters before its
     sort, then its constructors, members of its module, and their
     arguments, in which every member's name is a variable linked to its
     declaration, and each argument binds its name for the next. *)
  let group ch env ps_first ps ms =
    let self x = { v_link = Site { s_unit = st.unit; s_anchor = anchor_of ch x }; v_mod = MNone } in
    let base = List.fold_left (fun env ((x, _), _) -> push x (self x) env) env ms in
    (* The chain of the module the group's recursor module [Rec] is in: [T]
       for [mutual T], which [ch] is; otherwise the first member's module. *)
    let rch = if ps_first then ch else (match ms with ((x0, _), _) :: _ -> ch @ [ x0 ] | [] -> ch) in
    let declm j x =
      let i = next st x in
      declare st i (anchor_of ch x) Mod;
      (* A member: its function of [Rec] too; the first member of a group
         not declared by [mutual], [Rec] itself, filed in its module. *)
      st.occ.(i).extra <- [ (anchor_of (rch @ [ "Rec" ]) ("rec_" ^ x), Def) ];
      if not ps_first && j = 0 then begin
        st.occ.(i).extra <- (anchor_of rch "Rec", Mod) :: st.occ.(i).extra;
        st.recs <- { r_chain = rch; r_group = ch; r_name = i; r_members = List.map (fun ((y, _), _) -> y) ms } :: st.recs
      end;
      st.toc <- { te_depth = List.length ch; te_name = x; te_anchor = anchor_of ch x; te_kw = "inductive"; te_kind = Mod }
                :: st.toc
    in
    let envu =
      if ps_first then fst (params st env ps)
      else (match ms with ((x, _), _) :: _ -> declm 0 x; fst (params st env ps) | [] -> env)
    in
    (match ms with
     | [ ((x, _), _) ] -> Hashtbl.replace st.items (fp, ch @ [ x; "rec" ]) (self x).v_link
     | _ -> ());
    List.iteri (fun j ((x, t), cs) ->
        if ps_first || j > 0 then declm j x;
        let rec pis env t =
          match t with
          | C.Coq_pi (y, a, b) -> let v = bind st y in term st env a; pis (push y v env) b
          | _ -> term st envu t; env
        in
        let enva = pis envu t in
        let k = List.length enva.sc - List.length env.sc in
        let take n l = List.filteri (fun i _ -> i < n) l in
        let envs = { sc = take k enva.sc @ base.sc; vs = take k enva.vs @ base.vs } in
        List.iter (fun (c, args) ->
            declare st (next st c) (anchor_of (ch @ [ x ]) c) Def;
            st.toc <- { te_depth = List.length ch + 1; te_name = c; te_anchor = anchor_of (ch @ [ x ]) c;
                        te_kw = "|"; te_kind = Def } :: st.toc;
            ignore (List.fold_left (fun env (y, a) ->
                let v = bind st y in term st env a; push y v env) envs args)) cs) ms
  in
  let loc = match c with
   | C.Coq_c_def (_, x, a, b) ->
       let i = decl None x Def in def_parts st env i a b; L_def (ch, x, st.frame_ps, count_params st i)
   | C.Coq_c_axiom (x, a) -> ignore (decl (Some "axiom") x Def); term st env a; L_def (ch, x, st.frame_ps, 0)
   (* [mutual T (ps) where inductive … end end]: the module [T], then the
      group in its frame, its parameters first. *)
   | C.Coq_c_mod (_, x, [], C.Coq_md_where [ C.Coq_c_ind (_, _, ps, ms) ])
     when (match st.toks.(st.vars.(st.cur) - 1).t with P.MUTUAL _ -> true | _ -> false) ->
       let i = decl (Some "mutual") x Mod in
       (* The recursor module the group files, at the group's name. *)
       st.occ.(i).extra <- [ (anchor_of (ch @ [ x ]) "Rec", Mod) ];
       st.recs <- { r_chain = ch @ [ x ]; r_group = ch @ [ x ]; r_name = i; r_members = List.map (fun ((y, _), _) -> y) ms }
                  :: st.recs;
       group (ch @ [ x ]) env true ps ms;
       (match ms with ((x0, _), _) :: _ -> L_ind (ch @ [ x ], x0, st.frame_ps) | [] -> L_none)
   | C.Coq_c_mod (_, x, ps, md) ->
       ignore (decl (Some "module") x Mod);
       let env', vbs = params st env ps in
       (match md with
        | C.Coq_md_where body ->
            let k = st.frame_ps in
            st.frame_ps <- k + List.length ps;
            ignore (cmds st fp (ch @ [ x ]) (f @ o, fv @ ov) (E.pents ps, List.rev vbs) body);
            st.frame_ps <- k
        | C.Coq_md_alias e -> ignore (modv st env' e));
       L_mod (ch, x)
   | C.Coq_c_import fq -> unit_path st fq; L_none
   | C.Coq_c_open (fq, ip, args, its) ->
       let m = target st env fq ip args in
       (* An exported item is a member of the module, and an entry of the
          contents; a [use]d one, or an [as] alias, only names one in scope. *)
       let ds = items st m its in
       List.iter2 (fun (d, i, _, l) (_, pv) ->
           let k = if l = None then Mod else Def in
           declare st i (anchor_of ch d) k;
           if not pv then entry ch d "export" k;
           Option.iter (Hashtbl.replace st.items (fp, ch @ [ d ])) l) ds its;
       (match ds with [] -> L_none | _ -> L_open (ch, st.frame_ps, List.map (fun (d, _, _, _) -> d) ds))
   | C.Coq_c_eval (e, t) ->
       let k = List.length st.evals in
       st.evals <- (e, t) :: st.evals; term st env e; Option.iter (term st env) t; L_eval (k, t <> None)
   | C.Coq_c_error e -> raise (Misaligned ("rejected by the parser: " ^ e))
   (* An inductive alias: its name, a module, its parameters, then the
      type it names, as a module alias's target. *)
   | C.Coq_c_ind_alias (_, x, ps, e) ->
       ignore (decl (Some "inductive") x Mod);
       let env', _ = params st env ps in
       ignore (modv st env' e); L_alias (ch, x, st.frame_ps, List.length ps)
   (* A record alias: as an inductive alias. *)
   | C.Coq_c_record_alias (_, x, ps, e) ->
       ignore (decl (Some "record") x Mod);
       let env', _ = params st env ps in
       ignore (modv st env' e); L_alias (ch, x, st.frame_ps, List.length ps)
   (* A record type: its name, a type and a module, its parameters, its
      sort, then its fields, members of its module, each type seeing the
      fields before it, then its with-area, in the record's frame
      ([ElabSpec.record_ents]), the record in scope outside it. *)
   | C.Coq_c_record (_, x, ps, s, fs, cs) ->
       ignore (decl (Some "record") x Mod);
       let env', vbs = params st env ps in
       term st env' s;
       ignore (List.fold_left (fun envf (y, a) ->
           let i = next st y in
           declare st i (anchor_of (ch @ [ x ]) y) Def;
           entry (ch @ [ x ]) y "field" Def;
           term st envf a;
           push y { v_link = Site { s_unit = st.unit; s_anchor = anchor_of (ch @ [ x ]) y }; v_mod = MNone } envf)
         env' fs);
       (* The value the module is at: a binder no name denotes. *)
       let self = { v_link = Site { s_unit = st.unit; s_anchor = "" }; v_mod = MNone } in
       let p = { S.q_unit = fp; S.q_chain = ch @ [ x ] } in
       let k = st.frame_ps in
       st.frame_ps <- k + List.length ps + 1;
       ignore (cmds st fp (ch @ [ x ]) (E.Coq_en_mem (x, p) :: f @ o, fv @ ov)
                 (E.record_ents fp ch x ps fs, self :: List.rev vbs) cs);
       st.frame_ps <- k;
       L_record (ch, x, k)
   (* A builtin binding: its kind, which declares nothing and links where
      the type it binds does, then the type. *)
   | C.Coq_c_builtin (k, x) ->
       let i = next st k in
       ignore (modv st env x);
       st.occ.(i).link <- st.occ.(st.cur - 1).link; L_none
   (* A group: its first member's name, its uniform parameters, then its
      members ([group]). *)
   | C.Coq_c_ind (_, _, ps, ms) ->
       group ch env false ps ms;
       (match ms with ((x0, _), _) :: _ -> L_ind (ch, x0, st.frame_ps) | [] -> L_none)
   (* A mutual definition: its common parameters, then each function, a
      definition of the frame: its name, its parameters, the last its
      scrutinee, its result type under them, then its clauses, each its
      constructor and its names, seeing only the common parameters. *)
   | C.Coq_c_mdef (_, ps, fs) ->
       let envd, _ = params st env ps in
       let binds env ys = List.fold_left (fun env y -> let v = bind st y in push y v env) env ys in
       List.iter (fun (((g, gps), a), bs) ->
           ignore (decl (Some "mutual def") g Def);
           let envg, _ = params st envd gps in
           term st envg a;
           List.iter (fun ((c, ys), b) -> st.occ.(next st c).bare <- true; term st (binds envd ys) b) bs) fs;
       L_mdef (ch, st.frame_ps, List.length ps,
               List.map (fun (((g, gps), _), bs) -> (g, List.length gps, List.map (fun ((c, _), _) -> c) bs)) fs)
  in
  st.cmd_recs <- { cr_loc = loc; cr_sels = List.rev st.sels } :: st.cmd_recs;
  st.sels <- outer;
  next_frame st fp ch o f c

and next_frame st fp ch o f c =
  match El.elab_cmd fp ch o f c with
  | El.Coq_eok (f', _) -> f'
  | El.Coq_eerr e -> st.notes <- ("elaboration: " ^ e) :: st.notes; f

and cmds st fp ch (o, ov) (f, fv) cs =
  List.fold_left (fun f c -> cmd st fp ch (o, ov) (f, fv) c) f cs

(* A leading import or open: read in the scope [l] of the parameter types,
   which [elab_lead] extends. *)
let lead st fp (l : E.ent list) (c : C.cmd) : E.ent list =
  ignore (cmd st fp [] (l, []) ([], []) c);
  match El.elab_lead l [ c ] with
  | El.Coq_eok (l', _) -> l'
  | El.Coq_eerr e -> st.notes <- ("elaboration: " ^ e) :: st.notes; l

(* ------------------------------------------------------------------ *)
(* Units *)

type unit_info = {
  u_file : string list;        (* the file, relative to the root, as a path *)
  u_path : string list;        (* the unit it declares *)
  u_src : string;
  u_toks : tok array;
  u_comments : (int * int) list;
  u_vars : int array;
  u_occ : occ array;
  u_toc : toc_entry list;      (* the declarations of the body at every depth, in order *)
  mutable u_notes : string list;  (* the walk's, then the checked unit's ([record_selections]) *)
  u_evals : (int * int) list;  (* each eval's first and last token, in order *)
  u_recs : rec_site list;      (* the groups declared, in order *)
  u_cmds : cmd_rec list;       (* each command's selections, the unit's parameters' first *)
}

let read_file p = In_channel.with_open_bin p In_channel.input_all

(* Where each eval of a unit ends.  The [i]-th EVAL token starts the [i]-th
   eval walked (the walk is in source order, and EVAL starts only an eval);
   the command ends before one of the tokens that may follow a command.  The
   first such token for which the tokens from EVAL on parse, as the body of
   a module, to exactly the walked eval is its end: the span is read off the
   parser, never guessed. *)
let eval_spans (toks : tok array) (evals : (C.obj * C.obj option) list) : (int * int) list =
  let dummy = (Lexing.dummy_pos, Lexing.dummy_pos) in
  let follows = function
    | P.MODULE _ | P.PRIVATE _ | P.ABSTRACT _ | P.DEF _ | P.THEOREM _ | P.LEMMA _ | P.FACT _
    | P.REMARK _ | P.LET _ | P.GIVEN _ | P.AXIOM _ | P.IMPORT _ | P.OPEN _ | P.EVAL _ | P.INDUCTIVE _
    | P.BUILTIN _ | P.MUTUAL _ | P.RECORD _ | P.END _ | P.EOF _ -> true
    | _ -> false in
  let parses i j (e, t) =
    let body = Array.to_list (Array.map (fun k -> k.t) (Array.sub toks i (j - i))) in
    let ts = Array.of_list ([ P.MODULE dummy; P.VAR (dummy, "T"); P.WHERE dummy ] @ body
                            @ [ P.END dummy; P.EOF dummy ]) in
    let rec buf k = lazy (P.MenhirLibParser.Inter.Buf_cons (ts.(min k (Array.length ts - 1)), buf (k + 1))) in
    match P.prog Main.parser_log_fuel (buf 0) with
    | P.MenhirLibParser.Inter.Parsed_pr ((_, (_, [ C.Coq_c_eval (e', t') ])), _) -> e' = e && t' = t
    | _ -> false
  in
  let starts = List.filter_map Fun.id
      (List.mapi (fun i t -> match t.t with P.EVAL _ -> Some i | _ -> None) (Array.to_list toks)) in
  if List.length starts <> List.length evals then
    raise (Misaligned (Printf.sprintf "%d eval tokens, %d evals" (List.length starts) (List.length evals)));
  List.map2 (fun i ev ->
      let rec go j =
        if j >= Array.length toks then raise (Misaligned (Printf.sprintf "the eval at byte %d" toks.(i).s))
        else if follows toks.(j).t && parses i j ev then (i, j - 1)
        else go (j + 1) in
      go (i + 2)) starts evals

let walk (file : string list) (src : string) (items : (string list * string list, link) Hashtbl.t) : unit_info =
  let toks = lex src in
  let ((leads, ((fp, ps), cs)) : C.prog) =
    match P.prog Main.parser_log_fuel (buf_of toks 0) with
    | P.MenhirLibParser.Inter.Parsed_pr (p, _) -> p
    | _ -> failwith "parse error"
  in
  let vars = Array.of_list (List.filter_map Fun.id
      (List.mapi (fun i t -> match t.t with
           | P.VAR _ -> Some i
           | _ -> None) (Array.to_list toks))) in
  let occ = Array.init (Array.length vars) (fun _ -> { link = None; anchor = None; kind = None; bare = false; extra = [] }) in
  let st = { unit = fp; toks; vars; occ; cur = 0; items; toc = []; notes = []; evals = []; recs = [];
             sels = []; cmd_recs = []; frame_ps = List.length ps } in
  let l = List.fold_left (lead st fp) [] leads in
  List.iter (fun x -> let i = next st x in declare st i "" Unit) fp;
  let env, vbs = params st { sc = l; vs = [] } ps in
  ignore env;
  st.cmd_recs <- { cr_loc = L_params; cr_sels = List.rev st.sels } :: st.cmd_recs;
  st.sels <- [];
  (* The leading commands again, as the frame's first commands. *)
  let f = List.fold_left (fun f c -> next_frame st fp [] l f c) (E.pents ps) leads in
  ignore (cmds st fp [] (l, []) (f, List.rev vbs) cs);
  if st.cur <> Array.length vars then
    raise (Misaligned (Printf.sprintf "%d of %d names paired" st.cur (Array.length vars)));
  { u_file = file; u_path = fp; u_src = src; u_toks = toks; u_comments = comments src toks;
    u_vars = vars; u_occ = occ; u_toc = List.rev st.toc; u_notes = List.rev st.notes;
    u_evals = eval_spans toks (List.rev st.evals); u_recs = List.rev st.recs; u_cmds = List.rev st.cmd_recs }

(* The order of unit paths: segment by segment, each by [String.compare],
   and a path before every path it is a prefix of, so [X] comes before
   [X›Properties].  Sorting the entries of a directory by their file names
   does not give this order: the directory [X] sorts before the file
   [X.mctt], so the units under [X/] would come before [X]. *)
let rec compare_unit_path (p : string list) (q : string list) : int =
  match p, q with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: p', y :: q' ->
      let c = String.compare x y in
      if c <> 0 then c else compare_unit_path p' q'

(* The units under [root/dir], as paths, in no particular order, consed
   onto [acc]. *)
let rec find_units_raw root dir acc =
  let a = Sys.readdir (Filename.concat root dir) in
  Array.fold_left (fun acc f ->
      let rel = if dir = "" then f else dir ^ "/" ^ f in
      if Sys.is_directory (Filename.concat root rel) then find_units_raw root rel acc
      else if Filename.check_suffix f ".mctt" then
        String.split_on_char '/' (Filename.chop_suffix rel ".mctt") :: acc
      else acc) acc a

(* The same, in reverse order of [compare_unit_path], consed onto [acc]. *)
let find_units root dir acc =
  List.rev_append (List.sort compare_unit_path (find_units_raw root dir [])) acc

type lib = {
  root : string;
  units : unit_info list;                       (* by [compare_unit_path] *)
  failed : (string list * string) list;         (* files that do not line up *)
  thetas : (string list, S.gdeps) Hashtbl.t;    (* each checked unit's global context *)
  outputs : (string list, string list) Hashtbl.t;  (* each checked unit's evals, as [mctt] prints them *)
  nats : (string list, S.qname) Hashtbl.t;      (* the type each checked unit has bound as [ℕ] *)
  items : (string list * string list, link) Hashtbl.t;
}

(* ------------------------------------------------------------------ *)
(* Selections through record values *)

(* A member [y] selected from a term [h], [h.y], is a member of the module
   of the record [h]'s type.  The walk cannot know that record; the core's
   typed fill finds it, and files [h.y] as
   [a_mem (record_value_module P Rs h) y], where
   [record_value_module P Rs h = me_apps (qname_mod P) (Rs ++ [h])]
   (Core/TypedElab/Fill.v).  The links of such selections are read off the
   checked unit, as filed, and the log of its run, which holds its evals:
   - [record_cands] lists, for the declaration of one command, its
     selections through record values, as [(y, P)], in source order;
   - [record_selections] pairs them with the command's selections that
     the walk did not link ([sel]), in order and by name. *)

(* The qname of a module path [U.x.y]. *)
let rec path_qname (h : S.modexp) (acc : string list) : S.qname option =
  match h with
  | S.Coq_me_unit p -> Some { S.q_unit = p; S.q_chain = acc }
  | S.Coq_me_mem (h', y) -> path_qname h' (y :: acc)
  | _ -> None

(* A module expression's head and arguments. *)
let rec me_spine (h : S.modexp) (args : S.exp list) : S.modexp * S.exp list =
  match h with
  | S.Coq_me_app (h', e) -> me_spine h' (e :: args)
  | _ -> (h, args)

(* [record_value_module P Rs M]: the record [P] and the arguments [Rs] and
   [M].  The fill infers [Rs], as normal forms, in which a field is a
   projection [a_proj], not a selection; [(P Rs M).y] written out has
   them in the source. *)
let record_value th (h : S.modexp) : (S.qname * S.exp list) option =
  match me_spine h [] with
  | _, [] -> None
  | b, args ->
      match path_qname b [] with
      | Some p when McttExtracted.Members.record_lookup th [] p <> None -> Some (p, args)
      | _ -> None

(* The selections through record values of filed terms, in the order the
   walk visits the source they come from: a selection after its value, so
   [M.y.z] gives [y] then [z]; an eliminator's scrutinee before its blocks;
   the entries of a context outermost first.  An eliminator's uniform
   parameters, which the fill infers and the source does not have, are
   skipped. *)
let rec rc_exp th (e : S.exp) : (string * S.qname) list =
  match e with
  | S.Coq_a_univ m | S.Coq_a_succl m | S.Coq_a_proj (_, m) -> rc_exp th m
  | S.Coq_a_maxl (a, b) | S.Coq_a_pi (a, b) | S.Coq_a_fn (a, b) | S.Coq_a_app (a, b) ->
      rc_exp th a @ rc_exp th b
  | S.Coq_a_exfalso (a, m) -> rc_exp th m @ rc_exp th a
  | S.Coq_a_let (S.Coq_b_def (oa, m), b) -> rc_opt th oa @ rc_exp th m @ rc_exp th b
  | S.Coq_a_let (S.Coq_b_mod u, b) -> rc_unit th u @ rc_exp th b
  | S.Coq_a_mem (h, y) -> rc_sel th h y
  | S.Coq_a_tuple (t, fs) -> rc_exp th t @ List.concat_map (fun (_, m) -> rc_exp th m) fs
  | S.Coq_a_elim (_, _, _, bks, m) ->
      rc_exp th m
      @ List.concat_map (fun (S.Coq_eb_mk (_, oz, a, bs)) ->
          rc_opt th oz @ rc_exp th a @ List.concat_map (fun (_, b) -> rc_exp th b) bs) bks
  | _ -> []

and rc_opt th = function Some e -> rc_exp th e | None -> []

and rc_sel th h y =
  match record_value th h with
  | Some (p, args) -> List.concat_map (rc_exp th) args @ [ (y, p) ]
  | None -> rc_mod th h

and rc_mod th (h : S.modexp) =
  match h with
  | S.Coq_me_mem (h', y) -> rc_sel th h' y
  | S.Coq_me_app (h', e) -> rc_mod th h' @ rc_exp th e
  | S.Coq_me_lit u -> rc_unit th u
  | S.Coq_me_unit _ | S.Coq_me_var _ -> []

and rc_ctx th (d : S.centry list) = List.concat_map (rc_centry th) (List.rev d)

and rc_centry th = function
  | S.Coq_ce_ass a -> rc_exp th a
  | S.Coq_ce_def (a, m) -> rc_exp th a @ rc_exp th m
  | S.Coq_ce_mod u -> rc_unit th u
  | S.Coq_ce_dm (a, m, u) -> rc_exp th a @ rc_exp th m @ rc_unit th u

and rc_unit th (S.Coq_gu_mk (d, md)) =
  rc_ctx th d @ (match md with S.Coq_md_alias h -> rc_mod th h | S.Coq_md_body (_, g) -> rc_gmod th g)

and rc_gmod th = function
  | S.Coq_gm_nil -> []
  | S.Coq_gm_ext (g, _, e) -> rc_gmod th g @ rc_gentry th e
  (* An open of a local body: the module opened, then, if it is a record
     value's, each member an item names, a selection from it. *)
  | S.Coq_gm_open (g, h, its) ->
      rc_gmod th g @ rc_mod th h
      @ (match record_value th h with
          | Some (p, _) -> List.filter_map (fun ((on, _), _) -> Option.map (fun n -> (n, p)) on) its
          | None -> [])

and rc_gentry th = function
  | S.Coq_ge_def (_, _, a, om) -> rc_exp th a @ rc_opt th om
  | S.Coq_ge_mod (_, u) -> rc_unit th u
  | S.Coq_ge_def_mod (_, a, m, u) -> rc_exp th a @ rc_exp th m @ rc_unit th u
  | S.Coq_ge_record (_, _, d, _) -> rc_record th 0 d
  | S.Coq_ge_ind (_, _, _, d, _) -> rc_ind th 0 d

(* A context without its [k] outermost entries, the last ones. *)
and outer_drop k (d : S.centry list) = List.filteri (fun i _ -> i < List.length d - k) d

(* A record: its parameters but the [k] outermost, the frames', then its
   sort and its fields. *)
and rc_record th k (d : (S.exp, S.centry) S.record_decl_g) =
  rc_ctx th (outer_drop k d.S.record_params) @ rc_exp th d.S.record_sort
  @ List.concat_map (fun (_, a) -> rc_exp th a) d.S.record_fields

(* A group: its parameters but the [k] outermost, the frames', then each
   member's own parameters, the sort (which the group has once, after its
   first member's parameters) and its constructors' arguments. *)
and rc_ind th k (d : (S.exp, S.centry) S.ind_decl_g) =
  let rec pt = function
    | S.Coq_pt_pi (a, r) -> rc_exp th a @ pt r
    | S.Coq_pt_self (_, es) -> List.concat_map (rc_exp th) es in
  rc_ctx th (outer_drop k d.S.ind_uparams)
  @ List.concat (List.mapi (fun j (m : (S.exp, S.centry) S.imember_g) ->
      rc_ctx th m.S.im_nparams @ (if j = 0 then rc_exp th d.S.ind_sort else [])
      @ List.concat_map (fun (_, args) ->
          List.concat_map (function S.Coq_ca_arg a -> rc_exp th a | S.Coq_ca_rec r -> pt r) args) m.S.im_cons)
      d.S.ind_members)

(* The entry [x] of a body, the last if several. *)
let rec gmod_entry (g : S.gmod) (x : string) : S.gentry option =
  match g with
  | S.Coq_gm_nil -> None
  | S.Coq_gm_ext (g', y, e) -> if y = x then Some e else gmod_entry g' x
  | S.Coq_gm_open (g', _, _) -> gmod_entry g' x

let unit_body (S.Coq_gu_mk (_, md)) = match md with S.Coq_md_body (_, g) -> Some g | S.Coq_md_alias _ -> None

(* The entry [x] of the frame at the member chain [ch] of a unit. *)
let entry_at (gu : S.gunit) (ch : string list) (x : string) : S.gentry option =
  let sub = function
    | S.Coq_ge_mod (_, u) | S.Coq_ge_def_mod (_, _, _, u) -> unit_body u
    | S.Coq_ge_record (_, _, _, g) | S.Coq_ge_ind (_, _, _, _, g) -> Some g
    | S.Coq_ge_def _ -> None in
  let rec go g = function
    | [] -> gmod_entry g x
    | y :: ch' -> Option.bind (Option.bind (gmod_entry g y) sub) (fun g' -> go g' ch') in
  Option.bind (unit_body gu) (fun g -> go g ch)

(* A definition's body without the binders of its [n] parameters, whose
   types the walk visits once, in the definition's type. *)
let rec strip_fns n (e : S.exp) = match n, e with
  | 0, _ -> e
  | _, S.Coq_a_fn (_, b) -> strip_fns (n - 1) b
  | _, _ -> e

(* A type without the domains of its first [n] parameters: those of the
   frames it is filed over ([cmd_loc]). *)
let rec skip_pis n (e : S.exp) = match n, e with
  | 0, _ -> e
  | _, S.Coq_a_pi (_, b) -> skip_pis (n - 1) b
  | _, _ -> e

(* The selections through record values of what a command declares. *)
let record_cands th (gu : S.gunit) (log : McttExtracted.Command1.eval_entry list) (l : cmd_loc) =
  let def k n = function
    | Some (S.Coq_ge_def (_, _, a, om)) -> rc_exp th (skip_pis k a) @ rc_opt th (Option.map (strip_fns (k + n)) om)
    | Some (S.Coq_ge_def_mod (_, a, m, u)) ->
        rc_exp th (skip_pis k a) @ rc_exp th (strip_fns (k + n) m) @ rc_unit th u
    | _ -> [] in
  match l with
  | L_def (ch, x, k, n) -> def k n (entry_at gu ch x)
  | L_mod (ch, x) ->
      (match entry_at gu ch x with
       | Some (S.Coq_ge_mod (_, S.Coq_gu_mk (d, md))) ->
           rc_ctx th d @ (match md with S.Coq_md_alias h -> rc_mod th h | S.Coq_md_body _ -> [])
       | _ -> [])
  | L_record (ch, x, k) ->
      (match entry_at gu ch x with Some (S.Coq_ge_record (_, _, d, _)) -> rc_record th k d | _ -> [])
  | L_ind (ch, x, k) ->
      (match entry_at gu ch x with Some (S.Coq_ge_ind (_, _, _, d, _)) -> rc_ind th k d | _ -> [])
  | L_alias (ch, x, k, n) ->
      (match entry_at gu ch x with
       | Some (S.Coq_ge_def_mod (_, a, m, _)) -> rc_exp th (skip_pis k a) @ rc_exp th (strip_fns (k + n) m)
       | _ -> [])
  (* An [as] alias is filed as an alias of the module opened, a [use]d
     member as the member of it, each over the frames' parameters. *)
  (* Each item repeats the module opened; a member of a record value's
     module is a selection from it, [a] of [open p use (a as b)]. *)
  | L_open (ch, k, ds) ->
      List.concat_map (fun d ->
          match entry_at gu ch d with
          | Some (S.Coq_ge_mod (_, S.Coq_gu_mk (_, S.Coq_md_alias h))) -> rc_mod th h
          | Some (S.Coq_ge_def (_, _, _, Some m)) -> rc_exp th (strip_fns k m)
          | _ -> []) ds
  (* Each function is filed as [λ Δ ys z. a_elim … Bks z] at the type
     [Π Δ ys z. A], with the blocks [Bks] of all the functions: the common
     parameters [Δ] are read off the first function's type, each
     function's own parameters and result type off its type, and its
     clauses off the block of the first function's eliminator whose
     branches are of its clauses' constructors. *)
  | L_mdef (ch, k, n, gs) ->
      let ty g = match entry_at gu ch g with Some (S.Coq_ge_def (_, _, a, _)) -> Some a | _ -> None in
      let rec doms k e = match k, e with
        | 0, _ -> ([], e)
        | _, S.Coq_a_pi (a, b) -> let ds, r = doms (k - 1) b in (a :: ds, r)
        | _, _ -> ([], e) in
      (match gs with
       | [] -> []
       | (g1, k1, _) :: _ ->
           let bks = match entry_at gu ch g1 with
             | Some (S.Coq_ge_def (_, _, _, Some m)) ->
                 (match strip_fns (k + n + k1) m with S.Coq_a_elim (_, _, _, bks, _) -> bks | _ -> [])
             | _ -> [] in
           (match ty g1 with
            | Some a -> List.concat_map (rc_exp th) (fst (doms n (snd (doms k a)))) | None -> [])
           @ List.concat_map (fun (g, _, cs) ->
               (match ty g with Some a -> rc_exp th (snd (doms (k + n) a)) | None -> [])
               @ (match List.find_opt (fun (S.Coq_eb_mk (_, _, _, bs)) ->
                   List.map (fun ((c, _), _) -> c) bs = cs) bks with
                 | Some (S.Coq_eb_mk (_, _, _, bs)) -> List.concat_map (fun (_, b) -> rc_exp th b) bs
                 | None -> [])) gs)
  | L_eval (k, annotated) ->
      (match List.nth_opt log k with
       | Some e -> rc_exp th e.McttExtracted.Command1.eval_entry_exp
                   @ (if annotated then rc_exp th e.McttExtracted.Command1.eval_entry_typ else [])
       | None -> [])
  | L_params -> let (S.Coq_gu_mk (d, _)) = gu in rc_ctx th d
  | L_none -> []

(* The links of the selections through record values of a checked unit,
   command by command.  A selection the walk linked to a member the core
   finds is one the command may have; one it did not is one it must have.
   Each is paired with the first selection of the core it can be, after
   the previous one's, in order, and again from the end, with the last.
   A selection that must be one links to the member of the record the two
   agree on: every selection of the core between them of its name is of
   that record.  Otherwise the selection does not link, and the unit has a
   note saying why. *)
let record_selections (u : unit_info) th (gu : S.gunit) log : unit =
  List.iter (fun cr ->
      if cr.cr_sels <> [] then begin
        let cs = Array.of_list (record_cands th gu log cr.cr_loc) in
        let nc = Array.length cs in
        let site (y, (p : S.qname)) = Pr.def_site th (S.Coq_me_unit p.S.q_unit) (p.S.q_chain @ [ y ]) in
        let own s = match s.sl_link with Some (Member (_, h, ch)) -> Pr.def_site th h ch | _ -> None in
        let its = Array.of_list (List.map (fun s -> (s, own s)) cr.cr_sels) in
        let ni = Array.length its in
        let fits (s, o) k =
          fst cs.(k) = s.sl_name && (match o with None -> true | Some q -> site cs.(k) = Some q) in
        let fwd = Array.make ni None and bwd = Array.make ni None in
        let j = ref 0 in
        Array.iteri (fun i it ->
            let rec find k = if k >= nc then None else if fits it k then Some k else find (k + 1) in
            match find !j with Some k -> fwd.(i) <- Some k; j := k + 1 | None -> ()) its;
        let j = ref (nc - 1) in
        for i = ni - 1 downto 0 do
          let rec find k = if k < 0 then None else if fits its.(i) k then Some k else find (k - 1) in
          match find !j with Some k -> bwd.(i) <- Some k; j := k - 1 | None -> ()
        done;
        Array.iteri (fun i (s, o) ->
            if o = None then begin
              let line = match u.u_toks.(u.u_vars.(s.sl_var)).t with
                | P.VAR ((p, _), _) -> p.Lexing.pos_lnum | _ -> 0 in
              let note why = u.u_notes <- u.u_notes @ [ Printf.sprintf "%s, line %d, %s" s.sl_name line why ] in
              match fwd.(i), bwd.(i) with
              | Some e, Some l when e <= l ->
                  let p = snd cs.(e) in
                  let rec agree k = k > l || ((fst cs.(k) <> s.sl_name || snd cs.(k) = p) && agree (k + 1)) in
                  if agree e then
                    u.u_occ.(s.sl_var).link <- Some (Member (u.u_path, S.Coq_me_unit p.S.q_unit, p.S.q_chain @ [ s.sl_name ]))
                  else note "a member of one of several records"
              | _ -> note "a member of no record the checker found"
            end) its
      end) u.u_cmds

(* The global context of every unit, the output of its evals and the type
   it binds as the natural numbers, from the checker: each unit runs as its
   own program, as [mctt] runs it.  The log of a run holds only the evals of
   the program run, so a unit another one imports needs a run of its own.

   The bindings are those the run ends with: its own [builtin] commands and
   those of the units it imports, merged ([Builtin.bt_merge]).  They are
   those of every point of the unit at which [ℕ] occurs: a run only gains
   bindings and never rebinds one, and a unit using [ℕ] where nothing is
   bound is rejected. *)
let check_units ?(extra_roots = []) root (us : unit_info list) thetas outputs nats =
  List.iter (fun u ->
      let r = Ep.main (Main.load_path_in (root :: extra_roots)) Main.read_unit Main.parser_log_fuel (buf_of u.u_toks 0) in
      match r, PrettyPrinter.eval_outputs r with
      | Ep.AllGood (_, bt, th, gu, log), Some out ->
          let th = (u.u_path, gu) :: th in
          Hashtbl.replace thetas u.u_path th;
          record_selections u th gu log;
          Hashtbl.replace outputs u.u_path out;
          (* [builtins] is a record of one field, [builtins_nat], which extraction
             leaves unboxed: the record is the field. *)
          Option.iter (Hashtbl.replace nats u.u_path) (bt : S.qname option)
      | _ -> ()) us

(* The functions of [Rec] for the views of each group of a checked unit, at
   the name [Rec]'s anchor is at: the core names them ([grec_names]) after
   the declared members' [rec_x], in member order, from the group as filed
   at the path of its first member. *)
let rec_view_anchors (us : unit_info list) thetas =
  List.iter (fun u ->
      match Hashtbl.find_opt thetas u.u_path with
      | None -> ()
      | Some th ->
          List.iter (fun r ->
              match r.r_members with
              | [] -> ()
              | m0 :: _ ->
                  let p = { S.q_unit = u.u_path; S.q_chain = r.r_group @ [ m0 ] } in
                  match McttExtracted.Members.ind_lookup th [] p with
                  | None -> ()
                  | Some d ->
                      let views = List.filteri (fun i _ -> i >= List.length r.r_members)
                          (McttExtracted.Command0.grec_names th [] d) in
                      let o = u.u_occ.(r.r_name) in
                      o.extra <- o.extra @ List.map (fun x -> (anchor_of (r.r_chain @ [ "Rec" ]) x, Def)) views)
            u.u_recs) us

let load ?(check = true) ?(extra_roots = []) root : lib =
  let items = Hashtbl.create 64 in
  let files = List.rev (find_units root "" []) in
  let units, failed =
    List.fold_left (fun (us, fs) file ->
        let src = read_file (Filename.concat root (String.concat "/" file ^ ".mctt")) in
        match walk file src items with
        | u -> (u :: us, fs)
        | exception Misaligned m -> (us, (file, "misaligned: " ^ m) :: fs)
        | exception Failure m -> (us, (file, m) :: fs)
        | exception Lexer.Error m -> (us, (file, m) :: fs)) ([], []) files
  in
  let units = List.rev units and failed = List.rev failed in
  let thetas = Hashtbl.create 64 and outputs = Hashtbl.create 64 and nats = Hashtbl.create 64 in
  if check then check_units ~extra_roots root units thetas outputs nats;
  rec_view_anchors units thetas;
  { root; units; failed; thetas; outputs; nats; items }

(* ------------------------------------------------------------------ *)
(* Resolution *)

(* A member, by [def_site]; a member an open declares is followed to the
   member it names. *)
let rec resolve lib depth (l : link) : site option =
  match l with
  | Site s -> Some s
  | Member (u, h, ch) ->
      match Hashtbl.find_opt lib.thetas u with
      | None -> None
      | Some th ->
          match Pr.def_site th h ch with
          | None -> None
          | Some q ->
              let here = { s_unit = q.S.q_unit; s_anchor = String.concat "." q.S.q_chain } in
              match Hashtbl.find_opt lib.items (q.S.q_unit, q.S.q_chain) with
              | Some l' when depth < 100 ->
                  (match resolve lib (depth + 1) l' with Some s -> Some s | None -> Some here)
              | _ -> Some here

(* Where [ℕ] links to in the unit [u]: the type bound as the natural
   numbers, a member of the global context like any other; nothing if the
   unit binds none. *)
let nat_site lib (u : string list) : site option =
  match Hashtbl.find_opt lib.nats u with
  | Some p -> resolve lib 0 (Member (u, S.Coq_me_unit p.S.q_unit, p.S.q_chain))
  | None -> None

type stats = { names : int; linked : int; binders : int; unresolved : (string list * string * int) list;
               dangling : (string list * string * site) list }

(* Every name occurrence of the checked units: linked, a binder, or not
   resolved; and every link to an anchor that does not exist. *)
let stats lib : stats =
  let anchors = Hashtbl.create 1024 in
  List.iter (fun u -> Array.iter (fun o -> List.iter (fun (a, _) -> Hashtbl.replace anchors (u.u_path, a) ()) (occ_anchors o)) u.u_occ) lib.units;
  let names = ref 0 and linked = ref 0 and binders = ref 0 and unres = ref [] and dang = ref [] in
  List.iter (fun u ->
      let checked = Hashtbl.mem lib.thetas u.u_path in
      Array.iteri (fun i o ->
          incr names;
          let x, line = match u.u_toks.(u.u_vars.(i)).t with
            | P.VAR ((p, _), x) -> (x, p.Lexing.pos_lnum) | _ -> ("", 0) in
          match Option.bind o.link (resolve lib 0) with
          | Some s ->
              incr linked;
              (* A link into a unit outside the set documented, as the
                 library is for the examples, is not checked. *)
              if s.s_anchor <> "" && List.exists (fun u' -> u'.u_path = s.s_unit) lib.units
                 && not (Hashtbl.mem anchors (s.s_unit, s.s_anchor)) then
                dang := (u.u_path, x, s) :: !dang
          | None ->
              if o.anchor <> None then incr binders
              else if checked && not o.bare then unres := (u.u_path, x, line) :: !unres) u.u_occ) lib.units;
  { names = !names; linked = !linked; binders = !binders; unresolved = List.rev !unres; dangling = List.rev !dang }

(* A unit path as the printer spells it, joined by [›]. *)
let unit_name fq = String.concat "\u{203A}" fq

(* The contents of a unit that do not link: an entry whose anchor no name
   of the page declares, and an anchor declared twice, which a link cannot
   tell apart.  The page gives every declared anchor to its name, as [id],
   and each entry links to [#] its anchor ([render_unit]). *)
let toc_problems (u : unit_info) : string list =
  let n = Hashtbl.create 256 in
  Array.iter (fun o -> List.iter (fun (a, _) ->
      if a <> "" then Hashtbl.replace n a (1 + Option.value (Hashtbl.find_opt n a) ~default:0)) (occ_anchors o)) u.u_occ;
  let name = unit_name u.u_path in
  List.filter_map (fun e ->
      if Hashtbl.mem n e.te_anchor then None
      else Some (Printf.sprintf "%s: the contents entry %s links to a missing anchor #%s" name e.te_name e.te_anchor))
    u.u_toc
  @ List.sort compare (Hashtbl.fold (fun a k acc ->
      if k > 1 then Printf.sprintf "%s: the anchor #%s is declared %d times" name a k :: acc else acc) n [])

(* The problems [--check] reports, one per line. *)
let problems ?(resolve = true) (lib : lib) : string list =
  List.map (fun (f, m) -> Printf.sprintf "%s: %s" (String.concat "/" f) m) lib.failed
  @ List.concat_map toc_problems lib.units
  @ (if not resolve then [] else
       let s = stats lib in
       List.filter_map (fun u -> if Hashtbl.mem lib.thetas u.u_path then None
                         else Some (Printf.sprintf "%s: not checked" (unit_name u.u_path))) lib.units
       @ List.concat_map (fun u -> if Hashtbl.mem lib.thetas u.u_path
                           then List.map (fun n -> Printf.sprintf "%s: %s" (unit_name u.u_path) n) u.u_notes else []) lib.units
       @ List.filter_map (fun u -> match Hashtbl.find_opt lib.outputs u.u_path with
           | Some out when List.length out <> List.length u.u_evals ->
               Some (Printf.sprintf "%s: %d evals, %d outputs" (unit_name u.u_path)
                       (List.length u.u_evals) (List.length out))
           | _ -> None) lib.units
       @ List.map (fun (u, x, l) -> Printf.sprintf "%s: %s, line %d, not resolved" (unit_name u) x l) s.unresolved
       @ List.map (fun (u, x, t) -> Printf.sprintf "%s: %s links to a missing anchor %s#%s" (unit_name u) x
                      (unit_name t.s_unit) t.s_anchor) s.dangling
       (* A unit that binds [ℕ] and uses it: the type bound has a site. *)
       @ List.filter_map (fun u ->
           if Hashtbl.mem lib.nats u.u_path && nat_site lib u.u_path = None
              && Array.exists (fun t -> match t.t with P.NAT _ -> true | _ -> false) u.u_toks
           then Some (Printf.sprintf "%s: \u{2115} not resolved" (unit_name u.u_path)) else None) lib.units)

(* Where the [n]-th occurrence of the name [x] in the unit [fq] links to. *)
let link_of lib fq x n : string =
  match List.find_opt (fun u -> u.u_path = fq) lib.units with
  | None -> "no unit"
  | Some u ->
      let k = ref 0 and r = ref "no occurrence" in
      Array.iteri (fun i o ->
          match u.u_toks.(u.u_vars.(i)).t with
          | P.VAR ((p, _), y) when y = x ->
              incr k;
              if !k = n then
                r := Printf.sprintf "line %d: %s" p.Lexing.pos_lnum
                    (match Option.bind o.link (resolve lib 0) with
                     | Some s -> unit_name s.s_unit ^ "#" ^ s.s_anchor
                     | None -> (match o.anchor with Some a -> "declares #" ^ a | None -> "unresolved"))
          | _ -> ()) u.u_occ;
      !r

(* ------------------------------------------------------------------ *)
(* HTML *)

let esc s =
  let b = Buffer.create (String.length s) in
  String.iter (function '<' -> Buffer.add_string b "&lt;" | '>' -> Buffer.add_string b "&gt;"
                      | '&' -> Buffer.add_string b "&amp;" | '"' -> Buffer.add_string b "&quot;"
                      | c -> Buffer.add_char b c) s;
  Buffer.contents b

let page_name fq = String.concat "." fq ^ ".html"

(* A unit's name as HTML, a line break allowed after each separator, so a
   long name wraps between its parts on a narrow screen. *)
let unit_name_html fq = String.concat "\u{203A}<wbr>" (List.map esc fq)

let href (from : string list) (s : site) =
  (if s.s_unit = from then "" else page_name s.s_unit) ^ (if s.s_anchor = "" then "" else "#" ^ s.s_anchor)

let is_keyword = function
  | P.VAR _ | P.INT _ | P.LLIT _ | P.LLITL _ | P.OMEGA _ | P.OMEGA2 _ | P.EOF _ -> false
  | P.ARROW _ | P.AT _ | P.BAR _ | P.COLON _ | P.COLONCOLON _ | P.COMMA _ | P.DARROW _
  | P.LPAREN _ | P.RPAREN _ | P.LBRACE _ | P.RBRACE _ | P.PLUS _ | P.STAR _
  | P.DOT _ | P.EQ _ | P.SEMI _ -> false
  | _ -> true

(* The literals: numerals, level literals [3l] and [2L] (for [ω+2]), [ω]
   (or [omega]), the first infinite level, and [ω^2], the size of the large
   universes. *)
let is_num = function
  | P.INT _ | P.LLIT _ | P.LLITL _ | P.OMEGA _ | P.OMEGA2 _ -> true
  | _ -> false

let is_type_kw = function
  | P.NAT _ | P.TYPE _ | P.LEVEL _ | P.TRUE_TY _ | P.FALSE_TY _ -> true
  | _ -> false

let kind_class = function Local -> "var" | Def -> "def" | Mod -> "mod" | Unit -> "unit"

(* Comment prose: [code] becomes code, blank lines separate paragraphs,
   << … >> is a verbatim block, "- " starts an item. *)
let prose (txt : string) =
  let b = Buffer.create 256 in
  let lines = String.split_on_char '\n' txt in
  let ind l = let n = String.length l in let i = ref 0 in
    while !i < n && l.[!i] = ' ' do incr i done; if !i = n then max_int else !i in
  let m = List.fold_left (fun m l -> min m (ind l)) max_int (List.tl lines @ [ "" ]) in
  let lines = List.mapi (fun k l ->
      if k = 0 || m = max_int || String.length l < m then String.trim l
      else String.sub l m (String.length l - m)) lines in
  let inline s =
    let o = Buffer.create 64 and d = ref 0 in
    String.iter (fun c ->
        match c with
        | '[' -> if !d = 0 then Buffer.add_string o "<code>" else Buffer.add_char o '['; incr d
        | ']' when !d > 0 -> decr d; if !d = 0 then Buffer.add_string o "</code>" else Buffer.add_char o ']'
        | c -> Buffer.add_string o (esc (String.make 1 c))) s;
    if !d > 0 then Buffer.add_string o "</code>";
    Buffer.contents o
  in
  let para = Buffer.create 128 and verb = ref false and vbuf = Buffer.create 128 in
  let flush () =
    if Buffer.length para > 0 then begin
      Buffer.add_string b ("<p>" ^ inline (Buffer.contents para) ^ "</p>\n"); Buffer.clear para end in
  List.iter (fun l ->
      let t = String.trim l in
      if !verb then
        (if t = ">>" then begin
           verb := false;
           Buffer.add_string b ("<pre class=\"verb\">" ^ esc (Buffer.contents vbuf) ^ "</pre>\n");
           Buffer.clear vbuf end
         else (Buffer.add_string vbuf l; Buffer.add_char vbuf '\n'))
      else if t = "<<" then (flush (); verb := true)
      else if t = "" then flush ()
      else if String.length t > 2 && t.[0] = '-' && t.[1] = ' ' then
        (flush (); Buffer.add_string para ("&bull; " ^ String.sub t 2 (String.length t - 2)))
      else (if Buffer.length para > 0 then Buffer.add_char para ' '; Buffer.add_string para t)) lines;
  flush (); Buffer.contents b

let comment_text src (a, e) = String.sub src (a + 2) (e - a - 4)

(* The column of byte [p], in characters: UTF-8 continuation bytes do not
   count, so a line with [→] or [ℕ] before [p] aligns as displayed. *)
let col src p =
  let i = ref p and n = ref 0 in
  while !i > 0 && src.[!i - 1] <> '\n' do
    decr i; if Char.code src.[!i] land 0xC0 <> 0x80 then incr n
  done;
  !n

let line_start src p =
  let i = ref (p - 1) in
  while !i >= 0 && (src.[!i] = ' ' || src.[!i] = '\t') do decr i done;
  !i < 0 || src.[!i] = '\n'

let nav = "<nav><a href=\"index.html\">McTT library</a> &middot; <a href=\"../index.html\">McTT</a> \
           &middot; <a href=\"../toc.html\">Rocq development</a></nav>\n"

(* The kind of every anchor, for the class of a link to it. *)
let anchor_kinds lib =
  let t = Hashtbl.create 1024 in
  List.iter (fun u -> Array.iter (fun o ->
      List.iter (fun (a, k) -> Hashtbl.replace t (u.u_path, a) k) (occ_anchors o)) u.u_occ) lib.units;
  t

(* An eval's output, folded: [<details>] opens and closes it without
   scripts, and a click on the open output closes it too.  The box starts
   at the eval's column [--col]; on a narrow screen the stylesheet caps
   that indent, so a deep eval's output still fits the screen. *)
let eval_box (c : int) (out : string) : string =
  Printf.sprintf "<details class=\"eval\" style=\"--col:%dch\"><summary>output</summary>\
                  <pre class=\"out\" onclick=\"this.parentElement.open=false\">%s</pre></details>\n" c (esc out)

(* Without it a phone lays the page out at a desktop's width, and the
   stylesheet's narrow layout never applies. *)
let viewport = "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"

(* The contents as a tree: an entry's children are the entries after it
   that are deeper, up to the next one that is not.  A module's members
   and an inductive's constructors follow its name in the source. *)
type toc = Toc of toc_entry * toc list

let rec toc_forest d (es : toc_entry list) : toc list * toc_entry list =
  match es with
  | e :: rest when e.te_depth >= d ->
      let kids, rest = toc_forest (e.te_depth + 1) rest in
      let sibs, rest = toc_forest d rest in
      (Toc (e, kids) :: sibs, rest)
  | _ -> ([], es)

(* The contents of the unit [fq], one entry per declaration, nested as
   its modules are; an entry with members folds them in a [<details>].
   One [<nav>] serves both layouts of the stylesheet: a side panel beside
   the text on a wide screen; on a narrow one, a drawer the "Contents"
   button opens, as the target of its link, and any link closes, the
   entries' included, as the target moves to their anchor.  [#-close] is
   no anchor, so it closes the drawer in place; names never start with
   [-], so neither [-contents] nor [-close] is a name's anchor. *)
let toc_html fq (es : toc_entry list) : string =
  let b = Buffer.create 1024 in
  let rec node (Toc (e, kids)) =
    let line = Printf.sprintf "<span class=\"kw\">%s</span> <a class=\"%s\" href=\"#%s\">%s</a>"
        (esc e.te_kw) (kind_class e.te_kind) (esc e.te_anchor) (esc e.te_name) in
    match kids with
    | [] -> Printf.bprintf b "<li>%s</li>" line
    | _ ->
        Printf.bprintf b "<li><details open><summary>%s</summary><ul>" line;
        List.iter node kids; Buffer.add_string b "</ul></details></li>"
  in
  Printf.bprintf b "<a class=\"toc-open\" href=\"#-contents\">&#9776; Contents</a>\n\
                    <nav class=\"toc\" id=\"-contents\" aria-label=\"Contents\"><div class=\"toc-head\">\
                    <a href=\"#\">%s</a> <a class=\"toc-close\" href=\"#-close\" aria-label=\"Close\">&times;</a></div><ul>"
    (unit_name_html fq);
  List.iter node (fst (toc_forest 0 es));
  Buffer.add_string b "</ul></nav>\n";
  Buffer.contents b

let render_unit lib kinds (u : unit_info) : string =
  let src = u.u_src in
  let b = Buffer.create (4 * String.length src) in
  let var_ix = Hashtbl.create 64 in
  let nat = nat_site lib u.u_path in
  Array.iteri (fun i t -> Hashtbl.replace var_ix t i) u.u_vars;
  let evs =
    List.map (fun c -> (fst c, `C c)) u.u_comments
    @ List.filter_map Fun.id (Array.to_list (Array.mapi (fun i t ->
        match t.t with P.EOF _ -> None | _ -> Some (t.s, `T i)) u.u_toks)) in
  let evs = List.sort compare evs in
  let in_code = ref false and pos = ref 0 in
  let open_code () = if not !in_code then (Buffer.add_string b "<pre class=\"code\">"; in_code := true) in
  let close_code () = if !in_code then (Buffer.add_string b "</pre>\n"; in_code := false) in
  let gap upto =
    if !in_code then Buffer.add_string b (esc (String.sub src !pos (upto - !pos)));
    pos := upto
  in
  (* The output boxes: by the last token of their eval, the box's column and
     text.  None if the unit's outputs are missing or out of step. *)
  let boxes = Hashtbl.create 16 in
  (match Hashtbl.find_opt lib.outputs u.u_path with
   | Some out when List.length out = List.length u.u_evals ->
       List.iter2 (fun (i, j) o -> Hashtbl.add boxes j (col src u.u_toks.(i).s, o)) u.u_evals out
   | _ -> ());
  let pending = ref [] in
  (* The boxes of the evals ended so far go below the line they end on:
     the code block closes at the first line break before [upto]. *)
  let flush upto =
    if !pending <> [] then
      match String.index_from_opt src !pos '\n' with
      | Some k when k < upto ->
          gap k; pos := k + 1; close_code ();
          List.iter (fun (c, o) -> Buffer.add_string b (eval_box c o)) (List.rev !pending);
          pending := []
      | _ -> ()
  in
  List.iter (fun (p, ev) ->
      flush p;
      match ev with
      | `C (a, e) when line_start src a && col src a = 0 ->
          (* a comment at the start of a line is prose between code blocks *)
          if !in_code then begin
            let g = String.sub src !pos (a - !pos) in
            let g = match String.rindex_opt g '\n' with Some k -> String.sub g 0 k | None -> g in
            Buffer.add_string b (esc g); pos := a; close_code ()
          end;
          pos := e;
          Buffer.add_string b ("<div class=\"doc\">" ^ prose (comment_text src (a, e)) ^ "</div>\n");
          if !pos < String.length src && src.[!pos] = '\n' then incr pos
      | `C (a, e) ->
          gap a; open_code ();
          Buffer.add_string b ("<span class=\"com\">" ^ esc (String.sub src a (e - a)) ^ "</span>"); pos := e
      | `T i ->
          let t = u.u_toks.(i) in
          if not !in_code then begin
            let k = ref p in while !k > !pos && src.[!k - 1] <> '\n' do decr k done;
            pos := !k; open_code ()
          end;
          gap t.s;
          let txt = esc (String.sub src t.s (t.e - t.s)) in
          (match t.t with
           | P.VAR _ when Hashtbl.mem var_ix i ->
               let o = u.u_occ.(Hashtbl.find var_ix i) in
               let target = Option.bind o.link (resolve lib 0) in
               let cls = match o.kind, target with
                 | Some k, _ -> kind_class k
                 | None, Some s when s.s_anchor = "" -> "unit"
                 | None, Some s ->
                     (match Hashtbl.find_opt kinds (s.s_unit, s.s_anchor) with
                      | Some k -> kind_class k | None -> "def")
                 | None, None -> "free" in
               let cls = if o.anchor <> None then cls ^ " bind" else cls in
               let id = match o.anchor with Some a when a <> "" -> Printf.sprintf " id=\"%s\"" (esc a) | _ -> "" in
               (* The extra anchors wrap the name, so a link to one shows it. *)
               List.iter (fun (a, _) -> Printf.bprintf b "<span id=\"%s\">" (esc a)) o.extra;
               (match target with
                | Some s -> Printf.bprintf b "<a class=\"%s\"%s href=\"%s\">%s</a>" cls id (esc (href u.u_path s)) txt
                | None -> Printf.bprintf b "<span class=\"%s\"%s>%s</span>" cls id txt);
               List.iter (fun _ -> Buffer.add_string b "</span>") o.extra
           | P.NAT _ when nat <> None ->
               Printf.bprintf b "<a class=\"ty\" href=\"%s\">%s</a>" (esc (href u.u_path (Option.get nat))) txt
           | tk when is_num tk -> Printf.bprintf b "<span class=\"num\">%s</span>" txt
           | tk when is_type_kw tk -> Printf.bprintf b "<span class=\"ty\">%s</span>" txt
           | tk when is_keyword tk -> Printf.bprintf b "<span class=\"kw\">%s</span>" txt
           | _ -> Printf.bprintf b "<span class=\"sym\">%s</span>" txt);
          pos := t.e;
          pending := List.rev_append (Hashtbl.find_all boxes i) !pending) evs;
  flush (String.length src + 1);
  if !in_code then begin
    Buffer.add_string b (esc (String.trim (String.sub src !pos (String.length src - !pos)))); close_code ()
  end;
  let name = unit_name u.u_path in
  Printf.sprintf
    "<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\">%s<title>%s</title>\
     <link rel=\"stylesheet\" href=\"mctt.css\"></head><body class=\"unit-page\">\n%s%s\
     <h1>%s</h1>\n%s</body></html>\n"
    viewport name (toc_html u.u_path u.u_toc) nav (unit_name_html u.u_path) (Buffer.contents b)

let summary (u : unit_info) =
  match u.u_comments with
  | (a, e) :: _ when line_start u.u_src a ->
      let t = String.trim (comment_text u.u_src (a, e)) in
      let t = String.concat " " (List.filter (( <> ) "")
          (String.split_on_char ' ' (String.map (function '\n' -> ' ' | c -> c) t))) in
      let t = match String.index_opt t '.' with Some k -> String.sub t 0 (k + 1) | None -> t in
      prose t
  | _ -> ""

let css = {|body{max-width:58em;margin:2em auto;padding:0 1em;font-family:"Iowan Old Style","Palatino Linotype",Georgia,serif;line-height:1.5;color:#222;background:#fdfdfb}
nav{font-size:.9em;margin-bottom:1em}nav a{color:#555}
h1{font-family:Menlo,Consolas,monospace;font-size:1.5em;border-bottom:1px solid #ddd;padding-bottom:.3em}
pre.code{font-family:"JetBrains Mono",Menlo,Consolas,monospace;font-size:.88em;background:#f6f7f9;border-left:3px solid #c9d3e0;padding:.6em 1em;overflow-x:auto;line-height:1.4}
pre.verb{font-family:Menlo,Consolas,monospace;font-size:.88em;background:#fafafa;padding:.4em 1em}
div.doc{margin:1em 0}div.doc code{font-family:Menlo,Consolas,monospace;font-size:.9em;background:#f1f1ee;padding:0 .2em}
.kw{color:#8a2be2;font-weight:600}.ty{color:#0b7a75}.num{color:#b35c00}.sym{color:#777}
.com{color:#6a737d;font-style:italic}
a.def,a.mod,a.unit,a.var,a.ty{text-decoration:none}a:hover{text-decoration:underline}
.def{color:#1f4fa3}.mod{color:#a3341f}.unit{color:#a3341f}.var{color:#333}.free{color:#c00}
.bind.def,.bind.mod{font-weight:700}
:target{background:#fff3b0}
nav.toc,nav.toc:target{font-family:Menlo,Consolas,monospace;font-size:.8em;line-height:1.5;background:#f7f7f4;margin:0;box-sizing:border-box}
nav.toc ul{list-style:none;margin:0;padding-left:1.2em}nav.toc>ul{padding-left:0}
nav.toc li{margin:.05em 0;overflow-wrap:anywhere}nav.toc summary{cursor:pointer}
nav.toc a{text-decoration:none}nav.toc a:hover{text-decoration:underline}
nav.toc .toc-head{font-weight:700;padding-bottom:.4em;margin-bottom:.4em;border-bottom:1px solid #ddd}
nav.toc .toc-head a{color:#a3341f}
a.toc-open,a.toc-close{display:none}
@media (min-width:64em){
body.unit-page{margin-left:max(20rem,calc(50vw - 29em))}
nav.toc{position:fixed;top:0;left:0;bottom:0;width:18rem;overflow-y:auto;padding:1em;border-right:1px solid #ddd}
}
@media (max-width:63.99em){
nav.toc{display:none}
nav.toc:target{display:block;position:fixed;top:0;left:0;right:0;bottom:0;z-index:10;overflow-y:auto;padding:1em 1.2em;font-size:.95em}
nav.toc .toc-head{display:flex;justify-content:space-between}
a.toc-open{display:block;position:fixed;top:.5em;right:.5em;z-index:5;padding:.2em .7em;font-size:.9em;color:#333;text-decoration:none;background:#fdfdfb;border:1px solid #c9d3e0;border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,.15)}
a.toc-close{display:inline;font-size:1.4em;line-height:1;color:#555}
:target{scroll-margin-top:2.6em}
}
details.eval{font-family:"JetBrains Mono",Menlo,Consolas,monospace;font-size:.88em;margin-top:-.6em;margin-bottom:.6em;padding-left:1em;margin-left:var(--col,0)}
details.eval summary{cursor:pointer;color:#6a737d;font-size:.9em;width:max-content}
details.eval pre.out{cursor:pointer;margin:.2em 0;padding:.3em .8em;border:1px solid #dde3ea;border-radius:3px;background:#fbfcfd;white-space:pre-wrap;line-height:1.4}
ul.units{list-style:none;padding-left:0}ul.units li{margin:.5em 0}ul.units p{display:inline;margin:0;color:#555}
html{-webkit-text-size-adjust:100%;text-size-adjust:100%}
@media (max-width:40em){
body{overflow-wrap:anywhere}
pre.verb{overflow-x:auto}
details.eval{margin-left:min(var(--col,0px),25%)}
}
|}

let rec mkdir_p d =
  if not (Sys.file_exists d) then begin mkdir_p (Filename.dirname d); Sys.mkdir d 0o755 end

let write_site lib out =
  mkdir_p out;
  let w f s = Out_channel.with_open_bin (Filename.concat out f) (fun oc -> output_string oc s) in
  w "mctt.css" css;
  let kinds = anchor_kinds lib in
  List.iter (fun u -> w (page_name u.u_path) (render_unit lib kinds u)) lib.units;
  let item u = Printf.sprintf "<li><a class=\"unit\" href=\"%s\">%s</a> %s</li>\n"
      (page_name u.u_path) (unit_name_html u.u_path) (summary u) in
  let prel, progs = List.partition (fun u -> List.hd u.u_path = "Prelude") lib.units in
  w "index.html"
    (Printf.sprintf "<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\">%s<title>McTT library</title>\
                     <link rel=\"stylesheet\" href=\"mctt.css\"></head><body>\n%s<h1>The McTT library</h1>\n\
                     <h2>Prelude</h2><ul class=\"units\">%s</ul><h2>Programs</h2><ul class=\"units\">%s</ul></body></html>\n"
       viewport nav (String.concat "" (List.map item prel)) (String.concat "" (List.map item progs)))
