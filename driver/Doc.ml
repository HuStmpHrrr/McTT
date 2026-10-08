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
     (Extraction/Privacy.v), over the global context the checker built.

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

type occ = { mutable link : link option; mutable anchor : string option; mutable kind : kind option }

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
   denotes.  [vs] lists one per [en_var] entry of [sc], in order. *)
type vb = { v_link : link; v_mod : mden }

type env = { sc : E.ent list; vs : vb list }

let push x v env = { sc = E.Coq_en_var x :: env.sc; vs = v :: env.vs }

type st = {
  unit : string list;          (* the unit's declared path *)
  toks : tok array;
  vars : int array;            (* token index of the i-th VAR *)
  occ : occ array;             (* indexed like [vars] *)
  mutable cur : int;           (* the next VAR to pair *)
  items : (string list * string list, link) Hashtbl.t;  (* open items, see [items] below *)
  decls : (string * kind) list ref;                     (* the unit's top-level declarations *)
  mutable notes : string list;
  mutable evals : (C.obj * C.obj option) list;  (* the evals walked, last first *)
}

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
       | E.Coq_en_var _ ->
           if E.binders env.sc <> List.length env.vs then
             raise (Misaligned "scope out of step with its binders");
           Some (e, Some (List.nth env.vs k))
       | _ -> Some (e, None))

let opt_list = function Some c -> [ c ] | None -> []

let qname_mden (p : S.qname) = MGlobal (S.Coq_me_unit p.S.q_unit, p.S.q_chain)

(* A head name, in term or module position. *)
let head st env i x : mden =
  match lookup env x with
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
  Option.iter (refer st i) (member_link st m y);
  member_mden m y

let unit_path st fq =
  List.iter (fun x -> let i = next st x in refer st i (Site { s_unit = fq; s_anchor = "" })) fq

(* ------------------------------------------------------------------ *)
(* Objects: the binders of [Elaborator.elab], clause by clause. *)

let rec term st env (o : C.obj) : unit =
  match o with
  | C.Coq_typ _ | C.Coq_level | C.Coq_llit _
  | C.Coq_nat | C.Coq_zero | C.Coq_true_ty | C.Coq_true_tm | C.Coq_false_ty -> ()
  | C.Coq_suniv o | C.Coq_succl o -> term st env o
  | C.Coq_maxl (o1, o2) -> term st env o1; term st env o2
  | C.Coq_succ o -> term st env o
  | C.Coq_natrec (n, mx, m, z, sx, sr, s) ->
      term st env n;
      let a = bind st mx in term st (push mx a env) m;
      term st env z;
      let b = bind st sx in let c = bind st sr in
      term st (push sr c (push sx b env)) s
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
          let j = (match tok_after_var st i with P.AS _ -> next st d | _ -> i) in
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

(* [cmd st fp ch o ov f fv c]: the command [c] in the frame at member chain
   [ch], whose entries are [f] inside the scope [o]; [fv] and [ov] are the
   binders of [f] and [o].  The frame's next entries are [elab_cmd]'s. *)
let rec cmd st fp ch (o, ov) (f, fv) (c : C.cmd) : E.ent list =
  let env = { sc = f @ o; vs = fv @ ov } in
  let decl x k =
    let i = next st x in
    declare st i (anchor_of ch x) k;
    if ch = [] then st.decls := !(st.decls) @ [ (x, k) ];
    i
  in
  (match c with
   | C.Coq_c_def (_, x, a, b) -> let i = decl x Def in def_parts st env i a b
   | C.Coq_c_axiom (x, a) -> ignore (decl x Def); term st env a
   | C.Coq_c_mod (_, x, ps, md) ->
       ignore (decl x Mod);
       let env', vbs = params st env ps in
       (match md with
        | C.Coq_md_where body ->
            ignore (cmds st fp (ch @ [ x ]) (f @ o, fv @ ov) (E.pents ps, List.rev vbs) body)
        | C.Coq_md_alias e -> ignore (modv st env' e))
   | C.Coq_c_import fq -> unit_path st fq
   | C.Coq_c_open (fq, ip, args, its) ->
       let m = target st env fq ip args in
       List.iter (fun (d, i, _, l) ->
           declare st i (anchor_of ch d) (if l = None then Mod else Def);
           Option.iter (Hashtbl.replace st.items (fp, ch @ [ d ])) l) (items st m its)
   | C.Coq_c_eval (e, t) -> st.evals <- (e, t) :: st.evals; term st env e; Option.iter (term st env) t
   | C.Coq_c_error e -> raise (Misaligned ("rejected by the parser: " ^ e)));
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
  u_decls : (string * kind) list;
  u_notes : string list;
  u_evals : (int * int) list;  (* each eval's first and last token, in order *)
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
    | P.REMARK _ | P.LET _ | P.GIVEN _ | P.AXIOM _ | P.IMPORT _ | P.OPEN _ | P.EVAL _
    | P.END _ | P.EOF _ -> true
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
      (List.mapi (fun i t -> match t.t with P.VAR _ -> Some i | _ -> None) (Array.to_list toks))) in
  let occ = Array.init (Array.length vars) (fun _ -> { link = None; anchor = None; kind = None }) in
  let st = { unit = fp; toks; vars; occ; cur = 0; items; decls = ref []; notes = []; evals = [] } in
  let l = List.fold_left (lead st fp) [] leads in
  List.iter (fun x -> let i = next st x in declare st i "" Unit) fp;
  let env, vbs = params st { sc = l; vs = [] } ps in
  ignore env;
  (* The leading commands again, as the frame's first commands. *)
  let f = List.fold_left (fun f c -> next_frame st fp [] l f c) (E.pents ps) leads in
  ignore (cmds st fp [] (l, []) (f, List.rev vbs) cs);
  if st.cur <> Array.length vars then
    raise (Misaligned (Printf.sprintf "%d of %d names paired" st.cur (Array.length vars)));
  { u_file = file; u_path = fp; u_src = src; u_toks = toks; u_comments = comments src toks;
    u_vars = vars; u_occ = occ; u_decls = !(st.decls); u_notes = List.rev st.notes;
    u_evals = eval_spans toks (List.rev st.evals) }

let rec find_units root dir acc =
  let a = Sys.readdir (Filename.concat root dir) in
  Array.sort compare a;
  Array.fold_left (fun acc f ->
      let rel = if dir = "" then f else dir ^ "/" ^ f in
      if Sys.is_directory (Filename.concat root rel) then find_units root rel acc
      else if Filename.check_suffix f ".mctt" then
        String.split_on_char '/' (Filename.chop_suffix rel ".mctt") :: acc
      else acc) acc a

type lib = {
  root : string;
  units : unit_info list;                       (* in file order *)
  failed : (string list * string) list;         (* files that do not line up *)
  thetas : (string list, S.gdeps) Hashtbl.t;    (* each checked unit's global context *)
  outputs : (string list, string list) Hashtbl.t;  (* each checked unit's evals, as [mctt] prints them *)
  items : (string list * string list, link) Hashtbl.t;
}

(* The global context of every unit and the output of its evals, from the
   checker: each unit runs as its own program, as [mctt] runs it.  The log
   of a run holds only the evals of the program run, so a unit another one
   imports needs a run of its own. *)
let check_units root (us : unit_info list) thetas outputs =
  List.iter (fun u ->
      let r = Ep.main (Main.load_path root) Main.read_unit Main.parser_log_fuel (buf_of u.u_toks 0) in
      match r, PrettyPrinter.eval_outputs r with
      | Ep.AllGood (_, th, gu, _), Some out ->
          Hashtbl.replace thetas u.u_path ((u.u_path, gu) :: th);
          Hashtbl.replace outputs u.u_path out
      | _ -> ()) us

let load ?(check = true) root : lib =
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
  let thetas = Hashtbl.create 64 and outputs = Hashtbl.create 64 in
  if check then check_units root units thetas outputs;
  { root; units; failed; thetas; outputs; items }

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

type stats = { names : int; linked : int; binders : int; unresolved : (string list * string * int) list;
               dangling : (string list * string * site) list }

(* Every name occurrence of the checked units: linked, a binder, or not
   resolved; and every link to an anchor that does not exist. *)
let stats lib : stats =
  let anchors = Hashtbl.create 1024 in
  List.iter (fun u -> Array.iter (fun o -> Option.iter (fun a -> Hashtbl.replace anchors (u.u_path, a) ()) o.anchor) u.u_occ) lib.units;
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
              if s.s_anchor <> "" && not (Hashtbl.mem anchors (s.s_unit, s.s_anchor)) then
                dang := (u.u_path, x, s) :: !dang
          | None ->
              if o.anchor <> None then incr binders
              else if checked then unres := (u.u_path, x, line) :: !unres) u.u_occ) lib.units;
  { names = !names; linked = !linked; binders = !binders; unresolved = List.rev !unres; dangling = List.rev !dang }

(* A unit path as the printer spells it, joined by [›]. *)
let unit_name fq = String.concat "\u{203A}" fq

(* The problems [--check] reports, one per line. *)
let problems ?(resolve = true) (lib : lib) : string list =
  List.map (fun (f, m) -> Printf.sprintf "%s: %s" (String.concat "/" f) m) lib.failed
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
                      (unit_name t.s_unit) t.s_anchor) s.dangling)

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

let href (from : string list) (s : site) =
  (if s.s_unit = from then "" else page_name s.s_unit) ^ (if s.s_anchor = "" then "" else "#" ^ s.s_anchor)

let is_keyword = function
  | P.VAR _ | P.INT _ | P.LLIT _ | P.LLITL _ | P.OMEGA _ | P.EOF _ -> false
  | P.ARROW _ | P.AT _ | P.BAR _ | P.COLON _ | P.COLONCOLON _ | P.COMMA _ | P.DARROW _
  | P.LPAREN _ | P.RPAREN _ | P.LBRACE _ | P.RBRACE _ | P.PLUS _
  | P.DOT _ | P.EQ _ | P.SEMI _ -> false
  | _ -> true

(* The literals: numerals, level literals [3l], large sizes [2L], and [ω]
   (or [omega]), the size of the first large universe. *)
let is_num = function
  | P.INT _ | P.LLIT _ | P.LLITL _ | P.OMEGA _ -> true
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
      match o.anchor, o.kind with
      | Some a, Some k -> Hashtbl.replace t (u.u_path, a) k
      | _ -> ()) u.u_occ) lib.units;
  t

(* An eval's output, folded: [<details>] opens and closes it without
   scripts, and a click on the open output closes it too. *)
let eval_box (c : int) (out : string) : string =
  Printf.sprintf "<details class=\"eval\" style=\"margin-left:%dch\"><summary>output</summary>\
                  <pre class=\"out\" onclick=\"this.parentElement.open=false\">%s</pre></details>\n" c (esc out)

let render_unit lib kinds (u : unit_info) : string =
  let src = u.u_src in
  let b = Buffer.create (4 * String.length src) in
  let var_ix = Hashtbl.create 64 in
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
           | P.VAR _ ->
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
               (match target with
                | Some s -> Printf.bprintf b "<a class=\"%s\"%s href=\"%s\">%s</a>" cls id (esc (href u.u_path s)) txt
                | None -> Printf.bprintf b "<span class=\"%s\"%s>%s</span>" cls id txt)
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
  let toc = String.concat "" (List.map (fun (x, k) ->
      Printf.sprintf "<li><span class=\"kw\">%s</span> <a href=\"#%s\">%s</a></li>"
        (match k with Mod -> "module" | _ -> "def") (esc x) (esc x)) u.u_decls) in
  Printf.sprintf
    "<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\"><title>%s</title>\
     <link rel=\"stylesheet\" href=\"mctt.css\"></head><body>\n%s\
     <h1>%s</h1>\n<details class=\"toc\"><summary>Contents</summary><ul>%s</ul></details>\n%s</body></html>\n"
    name nav name toc (Buffer.contents b)

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
a.def,a.mod,a.unit,a.var{text-decoration:none}a:hover{text-decoration:underline}
.def{color:#1f4fa3}.mod{color:#a3341f}.unit{color:#a3341f}.var{color:#333}.free{color:#c00}
.bind.def,.bind.mod{font-weight:700}
:target{background:#fff3b0}
details.toc{font-size:.9em;margin-bottom:1em}details.toc ul{columns:3;list-style:none;padding-left:1em}
details.eval{font-family:"JetBrains Mono",Menlo,Consolas,monospace;font-size:.88em;margin-top:-.6em;margin-bottom:.6em;padding-left:1em}
details.eval summary{cursor:pointer;color:#6a737d;font-size:.9em;width:max-content}
details.eval pre.out{cursor:pointer;margin:.2em 0;padding:.3em .8em;border:1px solid #dde3ea;border-radius:3px;background:#fbfcfd;white-space:pre-wrap;line-height:1.4}
ul.units{list-style:none;padding-left:0}ul.units li{margin:.5em 0}ul.units p{display:inline;margin:0;color:#555}
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
      (page_name u.u_path) (unit_name u.u_path) (summary u) in
  let prel, progs = List.partition (fun u -> List.hd u.u_path = "Prelude") lib.units in
  w "index.html"
    (Printf.sprintf "<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\"><title>McTT library</title>\
                     <link rel=\"stylesheet\" href=\"mctt.css\"></head><body>\n%s<h1>The McTT library</h1>\n\
                     <h2>Prelude</h2><ul class=\"units\">%s</ul><h2>Programs</h2><ul class=\"units\">%s</ul></body></html>\n"
       nav (String.concat "" (List.map item prel)) (String.concat "" (List.map item progs)))
