open McttExtracted.Entrypoint
open McttExtracted.Command1
module Command1 = McttExtracted.Command1
open McttExtracted.Syntax
module Parser = McttExtracted.Parser
module ParserMessages = McttExtracted.ParserMessages

(************************************************************)
(* Formatting helpers *)
(************************************************************)

let pp_print_paren_if
    (cond : bool)
    (body : Format.formatter -> unit -> unit)
    (f : Format.formatter)
    () : unit =
  if cond then Format.pp_print_char f '(';
  body f ();
  if cond then Format.pp_print_char f ')'

(* The printer's spellings of the tokens that have a Unicode form.  Each is
   one character wide, which Format is told with [pp_print_as] or [@<1>%s],
   since it counts bytes. *)
let s_arrow = "\u{2192}" (* → for -> *)
let s_darrow = "\u{21D2}" (* ⇒ for => *)
let s_lambda = "\u{03BB}" (* λ for fun *)
let s_pi = "\u{2200}" (* ∀ for forall; Π is also accepted *)
let s_eq = "\u{2254}" (* ≔ for := *)
let s_coloncolon = "\u{203A}" (* › for :: *)
let s_nat = "\u{2115}" (* ℕ for Nat *)
let s_true_ty = "\u{22A4}" (* ⊤ for True *)
let s_false_ty = "\u{22A5}" (* ⊥ for False *)
let s_true_tm = "\u{22C6}" (* ⋆ for true *)
let s_omega = "\u{03C9}" (* ω for omega *)
let s_cdot = "\u{00B7}" (* · for * *)

let pp_sym (f : Format.formatter) (s : string) : unit = Format.pp_print_as f 1 s

(* A string that may contain Unicode, at its width in characters: the bytes
   that are not UTF-8 continuation bytes. *)
let utf8_width (s : string) : int =
  let n = ref 0 in
  String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr n) s;
  !n

let pp_u (f : Format.formatter) (s : string) : unit = Format.pp_print_as f (utf8_width s) s

(* [Format.pp_print_text] with the words at their width in characters: a
   space is a break hint, a newline a forced one. *)
let pp_text_u (f : Format.formatter) (s : string) : unit =
  List.iteri
    (fun i line ->
      if i > 0 then Format.pp_force_newline f ();
      List.iteri
        (fun j w -> if j > 0 then Format.pp_print_space f (); pp_u f w)
        (String.split_on_char ' ' line))
    (String.split_on_char '\n' s)

(************************************************************)
(* Formatting Cst.obj *)
(************************************************************)
let rec get_nat_of_obj : Cst.obj -> int option = function
  | Cst.Coq_num n -> Some n
  | _ -> None

let rec get_fn_params_of_obj : Cst.obj -> (string * Cst.obj) list * Cst.obj =
  function
  | Cst.Coq_fn (px, ep, ebody) ->
     let params, ebody' = get_fn_params_of_obj ebody in
     ((px, ep) :: params, ebody')
  | ebody -> ([], ebody)

let rec get_pi_params_of_obj : Cst.obj -> (string * Cst.obj) list * Cst.obj =
  function
  | Cst.Coq_pi (px, ep, eret) ->
     let params, eret' = get_pi_params_of_obj eret in
     ((px, ep) :: params, eret')
  | eret -> ([], eret)

(* A run of nested [letb]s prints as one [let] with several bindings, which is
   how it was written. *)
let rec get_letb_decls_of_obj : Cst.obj -> Cst.decl list * Cst.obj = function
  | Cst.Coq_letb (d, ebody) ->
     let decls, ebody' = get_letb_decls_of_obj ebody in
     (d :: decls, ebody')
  | ebody -> ([], ebody)

let format_mods (f : Format.formatter) (m : Cst.mods) : unit =
  if m.Cst.md_private then Format.pp_print_string f "private ";
  if m.Cst.md_abstract then Format.pp_print_string f "abstract "

(* The items of an open: [as W] first, then the member items, consecutive
   ones of the same privacy sharing a [use] or [export] list; [c] is the item
   [(c, c)], [c as d] is [(c, d)]. *)
let format_items (f : Format.formatter) (its : ((string option * string) * bool) list) : unit =
  let open Format in
  List.iter (function ((None, w), _) -> fprintf f " as %s" w | _ -> ()) its;
  let item (n, d) = if n = d then n else n ^ " as " ^ d in
  let rec groups = function
    | [] -> []
    | ((Some n, d), pv) :: rest ->
       (match groups rest with
        | (pv', l) :: gs when pv' = pv -> (pv, item (n, d) :: l) :: gs
        | gs -> (pv, [item (n, d)]) :: gs)
    | ((None, _), _) :: rest -> groups rest in
  List.iter
    (fun (pv, l) -> fprintf f " %s (%s)" (if pv then "use" else "export") (String.concat "; " l))
    (groups its)

(* A unit path, its names joined by [›]. *)
let string_of_upath (fp : string list) : string = String.concat s_coloncolon fp

(* [›] joins a file path and [.] an internal one; either half may be empty. *)
let string_of_qpath (fp : string list) (ip : string list) : string =
  match (fp, ip) with
  | [], _ -> String.concat "." ip
  | _, [] -> string_of_upath fp
  | _, _ -> string_of_upath fp ^ "." ^ String.concat "." ip

let pp_upath (f : Format.formatter) (fp : string list) : unit = pp_u f (string_of_upath fp)

let rec format_obj_prec (p : int) (f : Format.formatter) : Cst.obj -> unit =
  let open Format in
  function
  (* A universe prints at its shortest spelling: at a finite literal level
     as [Type@<n>], at [ω] as [Type@ω], at [ω+n] as [Type@<n>L], and at any
     other level as [Type@{t}].  The large universe [ω²+i] prints as
     [Type@{ω^2}] or [Type@{ω^2+i}], its surface syntax. *)
  | Cst.Coq_typ 0 -> fprintf f "Type@@{@<1>%s^2}" s_omega
  | Cst.Coq_typ i -> fprintf f "Type@@{@<1>%s^2+%d}" s_omega i
  | Cst.Coq_suniv (Cst.Coq_llit (0, n)) -> fprintf f "Type@@%d" n
  | Cst.Coq_suniv (Cst.Coq_llit (1, 0)) -> fprintf f "Type@@@<1>%s" s_omega
  | Cst.Coq_suniv (Cst.Coq_llit (1, n)) -> fprintf f "Type@@%dL" n
  | Cst.Coq_suniv e -> fprintf f "@[<hov 2>Type@@{%a}@]" (format_obj_prec 0) e
  | Cst.Coq_level 0 -> fprintf f "Level"
  | Cst.Coq_level n -> fprintf f "Level@@%d" n
  (* A level literal: [<n>l] when finite, else [ω·a+b] with [·a] dropped at
     [a = 1] and [+b] dropped at [b = 0].  The level [ω+n] has the shorter
     spelling [<n>L] too, but prints as [ω+n], as it always has. *)
  | Cst.Coq_llit (0, n) -> fprintf f "%dl" n
  | Cst.Coq_llit (a, b) ->
     fprintf f "@<1>%s" s_omega;
     if a <> 1 then fprintf f "@<1>%s%d" s_cdot a;
     if b <> 0 then fprintf f "+%d" b
  | Cst.Coq_succl e ->
     let impl f () = fprintf f "succl@ %a" (format_obj_prec 2) e in
     pp_open_hovbox f 2;
     pp_print_paren_if (p >= 2) impl f ();
     pp_close_box f ()
  | Cst.Coq_maxl (e1, e2) ->
     let impl f () =
       fprintf f "maxl@ %a@ %a" (format_obj_prec 2) e1 (format_obj_prec 2) e2
     in
     pp_open_hovbox f 2;
     pp_print_paren_if (p >= 2) impl f ();
     pp_close_box f ()
  | Cst.Coq_nat -> pp_sym f s_nat
  | Cst.Coq_num n -> fprintf f "%d" n
  | Cst.Coq_elim (escr, bks) ->
     let binder f (x, oa) =
       match oa with
       | None -> pp_print_string f x
       | Some a -> fprintf f "(%s :@ %a)" x format_obj a
     in
     let impl f () =
       fprintf f "@[<hv 0>@[<hov 2>elim %a@]" format_obj escr;
       List.iter
         (fun (((at, xs), em), bs) ->
           fprintf f "@ @[<hov 2>%s %a@ @<1>%s@ %a@]" (if at then "at" else "with")
             (pp_print_list ~pp_sep:pp_print_space binder) xs s_arrow format_obj em;
           List.iter
             (fun ((c, ys), eb) ->
               fprintf f "@ @[<hov 2>| %s%s @<1>%s@ %a@]" c
                 (String.concat "" (List.map (fun y -> if y = "," then "," else " " ^ y) ys))
                 s_darrow format_obj eb)
             bs)
         bks;
       fprintf f "@ end@]"
     in
     pp_print_paren_if (p >= 1) impl f ()
  (* [record T where f := M; … end]: an object, not an atom, so it takes
     parentheses as an argument or before a selection. *)
  | Cst.Coq_tuple (et, fs) ->
     let field f (y, em) = fprintf f "@[<hov 2>%s @<1>%s@ %a@]" y s_eq format_obj em in
     let impl f () =
       fprintf f "@[<hv 2>@[<hov 2>record %a@ where@]" (format_obj_prec 1) et;
       if fs <> [] then
         fprintf f "@ %a" (pp_print_list ~pp_sep:(fun f () -> fprintf f ";@ ") field) fs;
       fprintf f "@;<1 -2>end@]"
     in
     pp_print_paren_if (p >= 1) impl f ()
  | Cst.Coq_true_ty -> pp_sym f s_true_ty
  | Cst.Coq_true_tm -> pp_sym f s_true_tm
  | Cst.Coq_false_ty -> pp_sym f s_false_ty
  | Cst.Coq_exfalso (escr, mx, em) ->
     let impl f () =
       fprintf f "@[<hov 2>exfalso %a@ return %s .@ %a@]" format_obj escr mx
         format_obj em
     in
     pp_print_paren_if (p >= 1) impl f ()
  | Cst.Coq_app (ef, ea) ->
     let impl f () =
       fprintf f "%a@ %a" (format_obj_prec 1) ef (format_obj_prec 2) ea
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 2) impl f ();
     pp_close_box f ()
  | Cst.Coq_fn (px, ep, ebody) ->
     let params, ebody' = get_fn_params_of_obj ebody in
     let impl f () =
       pp_sym f s_lambda; pp_print_char f ' ';
       pp_open_tbox f ();
       pp_set_tab f ();
       pp_print_list ~pp_sep:pp_print_tab format_obj_param f ((px, ep) :: params);
       pp_close_tbox f ();
       begin
         if List.compare_length_with params 0 = 0
         then pp_print_space f ()
         else pp_force_newline f ()
       end;
       fprintf f "@<1>%s @[<hov 2>%a@]" s_arrow format_obj ebody'
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()
  | Cst.Coq_pi (px, ep, eret) ->
     let params, eret' = get_pi_params_of_obj eret in
     let impl f () =
       pp_sym f s_pi; pp_print_char f ' ';
       pp_open_tbox f ();
       pp_set_tab f ();
       pp_print_list ~pp_sep:pp_print_tab format_obj_param f ((px, ep) :: params);
       pp_close_tbox f ();
       begin
         if List.compare_length_with params 0 = 0
         then pp_print_space f ()
         else pp_force_newline f ()
       end;
       fprintf f "@<1>%s @[<hov 2>%a@]" s_arrow format_obj eret'
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()
  | Cst.Coq_var x -> pp_print_string f x
  | Cst.Coq_glob path -> pp_upath f path
  (* Dot binds tighter than application, so the target prints at the precedence
     of an application argument. *)
  | Cst.Coq_proj (e, x) -> fprintf f "%a.%s" (format_obj_prec 2) e x
  | Cst.Coq_letb _ as e ->
     let decls, ebody = get_letb_decls_of_obj e in
     let impl f () =
       fprintf f "let @[<hv 0>%a@]@ in @[<hov 2>%a@]@ end"
         (pp_print_list ~pp_sep:(fun f () -> fprintf f ";@ ") format_decl) decls
         format_obj ebody
     in
     pp_open_hvbox f 0;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()

and format_decl (f : Format.formatter) : Cst.decl -> unit =
  let open Format in
  function
  | Cst.Coq_d_def (x, Some ea, eb) ->
     fprintf f "@[<hov 2>%s : %a @<1>%s@ %a@]" x format_obj ea s_eq format_obj eb
  | Cst.Coq_d_def (x, None, eb) ->
     fprintf f "@[<hov 2>%s @<1>%s@ %a@]" x s_eq format_obj eb
  | Cst.Coq_d_mod (x, params, md) -> format_module f x params md

(* [module x (ps) where … end] or [module x (ps) := E]. *)
and format_module (f : Format.formatter) (x : string) params (md : Cst.mdef) : unit =
  let open Format in
  match md with
  | Cst.Coq_md_where cs ->
     pp_open_vbox f 2;
     fprintf f "module %s" x;
     List.iter (fun p -> fprintf f " %a" format_obj_param p) params;
     pp_print_string f " where";
     List.iter (fun c -> fprintf f "@ %a" format_cmd c) cs;
     fprintf f "@;<1 -2>end";
     pp_close_box f ()
  | Cst.Coq_md_alias e ->
     fprintf f "@[<hov 2>module %s" x;
     List.iter (fun p -> fprintf f " %a" format_obj_param p) params;
     fprintf f " @<1>%s@ %a@]" s_eq format_obj e

(* [inductive x (ps) : T where | c … with y : U where … end]: a group,
   its uniform parameters after its first member's name. *)
and format_group priv ps (f : Format.formatter) ms : unit =
  let open Format in
  fprintf f "@[<v 2>%sinductive" (if priv then "private " else "");
  List.iteri
    (fun i ((x, t), cs) ->
      if i = 0 then begin
        fprintf f " %s" x;
        List.iter (fun p -> fprintf f " %a" format_obj_param p) ps
      end else fprintf f "@;<1 -2>with %s" x;
      fprintf f " : %a where" format_obj t;
      List.iter
        (fun (c, args) ->
          fprintf f "@ | %s" c;
          List.iter (fun p -> fprintf f " %a" format_obj_param p) args)
        cs)
    ms;
  fprintf f "@;<1 -2>end";
  pp_close_box f ()

and format_cmd (f : Format.formatter) : Cst.cmd -> unit =
  let open Format in
  function
  (* [mutual T (ps) where inductive … end end]: the group, with its
     recursor module, in the module [T]. *)
  | Cst.Coq_c_mod (priv, g, [], Cst.Coq_md_where [ Cst.Coq_c_ind (false, true, ps, ms) ]) ->
     fprintf f "@[<v 2>%smutual %s" (if priv then "private " else "") g;
     List.iter (fun p -> fprintf f " %a" format_obj_param p) ps;
     fprintf f " where@ %a@;<1 -2>end@]" (format_group false []) ms
  | Cst.Coq_c_mod (priv, x, params, md) ->
     if priv then Format.pp_print_string f "private ";
     format_module f x params md
  | Cst.Coq_c_def (m, x, ea, eb) ->
     fprintf f "@[<v 2>%adef %s : %a @<1>%s@ %a@;<1 -2>end" format_mods m x
       format_obj ea s_eq format_obj eb;
     pp_close_box f ()
  | Cst.Coq_c_axiom (x, ea) ->
     fprintf f "@[<hov 2>axiom %s :@ %a@]" x format_obj ea
  | Cst.Coq_c_import fp -> fprintf f "@[<hov 2>import %a@]" pp_upath fp
  | Cst.Coq_c_open (fp, ip, args, its) ->
     fprintf f "@[<hov 2>open %a" pp_u (string_of_qpath fp ip);
     List.iter (fun a -> fprintf f "@ %a" (format_obj_prec 2) a) args;
     fprintf f "%a@]" format_items its
  | Cst.Coq_c_error msg -> fprintf f "(* %s *)" msg
  | Cst.Coq_c_ind (priv, _, ps, ms) -> format_group priv ps f ms
  | Cst.Coq_c_mdef (m, ps, fs) ->
     fprintf f "@[<v 2>%amutual def" format_mods m;
     List.iter (fun p -> fprintf f " %a" format_obj_param p) ps;
     List.iteri
       (fun i (((g, gps), ea), bs) ->
         if i > 0 then fprintf f "@;<1 -2>with";
         fprintf f " %s" g;
         List.iter (fun p -> fprintf f " %a" format_obj_param p) gps;
         fprintf f " : %a @<1>%s" format_obj ea s_eq;
         List.iter
           (fun ((c, ys), eb) ->
             fprintf f "@ @[<hov 2>| %s%s @<1>%s@ %a@]" c
               (String.concat "" (List.map (fun y -> " " ^ y) ys))
               s_darrow format_obj eb)
           bs)
       fs;
     fprintf f "@;<1 -2>end";
     pp_close_box f ()
  | Cst.Coq_c_builtin (k, x) -> fprintf f "@[<hov 2>builtin %s @<1>%s@ %a@]" k s_eq format_obj x
  | Cst.Coq_c_ind_alias (priv, x, ps, e) ->
     fprintf f "@[<hov 2>%sinductive %s" (if priv then "private " else "") x;
     List.iter (fun p -> fprintf f " %a" format_obj_param p) ps;
     fprintf f " @<1>%s@ %a@]" s_eq format_obj e
  | Cst.Coq_c_record_alias (priv, x, ps, e) ->
     fprintf f "@[<hov 2>%srecord %s" (if priv then "private " else "") x;
     List.iter (fun p -> fprintf f " %a" format_obj_param p) ps;
     fprintf f " @<1>%s@ %a@]" s_eq format_obj e
  (* [record x (ps) : S where f : A; … with cs end]: the fields, then the
     with-area, if any; one [end] closes both. *)
  | Cst.Coq_c_record (priv, x, ps, es, fs, cs) ->
     fprintf f "@[<v 2>%srecord %s" (if priv then "private " else "") x;
     List.iter (fun p -> fprintf f " %a" format_obj_param p) ps;
     fprintf f " : %a where" format_obj es;
     List.iteri
       (fun i (y, ea) -> fprintf f "%s@ @[<hov 2>%s :@ %a@]" (if i > 0 then ";" else "") y format_obj ea)
       fs;
     if cs <> [] then begin
       fprintf f "@ @[<v 2>with";
       List.iter (fun c -> fprintf f "@ %a" format_cmd c) cs;
       fprintf f "@]"
     end;
     fprintf f "@;<1 -2>end@]"
  | Cst.Coq_c_eval (e, ot) -> begin
     match ot with
     | None -> fprintf f "@[<hov 2>eval %a@]" format_obj e
     | Some t ->
        fprintf f "@[<hov 2>eval %a@ : %a@]" format_obj e format_obj t
   end

and format_obj_param f (px, ep) = Format.fprintf f "(%s : %a)" px format_obj ep
and format_obj f = format_obj_prec 0 f

(************************************************************)
(* Formatting Cst.cmd and Cst.prog *)
(************************************************************)

let format_prog (f : Format.formatter) ((is, ((path, params), cs)) : Cst.prog) : unit =
  let open Format in
  List.iter (fun c -> fprintf f "%a@ " format_cmd c) is;
  pp_open_vbox f 2;
  (* The unit's own name is a [›] path *)
  fprintf f "module %a" pp_upath path;
  List.iter (fun p -> fprintf f " %a" format_obj_param p) params;
  pp_print_string f " where";
  List.iter (fun c -> fprintf f "@ %a" format_cmd c) cs;
  fprintf f "@;<1 -2>end";
  pp_close_box f ()

(************************************************************)
(* Formatting exp *)
(************************************************************)
(* The unit whose terms are printed: a global of that unit is printed by its
   member chain alone, the way it was written. *)
let current_unit : string list ref = ref []

(* The builtin bindings the run ended with ([builtin natural]). *)
let current_bt : McttExtracted.Builtin.builtins ref = ref McttExtracted.Builtin.bt_empty

(* The natural numbers bound where the terms printed are, as the bindings
   see them in the state of the eval printed: the type and its two
   constructors.  A chain of those constructors prints as the numeral it
   stands for, the type as [ℕ], and a constructor by its own name. *)
let nat_bind : (qname * string * string) option ref = ref None

let set_nat_bind (deps : gdeps) (xi : gstack) : unit =
  nat_bind :=
    (match McttExtracted.Builtin.nat_view deps xi !current_bt with
     | Some ((p, z), s) -> Some (p, z, s)
     | None -> None)

let is_bound_nat (p : qname) : bool =
  match !nat_bind with Some (q, _, _) -> p = q | None -> false

(* The state the printed terms live in, where it is known: that of the eval
   printed. *)
let current_state : (gdeps * gstack) ref = ref ([], [])

(* The program of a failed run, whose module declarations name the
   parameters of the frames of [current_state] declared in it. *)
let current_prog : Cst.prog option ref = ref None

(* The parameters of the module at the member chain [ch] of the commands
   [cs], as declared. *)
let rec declared_params (cs : Cst.cmd list) (ch : string list) : (string * Cst.obj) list option =
  match ch with
  | [] -> None
  | x :: ch' ->
     List.find_map
       (function
        | Cst.Coq_c_mod (_, y, ps, md) when y = x ->
           (match ch', md with
            | [], _ -> Some ps
            | _, Cst.Coq_md_where cs' -> declared_params cs' ch'
            | _, Cst.Coq_md_alias _ -> None)
        | _ -> None)
       cs

(* A name the printer generates for a binder. *)
let generated_name (y : string) : bool =
  String.length y > 1 && String.contains "xAM" y.[0]
  && String.for_all (fun c -> c >= '0' && c <= '9') (String.sub y 1 (String.length y - 1))

(* The names of the parameters of the stack of [current_state], one per
   entry of its [gs_tele], innermost first; [None] where the program does
   not declare the frame, or a name could be read as a generated one. *)
let frame_param_names () : string option list =
  let _, xi = !current_state in
  List.concat_map
    (fun (((q : qname), _), Coq_gu_mk (delta, _)) ->
      let n = List.length delta in
      let ps = match !current_prog with
        | Some (_, ((path, top), cs)) when q.q_unit = path ->
           if q.q_chain = [] then Some top else declared_params cs q.q_chain
        | _ -> None in
      match ps with
      | Some ps when List.length ps = n && not (List.exists (fun (y, _) -> generated_name y) ps) ->
         List.rev_map (fun (y, _) -> Some y) ps
      | _ -> List.init n (fun _ -> None))
    xi

(* A member of a frame of the stack printed, as the elaborator writes a use
   of it from inside the frame: the member [x] of the frame's module, applied
   first to the parameters of that frame and of the frames enclosing it, as
   variables, outermost first ([vars_desc]).  Those parameters are not
   written in the source, so the use prints as [x] alone, then the other
   arguments [args] are applied to it, which this returns.  [nloc] is the
   number of local binders around the use, inside the frames' parameters.
   [None] where the module [(fp, ms)] is no frame or the arguments do not
   start with those variables. *)
let frame_member (nloc : int) ((fp, ms) : string list * string list) (args : exp list) : exp list option =
  let _, xi = !current_state in
  let rec find inner = function
    | [] -> None
    | (((q : qname), _), u) :: xi' ->
       if q.q_unit = fp && q.q_chain = ms then
         Some (inner, List.length (McttExtracted.Syntax.gs_tele xi))
       else find (inner + List.length (McttExtracted.Syntax.gu_params u)) xi'
  in
  match find 0 xi with
  | None -> None
  | Some (inner, total) ->
     let n = total - inner and k = nloc + inner in
     let expected = List.init n (fun i -> Coq_a_var (k + n - 1 - i)) in
     let rec strip es args =
       match es, args with
       | [], rest -> Some rest
       | e :: es', a :: args' when e = a -> strip es' args'
       | _ -> None
     in
     strip expected args

(* The path a term spells as a chain of members from a unit, if it is one. *)
let path_of_term : exp -> qname option =
  let rec chain = function
    | Coq_me_unit fp -> Some (fp, [])
    | Coq_me_mem (h, y) -> Option.map (fun (fp, ms) -> (fp, ms @ [ y ])) (chain h)
    | _ -> None
  in
  function
  | Coq_a_mem (h, y) -> Option.map (fun (fp, ms) -> { q_unit = fp; q_chain = ms @ [ y ] }) (chain h)
  | _ -> None

(* A path naming the bound type: the type, or an inductive alias of it
   without arguments, as an [import … use (Nat)] declares one: a
   definition with a module part whose term is a path naming it. *)
let rec names_bound_nat (q : qname) : bool =
  is_bound_nat q ||
  (let deps, xi = !current_state in
   match McttExtracted.Members.gc_entry deps xi q with
   | Some (Coq_ge_def_mod (_, _, m, _)) ->
      (match path_of_term m with Some p -> p <> q && names_bound_nat p | None -> false)
   | _ -> false)

(* A constructor, written as such, as a member of its type's module from a
   unit, or as a definition of it there, as an [open] declares one. *)
let con_of : exp -> (qname * string) option =
  let rec chain = function
    | Coq_me_unit fp -> Some (fp, [])
    | Coq_me_mem (h, y) -> Option.map (fun (fp, ms) -> (fp, ms @ [ y ])) (chain h)
    | _ -> None
  in
  let rec go k = function
    | Coq_a_con (p, 0, c) -> Some (p, c)
    | Coq_a_con _ -> None
    | Coq_a_mem (h, c) ->
       (match chain h with
        | None -> None
        | Some (fp, ms) ->
           let deps, xi = !current_state in
           (match McttExtracted.Members.gc_resolve deps xi { q_unit = fp; q_chain = ms @ [ c ] } with
            (* A definition naming a constructor, as an [open] declares one,
               not one whose body is a value. *)
            | Some (Coq_ge_def (_, _, _, Some (Coq_a_mem (_, c') as body))) when k > 0 && c' = c -> go (k - 1) body
            (* The member of an inductive type's module that is its
               constructor. *)
            | Some (Coq_ge_def (_, _, _, Some (Coq_a_con (p, 0, c'))))
              when c' = c && p.q_unit = fp && p.q_chain = ms -> Some (p, c)
            | Some (Coq_ge_def _) -> None
            | _ -> Some ({ q_unit = fp; q_chain = ms }, c)))
    | _ -> None
  in
  go 8

let rec nat_of_chain : exp -> int option = function
  | Coq_a_app (f, e) ->
     (match con_of f, !nat_bind with
      | Some (p, c), Some (q, _, s) when p = q && c = s -> Option.map (( + ) 1) (nat_of_chain e)
      | _ -> None)
  | e ->
     (match con_of e, !nat_bind with
      | Some (p, c), Some (q, z, _) when p = q && c = z -> Some 0
      | _ -> None)

(* The declarations of the inductive types the printed terms see, where
   they are known: those of the state of the eval or the error printed. *)
let ind_decls : (exp, centry) ind_decl_g list ref = ref []

(* Every declaration of an inductive type in a body, the bodies of its
   modules included. *)
let rec gmod_decls : gmod -> (exp, centry) ind_decl_g list = function
  | Coq_gm_nil -> []
  | Coq_gm_open (phi, _, _) -> gmod_decls phi
  | Coq_gm_ext (phi, _, e) ->
     let here =
       match e with
       | Coq_ge_ind (_, _, _, d, phi') -> d :: gmod_decls phi'
       | Coq_ge_mod (_, Coq_gu_mk (_, Coq_md_body (_, phi'))) -> gmod_decls phi'
       | _ -> []
     in
     here @ gmod_decls phi

let unit_decls (Coq_gu_mk (_, md) : gunit) =
  match md with Coq_md_body (_, phi) -> gmod_decls phi | Coq_md_alias _ -> []

let set_ind_decls (deps : gdeps) (xi : gstack) : unit =
  ind_decls := List.concat_map (fun (_, u) -> unit_decls u) deps @ List.concat_map (fun (_, u) -> unit_decls u) xi

(* The member [m] of the group at [p], where the state printed has it. *)
let group_member (p : qname) (m : int) : (exp, centry) imember_g option =
  let deps, xi = !current_state in
  match McttExtracted.Members.ind_lookup deps xi p with
  | Some d -> McttExtracted.Syntax.ind_member d m
  | None -> None

(* The path of the module of the declared member [k] of the group at [p]:
   the group's own for its first member. *)
let member_path (p : qname) (k : int) : qname =
  let deps, xi = !current_state in
  match McttExtracted.Members.ind_lookup deps xi p with
  | Some d -> (match McttExtracted.Members.ind_mpath d k with Some pm -> pm | None -> p)
  | None -> p

(* A view's type former or constructor at its arguments is the
   container's, at the view's instance of the container's uniform
   parameters: the same term, written as the container's.  [None] where
   the head is no view. *)
let unview (e : exp) : exp option =
  match McttExtracted.Group.app_head e with
  | (Coq_a_ind (p, j) | Coq_a_con (p, j, _)) as h ->
     let deps, xi = !current_state in
     (match McttExtracted.Members.ind_lookup deps xi p with
      | Some d ->
         (match McttExtracted.Syntax.ind_member d j with
          | Some mj ->
             (match mj.im_head with
              | Coq_mh_view (qc, k, _, _) ->
                 let args = McttExtracted.Group.app_args e in
                 let nu = McttExtracted.Syntax.ind_nu d in
                 let us = List.filteri (fun i _ -> i < nu) args in
                 let rest = List.filteri (fun i _ -> i >= nu) args in
                 let h' = match h with Coq_a_con (_, _, c) -> Coq_a_con (qc, k, c) | _ -> Coq_a_ind (qc, k) in
                 Some (McttExtracted.Syntax.apps_exp h' (McttExtracted.Group.im_pre mj us @ rest))
              | Coq_mh_decl _ -> None)
          | None -> None)
      | None -> None)
  | _ -> None

(* The value [v] whose record's module [h] is, where it is one: the module
   of a record of the state printed, applied to as many arguments as the
   record has parameters, then to [v] ([record_value_module]). *)
let record_value_of (h : modexp) : exp option =
  let rec spine h args = match h with Coq_me_app (h', n) -> spine h' (n :: args) | _ -> (h, args) in
  let rec chain = function
    | Coq_me_unit fp -> Some (fp, [])
    | Coq_me_mem (h, y) -> Option.map (fun (fp, ms) -> (fp, ms @ [ y ])) (chain h)
    | _ -> None
  in
  match spine h [] with
  | head, (_ :: _ as args) ->
     (match chain head with
      | Some (fp, ms) ->
         let deps, xi = !current_state in
         (match McttExtracted.Members.record_lookup deps xi { q_unit = fp; q_chain = ms } with
          | Some r when List.length args = List.length r.record_params + 1 -> Some (List.nth args (List.length args - 1))
          | _ -> None)
      | None -> None)
  | _ -> None

(* The number of induction hypotheses a branch of [n] binders for the
   constructor [c] of the member [mk] binds, where it binds as many names
   as it should. *)
(* The groups an eliminator as written, with no group, can be of: those
   whose members' constructors its blocks' branches name, block by block. *)
let elim_groups (bks : exp eblock_g list) : (exp, centry) ind_decl_g list =
  List.filter
    (fun d ->
      List.length d.ind_members = List.length bks
      && List.for_all2
           (fun mk (Coq_eb_mk (_, _, _, bs)) -> List.map fst mk.im_cons = List.map (fun ((c, _), _) -> c) bs)
           d.ind_members bks)
    !ind_decls

(* The members the block [j] of an eliminator can be for: the member [j]
   of its group, or of every group it can be of. *)
(* With the group known, the member [j] if the block's branches are for its
   constructors, otherwise every member they are for (a block out of
   place), and the member [j] if none is. *)
let block_members (oq : qname option) (bks : exp eblock_g list) (j : int) : (exp, centry) imember_g list =
  match oq with
  | Some p ->
     let names = match List.nth_opt bks j with
       | Some (Coq_eb_mk (_, _, _, bs)) -> List.map (fun ((c, _), _) -> c) bs
       | None -> [] in
     let fits (mk : (exp, centry) imember_g) = List.map fst mk.im_cons = names in
     (match group_member p j with
      | Some mk when fits mk -> [ mk ]
      | o ->
         let deps, xi = !current_state in
         let all = match McttExtracted.Members.ind_lookup deps xi p with Some d -> d.ind_members | None -> [] in
         (match List.filter fits all with [] -> Option.to_list o | l -> l))
  | None ->
     (match elim_groups bks with
      | [] ->
         (* No group has these blocks: every member the block's branches
            are for. *)
         let names = match List.nth_opt bks j with
           | Some (Coq_eb_mk (_, _, _, bs)) -> List.map (fun ((c, _), _) -> c) bs
           | None -> [] in
         List.filter (fun (mk : (exp, centry) imember_g) -> List.map fst mk.im_cons = names)
           (List.concat_map (fun d -> d.ind_members) !ind_decls)
      | gs -> List.filter_map (fun d -> McttExtracted.Syntax.ind_member d j) gs)

let ihs_count (mk : (exp, centry) imember_g option) (c : string) (n : int) : int =
  match mk with
  | None -> 0
  | Some mk ->
     (match McttExtracted.Inductives.ind_con mk c with
      | None -> 0
      | Some gs ->
         let k = McttExtracted.Inductives.cargs_nrec gs in
         if n <> McttExtracted.Syntax.im_nn mk + List.length gs + k then 0 else k)

(* The number of induction hypotheses a branch of [n] binders for [c] binds,
   where every member its block can be for agrees on it. *)
let ihs_agreed (mks : (exp, centry) imember_g list) (c : string) (n : int) : int =
  match List.map (fun mk -> ihs_count (Some mk) c n) mks with
  | k :: ks when List.for_all (( = ) k) ks -> k
  | _ -> 0

(* The names a branch binds, its induction hypotheses after a comma, the
   marker [","]. *)
let mark_ihs (k : int) (ys : string list) : string list =
  let n = List.length ys in
  if k = 0 then ys
  else List.filteri (fun i _ -> i < n - k) ys @ ("," :: List.filteri (fun i _ -> i >= n - k) ys)

let exp_to_obj =
  let new_var, reset_var_suffix =
    let suffix = ref 0 in
    ( (fun () ->
        incr suffix;
        "x" ^ string_of_int !suffix),
      fun () -> suffix := 0 )
  in
  let new_mod, reset_mod_suffix =
    let suffix = ref 0 in
    ( (fun () ->
        incr suffix;
        "M" ^ string_of_int !suffix),
      fun () -> suffix := 0 )
  in
  let new_tyvar, reset_tyvar_suffix =
    let suffix = ref 0 in
    ( (fun () ->
        incr suffix;
        "A" ^ string_of_int !suffix),
      fun () -> suffix := 0 )
  in
  let rec impl (ctx : string list) (e : exp) : Cst.obj =
    match unview e with
    | Some e' -> impl ctx e'
    | None -> impl_seen ctx e
  and impl_seen (ctx : string list) : exp -> Cst.obj = function
    | (Coq_a_con _ | Coq_a_mem _ | Coq_a_app (Coq_a_con _, _) | Coq_a_app (Coq_a_mem _, _)) as e when nat_of_chain e <> None ->
       Cst.Coq_num (Option.get (nat_of_chain e))
    (* A member of a frame, applied to the frames' parameters as written. *)
    | (Coq_a_mem _ | Coq_a_app _) as e when frame_use ctx e <> None -> apply_rest ctx (Option.get (frame_use ctx e))
    | Coq_a_nlit n -> Cst.Coq_num n
    | Coq_a_ntok -> Cst.Coq_nat
    | Coq_a_level n -> Cst.Coq_level n
    | Coq_a_llit o -> Cst.Coq_llit o
    | Coq_a_succl e -> Cst.Coq_succl (impl ctx e)
    | Coq_a_maxl (e1, e2) -> Cst.Coq_maxl (impl ctx e1, impl ctx e2)
    | Coq_a_True -> Cst.Coq_true_ty
    | Coq_a_true -> Cst.Coq_true_tm
    | Coq_a_False -> Cst.Coq_false_ty
    | Coq_a_exfalso (em, escr) ->
       let mx = new_var () in
       let escr' = impl ctx escr in
       let em' = impl (mx :: ctx) em in
       Cst.Coq_exfalso (escr', mx, em')
    | Coq_a_typ i -> Cst.Coq_typ i
    | Coq_a_univ e -> Cst.Coq_suniv (impl ctx e)
    (* A variable past the local binders is a parameter of an open module,
       which has no name here: it prints as [$k], counting outwards. *)
    | Coq_a_var x -> var_to_obj ctx x
    | Coq_a_fn (ep, ebody) ->
       let px = match ep with Coq_a_typ _ | Coq_a_univ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let ebody' = impl (px :: ctx) ebody in
       Cst.Coq_fn (px, ep', ebody')
    | Coq_a_app (ef, ea) ->
       let ef' = impl ctx ef in
       let ea' = impl ctx ea in
       Cst.Coq_app (ef', ea')
    | Coq_a_pi (ep, eret) ->
       let px = match ep with Coq_a_typ _ | Coq_a_univ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let eret' = impl (px :: ctx) eret in
       Cst.Coq_pi (px, ep', eret')
    | Coq_a_let (Coq_b_def (oa, em), ebody) ->
       let px = match oa with Some (Coq_a_typ _ | Coq_a_univ _) -> new_tyvar () | _ -> new_var () in
       let ea' = Option.map (impl ctx) oa in
       let em' = impl ctx em in
       let ebody' = impl (px :: ctx) ebody in
       Cst.Coq_letb (Cst.Coq_d_def (px, ea', em'), ebody')
    | Coq_a_let (Coq_b_mod u, ebody) ->
       let px = new_mod () in
       let params, md = impl_unit ctx u in
       let ebody' = impl (px :: ctx) ebody in
       Cst.Coq_letb (Cst.Coq_d_mod (px, params, md), ebody')
    (* A member naming the bound type, directly or by an inductive alias
       without arguments, or one of its constructors, prints as they do. *)
    | Coq_a_mem (h, x) when (match chain_of h with
                             | Some (fp, ms) -> names_bound_nat { q_unit = fp; q_chain = ms @ [ x ] }
                             | None -> false) -> Cst.Coq_nat
    | Coq_a_mem (h, x) when (match chain_of h with
                             | Some (fp, ms) -> is_bound_nat { q_unit = fp; q_chain = ms }
                             | None -> false) -> Cst.Coq_var x
    (* A member of the module of a record value, as the access fill writes
       it: selected from the value. *)
    | Coq_a_mem (h, x) when record_value_of h <> None -> Cst.Coq_proj (impl ctx (Option.get (record_value_of h)), x)
    | Coq_a_mem (h, x) ->
       (match chain_of h with
        | Some (fp, ms) -> path_to_obj fp (ms @ [x])
        | None -> Cst.Coq_proj (impl_mod ctx h, x))
    (* The type bound as the natural numbers is [ℕ], and its constructors
       are named by their own names. *)
    | Coq_a_ind (p, 0) when is_bound_nat p -> Cst.Coq_nat
    | Coq_a_con (p, 0, c) when is_bound_nat p -> Cst.Coq_var c
    (* An inductive type is named by its member's path, which is its
       module's; a constructor is a member of that module. *)
    | Coq_a_ind (p, k) -> let q = member_path p k in path_to_obj q.q_unit q.q_chain
    (* A record type is named by its path; a field is selected as a member
       is; a tuple is a record value, at its type. *)
    | Coq_a_record p -> path_to_obj p.q_unit p.q_chain
    | Coq_a_proj (f, e) -> Cst.Coq_proj (impl ctx e, f)
    | Coq_a_tuple (t, fs) -> Cst.Coq_tuple (impl ctx t, List.map (fun (y, e) -> (y, impl ctx e)) fs)
    | Coq_a_con (p, k, c) -> let q = member_path p k in path_to_obj q.q_unit (q.q_chain @ [c])
    (* An eliminator: fresh names for what its motive and its branches
       bind. *)
    | Coq_a_elim (oq, _, m, bks, escr) ->
       let rec fresh k = if k = 0 then [] else let x = new_var () in x :: fresh (k - 1) in
       let escr' = impl ctx escr in
       let block j (Coq_eb_mk (nm, oz, em, bs)) =
         let mks = block_members oq bks j in
         let xs = fresh nm in
         let ys0 = List.filteri (fun i _ -> i < nm - 1) xs in
         let oz' = Option.map (impl (List.rev ys0 @ ctx)) oz in
         let binders = List.mapi (fun i x -> (x, if i = nm - 1 then oz' else None)) xs in
         let em' = impl (List.rev xs @ ctx) em in
         (* The induction hypotheses are of the motive's sort: named as types
            when the motive is a type, as other binders of a universe are. *)
         let is_univ = match em with Coq_a_typ _ | Coq_a_univ _ -> true | _ -> false in
         let bs' =
           List.map
             (fun ((c, n), eb) ->
               let k = ihs_agreed mks c n in
               let kt = if is_univ then k else 0 in
               let ys = fresh (n - kt) in
               let hs = List.init kt (fun _ -> new_tyvar ()) in
               let ys = ys @ hs in
               ((c, mark_ihs k ys), impl (List.rev ys @ ctx) eb))
             bs
         in
         (((j = m, binders), em'), bs')
       in
       Cst.Coq_elim (escr', List.mapi block bks)
  (* A use of a member of a frame from inside it ([frame_member]): its name,
     and the arguments past the frames' parameters, not yet printed (the
     guards that ask for it print nothing, so binders are named once). *)
  and frame_use (ctx : string list) (e : exp) : (Cst.obj * exp list) option =
    match McttExtracted.Group.app_head e with
    | Coq_a_mem (h, x) ->
       (match chain_of h with
        | Some (fp, ms) ->
           (match frame_member (List.length ctx) (fp, ms) (McttExtracted.Group.app_args e) with
            | Some rest ->
               let head = if names_bound_nat { q_unit = fp; q_chain = ms @ [ x ] } then Cst.Coq_nat else Cst.Coq_var x in
               Some (head, rest)
            | None -> None)
        | None -> None)
    | _ -> None
  (* The same for a module: a submodule of a frame applied to the frames'
     parameters, then to the arguments returned. *)
  and frame_mod_use (ctx : string list) (m : modexp) : (Cst.obj * exp list) option =
    let rec spine m args = match m with
      | Coq_me_app (h, e) -> spine h (e :: args)
      | _ -> (m, args) in
    match spine m [] with
    | Coq_me_mem (h, y), args ->
       (match chain_of h with
        | Some (fp, ms) ->
           (match frame_member (List.length ctx) (fp, ms) args with
            | Some rest -> Some (Cst.Coq_var y, rest)
            | None -> None)
        | None -> None)
    | _ -> None
  (* A head applied to arguments, printed. *)
  and apply_rest (ctx : string list) ((head, rest) : Cst.obj * exp list) : Cst.obj =
    List.fold_left (fun f a -> Cst.Coq_app (f, impl ctx a)) head rest
  (* A chain of selections from a unit, as the unit and the chain. *)
  and chain_of : modexp -> (string list * string list) option = function
    | Coq_me_unit fp -> Some (fp, [])
    | Coq_me_mem (h, y) ->
       (match chain_of h with Some (fp, ms) -> Some (fp, ms @ [y]) | None -> None)
    | _ -> None
  (* A chain from a unit is absolute.  Into the unit being printed, the
     member chain is what was written, its first member an ordinary name;
     into another unit, the unit is a [glob] head.  Either way the remaining
     members are a chain of [proj]s over the head. *)
  and path_to_obj (fp : string list) (ms : string list) : Cst.obj =
    let head, ip =
      if fp = !current_unit then
        (match ms with
         | x :: ip -> (Cst.Coq_var x, ip)
         (* The unit itself, named from inside. *)
         | [] -> (Cst.Coq_glob fp, []))
      else (Cst.Coq_glob fp, ms)
    in
    List.fold_left (fun e y -> Cst.Coq_proj (e, y)) head ip
  and var_to_obj (ctx : string list) (x : int) : Cst.obj =
    match List.nth_opt ctx x with
    | Some y -> Cst.Coq_var y
    | None ->
       let k = x - List.length ctx in
       (match List.nth_opt (frame_param_names ()) k with
        | Some (Some y) -> Cst.Coq_var y
        | _ -> Cst.Coq_var ("$" ^ string_of_int k))
  and impl_mod (ctx : string list) : modexp -> Cst.obj = function
    | Coq_me_unit fp -> path_to_obj fp []
    | Coq_me_var x -> var_to_obj ctx x
    | Coq_me_mem (h, y) ->
       (match chain_of h with
        | Some (fp, ms) -> path_to_obj fp (ms @ [y])
        | None -> Cst.Coq_proj (impl_mod ctx h, y))
    | Coq_me_app _ as m when frame_mod_use ctx m <> None -> apply_rest ctx (Option.get (frame_mod_use ctx m))
    | Coq_me_app (h, e) -> Cst.Coq_app (impl_mod ctx h, impl ctx e)
    (* A literal module, which only substitution produces, prints as a local
       module naming itself. *)
    | Coq_me_lit u ->
       let px = new_mod () in
       let params, md = impl_unit ctx u in
       Cst.Coq_letb (Cst.Coq_d_mod (px, params, md), Cst.Coq_var px)
  and impl_unit (ctx : string list) (Coq_gu_mk (delta, md) : gunit)
      : (string * Cst.obj) list * Cst.mdef =
    (* The parameter context lists the innermost parameter first. *)
    let ctx', params =
      List.fold_left
        (fun (ctx, ps) ce ->
          let ty = match ce with
            | Coq_ce_ass a | Coq_ce_def (a, _) | Coq_ce_dm (a, _, _) -> impl ctx a
            | Coq_ce_mod _ -> Cst.Coq_var "_" in
          let px = match ce with
            | Coq_ce_ass (Coq_a_typ _ | Coq_a_univ _) | Coq_ce_def ((Coq_a_typ _ | Coq_a_univ _), _) -> new_tyvar ()
            | _ -> new_var () in
          (px :: ctx, (px, ty) :: ps))
        (ctx, []) (List.rev delta)
    in
    let md' = match md with
      | Coq_md_alias h -> Cst.Coq_md_alias (impl_mod ctx' h)
      | Coq_md_body (_, phi) -> Cst.Coq_md_where (fst (impl_body ctx' phi))
    in
    (List.rev params, md')
  and impl_body (ctx : string list) : gmod -> Cst.cmd list * string list = function
    | Coq_gm_nil -> ([], ctx)
    | Coq_gm_ext (phi, x, ge) ->
       let cs, ctx' = impl_body ctx phi in
       let c = match ge with
         | Coq_ge_def (transp, priv, a, om) ->
            let m = { Cst.md_private = priv; Cst.md_abstract = not transp } in
            let a' = impl ctx' a in
            (match om with
             | Some e -> Cst.Coq_c_def (m, x, a', impl ctx' e)
             | None -> Cst.Coq_c_axiom (x, a'))
         | Coq_ge_mod (priv, u) ->
            let params, md = impl_unit ctx' u in
            Cst.Coq_c_mod (priv, x, params, md)
         (* A declaration is filed in a unit, never in a local body. *)
         | Coq_ge_ind (_, _, _, _, _) -> Cst.Coq_c_error "inductive declaration"
         | Coq_ge_def_mod (_, _, _, _) -> Cst.Coq_c_error "definition with a module part"
         | Coq_ge_record (_, _, _, _) -> Cst.Coq_c_error "record declaration"
       in
       (cs @ [c], x :: ctx')
    | Coq_gm_open (phi, h, its) ->
       let cs, ctx' = impl_body ctx phi in
       (* The target is a module expression, printed in place of a path;
          each item binds its name. *)
       let target = Format.asprintf "%a" format_obj (impl_mod ctx' h) in
       let names = List.map (fun ((_, d), _) -> d) its in
       (cs @ [Cst.Coq_c_open ([], [target], [], its)], List.rev_append names ctx')
  in
  (* The names of a context, innermost entry first, as binders are named;
     [given], innermost first too, the names the source gives some of
     them. *)
  let names_of (given : string option list) (delta : centry list) : string list =
    let n = List.length delta in
    snd (List.fold_left
      (fun (i, names) ce ->
        let px = match List.nth_opt given (n - 1 - i), ce with
          | Some (Some y), _ -> y
          | _, (Coq_ce_ass (Coq_a_typ _ | Coq_a_univ _) | Coq_ce_def ((Coq_a_typ _ | Coq_a_univ _), _)) -> new_tyvar ()
          | _, (Coq_ce_mod _ | Coq_ce_dm _) -> new_mod ()
          | _ -> new_var () in
        (i + 1, px :: names))
      (0, []) (List.rev delta))
  in
  (* A term in the context [delta], whose entries are named first. *)
  fun ?(delta = []) ?(names = []) exp ->
    reset_var_suffix ();
    reset_tyvar_suffix ();
    reset_mod_suffix ();
    let ctx = names_of names delta in
    impl ctx exp

let format_exp f exp = format_obj f (exp_to_obj exp)

let format_exp_in delta f exp = format_obj f (exp_to_obj ~delta exp)

(* The commands of the module at the member chain [ch] of the commands
   [cs], as declared. *)
let rec declared_cmds (cs : Cst.cmd list) (ch : string list) : Cst.cmd list option =
  match ch with
  | [] -> Some cs
  | x :: ch' ->
     List.find_map
       (function
        | Cst.Coq_c_mod (_, y, _, Cst.Coq_md_where cs') when y = x -> declared_cmds cs' ch'
        | _ -> None)
       cs

(* The names the definition [x] of the innermost frame of [current_state]
   gives its parameters, as declared in the program run, outermost first:
   the binders its type and its body both start with. *)
let def_param_names (x : string) : string list =
  let _, xi = !current_state in
  let cmds = match xi, !current_prog with
    | (((q : qname), _), _) :: _, Some (_, ((path, _), cs)) when q.q_unit = path -> declared_cmds cs q.q_chain
    | _ -> None in
  let rec common ty body =
    match ty, body with
    | Cst.Coq_pi (y, _, ty'), Cst.Coq_fn (y', _, body') when y = y' -> y :: common ty' body'
    | _ -> [] in
  match cmds with
  | None -> []
  | Some cs ->
     (match List.find_map (function Cst.Coq_c_def (_, y, a, m) when y = x -> Some (a, m) | _ -> None) cs with
      | Some (a, m) -> List.filter (fun y -> not (generated_name y)) (common a m)
      | None -> [])

(* The names the source gives the entries of [delta], the context inside
   the frames of a term of the definition [ox] where it is one, innermost
   first: its parameters, the outermost entries. *)
let given_names (ox : string option) (delta : centry list) : string option list =
  match ox with
  | None -> []
  | Some x ->
     let ps = def_param_names x and n = List.length delta in
     List.init n (fun i -> List.nth_opt ps (n - 1 - i))

let format_exp_named ox delta f exp = format_obj f (exp_to_obj ~delta ~names:(given_names ox delta) exp)

(************************************************************)
(* Formatting nf *)
(************************************************************)

let format_nf f nf = format_exp f (nf_to_exp nf)

(************************************************************)
(* Formatting main_result *)
(************************************************************)

let format_eval (f : Format.formatter) (r : Command1.eval_entry) : unit =
  set_ind_decls r.ev_deps r.ev_stack;
  set_nat_bind r.ev_deps r.ev_stack;
  current_state := (r.ev_deps, r.ev_stack);
  Format.fprintf f "@[<hov 2>Evaluate %a@ --> %a@ : %a@]" format_exp r.ev_exp
    format_nf r.ev_nf format_exp r.ev_typ


(* The source of a unit other than the program run, parsed, for the names
   its declarations give ([decl_names]); the driver sets it to its loader. *)
let unit_cst : (string list -> Cst.prog option) ref = ref (fun _ -> None)

(* The names a declared member gives, as written in the declaration at its
   path [pm], in the program run or the unit it is in: those of its
   non-uniform parameters, the binders of its type, and of each
   constructor's arguments. *)
let decl_names (pm : qname) : (string list * (string * string list) list) option =
  let prog =
    match !current_prog with
    | Some ((_, ((path, _), _)) as prg) when path = pm.q_unit -> Some prg
    | _ -> !unit_cst pm.q_unit
  in
  let rec find (cs : Cst.cmd list) (ch : string list) =
    match ch with
    | [] -> None
    | [ x ] ->
       List.find_map
         (function
          | Cst.Coq_c_ind (_, _, _, ms) ->
             List.find_map
               (fun ((y, t), cons) ->
                 if y = x then
                   Some (List.map fst (fst (get_pi_params_of_obj t)), List.map (fun (c, args) -> (c, List.map fst args)) cons)
                 else None)
               ms
          | _ -> None)
         cs
    | y :: ch' ->
       List.find_map
         (function
          | Cst.Coq_c_mod (_, z, _, Cst.Coq_md_where cs') when z = y -> find cs' ch'
          | _ -> None)
         cs
  in
  match prog with
  | Some (_, (_, cs)) -> find cs pm.q_chain
  | None -> None

(* The names of the binders of a member [mk] of the group at [p], for a
   skeleton of its block: the declaration's where it is found (for a view,
   its container's), otherwise names made from the constructor. *)
let member_names (p : qname) (k : int) (mk : (exp, centry) imember_g) : string list * (string * string list) list =
  let names =
    match mk.im_head with
    | Coq_mh_decl _ -> decl_names (member_path p k)
    | Coq_mh_view (qc, kc, _, _) -> decl_names (member_path qc kc)
  in
  let nn = McttExtracted.Syntax.im_nn mk in
  let ps = match names with
    | Some (ps, _) when List.length ps = nn -> ps
    | _ -> List.init nn (fun i -> "p" ^ string_of_int (i + 1)) in
  let cons =
    List.map
      (fun (c, gs) ->
        let n = List.length gs in
        match Option.bind names (fun (_, cs) -> List.assoc_opt c cs) with
        | Some ys when List.length ys = n -> (c, ys)
        | _ -> (c, List.init n (fun i -> c ^ string_of_int (i + 1))))
      mk.im_cons
  in
  (ps, cons)

(* The induction hypotheses of a branch: one per recursive argument, [h]
   alone for one, else [h] then the argument's name. *)
let ih_names (gs : exp carg_g list) (ys : string list) : string list =
  let recs = List.filteri (fun i _ -> match List.nth_opt gs i with Some (Coq_ca_rec _) -> true | _ -> false) ys in
  match recs with
  | [ _ ] -> [ "h" ]
  | _ -> List.map (fun y -> "h" ^ y) recs

(* The name of a member in a message: a declared one's, a view's type. *)
let member_label (delta : centry list) (p : qname) (us : exp list) (k : int) (mk : (exp, centry) imember_g) : string =
  match mk.im_head with
  | Coq_mh_decl _ -> (match List.rev (member_path p k).q_chain with x :: _ -> x | [] -> "?")
  | Coq_mh_view _ ->
     Format.asprintf "%a" (format_exp_in delta) (McttExtracted.Syntax.apps_exp (Coq_a_ind (p, k)) us)

(* The eliminator [elim scr] of the group at [p] at the uniform parameters
   [us], as it should be written, one line per block head and per branch:
   every member's block in member order, [at] on the member [j]'s, each
   with its binders, the scrutinee's typed, and each branch with its
   arguments and its induction hypotheses, the bodies left out. *)
let format_elim_skeleton (delta : centry list) (f : Format.formatter) (p, us, j, scr) : unit =
  let open Format in
  let deps, xi = !current_state in
  let ms = match McttExtracted.Members.ind_lookup deps xi p with Some d -> d.ind_members | None -> [] in
  let j = if j < List.length ms then j else 0 in
  let str obj = asprintf "%a" format_obj obj in
  pp_open_vbox f 0;
  fprintf f "elim %s" (str (exp_to_obj ~delta scr));
  List.iteri
    (fun k mk ->
      let ps, cons = member_names p k mk in
      let ty = List.fold_left (fun t y -> Cst.Coq_app (t, Cst.Coq_var y))
                 (exp_to_obj ~delta (McttExtracted.Syntax.apps_exp (Coq_a_ind (p, k)) us)) ps in
      let binders = String.concat "" (List.map (fun y -> y ^ " ") ps) ^ "(z : " ^ str ty ^ ")" in
      if k > 0 then pp_print_cut f () else pp_print_string f " ";
      pp_u f (Printf.sprintf "%s %s %s \u{2026}" (if k = j then "at" else "with") binders s_arrow);
      List.iter
        (fun (c, ys) ->
          let gs = match McttExtracted.Inductives.ind_con mk c with Some gs -> gs | None -> [] in
          let hs = ih_names gs ys in
          pp_print_cut f ();
          fprintf f "%a" pp_u
            (Printf.sprintf "| %s%s%s %s \u{2026}" c
               (String.concat "" (List.map (fun y -> " " ^ y) (ps @ ys)))
               (if hs = [] then "" else "," ^ String.concat "" (List.map (fun h -> " " ^ h) hs))
               s_darrow))
        cons)
    ms;
  pp_print_cut f ();
  pp_print_string f "end";
  pp_close_box f ()

let rec format_run_error (f : Format.formatter) (e : Command1.run_error) : unit =
  match e with
  (* The natural numbers bound where the error occurred: the innermost
     state's. *)
  | Coq_re_nat (deps, xi, nv, e') ->
     nat_bind := Option.map (fun ((p, z), s) -> (p, z, s)) nv;
     current_state := (deps, xi);
     set_ind_decls deps xi;
     format_run_error f e'
  | _ ->
  (* The stack of the failing command, where the error has it; the units
     it imports are not at hand. *)
  (match e with
   | Coq_re_def (_, xi, _, _) | Coq_re_def_typ (_, xi, _) | Coq_re_eval_typ (xi, _, _)
   | Coq_re_eval_check (xi, _, _) | Coq_re_eval_infer (xi, _) | Coq_re_level (xi, _, _)
   | Coq_re_elim_blocks (xi, _, _, _, _, _) | Coq_re_elim_scrutinee (xi, _, _, _, _)
   | Coq_re_elim_no_group (xi, _, _) | Coq_re_elim_ambiguous (xi, _, _, _)
   | Coq_re_access_no_type (xi, _, _, _, _) | Coq_re_access_not_record (xi, _, _, _, _, _)
   | Coq_re_record_field (xi, _, _, _, _, _, _) ->
      set_ind_decls (fst !current_state) xi;
      current_state := (fst !current_state, xi)
   | _ -> ());
  format_run_error_in f e

and format_run_error_in (f : Format.formatter) : Command1.run_error -> unit =
  let open Format in
  function
  | Coq_re_msg msg -> fprintf f "@[<hov 2>Error: %s@]" msg
  | Coq_re_def (x, _, typ, exp) ->
     fprintf f "@[<hov 2>Error: the body of %s,@ %a,@ is not of type@ %a@]" x
       format_exp exp format_exp typ
  | Coq_re_def_typ (x, _, typ) ->
     fprintf f "@[<hov 2>Error: the type of %s,@ %a,@ is not a type@]" x
       format_exp typ
  | Coq_re_eval_typ (_, exp, typ) ->
     fprintf f "@[<hov 2>Error: the ascribed type of@ %a,@ %a,@ is not a type@]"
       format_exp exp format_exp typ
  | Coq_re_eval_check (_, exp, typ) ->
     fprintf f "@[<hov 2>Error:@ %a@ is not of type@ %a@]" format_exp exp
       format_exp typ
  (* The level of a universe that is no level, in the binders crossed to
     reach it; a numeral there is a natural number, not the level. *)
  | Coq_re_level (_, delta, t) ->
     let hint f () =
       match get_nat_of_obj (exp_to_obj ~delta t) with
       | Some n -> fprintf f ";@ write %dl for the level %d" n n
       | None -> () in
     fprintf f "@[<hov 2>Error:@ %a@ is not of type Level@@n for any n@ (the level of@ %a)%a@]"
       (format_exp_in delta) t (format_exp_in delta) (Coq_a_univ t) hint ()
  | Coq_re_eval_infer (_, exp) ->
     fprintf f "@[<hov 2>Error:@ %a@ has no inferable type@]" format_exp exp
  | Coq_re_cycle ch ->
     fprintf f "@[<hov 2>Error: cyclic import:@ %a@]"
       pp_u (String.concat (" " ^ s_arrow ^ " ") (List.map string_of_upath ch))
  | Coq_re_unit (fp, msg) ->
     fprintf f "@[<hov 2>Error: %a:@ %s@]" pp_upath fp msg
  (* A private member is named by the module declaring it, from its unit. *)
  (* Option B: an alias, or any module but by the direct path of an
     inductive type, is no term. *)
  | Coq_re_mod_term q ->
     fprintf f "@[<hov 2>Error: %a is a module, not a term@]" pp_u (string_of_qpath q.q_unit q.q_chain)
  | Coq_re_not_ind q ->
     fprintf f "@[<hov 2>Error: %a is not an inductive type@]" pp_u (string_of_qpath q.q_unit q.q_chain)
  | Coq_re_private (q, x) ->
     fprintf f "@[<hov 2>Error: %a is private@]" pp_u (string_of_qpath q.q_unit (q.q_chain @ [x]))
  (* A member selected from a term, in the binders crossed to reach it:
     the term's type is not inferred, or is no record type. *)
  | Coq_re_access_no_type (_, ox, delta, m, y) ->
     fprintf f "@[<hov 2>Error: %s is selected from@ %a,@ whose type cannot be inferred@]"
       y (format_exp_named ox delta) m
  (* A record type applied to a value where a term stands: what it is, and
     what to write instead. *)
  | Coq_re_record_value_term (_, ox, delta, m, n) ->
     let head = McttExtracted.Group.app_head m and args = McttExtracted.Group.app_args m in
     let ty = McttExtracted.Syntax.apps_exp head (List.filteri (fun i _ -> i < n) args) in
     let v = List.nth args n in
     fprintf f "@[<hov 2>Error: %a@ is the module of the record value@ %a;@ write@ (%a).f@ for a field,@ or@ %a@ for the type@]"
       (format_exp_named ox delta) m (format_exp_named ox delta) v (format_exp_named ox delta) m
       (format_exp_named ox delta) ty
  | Coq_re_record_fields_order (q, xs, y, x) ->
     fprintf f "@[<hov 2>Error: fields of %a must be given in order:@ %s;@ got %s before %s@]"
       pp_u (string_of_qpath q.q_unit q.q_chain) (String.concat ", " xs) y x
  | Coq_re_record_field_unknown (q, y) ->
     fprintf f "@[<hov 2>Error: %s is not a field of record %a@]" y pp_u (string_of_qpath q.q_unit q.q_chain)
  | Coq_re_record_field_missing (q, x) ->
     fprintf f "@[<hov 2>Error: field %s of record %a is missing@]" x pp_u (string_of_qpath q.q_unit q.q_chain)
  (* A field whose value is not of its type, in the binders crossed to
     reach the record value: the type is the field's at the record's
     parameters and the fields before it. *)
  | Coq_re_record_field (_, ox, delta, q, x, m, a) ->
     fprintf f "@[<hov 2>Error: field %s of record %a:@ %a@ is not of type@ %a@]"
       x pp_u (string_of_qpath q.q_unit q.q_chain) (format_exp_named ox delta) m (format_exp_named ox delta) a
  | Coq_re_record_member (q, y) ->
     fprintf f "@[<hov 2>Error: %s is not a member of record %a: neither a field nor a member of its with-area@]"
       y pp_u (string_of_qpath q.q_unit q.q_chain)
  | Coq_re_access_not_record (_, ox, delta, m, a, y) ->
     fprintf f "@[<hov 2>Error: %s is selected from@ %a,@ of type@ %a,@ which is not a record type@]"
       y (format_exp_named ox delta) m (format_exp_named ox delta) a
  (* A private entry of a local body, from the local module. *)
  | Coq_re_private_local (ch, x) ->
     fprintf f "@[<hov 2>Error: %s is private in a local module, but it is used outside it@]" (String.concat "." (ch @ [x]))
  | Coq_re_nested (x, c, y, h) ->
     fprintf f "@[<hov 2>Error: %s occurs in a non-uniform argument of@ %a@ in the argument %s of %s;@ a group may nest only at the uniform parameters of a declared type of a filed group@]"
       x format_exp h y c
  | Coq_re_mdef_count (n, m) ->
     fprintf f "@[<hov 2>Error: a mutual definition has one function per member of its group:@ the group has %d %s,@ the definition %d %s@]"
       n (if n = 1 then "member" else "members") m (if m = 1 then "function" else "functions")
  | Coq_re_mdef_nparams (g, m, n) ->
     fprintf f "@[<hov 2>Error: %s has %d non-uniform %s,@ its member %d@]"
       g m (if m = 1 then "parameter" else "parameters") n
  (* An eliminator's scrutinee whose type is not inferred, or is no
     inductive type: the eliminator's group is read off that type. *)
  | Coq_re_elim_scrutinee (_, ox, delta, m, None) ->
     fprintf f "@[<hov 2>Error: the scrutinee@ %a@ of an eliminator has no inferable type@]"
       (format_exp_named ox delta) m
  | Coq_re_elim_scrutinee (_, ox, delta, m, Some a) ->
     fprintf f "@[<hov 2>Error: the scrutinee@ %a@ of an eliminator is of type@ %a,@ which is not an inductive type@]"
       (format_exp_named ox delta) m (format_exp_named ox delta) a
  (* An eliminator no reading of which fits its blocks. *)
  | Coq_re_elim_no_group (_, delta, e) ->
     let scr = match e with Coq_a_elim (_, _, _, _, s) -> s | s -> s in
     fprintf f "@[<hov 2>Error: no group fits the blocks of the eliminator of@ %a@]" (format_exp_in delta) scr
  (* An eliminator several readings of which fit its blocks, each named by
     its group's type former at its uniform parameters. *)
  | Coq_re_elim_ambiguous (_, delta, e, rs) ->
     let scr = match e with Coq_a_elim (_, _, _, _, s) -> s | s -> s in
     let reading (q, us) = Format.asprintf "%a" (format_exp_in delta) (McttExtracted.Syntax.apps_exp (Coq_a_ind (q, 0)) us) in
     fprintf f "@[<hov 2>Error: the eliminator of@ %a@ is ambiguous:@ its blocks fit the eliminators of@ %a@]"
       (format_exp_in delta) scr pp_u (String.concat " and of " (List.map reading rs))
  (* An eliminator whose blocks are not those of its group: what is
     missing, extra or out of order, then the eliminator as it should be. *)
  | Coq_re_elim_blocks (_, delta, Coq_a_elim (Some p, us, _, bks, scr), missing, extra, j) ->
     let deps, xi = !current_state in
     let ms = match McttExtracted.Members.ind_lookup deps xi p with Some d -> d.ind_members | None -> [] in
     let labels = List.mapi (fun k mk -> member_label delta p us k mk) ms in
     let label k = Option.value (List.nth_opt labels k) ~default:"?" in
     let block i =
       match List.nth_opt bks i with
       | Some (Coq_eb_mk (_, _, _, [])) -> Printf.sprintf "block %d (no branches)" (i + 1)
       | Some (Coq_eb_mk (_, _, _, bs)) ->
          Printf.sprintf "block %d (branches %s)" (i + 1) (String.concat ", " (List.map (fun ((c, _), _) -> c) bs))
       | None -> Printf.sprintf "block %d" (i + 1) in
     let why =
       (match missing with
        | [] -> []
        | [ k ] -> [ "the block for " ^ label k ^ " is missing" ]
        | ks -> [ "the blocks for " ^ String.concat ", " (List.map label ks) ^ " are missing" ])
       @ (match extra with
          | [] -> []
          | [ i ] -> [ block i ^ " is for no member left" ]
          | is -> [ String.concat ", " (List.map block is) ^ " are for no member left" ])
       @ (if missing = [] && extra = [] then [ "the blocks are not in member order" ] else []) in
     fprintf f "@[<v 2>@[<hov 2>Error: an eliminator has one block per member of its group,@ in member order:@ %a;@ %a.@]@,The eliminator should read:@,%a@]"
       pp_u (String.concat ", " labels) pp_u (String.concat "; " why) (format_elim_skeleton delta) (p, us, j, scr)
  | Coq_re_elim_blocks _ -> fprintf f "@[<hov 2>Error: the blocks of an eliminator are not those of its group@]"
  | Coq_re_view (x, ((qc, k), cs), why) ->
     let open McttExtracted.IndDecl in
     let inst = McttExtracted.Syntax.apps_exp (Coq_a_ind (qc, k)) cs in
     (match why with
      | Coq_vw_container ->
         fprintf f "@[<hov 2>Error: %s nests inside@ %a,@ which is no declared type of a filed group@]" x format_exp inst
      | Coq_vw_cls (c, y, _) ->
         fprintf f "@[<hov 2>Error: %s nests inside@ %a,@ whose constructor %s's argument %s is not positive in %s there@]"
           x format_exp inst c y x
      | Coq_vw_untyped ->
         fprintf f "@[<hov 2>Error: %s nests inside@ %a,@ at which a parameter or a sibling of the container is not typed@]" x format_exp inst
      | Coq_vw_mentions_group ->
         fprintf f "@[<hov 2>Error: %s nests inside@ %a,@ a non-uniform parameter of which mentions the group@]" x format_exp inst)
  | Coq_re_ind_npar (x, k, delta, t, s) ->
     fprintf f "@[<hov 2>Error: the type of the non-uniform parameter %d of %s,@ %a,@ is not in the sort of %s,@ %a@]"
       (k + 1) x (format_exp_in delta) t x (format_exp_in delta) s
  | Coq_re_import e ->
     let open McttExtracted.Opens in
     (match e with
      | Coq_xe_target _ -> fprintf f "@[<hov 2>Error: ill-formed open@]"
      | Coq_xe_member (h, n) ->
         (* A chain from a unit is printed as a privacy error names it. *)
         let rec chain = function
           | Coq_me_unit fp -> Some (fp, [])
           | Coq_me_mem (h, y) -> Option.map (fun (fp, ch) -> (fp, ch @ [y])) (chain h)
           | _ -> None in
         (match chain h with
          | Some (fp, ch) -> fprintf f "@[<hov 2>Error: %a is not a member@]" pp_u (string_of_qpath fp (ch @ [n]))
          | None -> fprintf f "@[<hov 2>Error:@ %a@ is not a member@]" format_exp (Coq_a_mem (h, n)))
      | Coq_xe_both n -> fprintf f "@[<hov 2>Error: %s is used and exported@]" n
      | Coq_xe_fresh n -> fprintf f "@[<hov 2>Error: %s is already declared@]" n)
  | Coq_re_branch_arity (c, n, k, a, r) ->
     let count n one many = Printf.sprintf "%d %s" n (if n = 1 then one else many) in
     let parts =
       (if k > 0 then [count k "parameter" "parameters"] else [])
       @ [count a "argument" "arguments"]
       @ (if r > 0 then [count r "induction hypothesis" "induction hypotheses"] else []) in
     fprintf f "@[<hov 2>Error: the branch %s binds %s but needs %d (%s)@]"
       c (count n "name" "names") (k + a + r) (String.concat ", " parts)
  | Coq_re_branch_unknown c ->
     fprintf f "@[<hov 2>Error: %s is not a constructor of the eliminated type@]" c
  | Coq_re_branch_missing c ->
     fprintf f "@[<hov 2>Error: the eliminator has no branch for %s@]" c
  | Coq_re_branch_dup c ->
     fprintf f "@[<hov 2>Error: the eliminator has two branches for %s@]" c
  | Coq_re_branch_order cs ->
     fprintf f "@[<hov 2>Error: the branches must follow the order of the constructors:@ %s@]"
       (String.concat ", " cs)
  | Coq_re_lit (McttExtracted.Builtin.Coq_le_num n) ->
     fprintf f "@[<hov 2>Error: unknown numeral %d: no natural-number type is bound@]" n
  | Coq_re_lit McttExtracted.Builtin.Coq_le_tok ->
     fprintf f "@[<hov 2>Error: unknown type %a: no natural-number type is bound@]" pp_sym s_nat
  | Coq_re_nat (_, _, _, e') -> format_run_error_in f e'

(* What [format_main_result] prints for each entry of a successful run's
   log, one string per eval, in order: each entry starts a line of its own,
   at column 0 and with the default margin, so formatting it alone gives
   the same text. *)
let eval_outputs : main_result -> string list option = function
  | AllGood ((_, ((path, _), _)), bt, _, _, log) ->
     current_unit := path;
     current_prog := None;
     current_bt := bt;
     Some (List.map (Format.asprintf "%a" format_eval) log)
  | _ -> None

let format_main_result (f : Format.formatter) : main_result -> unit =
  let open Format in
  function
  | AllGood ((_, ((path, _), _)), bt, _, _, log) ->
     current_unit := path;
     current_prog := None;
     current_bt := bt;
     pp_open_vbox f 0;
     List.iteri
       (fun i r ->
         if i > 0 then pp_print_cut f ();
         format_eval f r)
       log;
     pp_close_box f ()
  | RunFailure (((_, ((path, _), _)) as prg), e) ->
     current_unit := path;
     current_prog := Some prg;
     current_state := ([], []);
     nat_bind := None;
     format_run_error f e
  | ElaborationFailure (_, msg) -> fprintf f "@[<hov 2>Error: %s@]" msg
  (* [ω^2] is accepted only in a large universe, [Type@{ω^2+i}]: anywhere
     else, whatever the parser state, it is a level beyond every level. *)
  | ParserFailure (_, (Parser.OMEGA2 _ as t)) ->
     fprintf f "@[<hov 2>Error: on %a:@ %a@]" Lexer.format_token t pp_text_u
       "ω^2 is not a level: every level is below it. It is written only in a large universe, \"Type@{ω^2}\" or \"Type@{ω^2+i}\"."
  | ParserFailure (s, t) ->
     fprintf f "@[<hov 2>Error: on %a:@ %a@]" Lexer.format_token t pp_text_u
       (String.trim (ParserMessages.message (Parser.Aut.coq_N_of_state s)))
  | ParserTimeout fuel -> fprintf f "@[<hov 2>Error: parser timeout with fuel %d@]" fuel
