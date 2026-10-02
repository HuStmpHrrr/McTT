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

(************************************************************)
(* Formatting Cst.obj *)
(************************************************************)
let rec get_nat_of_obj : Cst.obj -> int option = function
  | Cst.Coq_zero -> Some 0
  | Cst.Coq_succ e -> Option.map (( + ) 1) (get_nat_of_obj e)
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

let rec format_obj_prec (p : int) (f : Format.formatter) : Cst.obj -> unit =
  let open Format in
  function
  | Cst.Coq_typ i -> fprintf f "Type@%d" i
  | Cst.Coq_nat -> fprintf f "Nat"
  | Cst.Coq_zero -> fprintf f "0"
  | Cst.Coq_succ e -> begin
     match get_nat_of_obj e with
     | Some n -> fprintf f "%d" (1 + n)
     | None ->
        let impl f () = fprintf f "succ@ %a" (format_obj_prec 2) e in
        pp_open_hovbox f 2;
        pp_print_paren_if (p >= 2) impl f ();
        pp_close_box f ()
   end
  | Cst.Coq_natrec (escr, mx, em, ez, sx, sr, es) ->
     let impl f () =
       fprintf f
         "@[<hv 0>@[<hov 2>rec %a@ return %s . %a@]@ @[<hov 2>| zero =>@ \
          %a@]@ @[<hov 2>| succ %s, %s =>@ %a@]@ end@]"
         format_obj escr mx format_obj em format_obj ez sx sr format_obj es
     in
     pp_print_paren_if (p >= 1) impl f ()
  | Cst.Coq_true_ty -> fprintf f "True"
  | Cst.Coq_true_tm -> fprintf f "true"
  | Cst.Coq_false_ty -> fprintf f "False"
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
       pp_print_string f "fun ";
       pp_open_tbox f ();
       pp_set_tab f ();
       pp_print_list ~pp_sep:pp_print_tab format_obj_param f ((px, ep) :: params);
       pp_close_tbox f ();
       begin
         if List.compare_length_with params 0 = 0
         then pp_print_space f ()
         else pp_force_newline f ()
       end;
       fprintf f "-> @[<hov 2>%a@]" format_obj ebody'
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()
  | Cst.Coq_pi (px, ep, eret) ->
     let params, eret' = get_pi_params_of_obj eret in
     let impl f () =
       pp_print_string f "forall ";
       pp_open_tbox f ();
       pp_set_tab f ();
       pp_print_list ~pp_sep:pp_print_tab format_obj_param f ((px, ep) :: params);
       pp_close_tbox f ();
       begin
         if List.compare_length_with params 0 = 0
         then pp_print_space f ()
         else pp_force_newline f ()
       end;
       fprintf f "-> @[<hov 2>%a@]" format_obj eret'
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()
  | Cst.Coq_var x -> pp_print_string f x
  | Cst.Coq_glob path -> pp_print_string f (String.concat "::" path)
  (* Dot binds tighter than application, so the target prints at the precedence
     of an application argument. *)
  | Cst.Coq_proj (e, x) -> fprintf f "%a.%s" (format_obj_prec 2) e x
  | Cst.Coq_letb _ as e ->
     let decls, ebody = get_letb_decls_of_obj e in
     let impl f () =
       pp_print_string f "let";
       List.iter (fun d -> fprintf f "@ %a" format_decl d) decls;
       fprintf f "@ in @[<hov 2>%a@]@;<1 -2>end" format_obj ebody
     in
     pp_open_vbox f 2;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()

and format_decl (f : Format.formatter) : Cst.decl -> unit =
  let open Format in
  function
  | Cst.Coq_d_def (m, x, ea, eb) ->
     fprintf f "@[<hov 2>%adef %s : %a :=@ %a@]" format_mods m x format_obj ea
       format_obj eb
  | Cst.Coq_d_mod (x, e) -> fprintf f "@[<hov 2>module %s :=@ %a@]" x format_obj e

and format_obj_param f (px, ep) = Format.fprintf f "(%s : %a)" px format_obj ep
and format_obj f = format_obj_prec 0 f

(************************************************************)
(* Formatting Cst.cmd and Cst.prog *)
(************************************************************)

let format_ispec (f : Format.formatter) : Cst.ispec -> unit =
  let open Format in
  function
  | Cst.Coq_i_open -> ()
  | Cst.Coq_i_as x -> fprintf f " as %s" x
  | Cst.Coq_i_use ns -> fprintf f " use (%s)" (String.concat "; " ns)

(* [::] joins a file path and [.] an internal one; either half may be empty. *)
let string_of_qpath (fp : string list) (ip : string list) : string =
  match (fp, ip) with
  | [], _ -> String.concat "." ip
  | _, [] -> String.concat "::" fp
  | _, _ -> String.concat "::" fp ^ "." ^ String.concat "." ip

let rec format_cmd (f : Format.formatter) : Cst.cmd -> unit =
  let open Format in
  function
  | Cst.Coq_c_mod (path, params, cs) ->
     pp_open_vbox f 2;
     fprintf f "module %s" (String.concat "." path);
     List.iter (fun p -> fprintf f " %a" format_obj_param p) params;
     pp_print_string f " where";
     List.iter (fun c -> fprintf f "@ %a" format_cmd c) cs;
     fprintf f "@;<1 -2>end";
     pp_close_box f ()
  | Cst.Coq_c_def (m, x, ea, eb) ->
     fprintf f "@[<v 2>%adef %s : %a :=@ %a@;<1 -2>end" format_mods m x
       format_obj ea format_obj eb;
     pp_close_box f ()
  | Cst.Coq_c_import (fp, ip, spec) ->
     fprintf f "import %s%a" (string_of_qpath fp ip) format_ispec spec
  | Cst.Coq_c_eval (e, ot) -> begin
     match ot with
     | None -> fprintf f "@[<hov 2>eval %a@]" format_obj e
     | Some t ->
        fprintf f "@[<hov 2>eval %a@ : %a@]" format_obj e format_obj t
   end

let format_prog (f : Format.formatter) ((is, ((path, params), cs)) : Cst.prog) : unit =
  let open Format in
  List.iter (fun c -> fprintf f "%a@ " format_cmd c) is;
  pp_open_vbox f 2;
  (* The unit's own name is a [::] path *)
  fprintf f "module %s" (String.concat "::" path);
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

let exp_to_obj =
  let new_var, reset_var_suffix =
    let suffix = ref 0 in
    ( (fun () ->
        incr suffix;
        "x" ^ string_of_int !suffix),
      fun () -> suffix := 0 )
  in
  let new_tyvar, reset_tyvar_suffix =
    let suffix = ref 0 in
    ( (fun () ->
        incr suffix;
        "A" ^ string_of_int !suffix),
      fun () -> suffix := 0 )
  in
  let rec impl (ctx : string list) : exp -> Cst.obj = function
    | Coq_a_zero -> Cst.Coq_zero
    | Coq_a_succ e -> Cst.Coq_succ (impl ctx e)
    | Coq_a_natrec (em, ez, es, escr) ->
       let mx = new_var () in
       let sx = new_var () in
       let sr = match em with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let escr' = impl ctx escr in
       let em' = impl (mx :: ctx) em in
       let ez' = impl ctx ez in
       let es' = impl (sr :: sx :: ctx) es in
       Cst.Coq_natrec (escr', mx, em', ez', sx, sr, es')
    | Coq_a_nat -> Cst.Coq_nat
    | Coq_a_True -> Cst.Coq_true_ty
    | Coq_a_true -> Cst.Coq_true_tm
    | Coq_a_False -> Cst.Coq_false_ty
    | Coq_a_exfalso (em, escr) ->
       let mx = new_var () in
       let escr' = impl ctx escr in
       let em' = impl (mx :: ctx) em in
       Cst.Coq_exfalso (escr', mx, em')
    | Coq_a_typ i -> Cst.Coq_typ i
    (* A variable past the local binders is a parameter of an open module,
       which has no name here: it prints as [$k], counting outwards. *)
    | Coq_a_var x ->
       (match List.nth_opt ctx x with
        | Some y -> Cst.Coq_var y
        | None -> Cst.Coq_var ("$" ^ string_of_int (x - List.length ctx)))
    | Coq_a_fn (ep, ebody) ->
       let px = match ep with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let ebody' = impl (px :: ctx) ebody in
       Cst.Coq_fn (px, ep', ebody')
    | Coq_a_app (ef, ea) ->
       let ef' = impl ctx ef in
       let ea' = impl ctx ea in
       Cst.Coq_app (ef', ea')
    | Coq_a_pi (ep, eret) ->
       let px = match ep with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let eret' = impl (px :: ctx) eret in
       Cst.Coq_pi (px, ep', eret')
    (* A path is absolute.  Into the unit being printed, the member chain is
       what was written, its first member an ordinary name; into another unit,
       the unit is a [glob] head.  Either way the remaining members are a
       chain of [proj]s over the head. *)
    | Coq_a_glob p ->
       let head, ip =
         if p.p_unit = !current_unit then
           (match p.p_mems with
            | x :: ip -> (Cst.Coq_var x, ip)
            (* Unreachable: [path_valid] rules out an empty member chain. *)
            | [] -> (Cst.Coq_var "_", []))
         else (Cst.Coq_glob p.p_unit, p.p_mems)
       in
       List.fold_left (fun e y -> Cst.Coq_proj (e, y)) head ip
  in
  fun exp ->
    reset_var_suffix ();
    reset_tyvar_suffix ();
    impl [] exp

let format_exp f exp = format_obj f (exp_to_obj exp)

(************************************************************)
(* Formatting nf *)
(************************************************************)

let format_nf f nf = format_exp f (nf_to_exp nf)

(************************************************************)
(* Formatting main_result *)
(************************************************************)

let format_eval (f : Format.formatter) (r : Command1.eval_entry) : unit =
  Format.fprintf f "@[<hov 2>Evaluate %a@ --> %a@ : %a@]" format_exp r.ev_exp
    format_nf r.ev_nf format_exp r.ev_typ

let format_run_error (f : Format.formatter) : Command1.run_error -> unit =
  let open Format in
  function
  | Coq_re_msg msg -> fprintf f "@[<hov 2>Error: %s@]" msg
  | Coq_re_def (x, _, typ, exp) ->
     fprintf f "@[<hov 2>Error: the body of %s,@ %a,@ is not of type@ %a@]" x
       format_exp exp format_exp typ
  | Coq_re_eval_check (_, exp, typ) ->
     fprintf f "@[<hov 2>Error:@ %a@ is not of type@ %a@]" format_exp exp
       format_exp typ
  | Coq_re_eval_infer (_, exp) ->
     fprintf f "@[<hov 2>Error:@ %a@ has no inferable type@]" format_exp exp
  | Coq_re_cycle ch ->
     fprintf f "@[<hov 2>Error: cyclic import:@ %s@]"
       (String.concat " -> " (List.map Command1.path_str ch))
  | Coq_re_unit (fp, msg) ->
     fprintf f "@[<hov 2>Error: %s:@ %s@]" (Command1.path_str fp) msg

let format_main_result (f : Format.formatter) : main_result -> unit =
  let open Format in
  function
  | AllGood ((_, ((path, _), _)), _, _, log) ->
     current_unit := path;
     pp_open_vbox f 0;
     List.iteri
       (fun i r ->
         if i > 0 then pp_print_cut f ();
         format_eval f r)
       log;
     pp_close_box f ()
  | RunFailure ((_, ((path, _), _)), e) ->
     current_unit := path;
     format_run_error f e
  | ElaborationFailure (_, msg) -> fprintf f "@[<hov 2>Error: %s@]" msg
  | ParserFailure (s, t) ->
     fprintf f "@[<hov 2>Error: on %a:@ %a@]" Lexer.format_token t pp_print_text
       (String.trim (ParserMessages.message (Parser.Aut.coq_N_of_state s)))
  | ParserTimeout fuel -> fprintf f "@[<hov 2>Error: parser timeout with fuel %d@]" fuel
