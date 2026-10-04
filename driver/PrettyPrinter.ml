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
     fprintf f "@[<hov 2>%s : %a :=@ %a@]" x format_obj ea format_obj eb
  | Cst.Coq_d_def (x, None, eb) ->
     fprintf f "@[<hov 2>%s :=@ %a@]" x format_obj eb
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
     fprintf f " :=@ %a@]" format_obj e

and format_cmd (f : Format.formatter) : Cst.cmd -> unit =
  let open Format in
  function
  | Cst.Coq_c_mod (priv, x, params, md) ->
     if priv then Format.pp_print_string f "private ";
     format_module f x params md
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

and format_obj_param f (px, ep) = Format.fprintf f "(%s : %a)" px format_obj ep
and format_obj f = format_obj_prec 0 f

(************************************************************)
(* Formatting Cst.cmd and Cst.prog *)
(************************************************************)

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
    | Coq_a_var x -> var_to_obj ctx x
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
    | Coq_a_let (Coq_b_def (oa, em), ebody) ->
       let px = match oa with Some (Coq_a_typ _) -> new_tyvar () | _ -> new_var () in
       let ea' = Option.map (impl ctx) oa in
       let em' = impl ctx em in
       let ebody' = impl (px :: ctx) ebody in
       Cst.Coq_letb (Cst.Coq_d_def (px, ea', em'), ebody')
    | Coq_a_let (Coq_b_mod u, ebody) ->
       let px = new_mod () in
       let params, md = impl_unit ctx u in
       let ebody' = impl (px :: ctx) ebody in
       Cst.Coq_letb (Cst.Coq_d_mod (px, params, md), ebody')
    | Coq_a_mem (h, x) ->
       (match chain_of h with
        | Some (fp, ms) -> path_to_obj fp (ms @ [x])
        | None -> Cst.Coq_proj (impl_mod ctx h, x))
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
    | None -> Cst.Coq_var ("$" ^ string_of_int (x - List.length ctx))
  and impl_mod (ctx : string list) : modexp -> Cst.obj = function
    | Coq_me_unit fp -> path_to_obj fp []
    | Coq_me_var x -> var_to_obj ctx x
    | Coq_me_mem (h, y) ->
       (match chain_of h with
        | Some (fp, ms) -> path_to_obj fp (ms @ [y])
        | None -> Cst.Coq_proj (impl_mod ctx h, y))
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
            | Coq_ce_ass a | Coq_ce_def (a, _) -> impl ctx a
            | Coq_ce_mod _ -> Cst.Coq_var "_" in
          let px = match ce with
            | Coq_ce_ass (Coq_a_typ _) | Coq_ce_def (Coq_a_typ _, _) -> new_tyvar ()
            | _ -> new_var () in
          (px :: ctx, (px, ty) :: ps))
        (ctx, []) (List.rev delta)
    in
    let md' = match md with
      | Coq_md_alias h -> Cst.Coq_md_alias (impl_mod ctx' h)
      | Coq_md_body phi -> Cst.Coq_md_where (fst (impl_body ctx' phi))
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
             | None -> Cst.Coq_c_def (m, x, a', Cst.Coq_var "_"))
         | Coq_ge_mod (priv, u) ->
            let params, md = impl_unit ctx' u in
            Cst.Coq_c_mod (priv, x, params, md)
       in
       (cs @ [c], x :: ctx')
    | Coq_gm_import (phi, h, its) ->
       let cs, ctx' = impl_body ctx phi in
       (* The target is a module expression, printed in place of a path;
          each item binds its name. *)
       let target = Format.asprintf "%a" format_obj (impl_mod ctx' h) in
       let names = List.map (fun ((_, d), _) -> d) its in
       let spec = match its with
         | [] -> Cst.Coq_i_open
         | [((None, y), _)] -> Cst.Coq_i_as y
         | _ -> Cst.Coq_i_use (List.map (fun ((n, d), _) -> match n with Some n -> n | None -> d) its)
       in
       (cs @ [Cst.Coq_c_import ([], [target], spec)], List.rev_append names ctx')
  in
  fun exp ->
    reset_var_suffix ();
    reset_tyvar_suffix ();
    reset_mod_suffix ();
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
       (String.concat " -> " (List.map (String.concat "::") ch))
  | Coq_re_unit (fp, msg) ->
     fprintf f "@[<hov 2>Error: %s:@ %s@]" ((String.concat "::") fp) msg
  (* A private member is named by the module declaring it, from its unit. *)
  | Coq_re_private (q, x) ->
     fprintf f "@[<hov 2>Error: %s is private@]" (string_of_qpath q.q_unit (q.q_chain @ [x]))
  (* A private entry of a local body, from the local module. *)
  | Coq_re_private_local (ch, x) ->
     fprintf f "@[<hov 2>Error: %s is private@]" (String.concat "." (ch @ [x]))
  | Coq_re_import e ->
     let open McttExtracted.Imports in
     (match e with
      | Coq_xe_target _ -> fprintf f "@[<hov 2>Error: ill-formed import@]"
      | Coq_xe_member (h, n) ->
         (* A chain from a unit is printed as a privacy error names it. *)
         let rec chain = function
           | Coq_me_unit fp -> Some (fp, [])
           | Coq_me_mem (h, y) -> Option.map (fun (fp, ch) -> (fp, ch @ [y])) (chain h)
           | _ -> None in
         (match chain h with
          | Some (fp, ch) -> fprintf f "@[<hov 2>Error: %s is not a member@]" (string_of_qpath fp (ch @ [n]))
          | None -> fprintf f "@[<hov 2>Error:@ %a@ is not a member@]" format_exp (Coq_a_mem (h, n)))
      | Coq_xe_both n -> fprintf f "@[<hov 2>Error: %s is used and exported@]" n
      | Coq_xe_fresh n -> fprintf f "@[<hov 2>Error: %s is already declared@]" n)

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
