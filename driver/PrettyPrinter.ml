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
  | Cst.Coq_c_axiom (x, ea) ->
     fprintf f "@[<hov 2>axiom %s :@ %a@]" x format_obj ea
  | Cst.Coq_c_import fp -> fprintf f "@[<hov 2>import %s@]" (String.concat "::" fp)
  | Cst.Coq_c_open (fp, ip, args, its) ->
     fprintf f "@[<hov 2>open %s" (string_of_qpath fp ip);
     List.iter (fun a -> fprintf f "@ %a" (format_obj_prec 2) a) args;
     fprintf f "%a@]" format_items its
  | Cst.Coq_c_error msg -> fprintf f "(* %s *)" msg
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
(* The unit whose terms are printed: a constant or a unit member of that unit
   is printed by its member chain alone, the way it was written. *)
let current_unit : string list ref = ref []

(* What a de Bruijn index stands for, as the printer reads it: a name, a
   self slot (whose members print as plain names, as they are written), or
   the [i]-th parameter outwards of the enclosing frames, which has no name
   here and prints as [$i]. *)
(* A slot of the leading context read from by names: the name each member
   is declared as. *)
type pent = PName of string | PSelf | PParam of int | PSlot of (string * string) list

(* The slots a unit's leading opens declare, innermost first, as the
   elaborator binds them: an alias by its name, or the names read from it. *)
let lead_slots ((leads, _) : Cst.prog) : pent list =
  List.fold_left
    (fun l c -> match c with
      | Cst.Coq_c_open (_, _, _, [((None, w), _)]) -> PName w :: l
      | Cst.Coq_c_open (_, _, _, its) ->
         PSlot (List.map (fun ((n, d), _) -> ((match n with Some n -> n | None -> d), d)) its) :: l
      | _ -> l)
    [] leads

(* The entries of a context of the core, its leading part as [lslots]. *)
let pents_of_ctx (lslots : pent list) (ctx : centry list) : pent list =
  let n = List.length ctx and m = List.length lslots in
  let rec go j k = function
    | [] -> []
    | ce :: rest ->
       if j >= n - m && j - (n - m) < m then List.nth lslots (j - (n - m)) :: go (j + 1) k rest
       else match ce with
         | Coq_ce_ass _ -> PParam k :: go (j + 1) (k + 1) rest
         | Coq_ce_mod (Coq_gu_mk ([], Coq_md_body _)) -> PSelf :: go (j + 1) k rest
         | _ -> PParam k :: go (j + 1) (k + 1) rest
  in
  go 0 0 ctx

(* Whether a term mentions the variable [k]: a local module a term binds
   but does not use, as a member type's prefix often is, is not printed. *)
let rec mentions (k : int) : exp -> bool = function
  | Coq_a_typ _ | Coq_a_nat | Coq_a_zero | Coq_a_True | Coq_a_true | Coq_a_False | Coq_a_const _ -> false
  | Coq_a_var x -> x = k
  | Coq_a_succ e -> mentions k e
  | Coq_a_natrec (em, ez, es, escr) ->
     mentions (k + 1) em || mentions k ez || mentions (k + 2) es || mentions k escr
  | Coq_a_exfalso (em, escr) -> mentions (k + 1) em || mentions k escr
  | Coq_a_pi (a, b) | Coq_a_fn (a, b) -> mentions k a || mentions (k + 1) b
  | Coq_a_app (m, n) -> mentions k m || mentions k n
  | Coq_a_let (Coq_b_def (oa, m), b) ->
     (match oa with Some a -> mentions k a | None -> false) || mentions k m || mentions (k + 1) b
  | Coq_a_let (Coq_b_mod u, b) -> mentions_unit k u || mentions (k + 1) b
  | Coq_a_mem (h, _) -> mentions_mod k h
and mentions_mod (k : int) : modexp -> bool = function
  | Coq_me_unit _ -> false
  | Coq_me_var x -> x = k
  | Coq_me_mem (h, _) -> mentions_mod k h
  | Coq_me_app (h, n) -> mentions_mod k h || mentions k n
  | Coq_me_lit u -> mentions_unit k u
and mentions_unit (k : int) (Coq_gu_mk (delta, md) : gunit) : bool =
  let rec tele k = function
    | [] -> (k, false)
    | ce :: rest ->
       let (k', b) = tele k rest in
       (k' + 1, b || mentions_centry k' ce) in
  let (k', b) = tele k delta in
  b || (match md with
        | Coq_md_alias h -> mentions_mod k' h
        | Coq_md_body phi -> mentions_body k' phi)
and mentions_body (k : int) : gmod -> bool = function
  | Coq_gm_nil -> false
  | Coq_gm_ext (phi, _, ge) ->
     mentions_body k phi
     || (match ge with
         | Coq_ge_def (_, a, om) -> mentions (k + 1) a || (match om with Some m -> mentions (k + 1) m | None -> false)
         | Coq_ge_mod (_, u) -> mentions_unit (k + 1) u)
  | Coq_gm_open (phi, h, _, _) -> mentions_body k phi || mentions_mod (k + 1) h
and mentions_centry (k : int) : centry -> bool = function
  | Coq_ce_ass a -> mentions k a
  | Coq_ce_def (a, m) -> mentions k a || mentions k m
  | Coq_ce_mod u -> mentions_unit k u

let exp_to_obj (outer : pent list) =
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
  let is_self ctx k = (List.nth_opt ctx k = Some PSelf) in
  (* The name a member read from a leading slot is declared as. *)
  let slot_name ctx k c =
    match List.nth_opt ctx k with
    | Some (PSlot m) -> Some (match List.assoc_opt c m with Some d -> d | None -> c)
    | _ -> None in
  let rec impl (ctx : pent list) : exp -> Cst.obj = function
    | Coq_a_zero -> Cst.Coq_zero
    | Coq_a_succ e -> Cst.Coq_succ (impl ctx e)
    | Coq_a_natrec (em, ez, es, escr) ->
       let mx = new_var () in
       let sx = new_var () in
       let sr = match em with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let escr' = impl ctx escr in
       let em' = impl (PName mx :: ctx) em in
       let ez' = impl ctx ez in
       let es' = impl (PName sr :: PName sx :: ctx) es in
       Cst.Coq_natrec (escr', mx, em', ez', sx, sr, es')
    | Coq_a_nat -> Cst.Coq_nat
    | Coq_a_True -> Cst.Coq_true_ty
    | Coq_a_true -> Cst.Coq_true_tm
    | Coq_a_False -> Cst.Coq_false_ty
    | Coq_a_exfalso (em, escr) ->
       let mx = new_var () in
       let escr' = impl ctx escr in
       let em' = impl (PName mx :: ctx) em in
       Cst.Coq_exfalso (escr', mx, em')
    | Coq_a_typ i -> Cst.Coq_typ i
    | Coq_a_var x -> var_to_obj ctx x
    | Coq_a_fn (ep, ebody) ->
       let px = match ep with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let ebody' = impl (PName px :: ctx) ebody in
       Cst.Coq_fn (px, ep', ebody')
    | Coq_a_app (ef, ea) ->
       let ef' = impl ctx ef in
       let ea' = impl ctx ea in
       Cst.Coq_app (ef', ea')
    | Coq_a_pi (ep, eret) ->
       let px = match ep with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let eret' = impl (PName px :: ctx) eret in
       Cst.Coq_pi (px, ep', eret')
    | Coq_a_let (Coq_b_def (oa, em), ebody) ->
       let px = match oa with Some (Coq_a_typ _) -> new_tyvar () | _ -> new_var () in
       let ea' = Option.map (impl ctx) oa in
       let em' = impl ctx em in
       let ebody' = impl (PName px :: ctx) ebody in
       Cst.Coq_letb (Cst.Coq_d_def (px, ea', em'), ebody')
    | Coq_a_let (Coq_b_mod _, ebody) when not (mentions 0 ebody) -> impl (PName "_" :: ctx) ebody
    | Coq_a_let (Coq_b_mod u, ebody) ->
       let px = new_mod () in
       let params, md = impl_unit ctx u in
       let ebody' = impl (PName px :: ctx) ebody in
       Cst.Coq_letb (Cst.Coq_d_mod (px, params, md), ebody')
    (* A member of a body read from its self slot is a sibling, written by
       its name. *)
    | Coq_a_mem (Coq_me_var k, x) when is_self ctx k -> Cst.Coq_var x
    | Coq_a_mem (Coq_me_var k, x) when slot_name ctx k x <> None ->
       (match slot_name ctx k x with Some d -> Cst.Coq_var d | None -> Cst.Coq_var x)
    | Coq_a_mem (h, x) ->
       (match chain_of h with
        | Some (fp, ms) -> path_to_obj fp (ms @ [x])
        | None -> Cst.Coq_proj (impl_mod ctx h, x))
    (* A constant is named by its qualified name. *)
    | Coq_a_const q -> path_to_obj q.q_unit q.q_chain
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
  and var_to_obj (ctx : pent list) (x : int) : Cst.obj =
    match List.nth_opt ctx x with
    | Some (PName y) -> Cst.Coq_var y
    | Some PSelf | Some (PSlot _) -> Cst.Coq_var "self"
    | Some (PParam i) -> Cst.Coq_var ("$" ^ string_of_int i)
    | None -> Cst.Coq_var ("$" ^ string_of_int (x - List.length ctx))
  and impl_mod (ctx : pent list) : modexp -> Cst.obj = function
    | Coq_me_unit fp -> path_to_obj fp []
    | Coq_me_var x -> var_to_obj ctx x
    | Coq_me_mem (Coq_me_var k, y) when is_self ctx k -> Cst.Coq_var y
    | Coq_me_mem (Coq_me_var k, y) when slot_name ctx k y <> None ->
       (match slot_name ctx k y with Some d -> Cst.Coq_var d | None -> Cst.Coq_var y)
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
  and impl_unit (ctx : pent list) (Coq_gu_mk (delta, md) : gunit)
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
          (PName px :: ctx, (px, ty) :: ps))
        (ctx, []) (List.rev delta)
    in
    let md' = match md with
      | Coq_md_alias h -> Cst.Coq_md_alias (impl_mod ctx' h)
      | Coq_md_body phi -> Cst.Coq_md_where (impl_body ctx' phi)
    in
    (List.rev params, md')
  (* Each entry of a body is read under its self slot. *)
  and impl_body (ctx : pent list) : gmod -> Cst.cmd list = function
    | Coq_gm_nil -> []
    | Coq_gm_ext (phi, x, ge) ->
       let cs = impl_body ctx phi in
       let ctx' = PSelf :: ctx in
       let c = match ge with
         | Coq_ge_def (priv, a, om) ->
            let m = { Cst.md_private = priv; Cst.md_abstract = false } in
            let a' = impl ctx' a in
            (match om with
             | Some e -> Cst.Coq_c_def (m, x, a', impl ctx' e)
             | None -> Cst.Coq_c_axiom (x, a'))
         | Coq_ge_mod (priv, u) ->
            let params, md = impl_unit ctx' u in
            Cst.Coq_c_mod (priv, x, params, md)
       in
       cs @ [c]
    | Coq_gm_open (phi, h, oz, its) ->
       let cs = impl_body ctx phi in
       (* The target is a module expression, printed in place of a path. *)
       let target = Format.asprintf "%a" format_obj (impl_mod (PSelf :: ctx) h) in
       let its' = (match oz with Some z -> [((None, z), true)] | None -> [])
                   @ List.map (fun ((n, d), pv) -> ((Some n, d), pv)) its in
       cs @ [Cst.Coq_c_open ([], [target], [], its')]
  in
  fun exp ->
    reset_var_suffix ();
    reset_tyvar_suffix ();
    reset_mod_suffix ();
    impl outer exp

let format_exp_in outer f exp = format_obj f (exp_to_obj outer exp)
let format_exp f exp = format_exp_in [] f exp

(************************************************************)
(* Formatting nf *)
(************************************************************)

let format_nf_in outer f nf = format_exp_in outer f (nf_to_exp nf)
let format_nf f nf = format_nf_in [] f nf

(************************************************************)
(* Formatting main_result *)
(************************************************************)

(* The names of the current unit's leading opens. *)
let current_leads : pent list ref = ref []

let format_eval (f : Format.formatter) (r : Command1.eval_entry) : unit =
  let outer = pents_of_ctx !current_leads r.ev_ctx in
  Format.fprintf f "@[<hov 2>Evaluate %a@ --> %a@ : %a@]" (format_exp_in outer) r.ev_exp
    (format_nf_in outer) r.ev_nf (format_exp_in outer) r.ev_typ

let format_run_error (f : Format.formatter) : Command1.run_error -> unit =
  let open Format in
  let ex ctx = format_exp_in (pents_of_ctx !current_leads ctx) in
  function
  | Coq_re_msg msg -> fprintf f "@[<hov 2>Error: %s@]" msg
  | Coq_re_def (x, ctx, typ, exp) ->
     fprintf f "@[<hov 2>Error: the body of %s,@ %a,@ is not of type@ %a@]" x
       (ex ctx) exp (ex ctx) typ
  | Coq_re_eval_check (ctx, exp, typ) ->
     fprintf f "@[<hov 2>Error:@ %a@ is not of type@ %a@]" (ex ctx) exp
       (ex ctx) typ
  | Coq_re_eval_infer (ctx, exp) ->
     fprintf f "@[<hov 2>Error:@ %a@ has no inferable type@]" (ex ctx) exp
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
     fprintf f "@[<hov 2>Error: %s is private in a local module, but it is used outside it@]" (String.concat "." (ch @ [x]))
  | Coq_re_import (ctx, e) ->
     let open McttExtracted.Imports in
     (match e with
      | Coq_xe_target _ -> fprintf f "@[<hov 2>Error: ill-formed open@]"
      | Coq_xe_member (h, n) ->
         (* A chain from a unit is printed as a privacy error names it. *)
         let rec chain = function
           | Coq_me_unit fp -> Some (fp, [])
           | Coq_me_mem (h, y) -> Option.map (fun (fp, ch) -> (fp, ch @ [y])) (chain h)
           | _ -> None in
         (match chain h with
          | Some (fp, ch) -> fprintf f "@[<hov 2>Error: %s is not a member@]" (string_of_qpath fp (ch @ [n]))
          | None -> fprintf f "@[<hov 2>Error:@ %a@ is not a member@]" (ex ctx) (Coq_a_mem (h, n)))
      | Coq_xe_both n -> fprintf f "@[<hov 2>Error: %s is used and exported@]" n
      | Coq_xe_fresh n -> fprintf f "@[<hov 2>Error: %s is already declared@]" n)

let format_main_result (f : Format.formatter) : main_result -> unit =
  let open Format in
  function
  | AllGood (((_, ((path, _), _)) as prg), _, _, log) ->
     current_unit := path;
     current_leads := lead_slots prg;
     pp_open_vbox f 0;
     List.iteri
       (fun i r ->
         if i > 0 then pp_print_cut f ();
         format_eval f r)
       log;
     pp_close_box f ()
  | RunFailure (((_, ((path, _), _)) as prg), e) ->
     current_unit := path;
     current_leads := lead_slots prg;
     format_run_error f e
  | ElaborationFailure (_, msg) -> fprintf f "@[<hov 2>Error: %s@]" msg
  | ParserFailure (s, t) ->
     fprintf f "@[<hov 2>Error: on %a:@ %a@]" Lexer.format_token t pp_print_text
       (String.trim (ParserMessages.message (Parser.Aut.coq_N_of_state s)))
  | ParserTimeout fuel -> fprintf f "@[<hov 2>Error: parser timeout with fuel %d@]" fuel
