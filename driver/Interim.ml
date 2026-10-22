(* UNVERIFIED, INTERIM CODE.

   The verified checker ([Extraction.Command]) takes two functions whose
   termination proofs are still being written:

   - [views_search], which finds the views of a group as [views_bfs] does
     ([Core.Syntactic.Inductives.Group]); it will be replaced by the Rocq
     function proved to satisfy [views_ok] and [views_search_complete];
   - [site_search], which resolves a site of an eliminator's annotation as
     [site_resolves] does ([Core.Syntactic.Builtin]); it will be replaced by
     the Rocq decider built on [MemberType.mdenote_impl] and the order of
     every module expression over a well-formed global context.

   The two functions below mirror those relations exactly, with no limit
   and no cutoff, on the extracted deciders.  Their results carry no proof:
   until they are replaced, a wrong result here can only make a program run
   accept or reject wrongly; the Rocq theorems hold for any implementation
   meeting the interfaces. *)

open McttExtracted
open Syntax
open Datatypes
open Specif
module List = Stdlib.List

(* [views_bfs sibs meets acc tr Vs], breadth-first: the next instance adds
   its new views, its siblings and itself ([views_met]), whose instances
   met are queued after the others ([rcons_views] of their classified
   constructors).  Each view is decided once. *)
let views_search (theta : gdeps) (xi : gstack) (_ : Obj.t) (r : Command.raw_decl)
    (csd : (string * Group.rcarg list) list list) : Command1.views_found Command1.rres =
  let first =
    match r.Command.rd_members with m :: _ -> m.Command.rm_name | [] -> "" in
  let exception Rejected of Command1.run_error in
  (* The tables, aligned with the views found: siblings, classified
     constructors, non-uniform parameters. *)
  let table : (Group.rview * (Group.rview list * (string * Group.rcarg list) list * centry list)) list ref = ref [] in
  let find x = List.find_map (fun (y, e) -> if Group.rview_eq_dec x y then Some e else None) !table in
  let decide x =
    match find x with
    | Some e -> e
    | None ->
       let get = function
         | Coq_inl v -> v
         | Coq_inr why -> raise (Rejected (Command1.Coq_re_view (first, x, why)))
       in
       let ss = get (IndDecl.view_sibs_dec theta xi r x) in
       let cs = get (IndDecl.view_cls_dec theta xi r x) in
       let nv = get (IndDecl.view_nps_dec theta xi r x) in
       table := !table @ [ (x, (ss, cs, nv)) ];
       (ss, cs, nv)
  in
  let sibs x = let ss, _, _ = decide x in ss in
  let meets y = let _, cs, _ = decide y in Group.rcons_views cs in
  let rec bfs acc tr =
    match tr with
    | [] -> acc
    | x :: tr' ->
       let fresh = Group.views_met sibs acc x in
       bfs (acc @ fresh) (tr' @ List.concat_map meets fresh)
  in
  match bfs [] (List.concat_map Group.rcons_views csd) with
  | vs ->
     let ss = List.map (fun v -> let s, _, _ = decide v in s) vs in
     let csv = List.map (fun v -> let _, c, _ = decide v in c) vs in
     let nvs = List.map (fun v -> let _, _, n = decide v in n) vs in
     Command1.Coq_rok (Coq_existT (vs, Coq_existT (ss, Coq_existT (csv, nvs))))
  | exception Rejected e -> Command1.Coq_rerr e

(* [site_resolves]: the annotation's head denotes a member of a group, as
   any member does ([mdenote]), or is the type former of one; the uniform
   parameters are the first [ind_nu] arguments, strengthened past the
   binders the annotation is under. *)
let site_search (theta : gdeps) (xi : gstack) (_ : Obj.t) (s : Builtin.fill_site) : Builtin.fill_result option =
  let (gamma, d), z = s in
  let take n l = List.filteri (fun i _ -> i < n) l in
  let strengthen us = Group.img_pats (List.init d (fun _ -> true)) us in
  match Group.app_head z with
  | Coq_a_mem (h, x) ->
     (match MemberType.mdenote_impl theta xi (Builtin.ctx_holes d @ gamma) (Coq_me_mem (h, x)) with
      | Some (Members.Coq_ds_ind (theta', p, _, ns)) ->
         (match Members.ind_lookup theta xi p with
          | Some dd ->
             (match strengthen (take (Syntax.ind_nu dd) (Builtin.head_args theta' ns (Group.app_args z))) with
              | Some us -> Some (p, us)
              | None -> None)
          | None -> None)
      | _ -> None)
  | Coq_a_ind (p, _) ->
     (match Members.ind_lookup theta xi p with
      | Some dd ->
         (match strengthen (take (Syntax.ind_nu dd) (Group.app_args z)) with
          | Some us -> Some (p, us)
          | None -> None)
      | None -> None)
  | _ -> None
