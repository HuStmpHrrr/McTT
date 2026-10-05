(* mctt-doc: HTML pages for the units under a root.

     mctt-doc ROOT OUTDIR    one page per unit, and an index, in OUTDIR
     mctt-doc --check ROOT   report what does not line up or resolve
     mctt-doc --links ROOT X::Y NAME
                             where each occurrence of NAME in X::Y links to

   Both exit 1 if anything does not line up or resolve. *)

module D = McttLib.Doc

let () =
  let t0 = Unix.gettimeofday () in
  let report lib =
    let ps = D.problems lib in
    List.iter print_endline ps;
    let s = D.stats lib in
    Printf.eprintf "%d units, %d names: %d linked, %d binders, %d not resolved; %.2fs\n"
      (List.length lib.D.units) s.D.names s.D.linked s.D.binders (List.length s.D.unresolved)
      (Unix.gettimeofday () -. t0);
    ps = []
  in
  match Array.to_list Sys.argv with
  | [ _; "--check"; root ] -> exit (if report (D.load root) then 0 else 1)
  | [ _; root; out ] ->
      let lib = D.load root in
      let ok = report lib in
      D.write_site lib out;
      exit (if ok then 0 else 1)
  | [ _; "--links"; root; u; x ] ->
      let lib = D.load root in
      let fq = List.filter (( <> ) "") (String.split_on_char ':' u) in
      let rec go n = match D.link_of lib fq x n with
        | "no occurrence" -> () | l -> print_endline l; go (n + 1) in
      go 1
  | _ -> prerr_endline "usage: mctt-doc (ROOT OUTDIR | --check ROOT | --links ROOT UNIT NAME)"; exit 2
