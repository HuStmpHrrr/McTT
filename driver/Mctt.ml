open McttLib.Main

let () =
  let search_roots = ref [] in
  let files = ref [] in
  let usage =
    Printf.sprintf "Usage: %s [--search-root <dir>] <input-file>" Sys.argv.(0)
  in
  let specs =
    [ ( "--search-root",
        Arg.String (fun d -> search_roots := !search_roots @ [ d ]),
        "<dir> where imported units are looked up: X::Y is <dir>/X/Y.mctt; \
         given more than once, the roots are tried in order \
         (default: the current directory)" ) ]
  in
  Arg.parse specs (fun f -> files := f :: !files) usage;
  match !files with
  | [ filename ] ->
     let search_root, extra_roots =
       match !search_roots with [] -> (".", []) | r :: rs -> (r, rs) in
     exit (main_of_filename ~search_root ~extra_roots filename)
  | _ ->
     prerr_endline usage;
     exit 7
