open McttLib.Main

let () =
  let search_roots = ref [] in
  let files = ref [] in
  let usage =
    Printf.sprintf
      "Usage: %s [--search-root <dir>]... <input-file>\n\
       An imported unit X::Y is the file X/Y.mctt under a search root.  The \
       search roots, in lookup order, are: the --search-root directories in \
       the order given, then the entries of the colon-separated list %s \
       (empty entries are ignored), then the current directory.  A unit \
       found under several roots is read from the first."
      Sys.argv.(0) search_root_env
  in
  let specs =
    [ ( "--search-root",
        Arg.String (fun d -> search_roots := !search_roots @ [ d ]),
        "<dir> a directory where imported units are looked up; may be given \
         more than once, each adding a root" ) ]
  in
  Arg.parse specs (fun f -> files := f :: !files) usage;
  match !files with
  | [ filename ] ->
     exit (main_of_command_line !search_roots (Sys.getenv_opt search_root_env) filename)
  | _ ->
     prerr_endline usage;
     exit 7
