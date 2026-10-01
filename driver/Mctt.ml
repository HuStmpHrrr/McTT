open McttLib.Main

let () =
  let search_root = ref "." in
  let files = ref [] in
  let usage =
    Printf.sprintf "Usage: %s [--search-root <dir>] <input-file>" Sys.argv.(0)
  in
  let specs =
    [ ( "--search-root",
        Arg.Set_string search_root,
        "<dir> where imported units are looked up: X::Y is <dir>/X/Y.mctt \
         (default: the current directory)" ) ]
  in
  Arg.parse specs (fun f -> files := f :: !files) usage;
  match !files with
  | [ filename ] -> exit (main_of_filename ~search_root:!search_root filename)
  | _ ->
     prerr_endline usage;
     exit 7
