(* [search_root] is where an imported unit [X::Y] is looked up, as
   [search_root/X/Y.mctt]; it defaults to the current directory.  The
   [extra_roots] are tried after it, in order. *)
val main_of_filename : ?search_root:string -> ?extra_roots:string list -> string -> int
val main_of_program_string : ?search_root:string -> ?extra_roots:string list -> string -> int

(* The name of the environment variable listing extra search roots,
   [MCTT_SEARCH_ROOT]. *)
val search_root_env : string
(* [search_roots flags env] is the list of search roots of the command line,
   in lookup order: the [--search-root] directories [flags] in the order
   given, then the entries of [env], the colon-separated value of
   [MCTT_SEARCH_ROOT] if set (empty entries ignored), then the current
   directory. *)
val search_roots : string list -> string option -> string list
(* [main_of_command_line flags env filename] checks [filename] with the
   search roots [search_roots flags env]: what the executable runs. *)
val main_of_command_line : string list -> string option -> string -> int

(* The pieces of [main_of_lexbuf] the documentation generator reuses: the
   parser's fuel, the file of a unit under a search root, and the reading of
   an imported unit's source. *)
val parser_log_fuel : int
val load_path : string -> string list -> string option
(* The same under each of several search roots in turn. *)
val load_path_in : string list -> string list -> string option
val read_unit : string -> McttExtracted.Syntax.Cst.prog option
