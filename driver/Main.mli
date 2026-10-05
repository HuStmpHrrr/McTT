(* [search_root] is where an imported unit [X::Y] is looked up, as
   [search_root/X/Y.mctt]; it defaults to the current directory. *)
val main_of_filename : ?search_root:string -> string -> int
val main_of_program_string : ?search_root:string -> string -> int

(* The pieces of [main_of_lexbuf] the documentation generator reuses: the
   parser's fuel, the file of a unit under a search root, and the reading of
   an imported unit's source. *)
val parser_log_fuel : int
val load_path : string -> string list -> string option
val read_unit : string -> McttExtracted.Syntax.Cst.prog option
