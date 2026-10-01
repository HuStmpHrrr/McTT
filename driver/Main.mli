(* [search_root] is where an imported unit [X::Y] is looked up, as
   [search_root/X/Y.mctt]; it defaults to the current directory. *)
val main_of_filename : ?search_root:string -> string -> int
val main_of_program_string : ?search_root:string -> string -> int
