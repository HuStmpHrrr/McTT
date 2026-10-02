module Parser = McttExtracted.Parser
module Entrypoint = McttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let get_exit_code result : int =
  match result with
  | AllGood _ -> 0
  (* 1 and 2 have special meanings in Bash-like shells *)
  | RunFailure _ -> 3
  | ElaborationFailure _ -> 4
  | ParserFailure _ -> 5
  | ParserTimeout _ -> 6

(* A file that cannot be read, and a lexing error. *)
let unreadable_file_code = 8
let lexing_error_code = 5

(* The integer argument of the parser is a *log* version of fuel: 500 means
   2^500. *)
let parser_log_fuel = 500

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* The unit [X::Y] is the file [X/Y.mctt] under the search root. *)
let unit_file search_root fp =
  Filename.concat search_root (String.concat Filename.dir_sep fp ^ ".mctt")

let load_path search_root fp =
  let file = unit_file search_root fp in
  if Sys.file_exists file && not (Sys.is_directory file) then
    (try Some (read_file file) with Sys_error _ -> None)
  else None

(* What an imported unit's file contains, parsed; a lexing or parsing error
   makes it unreadable, which the interpreter reports against the unit. *)
let read_unit src =
  try
    match
      Parser.prog parser_log_fuel
        (Lexer.lexbuf_to_token_buffer (Lexing.from_string src))
    with
    | Parsed_pr (cst, _) -> Some cst
    | _ -> None
  with Lexer.Error _ -> None

let main_of_lexbuf ?(search_root = ".") lexbuf =
  match
    Lexer.lexbuf_to_token_buffer lexbuf
    |> Entrypoint.main (load_path search_root) read_unit parser_log_fuel
  with
  | r -> Format.printf "%a@." PrettyPrinter.format_main_result r; get_exit_code r
  | exception Lexer.Error msg -> Format.printf "Error: %s@." msg; lexing_error_code

let main_of_filename ?search_root filename =
  if Sys.file_exists filename && Sys.is_directory filename then begin
    Format.printf "Error: %s is a directory@." filename; unreadable_file_code
  end else
    match read_file filename with
    | src -> Lexing.from_string src |> main_of_lexbuf ?search_root
    | exception Sys_error msg -> Format.printf "Error: %s@." msg; unreadable_file_code

let main_of_program_string ?search_root program =
  Lexing.from_string program |> main_of_lexbuf ?search_root
