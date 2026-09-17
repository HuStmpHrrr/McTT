module Parser = McttExtracted.Parser
module Entrypoint = McttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let eval_failed : eval_result -> bool = function
  | EvalGood _ -> false
  | TypeCheckingFailure _ | TypeInferenceFailure _ -> true

let get_exit_code result : int =
  match result with
  (* A unit is only good if every one of its [eval]s is *)
  | AllGood (_, _, rs) -> if List.exists eval_failed rs then 3 else 0
  (* 1 and 2 have special meanings in Bash-like shells *)
  | ElaborationFailure _ -> 4
  | ParserFailure _ -> 5
  | ParserTimeout _ -> 6

let main_of_lexbuf lexbuf =
  Lexer.lexbuf_to_token_buffer lexbuf
  (* Here, the integer argument is a *log* version of fuel.
     Thus, 500 means 2^500. *)
  |> Entrypoint.main 500
  |> fun r -> Format.printf "%a@." PrettyPrinter.format_main_result r; get_exit_code r

let main_of_filename filename =
  Lexing.from_channel (open_in filename) |> main_of_lexbuf

let main_of_program_string program =
  Lexing.from_string program |> main_of_lexbuf
