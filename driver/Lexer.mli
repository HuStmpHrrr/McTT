(** A lexing error, with its message. *)
exception Error of string

val format_position : Format.formatter -> Lexing.position -> unit
val format_range : Format.formatter -> Lexing.position * Lexing.position -> unit
val format_token : Format.formatter -> McttExtracted.Parser.token -> unit
val read : Lexing.lexbuf -> McttExtracted.Parser.token

val lexbuf_to_token_buffer :
  Lexing.lexbuf -> McttExtracted.Parser.MenhirLibParser.Inter.buffer
val get_range_of_token : McttExtracted.Parser.token -> Lexing.position * Lexing.position
