{
  open Lexing
  open McttExtracted.Parser

  let get_range lexbuf = (lexbuf.lex_start_p, lexbuf.lex_curr_p)

  let format_position (f: Format.formatter) (p: position): unit =
    Format.fprintf
      f
      "line %d, column %d"
      p.pos_lnum
      (p.pos_cnum - p.pos_bol + 1)

  let format_range (f: Format.formatter) (p: position * position): unit =
    Format.fprintf
      f
      "@[<h>%a - %a@]"
      format_position (fst p)
      format_position (snd p)

  let token_to_string : token -> string =
    function
    | ARROW _ -> "->"
    | AT _ -> "@"
    | BAR _ -> "|"
    | COLON _ -> ":"
    | COLONCOLON _ -> "::"
    | COMMA _ -> ","
    | DARROW _ -> "=>"
    | LPAREN _ -> "("
    | RPAREN _ -> ")"
    | ZERO _ -> "zero"
    | SUCC _ -> "succ"
    | REC _ -> "rec"
    | RETURN _ -> "return"
    | END _ -> "end"
    | LAMBDA _ -> "fun"
    | PI _ -> "forall"
    | NAT _ -> "Nat"
    | TRUE_TY _ -> "True"
    | TRUE _ -> "true"
    | FALSE_TY _ -> "False"
    | EXFALSO _ -> "exfalso"
    | INT (_, i) -> string_of_int i
    | TYPE _ -> "Type"
    | VAR (_, s) -> s
    | EOF _ -> "<EOF>"
    | DOT _ -> "."
    | LET _ -> "let"
    | IN _ -> "in"
    | EQ _ -> ":="
    | MODULE _ -> "module"
    | WHERE _ -> "where"
    | DEF _ -> "def"
    | IMPORT _ -> "import"
    | AS _ -> "as"
    | USE _ -> "use"
    | PRIVATE _ -> "private"
    | ABSTRACT _ -> "abstract"
    | EVAL _ -> "eval"
    | SEMI _ -> ";"

  let get_range_of_token : token -> (position * position) =
    function
    | ARROW r
    | AT r
    | BAR r
    | COLON r
    | COLONCOLON r
    | COMMA r
    | DARROW r
    | LPAREN r
    | RPAREN r
    | ZERO r
    | SUCC r
    | REC r
    | RETURN r
    | END r
    | LAMBDA r
    | PI r
    | NAT r
    | TRUE_TY r
    | TRUE r
    | FALSE_TY r
    | EXFALSO r
    | TYPE r
    | EOF r
    | INT (r, _)
    | DOT r
    | LET r
    | IN r
    | EQ r
    | MODULE r
    | WHERE r
    | DEF r
    | IMPORT r
    | AS r
    | USE r
    | PRIVATE r
    | ABSTRACT r
    | EVAL r
    | SEMI r
    | VAR (r, _) -> r

  let format_token (f: Format.formatter) (t: token): unit =
    Format.fprintf
      f
      "@[<h>\"%s\" (at %a)@]"
      (token_to_string t)
      format_range (get_range_of_token t)
}

let string = ['a'-'z''A'-'Z']+

rule read =
  parse
  | "->" { ARROW (get_range lexbuf) }
  | '@' { AT (get_range lexbuf) }
  | '|' { BAR (get_range lexbuf) }
  | "::" { COLONCOLON (get_range lexbuf) }
  | ':' { COLON (get_range lexbuf) }
  | ',' { COMMA (get_range lexbuf) }
  | "=>" { DARROW (get_range lexbuf) }
  | "(*" { comment lexbuf }
  | '(' { LPAREN (get_range lexbuf) }
  | ')' { RPAREN (get_range lexbuf) }
  | "zero" { ZERO (get_range lexbuf) }
  | "succ" { SUCC (get_range lexbuf) }
  | "rec" { REC (get_range lexbuf) }
  | "return" { RETURN (get_range lexbuf) }
  | "end" { END (get_range lexbuf) }
  | "fun" { LAMBDA (get_range lexbuf) }
  | "forall" { PI (get_range lexbuf) }
  | [' ' '\t'] { read lexbuf }
  | ['\n'] { new_line lexbuf; read lexbuf }
  | "Nat" { NAT (get_range lexbuf) }
  | "True" { TRUE_TY (get_range lexbuf) }
  | "true" { TRUE (get_range lexbuf) }
  | "False" { FALSE_TY (get_range lexbuf) }
  | "exfalso" { EXFALSO (get_range lexbuf) }
  | ['0'-'9']+ as lxm { INT (get_range lexbuf, int_of_string lxm) }
  | "Type" { TYPE (get_range lexbuf) }
  | eof { EOF (get_range lexbuf) }
  | "." { DOT (get_range lexbuf) }
  | "let" {LET (get_range lexbuf) }
  | "in" {IN (get_range lexbuf) }
  | ":=" {EQ (get_range lexbuf) }
  | ';' { SEMI (get_range lexbuf) }
  | "module" { MODULE (get_range lexbuf) }
  | "where" { WHERE (get_range lexbuf) }
  | "def" { DEF (get_range lexbuf) }
  | "import" { IMPORT (get_range lexbuf) }
  | "as" { AS (get_range lexbuf) }
  | "use" { USE (get_range lexbuf) }
  | "private" { PRIVATE (get_range lexbuf) }
  | "abstract" { ABSTRACT (get_range lexbuf) }
  | "eval" { EVAL (get_range lexbuf) }
  | string { VAR (get_range lexbuf, Lexing.lexeme lexbuf) }
  | _ as c { failwith (Format.asprintf "@[<v 2>Lexer error:@ @[<v 2>Unexpected character %C@ at %a@]@]@." c format_position lexbuf.lex_start_p) }
and comment =
  parse
  | "*)" { read lexbuf }
  | _ { comment lexbuf }

{
  let rec lexbuf_to_token_buffer lexbuf =
    lazy
      begin
        try
          MenhirLibParser.Inter.Buf_cons (read lexbuf, lexbuf_to_token_buffer lexbuf)
        with
        | Failure s -> prerr_string s; raise Exit
      end
}
