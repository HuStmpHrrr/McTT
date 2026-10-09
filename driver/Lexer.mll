{
  open Lexing
  open McttExtracted.Parser

  (* A lexing error, with its message. *)
  exception Error of string

  let get_range lexbuf = (lexbuf.lex_start_p, lexbuf.lex_curr_p)

  (* Columns count characters, not bytes: each UTF-8 continuation byte read
     moves the beginning of the line one byte to the right.  [pos_cnum] stays
     a byte offset. *)
  let skip_continuation lexbuf (n : int) =
    let p = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { p with pos_bol = p.pos_bol + n }

  (* A token of [n] bytes spelled as one character. *)
  let wide lexbuf (n : int) =
    skip_continuation lexbuf (n - 1);
    get_range lexbuf

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

  (* A token as the printer spells it: the Unicode form where there is one
     (see [read] for both spellings). *)
  let token_to_string : token -> string =
    function
    | ARROW _ -> "\xe2\x86\x92"
    | AT _ -> "@"
    | BAR _ -> "|"
    | COLON _ -> ":"
    | COLONCOLON _ -> "\xe2\x80\xba"
    | COMMA _ -> ","
    | DARROW _ -> "\xe2\x87\x92"
    | LPAREN _ -> "("
    | RPAREN _ -> ")"
    | LBRACE _ -> "{"
    | RBRACE _ -> "}"
    | PLUS _ -> "+"
    | STAR _ -> "\xc2\xb7"
    | ZERO _ -> "zero"
    | SUCC _ -> "succ"
    | REC _ -> "rec"
    | RETURN _ -> "return"
    | END _ -> "end"
    | LAMBDA _ -> "\xce\xbb"
    | PI _ -> "\xe2\x88\x80"
    | LEVEL _ -> "Level"
    | SUCCL _ -> "succl"
    | MAXL _ -> "maxl"
    | LLIT (_, n) -> string_of_int n ^ "l"
    | LLITL (_, n) -> string_of_int n ^ "L"
    | OMEGA _ -> "\xcf\x89"
    | OMEGA2 _ -> "\xcf\x89^2"
    | NAT _ -> "\xe2\x84\x95"
    | TRUE_TY _ -> "\xe2\x8a\xa4"
    | TRUE _ -> "\xe2\x8b\x86"
    | FALSE_TY _ -> "\xe2\x8a\xa5"
    | EXFALSO _ -> "exfalso"
    | INT (_, i) -> string_of_int i
    | TYPE _ -> "Type"
    | VAR (_, s) -> s
    | EOF _ -> "<EOF>"
    | DOT _ -> "."
    | LET _ -> "let"
    | IN _ -> "in"
    | EQ _ -> "\xe2\x89\x94"
    | MODULE _ -> "module"
    | WHERE _ -> "where"
    | DEF _ -> "def"
    | IMPORT _ -> "import"
    | OPEN _ -> "open"
    | THEOREM _ -> "theorem"
    | LEMMA _ -> "lemma"
    | FACT _ -> "fact"
    | REMARK _ -> "remark"
    | GIVEN _ -> "given"
    | AXIOM _ -> "axiom"
    | AS _ -> "as"
    | USE _ -> "use"
    | EXPORT _ -> "export"
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
    | LBRACE r
    | RBRACE r
    | PLUS r
    | STAR r
    | ZERO r
    | SUCC r
    | REC r
    | RETURN r
    | END r
    | LAMBDA r
    | PI r
    | NAT r
    | LEVEL r
    | SUCCL r
    | MAXL r
    | LLIT (r, _)
    | LLITL (r, _)
    | OMEGA r
    | OMEGA2 r
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
    | OPEN r
    | THEOREM r
    | LEMMA r
    | FACT r
    | REMARK r
    | GIVEN r
    | AXIOM r
    | AS r
    | USE r
    | EXPORT r
    | PRIVATE r
    | ABSTRACT r
    | EVAL r
    | SEMI r
    | VAR (r, _) -> r

  let format_token (f: Format.formatter) (t: token): unit =
    Format.fprintf
      f
      "@[<h>\"%a\" (at %a)@]"
      (fun f s ->
        (* its width in characters, for Format, which counts bytes *)
        let n = ref 0 in
        String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr n) s;
        Format.pp_print_as f !n s)
      (token_to_string t)
      format_range (get_range_of_token t)
}

let string = ['a'-'z''A'-'Z']+

(* A UTF-8 character outside ASCII: a lead byte and its continuation bytes,
   reported whole when it is not a token. *)
let utf8 = ['\xc0'-'\xf7'] ['\x80'-'\xbf']*

(* Each Unicode spelling below is an alternative to an ASCII one and lexes to
   the same token, as its UTF-8 bytes:
     →  ->      ⇒  =>      λ  fun     ∀ Π  forall   ≔  :=    ›  ::
     ℕ  Nat     ⊤  True    ⊥  False   ⋆  true       ω  omega
     ·  *       ω^2  omega^2
   Identifiers are ASCII letters only, so [λx] is [λ] then [x], and no
   symbol needs a space around it. *)

rule read =
  parse
  | "->" { ARROW (get_range lexbuf) }
  | "\xe2\x86\x92" { ARROW (wide lexbuf 3) }
  | '@' { AT (get_range lexbuf) }
  | '|' { BAR (get_range lexbuf) }
  | "::" { COLONCOLON (get_range lexbuf) }
  | "\xe2\x80\xba" { COLONCOLON (wide lexbuf 3) }
  | ':' { COLON (get_range lexbuf) }
  | ',' { COMMA (get_range lexbuf) }
  | "=>" { DARROW (get_range lexbuf) }
  | "\xe2\x87\x92" { DARROW (wide lexbuf 3) }
  | "(*" { comment lexbuf }
  | '(' { LPAREN (get_range lexbuf) }
  | ')' { RPAREN (get_range lexbuf) }
  | '{' { LBRACE (get_range lexbuf) }
  | '+' { PLUS (get_range lexbuf) }
  | '*' { STAR (get_range lexbuf) }
  | "\xc2\xb7" { STAR (wide lexbuf 2) }
  | '}' { RBRACE (get_range lexbuf) }
  | "zero" { ZERO (get_range lexbuf) }
  | "succ" { SUCC (get_range lexbuf) }
  | "rec" { REC (get_range lexbuf) }
  | "return" { RETURN (get_range lexbuf) }
  | "end" { END (get_range lexbuf) }
  | "fun" { LAMBDA (get_range lexbuf) }
  | "\xce\xbb" { LAMBDA (wide lexbuf 2) }
  | "forall" { PI (get_range lexbuf) }
  | "\xe2\x88\x80" { PI (wide lexbuf 3) }
  | "\xce\xa0" { PI (wide lexbuf 2) }
  | [' ' '\t'] { read lexbuf }
  | ['\n'] { new_line lexbuf; read lexbuf }
  | "Level" { LEVEL (get_range lexbuf) }
  | "succl" { SUCCL (get_range lexbuf) }
  | "maxl" { MAXL (get_range lexbuf) }
  | ['0'-'9']+ 'l' as lxm
    { LLIT (get_range lexbuf, int_of_string (String.sub lxm 0 (String.length lxm - 1))) }
  (* A level literal [<n>L], the ordinal ω+n: the same level as [ω + n]. *)
  | ['0'-'9']+ 'L' as lxm
    { LLITL (get_range lexbuf, int_of_string (String.sub lxm 0 (String.length lxm - 1))) }
  | "\xcf\x89" { OMEGA (wide lexbuf 2) }
  | "omega" { OMEGA (get_range lexbuf) }
  (* [ω^2], one token, written only in a large universe [Type@{ω^2+i}]: it
     is not a level. *)
  | "\xcf\x89^2" { skip_continuation lexbuf 1; OMEGA2 (get_range lexbuf) }
  | "omega^2" { OMEGA2 (get_range lexbuf) }
  | "Nat" { NAT (get_range lexbuf) }
  | "\xe2\x84\x95" { NAT (wide lexbuf 3) }
  | "True" { TRUE_TY (get_range lexbuf) }
  | "\xe2\x8a\xa4" { TRUE_TY (wide lexbuf 3) }
  | "true" { TRUE (get_range lexbuf) }
  | "\xe2\x8b\x86" { TRUE (wide lexbuf 3) }
  | "False" { FALSE_TY (get_range lexbuf) }
  | "\xe2\x8a\xa5" { FALSE_TY (wide lexbuf 3) }
  | "exfalso" { EXFALSO (get_range lexbuf) }
  | ['0'-'9']+ as lxm { INT (get_range lexbuf, int_of_string lxm) }
  | "Type" { TYPE (get_range lexbuf) }
  | eof { EOF (get_range lexbuf) }
  | "." { DOT (get_range lexbuf) }
  | "let" {LET (get_range lexbuf) }
  | "in" {IN (get_range lexbuf) }
  | ":=" {EQ (get_range lexbuf) }
  | "\xe2\x89\x94" { EQ (wide lexbuf 3) }
  | ';' { SEMI (get_range lexbuf) }
  | "module" { MODULE (get_range lexbuf) }
  | "where" { WHERE (get_range lexbuf) }
  | "def" { DEF (get_range lexbuf) }
  | "import" { IMPORT (get_range lexbuf) }
  | "open" { OPEN (get_range lexbuf) }
  | "theorem" { THEOREM (get_range lexbuf) }
  | "lemma" { LEMMA (get_range lexbuf) }
  | "fact" { FACT (get_range lexbuf) }
  | "remark" { REMARK (get_range lexbuf) }
  | "given" { GIVEN (get_range lexbuf) }
  | "axiom" { AXIOM (get_range lexbuf) }
  | "as" { AS (get_range lexbuf) }
  | "use" { USE (get_range lexbuf) }
  | "export" { EXPORT (get_range lexbuf) }
  | "private" { PRIVATE (get_range lexbuf) }
  | "abstract" { ABSTRACT (get_range lexbuf) }
  | "eval" { EVAL (get_range lexbuf) }
  | string { VAR (get_range lexbuf, Lexing.lexeme lexbuf) }
  | utf8 as s { raise (Error (Format.asprintf "unexpected character \"%s\" at %a" s format_position lexbuf.lex_start_p)) }
  | _ as c { raise (Error (Format.asprintf "unexpected character %C at %a" c format_position lexbuf.lex_start_p)) }
and comment =
  parse
  | "*)" { read lexbuf }
  | eof { raise (Error "unterminated comment") }
  | ['\n'] { new_line lexbuf; comment lexbuf }
  | ['\x80'-'\xbf'] { skip_continuation lexbuf 1; comment lexbuf }
  | _ { comment lexbuf }

{
  let rec lexbuf_to_token_buffer lexbuf =
    lazy
      begin
        MenhirLibParser.Inter.Buf_cons (read lexbuf, lexbuf_to_token_buffer lexbuf)
      end
}
