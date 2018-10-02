# 1 "src/usexp/jbuild_lexer.mll"
 
  open Lexer_shared

(* The difference between the old and new syntax is that the old
   syntax allows backslash following by any characters other than 'n',
   'x', ... and interpret it as it. The new syntax is stricter in
   order to allow introducing new escape sequence in the future if
   needed. *)
type escape_mode =
  | In_block_comment (* Inside #|...|# comments (old syntax) *)
  | In_quoted_string

# 15 "src/usexp/jbuild_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\248\255\001\000\251\255\252\255\253\255\001\000\006\000\
    \255\255\006\000\249\255\250\255\010\000\253\255\002\000\004\000\
    \255\255\254\255\014\000\251\255\252\255\253\255\007\000\254\255\
    \255\255\017\000\009\000\252\255\253\255\001\000\255\255\254\255\
    \043\000\248\255\249\255\116\000\059\000\254\255\255\255\011\000\
    \094\000\139\000\149\000\174\000\235\000\002\001";
  Lexing.lex_backtrk =
   "\008\000\255\255\255\255\255\255\255\255\255\255\001\000\001\000\
    \255\255\255\255\255\255\255\255\003\000\255\255\002\000\002\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\003\000\255\255\
    \255\255\000\000\255\255\255\255\255\255\003\000\255\255\255\255\
    \003\000\255\255\255\255\005\000\003\000\255\255\255\255\006\000\
    \003\000\002\000\003\000\005\000\004\000\005\000";
  Lexing.lex_default =
   "\255\255\000\000\255\255\000\000\000\000\000\000\006\000\255\255\
    \000\000\255\255\000\000\000\000\013\000\000\000\255\255\255\255\
    \000\000\000\000\020\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\255\255\027\000\000\000\000\000\255\255\000\000\000\000\
    \034\000\000\000\000\000\255\255\255\255\000\000\000\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\007\000\008\000\255\255\007\000\009\000\255\255\007\000\
    \008\000\021\000\007\000\255\255\255\255\038\000\255\255\255\255\
    \021\000\000\000\025\000\022\000\000\000\000\000\000\000\000\000\
    \007\000\000\000\003\000\002\000\031\000\017\000\007\000\015\000\
    \005\000\004\000\255\255\030\000\255\255\015\000\000\000\000\000\
    \024\000\025\000\255\255\255\255\000\000\038\000\000\000\000\000\
    \039\000\000\000\000\000\006\000\010\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\037\000\000\000\000\000\
    \000\000\000\000\037\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\036\000\036\000\036\000\036\000\036\000\
    \036\000\036\000\036\000\036\000\036\000\000\000\000\000\000\000\
    \000\000\000\000\023\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\011\000\014\000\000\000\
    \016\000\000\000\000\000\000\000\000\000\029\000\014\000\037\000\
    \000\000\000\000\000\000\000\000\000\000\037\000\041\000\041\000\
    \041\000\041\000\041\000\041\000\041\000\041\000\041\000\041\000\
    \000\000\037\000\000\000\000\000\000\000\037\000\000\000\037\000\
    \000\000\000\000\000\000\035\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\000\000\000\000\000\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\028\000\255\255\000\000\000\000\000\000\019\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\033\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\000\000\000\000\000\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\006\000\000\000\000\000\006\000\007\000\
    \009\000\022\000\007\000\012\000\012\000\039\000\012\000\012\000\
    \018\000\255\255\025\000\018\000\255\255\255\255\255\255\255\255\
    \000\000\255\255\000\000\000\000\029\000\014\000\007\000\015\000\
    \000\000\000\000\012\000\026\000\012\000\012\000\255\255\255\255\
    \018\000\025\000\012\000\012\000\255\255\032\000\255\255\255\255\
    \032\000\255\255\255\255\000\000\002\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\012\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\032\000\255\255\255\255\
    \255\255\255\255\032\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\255\255\255\255\255\255\
    \255\255\255\255\018\000\036\000\036\000\036\000\036\000\036\000\
    \036\000\036\000\036\000\036\000\036\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\002\000\014\000\255\255\
    \015\000\255\255\255\255\255\255\255\255\026\000\012\000\032\000\
    \255\255\255\255\255\255\255\255\255\255\032\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \255\255\032\000\255\255\255\255\255\255\032\000\255\255\032\000\
    \255\255\255\255\255\255\032\000\035\000\035\000\035\000\035\000\
    \035\000\035\000\035\000\035\000\035\000\035\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\035\000\035\000\035\000\
    \035\000\035\000\035\000\041\000\041\000\041\000\041\000\041\000\
    \041\000\041\000\041\000\041\000\041\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\035\000\035\000\035\000\
    \035\000\035\000\035\000\255\255\255\255\255\255\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\043\000\
    \043\000\043\000\043\000\043\000\043\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\006\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\026\000\012\000\255\255\255\255\255\255\018\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\032\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\045\000\045\000\045\000\045\000\045\000\
    \045\000\255\255\255\255\255\255\044\000\044\000\044\000\044\000\
    \044\000\044\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\045\000\045\000\045\000\045\000\045\000\
    \045\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec token lexbuf =
   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 26 "src/usexp/jbuild_lexer.mll"
    ( Lexing.new_line lexbuf; token lexbuf )
# 191 "src/usexp/jbuild_lexer.ml"

  | 1 ->
# 28 "src/usexp/jbuild_lexer.mll"
    ( token lexbuf )
# 196 "src/usexp/jbuild_lexer.ml"

  | 2 ->
# 30 "src/usexp/jbuild_lexer.mll"
    ( Token.Lparen )
# 201 "src/usexp/jbuild_lexer.ml"

  | 3 ->
# 32 "src/usexp/jbuild_lexer.mll"
    ( Rparen )
# 206 "src/usexp/jbuild_lexer.ml"

  | 4 ->
# 34 "src/usexp/jbuild_lexer.mll"
    ( Buffer.clear escaped_buf;
      let start = Lexing.lexeme_start_p lexbuf in
      let s = quoted_string In_quoted_string lexbuf in
      lexbuf.lex_start_p <- start;
      Quoted_string s
    )
# 216 "src/usexp/jbuild_lexer.ml"

  | 5 ->
# 41 "src/usexp/jbuild_lexer.mll"
    ( block_comment lexbuf;
      token lexbuf
    )
# 223 "src/usexp/jbuild_lexer.ml"

  | 6 ->
# 45 "src/usexp/jbuild_lexer.mll"
    ( Sexp_comment )
# 228 "src/usexp/jbuild_lexer.ml"

  | 7 ->
# 47 "src/usexp/jbuild_lexer.mll"
    ( Eof )
# 233 "src/usexp/jbuild_lexer.ml"

  | 8 ->
# 49 "src/usexp/jbuild_lexer.mll"
    ( atom "" (Lexing.lexeme_start_p lexbuf) lexbuf )
# 238 "src/usexp/jbuild_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and atom acc start lexbuf =
   __ocaml_lex_atom_rec acc start lexbuf 12
and __ocaml_lex_atom_rec acc start lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 53 "src/usexp/jbuild_lexer.mll"
    ( lexbuf.lex_start_p <- start;
      error lexbuf "jbuild atoms cannot contain #|"
    )
# 252 "src/usexp/jbuild_lexer.ml"

  | 1 ->
# 57 "src/usexp/jbuild_lexer.mll"
    ( lexbuf.lex_start_p <- start;
      error lexbuf "jbuild atoms cannot contain |#"
    )
# 259 "src/usexp/jbuild_lexer.ml"

  | 2 ->
let
# 60 "src/usexp/jbuild_lexer.mll"
                                               s
# 265 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 61 "src/usexp/jbuild_lexer.mll"
    ( atom (if acc = "" then s else acc ^ s) start lexbuf
    )
# 270 "src/usexp/jbuild_lexer.ml"

  | 3 ->
# 64 "src/usexp/jbuild_lexer.mll"
    ( if acc = "" then
        error lexbuf "Internal error in the S-expression parser, \
                      please report upstream.";
      lexbuf.lex_start_p <- start;
      Token.Atom (Atom.of_string acc)
    )
# 280 "src/usexp/jbuild_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_atom_rec acc start lexbuf __ocaml_lex_state

and quoted_string mode lexbuf =
   __ocaml_lex_quoted_string_rec mode lexbuf 18
and __ocaml_lex_quoted_string_rec mode lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 73 "src/usexp/jbuild_lexer.mll"
    ( Buffer.contents escaped_buf )
# 292 "src/usexp/jbuild_lexer.ml"

  | 1 ->
# 75 "src/usexp/jbuild_lexer.mll"
    ( match escape_sequence mode lexbuf with
      | Newline -> quoted_string_after_escaped_newline mode lexbuf
      | Other   -> quoted_string                       mode lexbuf
    )
# 300 "src/usexp/jbuild_lexer.ml"

  | 2 ->
let
# 79 "src/usexp/jbuild_lexer.mll"
               s
# 306 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 80 "src/usexp/jbuild_lexer.mll"
    ( Lexing.new_line lexbuf;
      Buffer.add_string escaped_buf s;
      quoted_string mode lexbuf
    )
# 313 "src/usexp/jbuild_lexer.ml"

  | 3 ->
let
# 84 "src/usexp/jbuild_lexer.mll"
         c
# 319 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 85 "src/usexp/jbuild_lexer.mll"
    ( Buffer.add_char escaped_buf c;
      quoted_string mode lexbuf
    )
# 325 "src/usexp/jbuild_lexer.ml"

  | 4 ->
# 89 "src/usexp/jbuild_lexer.mll"
    ( if mode = In_block_comment then
        error lexbuf "unterminated quoted string";
      Buffer.contents escaped_buf
    )
# 333 "src/usexp/jbuild_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_quoted_string_rec mode lexbuf __ocaml_lex_state

and quoted_string_after_escaped_newline mode lexbuf =
   __ocaml_lex_quoted_string_after_escaped_newline_rec mode lexbuf 25
and __ocaml_lex_quoted_string_after_escaped_newline_rec mode lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 96 "src/usexp/jbuild_lexer.mll"
    ( quoted_string mode lexbuf )
# 345 "src/usexp/jbuild_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_quoted_string_after_escaped_newline_rec mode lexbuf __ocaml_lex_state

and block_comment lexbuf =
   __ocaml_lex_block_comment_rec lexbuf 26
and __ocaml_lex_block_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 100 "src/usexp/jbuild_lexer.mll"
    ( Buffer.clear escaped_buf;
      ignore (quoted_string In_block_comment lexbuf : string);
      block_comment lexbuf
    )
# 360 "src/usexp/jbuild_lexer.ml"

  | 1 ->
# 105 "src/usexp/jbuild_lexer.mll"
    ( ()
    )
# 366 "src/usexp/jbuild_lexer.ml"

  | 2 ->
# 108 "src/usexp/jbuild_lexer.mll"
    ( error lexbuf "unterminated block comment"
    )
# 372 "src/usexp/jbuild_lexer.ml"

  | 3 ->
# 111 "src/usexp/jbuild_lexer.mll"
    ( block_comment lexbuf
    )
# 378 "src/usexp/jbuild_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_block_comment_rec lexbuf __ocaml_lex_state

and escape_sequence mode lexbuf =
   __ocaml_lex_escape_sequence_rec mode lexbuf 32
and __ocaml_lex_escape_sequence_rec mode lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 116 "src/usexp/jbuild_lexer.mll"
    ( Lexing.new_line lexbuf;
      Newline )
# 391 "src/usexp/jbuild_lexer.ml"

  | 1 ->
let
# 118 "src/usexp/jbuild_lexer.mll"
                                       c
# 397 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 119 "src/usexp/jbuild_lexer.mll"
    ( let c =
        match c with
        | 'n' -> '\n'
        | 'r' -> '\r'
        | 'b' -> '\b'
        | 't' -> '\t'
        | _   -> c
      in
      Buffer.add_char escaped_buf c;
      Other
    )
# 411 "src/usexp/jbuild_lexer.ml"

  | 2 ->
let
# 130 "src/usexp/jbuild_lexer.mll"
              c1
# 417 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos
and
# 130 "src/usexp/jbuild_lexer.mll"
                            c2
# 422 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 1)
and
# 130 "src/usexp/jbuild_lexer.mll"
                                          c3
# 427 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 2) in
# 131 "src/usexp/jbuild_lexer.mll"
    ( let v = eval_decimal_escape c1 c2 c3 in
      if mode = In_quoted_string && v > 255 then
        error lexbuf "escape sequence in quoted string out of range"
          ~delta:(-1);
      Buffer.add_char escaped_buf (Char.chr v);
      Other
    )
# 437 "src/usexp/jbuild_lexer.ml"

  | 3 ->
let
# 138 "src/usexp/jbuild_lexer.mll"
              s
# 443 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 139 "src/usexp/jbuild_lexer.mll"
    ( if mode = In_quoted_string then
        error lexbuf "unterminated decimal escape sequence" ~delta:(-1);
      Buffer.add_char escaped_buf '\\';
      Buffer.add_string escaped_buf s;
      Other
    )
# 452 "src/usexp/jbuild_lexer.ml"

  | 4 ->
let
# 145 "src/usexp/jbuild_lexer.mll"
                     c1
# 458 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 1)
and
# 145 "src/usexp/jbuild_lexer.mll"
                                      c2
# 463 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 2) in
# 146 "src/usexp/jbuild_lexer.mll"
    ( let v = eval_hex_escape c1 c2 in
      Buffer.add_char escaped_buf (Char.chr v);
      Other
    )
# 470 "src/usexp/jbuild_lexer.ml"

  | 5 ->
let
# 150 "src/usexp/jbuild_lexer.mll"
                     s
# 476 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 151 "src/usexp/jbuild_lexer.mll"
    ( if mode = In_quoted_string then
        error lexbuf "unterminated hexadecimal escape sequence" ~delta:(-1);
      Buffer.add_char escaped_buf '\\';
      Buffer.add_string escaped_buf s;
      Other
    )
# 485 "src/usexp/jbuild_lexer.ml"

  | 6 ->
let
# 157 "src/usexp/jbuild_lexer.mll"
         c
# 491 "src/usexp/jbuild_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 158 "src/usexp/jbuild_lexer.mll"
    ( Buffer.add_char escaped_buf '\\';
      Buffer.add_char escaped_buf c;
      Other
    )
# 498 "src/usexp/jbuild_lexer.ml"

  | 7 ->
# 163 "src/usexp/jbuild_lexer.mll"
    ( if mode = In_quoted_string then
        error lexbuf "unterminated escape sequence" ~delta:(-1);
      Other
    )
# 506 "src/usexp/jbuild_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_escape_sequence_rec mode lexbuf __ocaml_lex_state

;;

