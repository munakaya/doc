# 29 "lib/deriving_json/deriving_Json_lexer.mll"
 
module Lexing =
    (*
      We override Lexing.engine in order to avoid creating a new position
      record each time a rule is matched.
      This reduces total parsing time by about 31%.
    *)
struct
  include Lexing

  external c_engine : lex_tables -> int -> lexbuf -> int = "caml_lex_engine"

  let engine tbl state buf =
    let result = c_engine tbl state buf in
      (*
      if result >= 0 then begin
  buf.lex_start_p <- buf.lex_curr_p;
  buf.lex_curr_p <- {buf.lex_curr_p
         with pos_cnum = buf.lex_abs_pos + buf.lex_curr_pos};
      end;
      *)
    result
end

open Printf
open Lexing

type lexbuf = {
  buf : Buffer.t;
  (* Buffer used to accumulate substrings *)

  mutable lnum : int;
  (* Current line number (starting from 1) *)

  mutable bol : int;
  (* Absolute position of the first character of the current line
     (starting from 0) *)

  lexbuf : Lexing.lexbuf;

}

let dec c =
  Char.code c - 48

let hex c =
  match c with
    '0'..'9' -> int_of_char c - int_of_char '0'
  | 'a'..'f' -> int_of_char c - int_of_char 'a' + 10
  | 'A'..'F' -> int_of_char c - int_of_char 'A' + 10
  | _ -> assert false

let json_error msg = failwith ("Deriving.Json: " ^ msg)

let custom_error descr v lexbuf =
  let offs = lexbuf.lex_abs_pos in
  let bol = v.bol in
  let pos1 = offs + lexbuf.lex_start_pos - bol in
  let pos2 = max pos1 (offs + lexbuf.lex_curr_pos - bol - 1) in
  let bytes =
    if pos1 = pos2 then
      sprintf "byte %i" (pos1+1)
    else
      sprintf "bytes %i-%i" (pos1+1) (pos2+1)
  in
  let msg = sprintf "Line %i, %s:\n%s" v.lnum bytes descr in
  json_error msg

let eof_error v lexbuf = custom_error "Unexpected end of input" v lexbuf
let byte_error v lexbuf = custom_error "Unexpected byte in string" v lexbuf
let tag_error ~typename v =
  custom_error
    (Printf.sprintf "Unexpected constructor %s for Json_%s" (Lexing.lexeme v.lexbuf) typename)
    v v.lexbuf

let lexer_error descr v lexbuf =
  custom_error
    (sprintf "%s '%s'" descr (Lexing.lexeme lexbuf))
    v lexbuf

let min10 = min_int / 10 - (if min_int mod 10 = 0 then 0 else 1)
let max10 = max_int / 10 + (if max_int mod 10 = 0 then 0 else 1)

exception Int_overflow

let extract_positive_int lexbuf =
  let start = lexbuf.lex_start_pos in
  let stop = lexbuf.lex_curr_pos in
  let s = lexbuf.lex_buffer in
  let n = ref 0 in
  for i = start to stop - 1 do
    if !n >= max10 then
      raise Int_overflow
    else
      n := 10 * !n + dec (Bytes.get s i)
  done;
  if !n < 0 then
    raise Int_overflow
  else
    !n

let extract_negative_int lexbuf =
  let start = lexbuf.lex_start_pos + 1 in
  let stop = lexbuf.lex_curr_pos in
  let s = lexbuf.lex_buffer in
  let n = ref 0 in
  for i = start to stop - 1 do
    if !n <= min10 then
      raise Int_overflow
    else
      n := 10 * !n - dec (Bytes.get s i)
  done;
  if !n > 0 then
    raise Int_overflow
  else
    !n

let newline v lexbuf =
  v.lnum <- v.lnum + 1;
  v.bol <- lexbuf.lex_abs_pos + lexbuf.lex_curr_pos


# 125 "lib/deriving_json/deriving_Json_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\252\255\253\255\254\255\255\255\001\000\254\255\255\255\
    \002\000\247\255\248\255\008\000\250\255\251\255\252\255\253\255\
    \254\255\255\255\072\000\095\000\133\000\249\255\003\000\253\255\
    \254\255\255\255\004\000\252\255\253\255\254\255\255\255\008\000\
    \252\255\253\255\254\255\004\000\255\255\006\000\000\000\253\255\
    \024\000\254\255\007\000\255\255\034\000\252\255\253\255\156\000\
    \255\255\166\000\254\255\188\000\198\000\253\255\254\255\255\255\
    \217\000\230\000\253\255\254\255\255\255\243\000\253\000\010\001\
    \253\255\254\255\255\255\020\001\030\001\043\001\250\255\251\255\
    \000\000\055\001\077\001\001\000\001\000\002\000\255\255\000\000\
    \008\000\004\000\010\000\001\000\009\000\254\255\021\000\001\000\
    \027\000\023\000\029\000\019\000\015\000\253\255\092\001\109\001\
    \119\001\151\001\129\001\161\001\183\001\193\001\005\000\253\255\
    \254\255\255\255\089\000\253\255\254\255\255\255\006\000\253\255\
    \254\255\255\255\203\001\252\255\253\255\254\255\255\255\219\001\
    \232\001\251\255\252\255\253\255\252\001\255\255\006\002\254\255\
    \020\002";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\007\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\003\000\255\255\004\000\003\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\002\000\
    \255\255\000\000\255\255\001\000\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\000\000\001\000\255\255\
    \255\255\255\255\255\255\000\000\001\000\255\255\255\255\255\255\
    \003\000\003\000\004\000\004\000\004\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \003\000\255\255\003\000\255\255\003\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\000\000\
    \255\255\255\255\255\255\255\255\003\000\255\255\000\000\255\255\
    \001\000";
  Lexing.lex_default =
   "\002\000\000\000\000\000\000\000\000\000\007\000\000\000\000\000\
    \010\000\000\000\000\000\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\255\255\255\255\255\255\000\000\024\000\000\000\
    \000\000\000\000\028\000\000\000\000\000\000\000\000\000\032\000\
    \000\000\000\000\000\000\255\255\000\000\255\255\255\255\000\000\
    \255\255\000\000\042\000\000\000\046\000\000\000\000\000\255\255\
    \000\000\255\255\000\000\255\255\054\000\000\000\000\000\000\000\
    \255\255\059\000\000\000\000\000\000\000\255\255\255\255\065\000\
    \000\000\000\000\000\000\255\255\255\255\071\000\000\000\000\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\000\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\104\000\000\000\
    \000\000\000\000\108\000\000\000\000\000\000\000\112\000\000\000\
    \000\000\000\000\116\000\000\000\000\000\000\000\000\000\255\255\
    \122\000\000\000\000\000\000\000\255\255\000\000\255\255\000\000\
    \255\255";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\038\000\000\000\000\000\000\000\038\000\000\000\038\000\
    \039\000\043\000\033\000\038\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \038\000\000\000\004\000\000\000\017\000\000\000\038\000\105\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\095\000\025\000\
    \030\000\017\000\035\000\036\000\000\000\040\000\000\000\000\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\041\000\000\000\000\000\094\000\000\000\042\000\
    \000\000\018\000\018\000\018\000\018\000\018\000\018\000\047\000\
    \078\000\000\000\048\000\049\000\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\003\000\000\000\017\000\000\000\
    \000\000\029\000\077\000\113\000\016\000\094\000\080\000\088\000\
    \015\000\018\000\018\000\018\000\018\000\018\000\018\000\079\000\
    \014\000\081\000\082\000\083\000\013\000\084\000\012\000\011\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\085\000\087\000\089\000\090\000\091\000\092\000\
    \093\000\019\000\019\000\019\000\019\000\019\000\019\000\020\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\000\000\000\000\
    \000\000\019\000\019\000\019\000\019\000\019\000\019\000\000\000\
    \000\000\000\000\000\000\000\000\109\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\000\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\050\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\055\000\056\000\
    \056\000\056\000\056\000\056\000\056\000\056\000\056\000\056\000\
    \001\000\006\000\009\000\023\000\027\000\103\000\111\000\043\000\
    \034\000\056\000\056\000\056\000\056\000\056\000\056\000\056\000\
    \056\000\056\000\056\000\062\000\000\000\000\000\060\000\061\000\
    \061\000\061\000\061\000\061\000\061\000\061\000\061\000\061\000\
    \000\000\000\000\045\000\061\000\061\000\061\000\061\000\061\000\
    \061\000\061\000\061\000\061\000\061\000\060\000\061\000\061\000\
    \061\000\061\000\061\000\061\000\061\000\061\000\061\000\068\000\
    \000\000\000\000\066\000\067\000\067\000\067\000\067\000\067\000\
    \067\000\067\000\067\000\067\000\067\000\067\000\067\000\067\000\
    \067\000\067\000\067\000\067\000\067\000\067\000\066\000\067\000\
    \067\000\067\000\067\000\067\000\067\000\067\000\067\000\067\000\
    \074\000\107\000\000\000\072\000\073\000\073\000\073\000\073\000\
    \073\000\073\000\073\000\073\000\073\000\095\000\000\000\073\000\
    \073\000\073\000\073\000\073\000\073\000\073\000\073\000\073\000\
    \073\000\000\000\000\000\000\000\075\000\000\000\000\000\000\000\
    \000\000\076\000\000\000\000\000\094\000\072\000\073\000\073\000\
    \073\000\073\000\073\000\073\000\073\000\073\000\073\000\101\000\
    \000\000\101\000\000\000\000\000\100\000\100\000\100\000\100\000\
    \100\000\100\000\100\000\100\000\100\000\100\000\086\000\000\000\
    \000\000\000\000\000\000\000\000\094\000\096\000\096\000\096\000\
    \096\000\096\000\096\000\096\000\096\000\096\000\096\000\096\000\
    \096\000\096\000\096\000\096\000\096\000\096\000\096\000\096\000\
    \096\000\098\000\098\000\098\000\098\000\098\000\098\000\098\000\
    \098\000\098\000\098\000\000\000\097\000\000\000\000\000\000\000\
    \000\000\000\000\099\000\000\000\099\000\000\000\053\000\098\000\
    \098\000\098\000\098\000\098\000\098\000\098\000\098\000\098\000\
    \098\000\098\000\098\000\098\000\098\000\098\000\098\000\098\000\
    \098\000\098\000\098\000\000\000\097\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\058\000\100\000\
    \100\000\100\000\100\000\100\000\100\000\100\000\100\000\100\000\
    \100\000\100\000\100\000\100\000\100\000\100\000\100\000\100\000\
    \100\000\100\000\100\000\118\000\119\000\119\000\119\000\119\000\
    \119\000\119\000\119\000\119\000\119\000\000\000\000\000\000\000\
    \000\000\000\000\064\000\119\000\119\000\119\000\119\000\119\000\
    \119\000\119\000\119\000\119\000\119\000\124\000\000\000\000\000\
    \125\000\126\000\126\000\126\000\126\000\126\000\126\000\126\000\
    \126\000\126\000\000\000\000\000\000\000\000\000\117\000\000\000\
    \000\000\000\000\000\000\070\000\127\000\128\000\128\000\128\000\
    \128\000\128\000\128\000\128\000\128\000\128\000\126\000\126\000\
    \126\000\126\000\126\000\126\000\126\000\126\000\126\000\126\000\
    \000\000\000\000\000\000\123\000\128\000\128\000\128\000\128\000\
    \128\000\128\000\128\000\128\000\128\000\128\000\000\000\000\000\
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
    \000\000\000\000\000\000\115\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \121\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\038\000\255\255\255\255\255\255\038\000\255\255\037\000\
    \037\000\042\000\031\000\037\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \038\000\255\255\000\000\255\255\008\000\255\255\037\000\102\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\072\000\022\000\
    \026\000\008\000\031\000\035\000\255\255\037\000\255\255\255\255\
    \011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
    \011\000\011\000\040\000\255\255\255\255\072\000\255\255\040\000\
    \255\255\011\000\011\000\011\000\011\000\011\000\011\000\044\000\
    \077\000\255\255\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\000\000\255\255\008\000\255\255\
    \255\255\026\000\076\000\110\000\008\000\072\000\079\000\087\000\
    \008\000\011\000\011\000\011\000\011\000\011\000\011\000\075\000\
    \008\000\080\000\081\000\082\000\008\000\083\000\008\000\008\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\084\000\086\000\088\000\089\000\090\000\091\000\
    \092\000\018\000\018\000\018\000\018\000\018\000\018\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \019\000\019\000\019\000\019\000\019\000\019\000\255\255\255\255\
    \255\255\018\000\018\000\018\000\018\000\018\000\018\000\255\255\
    \255\255\255\255\255\255\255\255\106\000\020\000\020\000\020\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\255\255\
    \019\000\019\000\019\000\019\000\019\000\019\000\020\000\020\000\
    \020\000\020\000\020\000\020\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\020\000\020\000\
    \020\000\020\000\020\000\020\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\052\000\052\000\
    \052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\
    \000\000\005\000\008\000\022\000\026\000\102\000\110\000\042\000\
    \031\000\056\000\056\000\056\000\056\000\056\000\056\000\056\000\
    \056\000\056\000\056\000\057\000\255\255\255\255\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \255\255\255\255\044\000\061\000\061\000\061\000\061\000\061\000\
    \061\000\061\000\061\000\061\000\061\000\062\000\062\000\062\000\
    \062\000\062\000\062\000\062\000\062\000\062\000\062\000\063\000\
    \255\255\255\255\063\000\063\000\063\000\063\000\063\000\063\000\
    \063\000\063\000\063\000\063\000\067\000\067\000\067\000\067\000\
    \067\000\067\000\067\000\067\000\067\000\067\000\068\000\068\000\
    \068\000\068\000\068\000\068\000\068\000\068\000\068\000\068\000\
    \069\000\106\000\255\255\069\000\069\000\069\000\069\000\069\000\
    \069\000\069\000\069\000\069\000\069\000\073\000\255\255\073\000\
    \073\000\073\000\073\000\073\000\073\000\073\000\073\000\073\000\
    \073\000\255\255\255\255\255\255\069\000\255\255\255\255\255\255\
    \255\255\069\000\255\255\255\255\073\000\074\000\074\000\074\000\
    \074\000\074\000\074\000\074\000\074\000\074\000\074\000\094\000\
    \255\255\094\000\255\255\255\255\094\000\094\000\094\000\094\000\
    \094\000\094\000\094\000\094\000\094\000\094\000\074\000\255\255\
    \255\255\255\255\255\255\255\255\073\000\095\000\095\000\095\000\
    \095\000\095\000\095\000\095\000\095\000\095\000\095\000\096\000\
    \096\000\096\000\096\000\096\000\096\000\096\000\096\000\096\000\
    \096\000\098\000\098\000\098\000\098\000\098\000\098\000\098\000\
    \098\000\098\000\098\000\255\255\096\000\255\255\255\255\255\255\
    \255\255\255\255\097\000\255\255\097\000\255\255\052\000\097\000\
    \097\000\097\000\097\000\097\000\097\000\097\000\097\000\097\000\
    \097\000\099\000\099\000\099\000\099\000\099\000\099\000\099\000\
    \099\000\099\000\099\000\255\255\096\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\057\000\100\000\
    \100\000\100\000\100\000\100\000\100\000\100\000\100\000\100\000\
    \100\000\101\000\101\000\101\000\101\000\101\000\101\000\101\000\
    \101\000\101\000\101\000\114\000\114\000\114\000\114\000\114\000\
    \114\000\114\000\114\000\114\000\114\000\255\255\255\255\255\255\
    \255\255\255\255\063\000\119\000\119\000\119\000\119\000\119\000\
    \119\000\119\000\119\000\119\000\119\000\120\000\255\255\255\255\
    \120\000\120\000\120\000\120\000\120\000\120\000\120\000\120\000\
    \120\000\120\000\255\255\255\255\255\255\255\255\114\000\255\255\
    \255\255\255\255\255\255\069\000\124\000\124\000\124\000\124\000\
    \124\000\124\000\124\000\124\000\124\000\124\000\126\000\126\000\
    \126\000\126\000\126\000\126\000\126\000\126\000\126\000\126\000\
    \255\255\255\255\255\255\120\000\128\000\128\000\128\000\128\000\
    \128\000\128\000\128\000\128\000\128\000\128\000\255\255\255\255\
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
    \255\255\255\255\255\255\114\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \120\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255";
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

let rec finish_string v lexbuf =
   __ocaml_lex_finish_string_rec v lexbuf 0
and __ocaml_lex_finish_string_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 170 "lib/deriving_json/deriving_Json_lexer.mll"
           ( Buffer.contents v.buf )
# 402 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 171 "lib/deriving_json/deriving_Json_lexer.mll"
           ( finish_escaped_char v lexbuf;
       finish_string v lexbuf )
# 408 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
let
# 173 "lib/deriving_json/deriving_Json_lexer.mll"
         c
# 414 "lib/deriving_json/deriving_Json_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 173 "lib/deriving_json/deriving_Json_lexer.mll"
           ( if c < '\x80' then
               Buffer.add_char v.buf c
             else
               finish_utf8_encoded_byte v c lexbuf;
             finish_string v lexbuf )
# 422 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 178 "lib/deriving_json/deriving_Json_lexer.mll"
           ( eof_error v lexbuf )
# 427 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_finish_string_rec v lexbuf __ocaml_lex_state

and finish_utf8_encoded_byte v c1 lexbuf =
   __ocaml_lex_finish_utf8_encoded_byte_rec v c1 lexbuf 5
and __ocaml_lex_finish_utf8_encoded_byte_rec v c1 lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 181 "lib/deriving_json/deriving_Json_lexer.mll"
         c2
# 440 "lib/deriving_json/deriving_Json_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 181 "lib/deriving_json/deriving_Json_lexer.mll"
            ( (* Even if encoded in UTF-8, a byte could not be greater than 255 ! *)
              if '\xC2' <= c1 && c1 < '\xC4' && '\x80' <= c2 && c2 < '\xC0' then
                let c = ((Char.code c1 lsl 6) lor Char.code c2) land 0xFF in
                Buffer.add_char v.buf (Char.chr c)
              else
                byte_error v lexbuf )
# 449 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 187 "lib/deriving_json/deriving_Json_lexer.mll"
            ( eof_error v lexbuf )
# 454 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_finish_utf8_encoded_byte_rec v c1 lexbuf __ocaml_lex_state

and finish_escaped_char v lexbuf =
   __ocaml_lex_finish_escaped_char_rec v lexbuf 8
and __ocaml_lex_finish_escaped_char_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 192 "lib/deriving_json/deriving_Json_lexer.mll"
           c
# 467 "lib/deriving_json/deriving_Json_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 192 "lib/deriving_json/deriving_Json_lexer.mll"
             ( Buffer.add_char v.buf c )
# 471 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 193 "lib/deriving_json/deriving_Json_lexer.mll"
         ( Buffer.add_char v.buf '\b' )
# 476 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 194 "lib/deriving_json/deriving_Json_lexer.mll"
         ( Buffer.add_char v.buf '\012' )
# 481 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 195 "lib/deriving_json/deriving_Json_lexer.mll"
         ( Buffer.add_char v.buf '\n' )
# 486 "lib/deriving_json/deriving_Json_lexer.ml"

  | 4 ->
# 196 "lib/deriving_json/deriving_Json_lexer.mll"
         ( Buffer.add_char v.buf '\r' )
# 491 "lib/deriving_json/deriving_Json_lexer.ml"

  | 5 ->
# 197 "lib/deriving_json/deriving_Json_lexer.mll"
         ( Buffer.add_char v.buf '\t' )
# 496 "lib/deriving_json/deriving_Json_lexer.ml"

  | 6 ->
let
# 198 "lib/deriving_json/deriving_Json_lexer.mll"
                a
# 502 "lib/deriving_json/deriving_Json_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 1)
and
# 198 "lib/deriving_json/deriving_Json_lexer.mll"
                           b
# 507 "lib/deriving_json/deriving_Json_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 2)
and
# 198 "lib/deriving_json/deriving_Json_lexer.mll"
                                      c
# 512 "lib/deriving_json/deriving_Json_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 3)
and
# 198 "lib/deriving_json/deriving_Json_lexer.mll"
                                                 d
# 517 "lib/deriving_json/deriving_Json_lexer.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 4) in
# 199 "lib/deriving_json/deriving_Json_lexer.mll"
         ( (* Even if encoded in UTF-8, a byte could not be greater than 255 ! *)
            if hex a = 0 && hex b = 0 then
       let c = (hex c lsl 4) lor hex d in
             Buffer.add_char v.buf (Char.chr c)
           else
       byte_error v lexbuf
   )
# 527 "lib/deriving_json/deriving_Json_lexer.ml"

  | 7 ->
# 206 "lib/deriving_json/deriving_Json_lexer.mll"
         ( lexer_error "Invalid escape sequence" v lexbuf )
# 532 "lib/deriving_json/deriving_Json_lexer.ml"

  | 8 ->
# 207 "lib/deriving_json/deriving_Json_lexer.mll"
         ( eof_error v lexbuf )
# 537 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_finish_escaped_char_rec v lexbuf __ocaml_lex_state

and read_comma v lexbuf =
   __ocaml_lex_read_comma_rec v lexbuf 22
and __ocaml_lex_read_comma_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 210 "lib/deriving_json/deriving_Json_lexer.mll"
          ( () )
# 549 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 211 "lib/deriving_json/deriving_Json_lexer.mll"
          ( lexer_error "Expected ',' but found" v lexbuf )
# 554 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 212 "lib/deriving_json/deriving_Json_lexer.mll"
          ( eof_error v lexbuf )
# 559 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_comma_rec v lexbuf __ocaml_lex_state

and read_comma_or_rbracket v lexbuf =
   __ocaml_lex_read_comma_or_rbracket_rec v lexbuf 26
and __ocaml_lex_read_comma_or_rbracket_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 215 "lib/deriving_json/deriving_Json_lexer.mll"
          ( `Comma )
# 571 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 216 "lib/deriving_json/deriving_Json_lexer.mll"
          ( `RBracket )
# 576 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 217 "lib/deriving_json/deriving_Json_lexer.mll"
          ( lexer_error "Expected ',' or ']' but found" v lexbuf )
# 581 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 218 "lib/deriving_json/deriving_Json_lexer.mll"
          ( eof_error v lexbuf )
# 586 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_comma_or_rbracket_rec v lexbuf __ocaml_lex_state

and finish_comment v lexbuf =
   __ocaml_lex_finish_comment_rec v lexbuf 31
and __ocaml_lex_finish_comment_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 221 "lib/deriving_json/deriving_Json_lexer.mll"
         ( () )
# 598 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 222 "lib/deriving_json/deriving_Json_lexer.mll"
         ( lexer_error "Unterminated comment" v lexbuf )
# 603 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 223 "lib/deriving_json/deriving_Json_lexer.mll"
         ( newline v lexbuf; finish_comment v lexbuf )
# 608 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 224 "lib/deriving_json/deriving_Json_lexer.mll"
         ( finish_comment v lexbuf )
# 613 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_finish_comment_rec v lexbuf __ocaml_lex_state

and read_space v lexbuf =
   __ocaml_lex_read_space_rec v lexbuf 37
and __ocaml_lex_read_space_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 229 "lib/deriving_json/deriving_Json_lexer.mll"
                             ( newline v lexbuf; read_space v lexbuf )
# 625 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 230 "lib/deriving_json/deriving_Json_lexer.mll"
                             ( finish_comment v lexbuf; read_space v lexbuf )
# 630 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 231 "lib/deriving_json/deriving_Json_lexer.mll"
                             ( newline v lexbuf; read_space v lexbuf )
# 635 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 232 "lib/deriving_json/deriving_Json_lexer.mll"
                             ( read_space v lexbuf )
# 640 "lib/deriving_json/deriving_Json_lexer.ml"

  | 4 ->
# 233 "lib/deriving_json/deriving_Json_lexer.mll"
                             ( () )
# 645 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_space_rec v lexbuf __ocaml_lex_state

and read_int v lexbuf =
   __ocaml_lex_read_int_rec v lexbuf 44
and __ocaml_lex_read_int_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 236 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( try extract_positive_int lexbuf
         with Int_overflow ->
           lexer_error "Int overflow" v lexbuf )
# 659 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 239 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( try extract_negative_int lexbuf
         with Int_overflow ->
           lexer_error "Int overflow" v lexbuf )
# 666 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 242 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( lexer_error "Expected integer but found" v lexbuf )
# 671 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 243 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( eof_error v lexbuf )
# 676 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_int_rec v lexbuf __ocaml_lex_state

and read_positive_int v lexbuf =
   __ocaml_lex_read_positive_int_rec v lexbuf 52
and __ocaml_lex_read_positive_int_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 246 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( try extract_positive_int lexbuf
         with Int_overflow ->
           lexer_error "Int overflow" v lexbuf )
# 690 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 249 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( lexer_error "Expected integer but found" v lexbuf )
# 695 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 250 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( eof_error v lexbuf )
# 700 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_positive_int_rec v lexbuf __ocaml_lex_state

and read_int32 v lexbuf =
   __ocaml_lex_read_int32_rec v lexbuf 57
and __ocaml_lex_read_int32_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 253 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( try Int32.of_string (Lexing.lexeme lexbuf)
         with _ ->
           lexer_error "Int32 overflow" v lexbuf )
# 714 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 256 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( lexer_error "Expected int32 but found" v lexbuf )
# 719 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 257 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( eof_error v lexbuf )
# 724 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_int32_rec v lexbuf __ocaml_lex_state

and read_int64 v lexbuf =
   __ocaml_lex_read_int64_rec v lexbuf 63
and __ocaml_lex_read_int64_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 260 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( try Int64.of_string (Lexing.lexeme lexbuf)
         with _ ->
           lexer_error "Int32 overflow" v lexbuf )
# 738 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 263 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( lexer_error "Expected int64 but found" v lexbuf )
# 743 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 264 "lib/deriving_json/deriving_Json_lexer.mll"
                         ( eof_error v lexbuf )
# 748 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_int64_rec v lexbuf __ocaml_lex_state

and read_number v lexbuf =
   __ocaml_lex_read_number_rec v lexbuf 69
and __ocaml_lex_read_number_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 267 "lib/deriving_json/deriving_Json_lexer.mll"
                ( nan )
# 760 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 268 "lib/deriving_json/deriving_Json_lexer.mll"
                ( infinity )
# 765 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 269 "lib/deriving_json/deriving_Json_lexer.mll"
                ( neg_infinity )
# 770 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 270 "lib/deriving_json/deriving_Json_lexer.mll"
                ( float_of_string (lexeme lexbuf) )
# 775 "lib/deriving_json/deriving_Json_lexer.ml"

  | 4 ->
# 271 "lib/deriving_json/deriving_Json_lexer.mll"
                ( lexer_error "Expected number but found" v lexbuf )
# 780 "lib/deriving_json/deriving_Json_lexer.ml"

  | 5 ->
# 272 "lib/deriving_json/deriving_Json_lexer.mll"
                ( eof_error v lexbuf )
# 785 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_number_rec v lexbuf __ocaml_lex_state

and read_string v lexbuf =
   __ocaml_lex_read_string_rec v lexbuf 102
and __ocaml_lex_read_string_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 275 "lib/deriving_json/deriving_Json_lexer.mll"
             ( Buffer.clear v.buf;
         finish_string v lexbuf )
# 798 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 277 "lib/deriving_json/deriving_Json_lexer.mll"
             ( lexer_error "Expected '\"' but found" v lexbuf )
# 803 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 278 "lib/deriving_json/deriving_Json_lexer.mll"
             ( eof_error v lexbuf )
# 808 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_string_rec v lexbuf __ocaml_lex_state

and read_lbracket v lexbuf =
   __ocaml_lex_read_lbracket_rec v lexbuf 106
and __ocaml_lex_read_lbracket_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 281 "lib/deriving_json/deriving_Json_lexer.mll"
             ( () )
# 820 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 282 "lib/deriving_json/deriving_Json_lexer.mll"
             ( lexer_error "Expected '[' but found" v lexbuf )
# 825 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 283 "lib/deriving_json/deriving_Json_lexer.mll"
             ( eof_error v lexbuf )
# 830 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_lbracket_rec v lexbuf __ocaml_lex_state

and read_rbracket v lexbuf =
   __ocaml_lex_read_rbracket_rec v lexbuf 110
and __ocaml_lex_read_rbracket_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 286 "lib/deriving_json/deriving_Json_lexer.mll"
             ( () )
# 842 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 287 "lib/deriving_json/deriving_Json_lexer.mll"
             ( lexer_error "Expected ']' but found" v lexbuf )
# 847 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 288 "lib/deriving_json/deriving_Json_lexer.mll"
             ( eof_error v lexbuf )
# 852 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_rbracket_rec v lexbuf __ocaml_lex_state

and read_case v lexbuf =
   __ocaml_lex_read_case_rec v lexbuf 114
and __ocaml_lex_read_case_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 291 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( try `Cst (extract_positive_int lexbuf)
                       with Int_overflow -> lexer_error "Int overflow" v lexbuf )
# 865 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 293 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( read_space v lexbuf;
       `NCst (read_positive_int v lexbuf) )
# 871 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 295 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( lexer_error "Expected positive integer or '[' but found" v lexbuf )
# 876 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 296 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( eof_error v lexbuf )
# 881 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_case_rec v lexbuf __ocaml_lex_state

and read_vcase v lexbuf =
   __ocaml_lex_read_vcase_rec v lexbuf 120
and __ocaml_lex_read_vcase_rec v lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 299 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( try `Cst (extract_positive_int lexbuf)
                       with Int_overflow -> lexer_error "Int overflow" v lexbuf )
# 894 "lib/deriving_json/deriving_Json_lexer.ml"

  | 1 ->
# 301 "lib/deriving_json/deriving_Json_lexer.mll"
                      ( try `Cst (extract_negative_int lexbuf)
                       with Int_overflow -> lexer_error "Int overflow" v lexbuf )
# 900 "lib/deriving_json/deriving_Json_lexer.ml"

  | 2 ->
# 303 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( read_space v lexbuf;
       let zero = read_positive_int v lexbuf in
       if (zero <> 0) then
         lexer_error
           (Printf.sprintf "Expected 0 but found %d" zero) v lexbuf;
       read_space v lexbuf;
       read_comma v lexbuf;
       read_space v lexbuf;
       `NCst (read_int v lexbuf) )
# 913 "lib/deriving_json/deriving_Json_lexer.ml"

  | 3 ->
# 312 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( lexer_error "Expected positive integer or '[' but found" v lexbuf )
# 918 "lib/deriving_json/deriving_Json_lexer.ml"

  | 4 ->
# 313 "lib/deriving_json/deriving_Json_lexer.mll"
                 ( eof_error v lexbuf )
# 923 "lib/deriving_json/deriving_Json_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_vcase_rec v lexbuf __ocaml_lex_state

;;

# 315 "lib/deriving_json/deriving_Json_lexer.mll"
 

let init_lexer ?buf lexbuf =
  let buf =
    match buf with
      None -> Buffer.create 256
    | Some buf -> buf
  in
  {
    buf = buf;
    lnum = 1;
    bol = 0;
    lexbuf = lexbuf;
  }

let read_bounded_int min max v lexbuf =
  let n = read_int v lexbuf in
  if n < min || n > max then
    lexer_error (Printf.sprintf "Int outside of bounds [%d - %d]" min max) v lexbuf
  else
    n

let read_tag_1 n v lexbuf =
  if n = read_int v lexbuf
  then n
  else lexer_error (Printf.sprintf "Int expected to be %d" n) v lexbuf

let read_tag_2 n1 n2 v lexbuf =
  let n = read_int v lexbuf in
  if n = n1 || n = n2
  then n
  else lexer_error (Printf.sprintf "Int expected to be either %d or %d" n1 n2) v lexbuf

let read_int v = read_space v v.lexbuf; read_int v v.lexbuf
let read_bounded_int ?(min = 0) ~max v =
  read_space v v.lexbuf; read_bounded_int min max v v.lexbuf
let read_tag_1 n v =
  read_space v v.lexbuf; read_tag_1 n v v.lexbuf
let read_tag_2 n1 n2 v =
  read_space v v.lexbuf; read_tag_2 n1 n2 v v.lexbuf
let read_int32 v = read_space v v.lexbuf; read_int32 v v.lexbuf
let read_int64 v = read_space v v.lexbuf; read_int64 v v.lexbuf
let read_number v = read_space v v.lexbuf; read_number v v.lexbuf
let read_string v = read_space v v.lexbuf; read_string v v.lexbuf

let read_case v = read_space v v.lexbuf; read_case v v.lexbuf
let read_vcase v = read_space v v.lexbuf; read_vcase v v.lexbuf

let read_lbracket v = read_space v v.lexbuf; read_lbracket v v.lexbuf
let read_rbracket v = read_space v v.lexbuf; read_rbracket v v.lexbuf
let read_comma v = read_space v v.lexbuf; read_comma v v.lexbuf
let read_comma_or_rbracket v =
  read_space v v.lexbuf; read_comma_or_rbracket v v.lexbuf


# 986 "lib/deriving_json/deriving_Json_lexer.ml"
