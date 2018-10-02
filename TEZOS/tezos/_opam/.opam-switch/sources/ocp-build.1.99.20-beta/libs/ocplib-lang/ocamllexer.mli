(**************************************************************************)
(*                                                                        *)
(*   Typerex Libraries                                                    *)
(*                                                                        *)
(*   Copyright 2011-2017 OCamlPro SAS                                     *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type token =
    Kwd of string
  | Ident of string
  | Int of int
  | Float of float
  | String of string
  | Char of char

type error =
  | Illegal_character of char
  | Unterminated_comment
  | Unterminated_string
  | Unterminated_string_in_comment
;;

exception Error of error * int * int

(** [make_lexer list_of_keywords] returns a lexer, i.e. a function, called
    on a [lexbuf] and returning a token, until EOF is reached. *)
val make_lexer : string list -> Lexing.lexbuf -> token option
val report_error : Format.formatter -> error -> unit
