# 1 "ide/protocol/xml_lexer.mll"
 (*
 * Xml Light, an small Xml parser/printer with DTD support.
 * Copyright (C) 2003 Nicolas Cannasse (ncannasse@motion-twin.com)
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

open Lexing

type error =
        | EUnterminatedComment
        | EUnterminatedString
        | EIdentExpected
        | ECloseExpected
        | ENodeExpected
        | EAttributeNameExpected
        | EAttributeValueExpected
        | EUnterminatedEntity

exception Error of error

type pos = int * int * int * int

type token =
        | Tag of string * (string * string) list * bool
        | PCData of string
        | Endtag of string
        | Eof

let last_pos = ref 0
and current_line = ref 0
and current_line_start = ref 0

let tmp = Buffer.create 200

let idents = Hashtbl.create 0

let _ = begin
        Hashtbl.add idents "nbsp;" " ";
        Hashtbl.add idents "gt;" ">";
        Hashtbl.add idents "lt;" "<";
        Hashtbl.add idents "amp;" "&";
        Hashtbl.add idents "apos;" "'";
        Hashtbl.add idents "quot;" "\"";
end

let init lexbuf =
        current_line := 1;
        current_line_start := lexeme_start lexbuf;
        last_pos := !current_line_start

let close lexbuf =
        Buffer.reset tmp

let pos lexbuf =
        !current_line , !current_line_start ,
        !last_pos ,
        lexeme_start lexbuf

let restore (cl,cls,lp,_) =
        current_line := cl;
        current_line_start := cls;
        last_pos := lp

let newline lexbuf =
        incr current_line;
        last_pos := lexeme_end lexbuf;
        current_line_start := !last_pos

let error lexbuf e =
        last_pos := lexeme_start lexbuf;
        raise (Error e)

[@@@ocaml.warning "-3"]       (* String.lowercase_ascii since 4.03.0 GPR#124 *)
let lowercase = String.lowercase
[@@@ocaml.warning "+3"]

# 92 "ide/protocol/xml_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\246\255\247\255\001\000\000\000\008\000\255\255\002\000\
    \000\000\010\000\253\255\000\000\001\000\254\255\250\255\011\000\
    \016\000\255\255\003\000\013\000\252\255\253\255\002\000\255\255\
    \005\000\002\000\254\255\017\000\252\255\253\255\003\000\255\255\
    \009\000\254\255\021\000\001\000\039\000\255\255\015\000\253\255\
    \037\000\254\255\101\000\255\255\231\000\040\001\254\255\118\001\
    \004\000\254\255\255\255\006\000\005\000\255\255\254\255\183\001\
    \254\255\005\002\024\000\253\255\061\000\215\000\216\000\217\000\
    \254\255\255\255\038\000\251\255\252\255\253\255\039\000\255\255\
    \254\255\036\000\251\255\252\255\253\255\005\000\255\255\254\255\
    ";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\007\000\006\000\004\000\255\255\000\000\
    \003\000\004\000\255\255\255\255\255\255\255\255\255\255\002\000\
    \001\000\255\255\000\000\255\255\255\255\255\255\003\000\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\003\000\255\255\
    \000\000\255\255\004\000\003\000\001\000\255\255\000\000\255\255\
    \255\255\255\255\001\000\255\255\255\255\255\255\255\255\000\000\
    \255\255\255\255\255\255\002\000\255\255\255\255\255\255\255\255\
    \255\255\000\000\255\255\255\255\002\000\002\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\004\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\004\000\255\255\255\255\
    ";
  Lexing.lex_default =
   "\003\000\000\000\000\000\003\000\255\255\255\255\000\000\255\255\
    \255\255\255\255\000\000\255\255\255\255\000\000\000\000\255\255\
    \255\255\000\000\255\255\020\000\000\000\000\000\255\255\000\000\
    \255\255\255\255\000\000\028\000\000\000\000\000\255\255\000\000\
    \255\255\000\000\036\000\255\255\036\000\000\000\255\255\000\000\
    \041\000\000\000\255\255\000\000\255\255\046\000\000\000\255\255\
    \049\000\000\000\000\000\255\255\255\255\000\000\000\000\056\000\
    \000\000\255\255\059\000\000\000\255\255\255\255\255\255\255\255\
    \000\000\000\000\067\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\074\000\000\000\000\000\000\000\255\255\000\000\000\000\
    ";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\008\000\007\000\255\255\000\000\006\000\255\255\006\000\
    \017\000\009\000\023\000\009\000\016\000\018\000\031\000\024\000\
    \017\000\016\000\023\000\032\000\037\000\000\000\031\000\038\000\
    \008\000\061\000\037\000\014\000\039\000\000\000\004\000\255\255\
    \009\000\011\000\009\000\016\000\079\000\012\000\013\000\025\000\
    \016\000\255\255\000\000\000\000\255\255\052\000\000\000\008\000\
    \061\000\008\000\022\000\035\000\005\000\255\255\001\000\255\255\
    \026\000\033\000\050\000\054\000\053\000\000\000\062\000\010\000\
    \071\000\072\000\076\000\078\000\069\000\255\255\000\000\000\000\
    \030\000\255\255\000\000\255\255\000\000\060\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\062\000\000\000\065\000\
    \000\000\079\000\000\000\255\255\064\000\255\255\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \077\000\000\000\070\000\072\000\000\000\000\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \043\000\000\000\000\000\000\000\000\000\000\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \063\000\062\000\063\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\063\000\
    \062\000\063\000\065\000\000\000\000\000\000\000\000\000\064\000\
    \002\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\021\000\000\000\000\000\
    \000\000\029\000\000\000\000\000\062\000\255\255\062\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\043\000\000\000\075\000\000\000\068\000\255\255\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\047\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\000\000\000\000\000\000\000\000\047\000\
    \000\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\000\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\000\000\000\000\000\000\000\000\000\000\000\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\000\000\000\000\000\000\000\000\047\000\000\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\057\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\000\000\000\000\000\000\000\000\057\000\000\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\000\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \000\000\000\000\000\000\000\000\057\000\000\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
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
    \000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\008\000\000\000\003\000\255\255\000\000\003\000\007\000\
    \018\000\005\000\024\000\009\000\015\000\015\000\032\000\019\000\
    \015\000\016\000\019\000\027\000\038\000\255\255\027\000\034\000\
    \008\000\058\000\034\000\004\000\035\000\255\255\000\000\003\000\
    \005\000\005\000\009\000\015\000\077\000\011\000\012\000\022\000\
    \016\000\036\000\255\255\255\255\036\000\051\000\255\255\005\000\
    \058\000\009\000\019\000\034\000\000\000\003\000\000\000\003\000\
    \025\000\030\000\048\000\052\000\051\000\255\255\060\000\005\000\
    \066\000\070\000\073\000\073\000\066\000\036\000\255\255\255\255\
    \027\000\034\000\255\255\034\000\255\255\058\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\060\000\255\255\060\000\
    \255\255\077\000\255\255\036\000\060\000\036\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \073\000\255\255\066\000\070\000\255\255\255\255\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \042\000\255\255\255\255\255\255\255\255\255\255\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \061\000\062\000\063\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\061\000\
    \062\000\063\000\062\000\255\255\255\255\255\255\255\255\062\000\
    \000\000\003\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\019\000\255\255\255\255\
    \255\255\027\000\255\255\255\255\061\000\034\000\063\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\044\000\255\255\073\000\255\255\066\000\036\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\045\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\255\255\255\255\255\255\255\255\045\000\
    \255\255\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\047\000\047\000\255\255\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\255\255\255\255\255\255\255\255\255\255\255\255\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\255\255\255\255\255\255\255\255\047\000\255\255\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\055\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\255\255\255\255\255\255\255\255\055\000\255\255\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\057\000\057\000\255\255\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \255\255\255\255\255\255\255\255\057\000\255\255\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
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
    \255\255\255\255\255\255\255\255\255\255\255\255";
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
# 101 "ide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        PCData "\n"
                )
# 350 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 106 "ide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        comment lexbuf;
                        token lexbuf
                )
# 359 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 112 "ide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        header lexbuf;
                        token lexbuf;
                )
# 368 "ide/protocol/xml_lexer.ml"

  | 3 ->
# 118 "ide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        let tag = ident_name lexbuf in
                        ignore_spaces lexbuf;
                        close_tag lexbuf;
                        Endtag tag
                )
# 379 "ide/protocol/xml_lexer.ml"

  | 4 ->
# 126 "ide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        let tag = ident_name lexbuf in
                        ignore_spaces lexbuf;
                        let attribs, closed = attributes lexbuf in
                        Tag(tag, attribs, closed)
                )
# 390 "ide/protocol/xml_lexer.ml"

  | 5 ->
# 134 "ide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (lexeme lexbuf);
                        PCData (pcdata lexbuf)
                )
# 400 "ide/protocol/xml_lexer.ml"

  | 6 ->
# 141 "ide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (entity lexbuf);
                        PCData (pcdata lexbuf)
                )
# 410 "ide/protocol/xml_lexer.ml"

  | 7 ->
# 148 "ide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (lexeme lexbuf);
                        PCData (pcdata lexbuf)
                )
# 420 "ide/protocol/xml_lexer.ml"

  | 8 ->
# 154 "ide/protocol/xml_lexer.mll"
              ( Eof )
# 425 "ide/protocol/xml_lexer.ml"

  | 9 ->
# 156 "ide/protocol/xml_lexer.mll"
                ( error lexbuf ENodeExpected )
# 430 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and ignore_spaces lexbuf =
   __ocaml_lex_ignore_spaces_rec lexbuf 15
and __ocaml_lex_ignore_spaces_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 160 "ide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        ignore_spaces lexbuf
                )
# 445 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 165 "ide/protocol/xml_lexer.mll"
                ( ignore_spaces lexbuf )
# 450 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 167 "ide/protocol/xml_lexer.mll"
                ( () )
# 455 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_ignore_spaces_rec lexbuf __ocaml_lex_state

and comment lexbuf =
   __ocaml_lex_comment_rec lexbuf 19
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 171 "ide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        comment lexbuf
                )
# 470 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 176 "ide/protocol/xml_lexer.mll"
                ( () )
# 475 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 178 "ide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedComment) )
# 480 "ide/protocol/xml_lexer.ml"

  | 3 ->
# 180 "ide/protocol/xml_lexer.mll"
                ( comment lexbuf )
# 485 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

and header lexbuf =
   __ocaml_lex_header_rec lexbuf 27
and __ocaml_lex_header_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 184 "ide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        header lexbuf
                )
# 500 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 189 "ide/protocol/xml_lexer.mll"
                ( () )
# 505 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 191 "ide/protocol/xml_lexer.mll"
                ( error lexbuf ECloseExpected )
# 510 "ide/protocol/xml_lexer.ml"

  | 3 ->
# 193 "ide/protocol/xml_lexer.mll"
                ( header lexbuf )
# 515 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_header_rec lexbuf __ocaml_lex_state

and pcdata lexbuf =
   __ocaml_lex_pcdata_rec lexbuf 34
and __ocaml_lex_pcdata_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 197 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp '\n';
                        newline lexbuf;
                        pcdata lexbuf
                )
# 531 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 203 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (lexeme lexbuf);
                        pcdata lexbuf
                )
# 539 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 208 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (lexeme lexbuf);
                        pcdata lexbuf;
                )
# 547 "ide/protocol/xml_lexer.ml"

  | 3 ->
# 213 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (entity lexbuf);
                        pcdata lexbuf
                )
# 555 "ide/protocol/xml_lexer.ml"

  | 4 ->
# 218 "ide/protocol/xml_lexer.mll"
                ( Buffer.contents tmp )
# 560 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_pcdata_rec lexbuf __ocaml_lex_state

and entity lexbuf =
   __ocaml_lex_entity_rec lexbuf 40
and __ocaml_lex_entity_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 222 "ide/protocol/xml_lexer.mll"
                (
                        let ident = lexeme lexbuf in
                        try
                                Hashtbl.find idents (lowercase ident)
                        with
                                Not_found -> "&" ^ ident
                )
# 578 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 230 "ide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedEntity) )
# 583 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_entity_rec lexbuf __ocaml_lex_state

and ident_name lexbuf =
   __ocaml_lex_ident_name_rec lexbuf 45
and __ocaml_lex_ident_name_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 234 "ide/protocol/xml_lexer.mll"
                ( lexeme lexbuf )
# 595 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 236 "ide/protocol/xml_lexer.mll"
                ( error lexbuf EIdentExpected )
# 600 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_ident_name_rec lexbuf __ocaml_lex_state

and close_tag lexbuf =
   __ocaml_lex_close_tag_rec lexbuf 48
and __ocaml_lex_close_tag_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 240 "ide/protocol/xml_lexer.mll"
                ( () )
# 612 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 242 "ide/protocol/xml_lexer.mll"
                ( error lexbuf ECloseExpected )
# 617 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_close_tag_rec lexbuf __ocaml_lex_state

and attributes lexbuf =
   __ocaml_lex_attributes_rec lexbuf 51
and __ocaml_lex_attributes_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 246 "ide/protocol/xml_lexer.mll"
                ( [], false )
# 629 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 248 "ide/protocol/xml_lexer.mll"
                ( [], true )
# 634 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 250 "ide/protocol/xml_lexer.mll"
                (
                        let key = attribute lexbuf in
                        let data = attribute_data lexbuf in
                        ignore_spaces lexbuf;
                        let others, closed = attributes lexbuf in
                        (key, data) :: others, closed
                )
# 645 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_attributes_rec lexbuf __ocaml_lex_state

and attribute lexbuf =
   __ocaml_lex_attribute_rec lexbuf 55
and __ocaml_lex_attribute_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 260 "ide/protocol/xml_lexer.mll"
                ( lexeme lexbuf )
# 657 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 262 "ide/protocol/xml_lexer.mll"
                ( error lexbuf EAttributeNameExpected )
# 662 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_attribute_rec lexbuf __ocaml_lex_state

and attribute_data lexbuf =
   __ocaml_lex_attribute_data_rec lexbuf 58
and __ocaml_lex_attribute_data_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 266 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.reset tmp;
                        last_pos := lexeme_end lexbuf;
                        dq_string lexbuf
                )
# 678 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 272 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.reset tmp;
                        last_pos := lexeme_end lexbuf;
                        q_string lexbuf
                )
# 687 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 278 "ide/protocol/xml_lexer.mll"
                ( error lexbuf EAttributeValueExpected )
# 692 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_attribute_data_rec lexbuf __ocaml_lex_state

and dq_string lexbuf =
   __ocaml_lex_dq_string_rec lexbuf 66
and __ocaml_lex_dq_string_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 282 "ide/protocol/xml_lexer.mll"
                ( Buffer.contents tmp )
# 704 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 284 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 1);
                        dq_string lexbuf
                )
# 712 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 289 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (entity lexbuf);
                        dq_string lexbuf
                )
# 720 "ide/protocol/xml_lexer.ml"

  | 3 ->
# 294 "ide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedString) )
# 725 "ide/protocol/xml_lexer.ml"

  | 4 ->
# 296 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 0);
                        dq_string lexbuf
                )
# 733 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_dq_string_rec lexbuf __ocaml_lex_state

and q_string lexbuf =
   __ocaml_lex_q_string_rec lexbuf 73
and __ocaml_lex_q_string_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 303 "ide/protocol/xml_lexer.mll"
                ( Buffer.contents tmp )
# 745 "ide/protocol/xml_lexer.ml"

  | 1 ->
# 305 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 1);
                        q_string lexbuf
                )
# 753 "ide/protocol/xml_lexer.ml"

  | 2 ->
# 310 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (entity lexbuf);
                        q_string lexbuf
                )
# 761 "ide/protocol/xml_lexer.ml"

  | 3 ->
# 315 "ide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedString) )
# 766 "ide/protocol/xml_lexer.ml"

  | 4 ->
# 317 "ide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 0);
                        q_string lexbuf
                )
# 774 "ide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_q_string_rec lexbuf __ocaml_lex_state

;;

