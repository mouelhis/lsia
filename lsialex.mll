{

(** ********************************************************************* *)
(** lSIA: Language for implementing Semantical Interface Automata          *)
(**                                                                       *)
(** by Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX                       *)
(**                                                                       *)
(** file : lsialex.mll : the lexer                                         *)
(**                                                                       *)
(** Copyright 2011 Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX           *)
(**                                                                       *)
(**  This program is free software: you can redistribute it and/or modify *)
(**  it under the terms of the GNU General Public License as published by *)
(**  the Free Software Foundation, either version 3 of the License, or    *)
(**  (at your option) any later version.                                  *)
(**                                                                       *)
(**  This program is distributed in the hope that it will be useful,      *)
(**  but WITHOUT ANY WARRANTY; without even the implied warranty of       *)
(**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the        *)
(**  GNU General Public License for more details.                         *)
(**                                                                       *)
(**  You should have received a copy of the GNU General Public License    *)
(**  along with this program.  If not, see <http://www.gnu.org/licenses/>.*)
(** ********************************************************************* *)
 
open Toolkit;;
open Lsiapar;;



(** The string buffer. 
    Strings being read are stored in it, and then copied *)
let _string_buff = ref (String.create (1024*20))

(** Current index in the string buffer *)
let _si = ref 0 

(** Clear the buffer *)
let new_string() = _si := 0
  
(** Put a character in the buffer *)
let string_put c =
  String.set !_string_buff !_si c;
  incr _si
  
(** Get a copy of the stored string *)
let get_string() =
  String.sub !_string_buff 0 !_si

(** Increase the lines count *)
let incr_linenum lexbuf = 
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- {pos with
    Lexing.pos_lnum = succ pos.Lexing.pos_lnum;
    (*Lexing.pos_bol = pos.Lexing.pos_cnum*)
  }
} 


let id_pat  = ['A'-'Z' 'a'-'z' '_'] [ '_' '-' '\'' 'A'-'Z' 'a'-'z' '0'-'9'] *

let enuma_pat  = '`' (id_pat as x)

let digit = ['0'-'9']

let nat_p = digit+

let int_p = ['-']? nat_p

let interval = (int_p as lb) ".." (int_p as ub)

let real_pat = ['-']? digit+ '.' digit*


rule token = parse
  | [' ' '\t']          { token lexbuf }     (* skip blanks *)
  | '\n'                { incr_linenum lexbuf; token lexbuf }  
  | "/*"                { comment 0 lexbuf ; token lexbuf }
  | "//"                { line_comment lexbuf ; token lexbuf }
  | '"'                 { new_string(); astring lexbuf ; STRING (get_string()) }
  | ','                 { COMMA }
  | ';'                 { SEMICOLON }
  | '{'                 { OPEN }
  | '}'                 { CLOSE }
  | "/\\"|'&'           { AND }
  | "\\/"|'|'           { OR } 
  | "||"                { COMPOSITION_OP}
  | "<==>"              { EQUIVALENT }
  | "==>"               { IMPLIES }
  | "->"                { ARROW }
  | "<=="               { IMPLIES_CONV }
  | "if"                { IF }
  | "then"              { THEN }
  | "else"              { ELSE }
  | '~'|'!'             { NOT }
  | "<="                { LESS_EQ }
  | ">="                { GREATER_EQ }
  | "<"                 { LESS }
  | ">"                 { GREATER }
  | "="                 { EQUALS } 
  | "!="                { DIFFERS }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { TIMES }
  | '/'                 { DIVIDE }
  | "int"               { INTEGERS }
  | "real"              { REALS }    
  | "enum"              { ENUM } 
  | "macro"             { MACRO }
  | "closed"		        { CLOSED }
  | "true"              { TRUE }
  | "false"             { FALSE }
  | "bool"              { BOOLS }
  | "states"            { STATES }
  | ":"                 { IN }
  | "local"             { LOCAL }
  | "init"              { INIT }
	| "initial"           { INITIAL }
  | "hidden"            { HIDDEN }
  | "shared"            { SHARE }
  | "by"              	{ BY }
  | "primitive"         { PRIMITIVE }
  | "composite"         { COMPOSITE}
  | "input"             { INPUT }
  | "output"            { OUTPUT }
  | "transitions"       { TRANSITIONS }
	| "inv"               { INVARIANT }
  | "pre"               { PRE }
  | "post"              { POST }
  | "transpred"         { TRANSPRED }
	| "unchanged"         { UNCHANGED }
  | eof                 { EOF }
  | "in:"               { INPUT_PARAMS }
  | "out:"              { OUTPUT_PARAMS }
  | "("                 { OPEN_PAREN }
  | ")"                 { CLOSE_PAREN }
  | id_pat as x         { ID x }
  | enuma_pat           { SYMBOL x }
  | interval            { INTERVAL (ios lb, ios ub) } 
  | nat_p as x          { NATURAL (ios x) }
  | real_pat as x       { REAL (fos x) }
  | _ as c              { epf "LEXER FAILED ON '%c'\n" c ; EOF}
  
and comment n = parse
  | "/*"                { comment (succ n) lexbuf }
  | "\n"                { incr_linenum lexbuf; comment n lexbuf }
  | "*/"                { if n > 0 then comment (pred n) lexbuf }
  | _                   { comment n lexbuf }
  
and line_comment = parse
  | "\n"                { incr_linenum lexbuf }
  | _                   { line_comment lexbuf }
  
and astring = parse
  | '"'                 { () }
  | _ as c              { string_put c ; astring lexbuf }
