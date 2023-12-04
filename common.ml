(*
 * lSIA : Language for implementing Semantical Interface Automata
 * 
 * by Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX
 * 
 * vincent-hugot.com
 * vincent.hugot@gmail.com
 * 
 * Copyright 2011 Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX
 * 
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 * 
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 * 
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 *) 
 
(** Common definitions *)

open Toolkit;;
 
(** Reference to the current lexing buffer. Used by the parser for error tracking purposes *)
let the_lexbuf = ref (None : Lexing.lexbuf option)

(** Types available to variables of the language *)
type var_type = 
  | VT_real
  | VT_int
  | VT_bool
  | VT_interval of (int * int)
  | VT_enum of string
  
let is_enum_type = function VT_enum _ -> true | _-> false
  
(** Get the string representing [var_type] in clear text *)
let string_of_var_type = function
  | VT_real  -> "real"
  | VT_int  ->  "int"
  | VT_bool  -> "bool"
  | VT_interval (x,y) -> spf "%d..%d" x y
  | VT_enum s -> s
  
(** alias for [string_of_var_type] *)
let sovt = string_of_var_type
  
(** Print a [var_type] to [stdout] *)
let print_var_type t = 
  pl (string_of_var_type t)
  
(** Possible action styles *)
type action_style = 
  AS_input | AS_output | AS_hidden 
  
let string_of_action_style = function
  | AS_input -> "Input"
  | AS_output -> "Output"
  | AS_hidden -> "Hidden"

let symbol_of_action_style = function 
  | AS_input -> "?"
  | AS_output -> "!"
  | AS_hidden -> ";"
  
  
(** Simple representation of a list of strings (Ids) *)
let strof_id_list = pretty_print_list id ", " "[" "]"
 
