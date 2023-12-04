(*
 * lSIA: Language for implementing Semantical Interface Automata
 * 
 * by Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX
 * 
 * vincent-hugot.com
 * vincent.hugot@gmail.com
 * 
 * Copyright 2010 Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX
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
 
open Toolkit;;
open Common;;
  
  
(** Build the parse tree from a source file *)
let parse_sia path =
  let lexbuf = Lexing.from_channel (open_in path) in
  lexbuf.Lexing.lex_curr_p <- 
    {lexbuf.Lexing.lex_curr_p with
    Lexing.pos_fname = path};
  the_lexbuf := Some lexbuf;
  let r = Lsiapar.sias Lsialex.token lexbuf in
  Parsing.clear_parser(); r
  
  
(** Show welcome message *)
let welcome() = pf "
** lSIA - Language for describing Semantical Interface Automata 
**  by Sebti MOUELHI
** ------------------------ 
** Ocaml version: %s    
** System: %s
** ------------------------ 

" Sys.ocaml_version Sys.os_type 


let testing l =
  let t = Global.empty "Checking Parse Tree" in
  let automata = ref [] in
	let shared = Hashtbl.create 10  in
	let components = Hashtbl.create 10  in
  let rec sub l = flush stdoutc; flush stderrc; match l with
    | "parse" :: path :: l -> Global.set t @@ parse_sia path; sub l
    | "print" :: prefix :: l -> Parse_tree.print (Global.get t) ~prefix:prefix; sub l
    | "msg" :: i :: msg :: l -> 
      let sep = repeat_pattern "****" 7 in
      let msg = spf "\n\n%s\n******** %s ********\n%s\n\n" sep msg sep in 
	    (if i = "e" then pe else pl) msg; sub l 
    | "mdepend" :: l -> Parse_tree.macro_depend (Global.get t); sub l
    | "mexpand" :: l -> Parse_tree.expand_everything (Global.get t); sub l
    | "type" :: l -> Parse_tree.typecheck_lvl0 (Global.get t); sub l
    | "sanitise" :: l -> Global.set t @@ Parse_tree.transform_expressions Parse_tree.sanitise_logic (Global.get t); sub l
    | "shared_vars" :: l -> Parse_tree.shared_variables (Global.get t) shared; sub l
		| "list_components" :: l -> Parse_tree.component_set (Global.get t) components; sub l 
		| "siautomaton" :: i ::l ->
      push (Ptree_to_sia.sia_from_ptree (Parse_tree.extract_interface i (Global.get t)) (Parse_tree.extract_shared (Global.get t)))
         automata;  sub l
		| "setreachability" :: l ->
				Ptree_to_sia.set_reachability (peek automata) ; sub l
		| "arecomposable_product" :: l ->
      let a1 = pop automata in
      String_print_ds.print_are_composable a1 (peek automata);
      pl @@ (String_print_ds.print_shared_actions a1 (peek automata)) ;
			pl @@ "(* ------------ *)" ;
			String_print_ds.print_shared_variables shared ;
			pl @@ "(* ------------ *)" ;
			String_print_ds.print_components components ;
			let prod = Ptree_to_sia.synchronize a1 (peek automata) shared components (Global.get t) in
      Ptree_to_sia.establish_semantics_of_product a1 (peek automata) prod ;
			pl @@ String_print_ds.sia_to_string @@ prod ;
			pl @@ "(* ------------ *)" ;
			let comp = Ptree_to_sia.composition prod in
			pl @@ String_print_ds.sia_to_string @@ comp ;
			pl @@ "(* ------------ *)" ;
			String_print_ds.print_shared_variables shared ;
			pl @@ "(* ------------ *)" ;
			String_print_ds.print_components components ;
			begin if comp.Datastructs.empty = false then
				pop_2 automata ; push comp automata
			end ;
 			sub l
		| "siatotext" :: l ->
      pl @@ String_print_ds.sia_to_string @@ peek automata;
      pl @@ String_print_ds.print_output_actions @@ peek automata;
      pl @@ String_print_ds.print_input_actions @@ peek automata;
      pl @@ String_print_ds.print_hidden_actions @@ peek automata;
      pl @@ String_print_ds.print_all_actions @@ peek automata ;
      sub l
		| [] -> ()
    | _ -> failwith "testing: invalid command line" 
  in sub l
  




(** Parse the command line *)
let parse_command_line cmd_list = 
  let rec sub = function
  | [] -> welcome() 
  | ("test"|"t") :: l -> welcome() ; testing l 
  | _ -> failwith "parse_command_line: invalid command line"
  in sub cmd_list


(** Entry point *)
let main = 
parse_command_line @@ tl al