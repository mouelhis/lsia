(** ***********************************************************************)
(** lSIA: Language for implementing Semantical Interface Automata         *)
(**                                                                       *)
(** by Sebti MOUELHI                                                      *)
(**                                                                       *)
(** file : string_print_ds.ml : prints data structures                    *)
(**                                                                       *)
(**  Copyright 2009-2010 Sebti MOUELHI                                    *)
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
(**                                                                       *)
(** ***********************************************************************) 

open Toolkit;;
open Common;;
open Automaton ;;
open Ptree_to_sia;;  
open Datastructs;;

(** Module Automaton.ml *)

(* Automaton.ml: a string representation of an automaton *)

let to_string a = 
  let buff = Buffer.create 100 in
  let add = Buffer.add_string buff in 
	add @@ "The automaton: \n" ;
	let get_label ss l ld = 	match List.length ld with
				| 0 -> ()
				| _ ->  add @@ va "\"%s\" --- %s ---> %s\n" ss l (string_of_string_set ld) in
	let iter_labels s nd = H.iter (get_label s) nd.targets in
  H.iter iter_labels a.nodes ;
  Buffer.contents buff
	
(* Automaton.ml: print if a state is reachable or not*)

let get_reachability_of_states a = 
	let state_node s n = 
		match n.reachable with 
			| true -> Printf.printf "%s: %s\n" s "reachable !"
			| false -> Printf.printf "%s: %s\n" s "unreachable !"
		in H.iter state_node a.nodes 
		
(* Automaton.ml: print if a state is illegal or not*)

let get_illegality_of_states a = 
	let state_node s n = 
		match n.illegal with 
			| true -> Printf.printf "%s: %s\n" s "illegal !"
			| false -> Printf.printf "%s: %s\n" s "legal !"
		in H.iter state_node a.nodes
		
(* Automaton.ml: print if a state is compatible or not*)
let get_compatibility_of_states a = 
	let state_node s n = 
		match n.compatible with 
			| true -> begin if n.illegal = true then 
									  Printf.printf "%s: %s\n" s "illegal !"
									else   
										Printf.printf "%s: %s\n" s "compatible !"
									end 
			| false -> Printf.printf "%s: %s\n" s "incompatible !"
		in H.iter state_node a.nodes


(** Module Ptree_to_ia.ml *)

(* Ptree_to_ia.ml: a string representation of a semantical ia *)
let sia_to_string ia = 
	let buff = Buffer.create 100 in
	let add = Buffer.add_string buff in
	match ia.empty with 
		| false -> 
			  add @@ va "Semantical interface automaton %s (start=%s)\n" ia.iname (string_of_state ia.start);
				let comp = begin if ia.composite then
						add @@ va "is composite !\n"
				else 
						add @@ va "is primitive !\n"
				end in 
				comp ;
				add @@ "Subcomponents: \n" ;
				let lsc sc = add @@ va "  %-44s\n" sc in
			  List.iter lsc ia.subcomponents ;
			  add @@ "Local variables: \n" ;
			  let lvars lv = add @@ va "  %-44s\n" (string_of_variable lv) in
			  List.iter lvars ia.lvariables ;
			  add @@ "Shared variables: \n" ;
			  let svars sv = add @@ va "  %-44s\n" (string_of_variable sv) in
			  List.iter svars ia.svariables ;
			  add @@ "Set of states: \n" ;
			  let sstates s = add @@ va "  %-44s\n" (string_of_state s)  in
			  List.iter sstates ia.stateset;
			  add @@ "Set of actions: \n" ;
			  let sactions a = add @@ va "  %-44s\n" (string_of_action a)  in
			  List.iter sactions ia.actions;
				add @@ "Semantics: \n" ;
			  add @@ va "  %-44s\n" (string_of_prepostpred (ref "") (hassoc ia.semantics)) ;
			  add @@ to_string ia.automaton ;
				Buffer.contents buff
		| true -> add @@ va "Semantical interface automaton %s is empty !!! \n" ia.iname ; 
			         Buffer.contents buff



	
(* Ptree_to_ia.ml: print an action list *)
let print_output_actions a = va "%s\n" (string_of_action_list (output_actions a))
let print_input_actions a = va "%s\n" (string_of_action_list (input_actions a))
let print_hidden_actions a = va "%s\n" (string_of_action_list (hidden_actions a))
let print_all_actions a = va "%s\n" (string_of_action_list (a.actions))

(* Ptree_to_ia.ml: print if two automata are composable or not *)
let print_are_composable a1 a2 = 
  if are_composable a1 a2 
  then
    ps "composable\n" 
  else 
    ps "non composable\n"

(* Ptree_to_ia.ml: print the set of shared actions *)	
let print_shared_actions a1 a2 =
  va "%s\n" (string_of_string_set (shared_external_actions a1 a2))

(* Main.ml: print the set of components *)
let print_components ht = 
	let print_comp_subcomps c ls = pf "%s => %s\n" c (string_of_string_set ls)
in H.iter print_comp_subcomps ht 

(* Main.ml: print the set of shared variables *)
let print_shared_variables ht = 
	let print_sh_comps s lc = pf "%s => %s\n" s (string_of_string_set lc)
in H.iter print_sh_comps ht 

let get_reachability_illegality_compatibility iaut = 
	get_reachability_of_states iaut.automaton ;
	get_illegality_of_states iaut.automaton ;
	get_compatibility_of_states iaut.automaton