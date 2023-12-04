(** ***********************************************************************)
(** lSIA: Language for implementing Semantical Interface Automata         *)
(**                                                                       *)
(** by Sebti MOUELHI                                                      *)
(**                                                                       *)
(** file : datastructs.ml : implements the automaton data structure       *)
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
open Parse_tree;;


(* nature of a state *)
type state_nature = 
    NAT_illegal | 
    NAT_incompatible | 
    NAT_compatible |
    NAT_indifferent |
		NAT_unreachable |
		NAT_reachable
		
(* state record *)
type state = {
  state_name : string;
  mutable nature : state_nature
}


(* variable record *)
type variable = {
  id : string ;
  vtype : var_type 
}

(* action record *)
type action = {
  sign : string ;
	mutable inp  : variable list ; (* list of input parameters *)
	mutable outp : variable list ; (* list of output parameters *) 
  kind : action_style ;
}

type prepost_transpred = {
	pre : Parse_tree.t ;
	post : Parse_tree.t ;
	transpred : Parse_tree.t ;
}


type prepost_implications = {
	prei : Parse_tree.t ;
	posti : Parse_tree.t ;
}
(* A record of shared variables *)
type shared_variables = {
  list_of_variables : variable list ;
	table : (variable, string list) H.t 
}

let variable_of_ptvariable = function
  | Variable (v, t) -> { id = v ; vtype =  t }
  | _ -> failwith "variable_of_ptvariable"

let string_of_state s = 
  match s.nature with  
  | NAT_illegal -> "ILL/" ^ s.state_name
  | NAT_compatible -> "C/" ^ s.state_name
  | NAT_incompatible -> "INC/" ^ s.state_name
  | NAT_indifferent -> "IND/" ^ s.state_name
	| NAT_unreachable -> "UNR/" ^ s.state_name
	| NAT_reachable -> "REA/" ^ s.state_name



let get_prepost_transpred semantics=
	let sems = H.create 10 in
	H.add sems SEM_pre True ; 
  H.add sems SEM_post True ;
	H.add sems SEM_transpred True ;
	let get_one_semantics = function 
		| Semantic (SEM_pre, pr) -> H.replace sems SEM_pre pr  
	  | Semantic (SEM_post, ps) -> H.replace sems SEM_post ps 
		| Semantic (SEM_transpred, eff) ->  H.replace sems SEM_transpred eff
		| _ -> failwith "datastructs.ml : get_prepost_transpred - Bad AST"
	in List.iter get_one_semantics semantics; 
	{
		pre = H.find sems SEM_pre ;
		post = H.find sems SEM_post ;
		transpred =  H.find sems SEM_transpred 
	}
	

let string_of_prepostpred str sems = 
	let rec iteration = function
		| (act,sem) :: tail -> str := !str ^ "*" ^ act ^ "-> { \n" ^ "Pre: "^ string_of_xp sem.pre ^ "\n" ^ 
										 "Post: "^ string_of_xp sem.post ^ "\n" ^
										 "Transition predicate: "^ string_of_xp sem.transpred ^ "}\n" ; iteration tail 
		| [] -> ()
  in iteration sems ; !str
	
	
(* The set of transitions of SIAs *)
type node = {
	mutable reachable : bool ;
	mutable illegal : bool ;
	mutable compatible : bool ;
	mutable targets : (string, string list) H.t ;
}

type automaton = {
	is_composite : bool ;
	mutable set_of_states : string list ;
	alphabet : string list ;
	initial_state : string;
	mutable nodes : (string, node) H.t ;
	mutable semantics_ : (string, prepost_transpred) H.t ;
}
	
(* The semantical interface automata data structure *)
type sia = {
  mutable iname : string ;
	composite : bool ;
	mutable empty : bool ;
	subcomponents : string list ;
  start : state ;
  mutable stateset : state list ;
  actions : action list ;
  svariables : variable list  ;
  lvariables : variable list  ;
  mutable semantics : (string, prepost_transpred) H.t ; 
	(* keys : action names ; values : semantics *)
  mutable automaton : automaton ; 
}

(* A state representation of a string *)
let state_of_string s = { 
  state_name = s; 
  nature = NAT_indifferent 
}


(* A string representation of an action *)
let string_of_action a =  a.sign ^ (symbol_of_action_style a.kind)

(* A string representation of a variable *)
let string_of_variable v =  v.id ^":"^ (string_of_var_type v.vtype)

let string_of_action_list =
  let quote an = "\"" ^ (string_of_action an) ^ "\"" in
  pretty_print_list quote ", " "{" "}"
