(** ***********************************************************************)
(** lSIA: Language for implementing Semantical Interface Automata         *)
(**                                                                       *)
(** by Sebti MOUELHI                                                      *)
(**                                                                       *)
(** file : ptree_to_sia.ml : implements the automaton data structure      *)
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
open Automaton ;;
open Datastructs ;;


exception PrimitiveInterfaceAutomaton of string
exception IllegalCompositionAttempt of string


(* Get the semantical interface automaton from an interface AST *)
let sia_from_ptree i shvars =
  let start = uw_state (uw_initial i.initial) in
	let st = get_shared_vars (Primitive i, shvars) in
	let convert_vtyc_to_var (v, t) = { id = v ; vtype = t } in
  let lst = hassoc st in
  let iactions = uw_transw i.inputs  in
  let oactions = uw_transw i.outputs in
  let hactions = uw_transw i.hiddens in
  let get_action kd = function Id act  ->  {sign = act ; inp = []; outp = []; kind = kd } | _ -> failwith "get_action" in
  let get_state = function State s -> state_of_string s | _-> failwith "get_state" in
	let get_label an all = string_of_action (List.find (fun e -> an = e.sign ) all) in
  let io = List.map (get_action AS_input) iactions @> List.map (get_action AS_output) oactions in
  let all_actions = io @> (List.map (get_action AS_hidden) hactions) in
  let alphabet = List.map string_of_action all_actions in
  let istates = uw_states i.states in
  let sm = H.create 10 in 
	let aut = Automaton.initialize_automaton false (List.map uw_state istates) alphabet start sm in
  let transitions = List.map uw_transition @@ uw_transitions i.transitions in
  let add_transition_semantics (k, n, a, p, sems) =
    let arrows = List.map uw_arrow a in
		let associate_parameters_to_actions = function (inp,outp) ->
				(List.find (fun act -> act.sign = n) all_actions).inp <- 
					(List.find (fun act -> act.sign = n) all_actions).inp @> (List.map variable_of_ptvariable inp) ; 
				(List.find (fun act -> act.sign = n) all_actions).outp <- 
					(List.find (fun act -> act.sign = n) all_actions).outp @> (List.map variable_of_ptvariable outp)
		in 
		let add_arrow = function (org, tget) ->
			Automaton.add_transition aut org (get_label n all_actions) tget 
    in List.iter add_arrow arrows ; 
		H.add sm n (get_prepost_transpred sems) ;
    H.add aut.semantics_ n (get_prepost_transpred sems) ;
		associate_parameters_to_actions (uw_parameters p)
  in List.iter add_transition_semantics transitions ;
  {
    iname = i.name ;
		composite = false ;
		empty = false ;
		subcomponents = [] ;
    start = (state_of_string start) ;
    stateset = List.map get_state istates ;
    actions = all_actions ;
    lvariables = List.map variable_of_ptvariable (uw_locals i.locals) ;
    svariables = List.map convert_vtyc_to_var lst ;
    semantics = sm ;
    automaton = aut 
  }


let action_signature a = a.sign 

let list_action_sign l = List.map action_signature l

let all_actions a = a.actions


(* The set of input, output, and hidden actions *)
let output_actions a = 
  let acs = all_actions a in 
  let rec ifoa = function
    | ac :: tlacs ->
	  ( match ac.kind with
	    | AS_output -> ac :: ifoa tlacs
	    | _ -> ifoa tlacs 
	  )
    | [] -> [] 
in ifoa acs

let input_actions a =
  let acs = all_actions a in 
  let rec ifia = function
    | ac :: tlacs ->
	  ( match ac.kind with
	    | AS_input -> ac :: ifia tlacs
	    | _ -> ifia tlacs
	  )
    | [] -> [] 
in ifia acs

let hidden_actions a =
  let acs = all_actions a in 
  let rec ifha = function
    | ac :: tlacs ->
	  ( match ac.kind with
	    | AS_hidden -> ac :: ifha tlacs
	    | _ -> ifha tlacs
	  )
    | [] -> [] 
in ifha acs

let is_output_action sign a =
	let out_actions =  output_actions a in
	let rec ifoa = function 
		| ac :: tlac -> 
			( match ac.sign = sign with 
				| true -> true 
				| false -> ifoa tlac
			)
		| [] -> false 
in ifoa out_actions

let is_input_action sign a =
	let in_actions =  input_actions a in
	let rec ifia = function 
		| ac :: tlac -> 
			( match ac.sign = sign with 
				| true -> true 
				| false -> ifia tlac
			)
		| [] -> false 
in ifia in_actions

let is_hidden_action sign a =
	let hid_actions =  hidden_actions a in
	let rec ifha = function 
		| ac :: tlac -> 
			( match ac.sign = sign with 
				| true -> true 
				| false -> ifha tlac
			)
		| [] -> false 
in ifha hid_actions

let is_action sign a = is_hidden_action sign a && is_input_action sign a && is_output_action sign a 

let are_composable a1 a2 =
      not (lists_intersect (output_actions a1) (output_actions a2)) &&
      not (lists_intersect (input_actions a1) (input_actions a2)) &&
      not (lists_intersect ((output_actions a1) @> (input_actions a1)) (hidden_actions a2)) &&
      not (lists_intersect (hidden_actions a1) ((output_actions a2) @> (input_actions a2)))

let shared_external_actions a1 a2 = (lists_intersection (list_action_sign (output_actions a1)) (list_action_sign (input_actions a2))) @<
			   (lists_intersection (list_action_sign (input_actions a1)) (list_action_sign (output_actions a2)))


let shared_output_actions_a1 a1 a2 =
	lists_intersection (list_action_sign (output_actions a1)) (shared_external_actions a1 a2) 

let shared_output_actions_a2 a1 a2 =
	lists_intersection (list_action_sign (output_actions a2)) (shared_external_actions a1 a2) 

let non_shared_actions a1 a2 =  
	lists_diff ((list_action_sign (all_actions a1)) @> (list_action_sign (all_actions a2)))  
						(shared_external_actions a1 a2)
						
						
							
let set_reachability iaut = 
	Automaton.set_reachability iaut.automaton ;
	let copy_reachability s n =
		let change_nature ss = 
			begin if n.reachable = false then
				begin	if ss.state_name = s then ss.nature <- NAT_unreachable end 
			else 
				begin if ss.state_name = s then ss.nature <- NAT_reachable end 
			end
		in List.iter change_nature iaut.stateset 	  
	in H.iter copy_reachability iaut.automaton.nodes 
	
let set_illegality iaut = 
	match iaut.composite with 
		| false -> ()
		| true  -> 
			let copy_illegality s n =
				let change_nature ss = 
					begin if n.illegal = false then
						begin	if ss.state_name = s then ss.nature <- NAT_compatible end 
					else 
						begin if ss.state_name = s then ss.nature <- NAT_illegal end 
				end
			in List.iter change_nature iaut.stateset 	  
		in H.iter copy_illegality iaut.automaton.nodes 
		
let establish_semantics_of_product a1 a2 prod =
	let non_shared = non_shared_actions a1 a2 in
	semantics_of_resulting_internal_actions a1.automaton a2.automaton prod.semantics (shared_output_actions_a1 a1 a2);
	let add_non_shared_semantics_a1 act =
		Hashtbl.add prod.semantics act (H.find a1.semantics act)
	in List.iter add_non_shared_semantics_a1 (lists_intersection (list_action_sign (all_actions a1)) non_shared) ;
	let add_non_shared_semantics_a2 act =
		Hashtbl.add prod.semantics act (H.find a2.semantics act)
	in List.iter add_non_shared_semantics_a2 (lists_intersection (list_action_sign (all_actions a2)) non_shared)
	
let get_enum_types_from_pt = function 
	| Sias (Enumeration_types enums, _, _, _, _) -> get_enumeration_types enums		
	| _ -> failwith "get_enum_types_from_pt"
	

		
let synchronize a1 a2 shared compset t = 
	let symbs = get_symbols_table_spec t in
	let enum_types = get_enum_types_from_pt t in
	let convert_couple_state (s1,s2) = s1 ^ "." ^ s2 in
	let compute_subcomponents =
		match (a1.composite, a2.composite) with
			| (true, true) -> a1.subcomponents @> a2.subcomponents
			| (false, true) -> [a1.iname] @> a2.subcomponents
			| (true, false) -> a1.subcomponents @> [a2.iname]
			| (false,false) ->  [a1.iname ; a2.iname] in 
	let get_composite sub = 
			match List.exists (fun (c,ls) -> List.exists (fun s -> sub = s) ls) (hassoc compset) with 
				| true -> 
					   let (c,_) = List.find (fun (c,ls) -> List.exists (fun s -> sub = s) ls) (hassoc compset) in 
						 c 
				| _ -> sub in
	let change_compset h =
			match get_composite a1.iname = get_composite a2.iname with
							| true -> H.replace h (get_composite a1.iname) (remove_duplicates (List.map
										(function x -> match x = a1.iname || x = a2.iname with
											| true -> a1.iname ^ "|" ^ a2.iname
											| false -> x) (Hashtbl.find h (get_composite a1.iname))))
							| false -> 
								    match get_composite a1.iname = a1.iname && get_composite a2.iname = a2.iname with 
											| true -> ()
											| false -> raise (IllegalCompositionAttempt
														(a1.iname ^ " and " ^ a2.iname ^" are not subcomponents of the same composite component !!"))
	in change_compset compset ;
	Hashtbl.remove compset a1.iname ;
	Hashtbl.remove compset a2.iname ;	 
	let change_shared_variables s lc =
		 H.replace shared s (remove_duplicates (List.map
										(function x -> match x = a1.iname || x = a2.iname with
											| true -> a1.iname ^ "|" ^ a2.iname
											| false -> x) lc))
	in H.iter change_shared_variables shared ;
	let to_ns_action = function a -> 
		begin if is_output_action a a1 then 
			{sign = a ; inp = [] ; outp = [] ; kind = AS_output }
		else if is_output_action a a2 then
			{sign = a ; inp = [] ; outp = [] ; kind = AS_output }
		else if is_input_action a a1 then 
		  {sign = a ; inp = [] ; outp = []; kind = AS_input }
		else if is_input_action a a2 then
			{sign = a ; inp = [] ; outp = []; kind = AS_input }
		else 
			{sign = a ; inp= []; outp = []; kind = AS_hidden}
		end in
	let to_hid_action a = {sign = a ; inp = []; outp = []; kind = AS_hidden}  
	in 
	let sems = H.create 10 in
	let prod = synchronized_product_semantics a1.automaton a2.automaton
																		 (shared_external_actions a1 a2)
																		 (List.map string_of_action (List.map to_ns_action (non_shared_actions a1 a2)))
																		 (shared_output_actions_a1 a1 a2)
																		 (shared_output_actions_a2 a1 a2) sems 
																		 symbs
																		 enum_types 
																		 t 
																		 (remove_duplicates (a1.svariables @> a2.svariables)) 
																		 (list_action_sign (output_actions a1)) 
																		 ((all_actions a1)) 
	in
	(* return the automaton *)
	let siaut = {
    iname = a1.iname ^ "*" ^ a2.iname ;
		composite = true ;
		empty = false ;
		subcomponents = compute_subcomponents ;
    start = state_of_string (a1.start.state_name ^ "." ^ a2.start.state_name) ;
    stateset = List.map state_of_string (List.map convert_couple_state  
				(product_lists a1.automaton.set_of_states a2.automaton.set_of_states));
    actions = List.map to_ns_action (non_shared_actions a1 a2) @> 
							List.map to_hid_action (shared_external_actions a1 a2);
    lvariables = remove_duplicates (a1.lvariables @> a2.lvariables) ;
    svariables = remove_duplicates (a1.svariables @> a2.svariables) ;
    semantics = sems  ; 
    automaton = prod
  } in set_reachability siaut ; 
			 set_illegality siaut ;
			 siaut
			
			
let composition product =
	match product.composite  with
		| false -> raise (PrimitiveInterfaceAutomaton product.iname)
		| true ->
				let remove_unreachable ia state  =
					match state.nature with
						| NAT_unreachable  ->  ia.stateset <- lists_diff ia.stateset [state]
						| _  ->  () in
			  let remove_incompatible ia state = 
					match state.nature with
						| NAT_incompatible | NAT_illegal  ->  ia.stateset <- lists_diff ia.stateset [state]
						| _  ->  () in
				let set_to_empty ia = 
					match is_empty product.automaton with 
						| false -> ()
						| true -> product.empty <- true 
				in
			  String.set product.iname (String.index product.iname '*') '|' ;
				set_reachability product ;
				Automaton.remove_unreachable_states product.automaton ;
				List.iter (remove_unreachable product) product.stateset ;
				Automaton.compute_composition product.automaton ;
				List.iter (remove_incompatible product) product.stateset ;
				set_to_empty product ;
				begin 
					if product.empty = false then
						set_reachability product ;
						Automaton.remove_unreachable_states product.automaton ;
						List.iter (remove_unreachable product) product.stateset ; 		
				end ;
				product
