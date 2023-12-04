(** ***********************************************************************)
(** lSIA: Language for implementing Semantical Interface Automata         *)
(**                                                                       *)
(** by Sebti MOUELHI                                                      *)
(**                                                                       *)
(** file : automaton.ml : implements the automaton data structure         *)
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
open Parse_tree ;;
open Datastructs;;

exception State_not_found of string 

(** Treatment of semantics : semantics compatibility check *)				
let semantics_shared_actions a1 a2 implications souta1=
	let get_implication_a1 act1 sem1 =
		let get_implication_a2 act2 sem2 =
			match act1 = act2 with
				| false ->   ()
				| true ->
					  begin
							match List.exists (function x -> x = act1) souta1 with
								| true ->  
(*                  Printf.printf "!!!!%s!!!!\n" act1 ;*)
									H.add implications act1
									{
										prei =  Binary_op (BOP_implies, Parenthesed_xp (Hashtbl.find a1.semantics_ act1).pre, Parenthesed_xp (Hashtbl.find a2.semantics_ act1).pre)  ;
										posti = Binary_op (BOP_implies, Parenthesed_xp (Hashtbl.find a2.semantics_ act1).post, Parenthesed_xp (Hashtbl.find a1.semantics_ act1).post) ;
										
									}
							  | false ->  	
(*									  Printf.printf "????%s????\n" act1 ;			*)
									H.add implications act1
									{ 
										prei =  Binary_op (BOP_implies, Parenthesed_xp (Hashtbl.find a2.semantics_ act1).pre, Parenthesed_xp (Hashtbl.find a1.semantics_ act1).pre)  ;
										posti = Binary_op (BOP_implies, Parenthesed_xp (Hashtbl.find a1.semantics_ act1).post, Parenthesed_xp (Hashtbl.find a2.semantics_ act1).post) ;
									}
						end 
		in H.iter get_implication_a2 a2.semantics_
	in H.iter get_implication_a1 a1.semantics_
	
	
let semantics_of_resulting_internal_actions a1 a2 sems souta1=
	let get_semantics_a1 act1 sem1 =
		let get_semantics_a2 act2 sem2 =
			match act1 = act2 with
				| false ->  ()
				| true -> 
					  begin
							match List.exists (function x -> x = act1) souta1 with
								| true ->  
									H.add sems act1
									{
										pre =  (Hashtbl.find a1.semantics_ act1).pre;
										post =  (Hashtbl.find a1.semantics_ act2).post;
										transpred = (Hashtbl.find a1.semantics_ act1).transpred
									}
							  | false ->  
									H.add sems act1
									{
										pre =  (Hashtbl.find a1.semantics_ act2).pre;
										post =  (Hashtbl.find a1.semantics_ act1).post;
										transpred = (Hashtbl.find a1.semantics_ act2).transpred									
									}
						end 
		in H.iter get_semantics_a2 a2.semantics_
	in H.iter get_semantics_a1 a1.semantics_

let types_ptree_to_cvc3 = function
	| VT_real -> "REAL"
	| VT_int  ->  "INT"
  | VT_bool  -> "BOOLEAN"
	| VT_interval (x,y) -> "interval_" ^ string_of_int_2 x ^ ".." ^ string_of_int_2 y 
	| VT_enum s -> s

let type_xp_cvc xp symbs enum_types  =
	let rec typ = function
	| Parenthesed_xp e ->  typ e
	| Unary_op(u, e) -> typ e
	| Binary_op(b, l, r) -> typ l
	| Conditional (c, t, f) -> typ t
  | True  -> VT_bool
	| False -> VT_bool
  | Natural n -> VT_int
  | Real r -> VT_real
	| Id id ->   
(*		  Printf.printf "####%s###" id ;*)
			begin match H.find symbs id with
				| VT_interval _ -> VT_int 
				| x -> x
			end      			
	| Symbol s ->
		let assoc = hassoc enum_types in
		let tp = ref "" in 
		let observe_one_type (t, lv)  = 
			if List.exists (fun x -> x = s) lv then
				tp :=  t in 
		List.iter observe_one_type assoc ; 
		VT_enum !tp 
	| x ->
		 failwith "type_xp_cvc / unexpected type"
    in typ xp
		
		
	
let translate_oneimplication_to_cvc3 symbs enum_types a1 a2 buff typ souta1 a=
	let implications = H.create 10 in
	let add = Buffer.add_string buff in
	add @@ "PUSH;\n" ;
	add @@ "QUERY ";
	let rec translate_formula = function
		| Parenthesed_xp e -> add @@ "( "; translate_formula e ; add @@ " )"
		| Binary_op(b, l, r) ->
			begin	match b with 
					| BOP_implies -> translate_formula l ; add @@ " => "; translate_formula r
					| BOP_equals -> 
							begin match type_xp_cvc l symbs enum_types with 
							  | VT_bool -> translate_formula l ; add @@ " <=> "; translate_formula r
								| _ -> translate_formula l ; add @@ " = "; translate_formula r 
							end	
					| BOP_and -> translate_formula l ; add @@ " AND "; translate_formula r
					| BOP_or -> translate_formula l ; add @@ " OR "; translate_formula r
					| BOP_less -> translate_formula l ; add @@ " < "; translate_formula r
					| BOP_greater -> translate_formula l ; add @@ " > "; translate_formula r
					| BOP_greater_eq -> translate_formula l ; add @@ " >= "; translate_formula r
					| BOP_less_eq -> translate_formula l ; add @@ " <= "; translate_formula r
					| BOP_equivalent -> add @@ " ( "; translate_formula l ; add @@ " => "; translate_formula r; add @@ " ) ";
						                  add @@ " ( "; translate_formula r ; add @@ " => "; translate_formula l; add @@ " ) "
					| BOP_differs -> add @@ "NOT " ; add @@ " ( "; translate_formula l ; add @@ " = "; translate_formula r ; add @@ " ) ";
  				| BOP_plus -> translate_formula l ; add @@ " + "; translate_formula r
					| BOP_minus -> translate_formula l ; add @@ " - "; translate_formula r
					| BOP_times -> translate_formula l ; add @@ " * "; translate_formula r
					| BOP_divide -> translate_formula l ; add @@ " / "; translate_formula r
			end
		| Unary_op(u, e) ->
			begin 	match u with
					| UOP_not -> add @@ "NOT "; translate_formula e
					| UOP_minus -> add @@ "-"; translate_formula e
					| UOP_plus -> translate_formula e
			end
  	| True  -> add @@ "TRUE"
		| False -> add @@ "FALSE"
  	| Natural n -> add @@ (string_of_int n)
  	| Real r -> add @@ (string_of_float r)
	  | Id id -> add @@ id
	  | Symbol s -> add @@ s
	  | x ->
      error "translate_semantics_to_cvc3_one" "unexpected node";
      print x ~prefix:"failed type> ";
      failwith "translate_semantics_to_cvc3_one / unexpected node" 
    in
		  semantics_shared_actions a1 a2 implications souta1 ;			
			begin match typ with  
				| "pres" ->  	
(*					Printf.printf "**%s**\n" a ;*)
					translate_formula (H.find implications a).prei ;  add @@ ";\n" ;
		   		add @@ "POP;\n" ;
				| "posts" -> translate_formula (H.find implications a).posti ; add @@ ";\n" ;
			 		add @@ "POP;\n" ;
				| _ -> failwith "translate_semantics_to_cvc3_one / unexpected string"
			end  
			
			
let add_cvc3header_oneimplication symbs enum_types a1 a2 shared svars typ outa1 all shrd_action =
	let buff = Buffer.create 100 in
	let add = Buffer.add_string buff in
	let intervals = ref [] in
	let counter = ref 0 in
  let one_type t lv =
			add @@ "DATATYPE\n" ;
			add @@ va " %s = " t ;
			
			while !counter < List.length lv do
			 begin
					if !counter =  (List.length lv) -1 then   
						add @@ va " %s\n" (List.nth lv !counter)
					else 
						add @@ va " %s |" (List.nth lv !counter)
					end ;
					counter := !counter + 1
			 done ;
			 counter := 0 ;
			add @@ "END;\n\n"
	in H.iter one_type enum_types ;
	let iasvariables_to_intervals svar =
			match svar.vtype with 
				| VT_interval (l,r) -> intervals := !intervals @> [VT_interval (l,r)] 
				| _ -> ()
	in List.iter iasvariables_to_intervals svars ;
(*	let ialvariables_to_intervals lvar =                                        *)
(*			match lvar.vtype with                                                   *)
(*				| VT_interval (l,r) -> intervals := !intervals @> [VT_interval (l,r)] *)
(*				| _ -> ()                                                             *)
(*	in List.iter ialvariables_to_intervals lvars ;                              *)
	intervals := remove_duplicates !intervals ;
	let intervals_to_cvc3 inter =
		add @@ va "%s : TYPE = SUBTYPE(LAMBDA (x: INT): " (types_ptree_to_cvc3 inter) ;
		match inter with 
			| VT_interval (l,r) -> add @@ va "x >= %s AND x <= %s);\n\n" (string_of_int l) (string_of_int r)
			| _  -> ()
	in List.iter intervals_to_cvc3 !intervals ;

	let declare_cvc3_vars var = 
			begin 
				if var.id <> "state" then
				   add @@ va "%s: %s;\n" var.id (types_ptree_to_cvc3 var.vtype) ;
			end 		          
	in 
(*	   List.iter declare_cvc3_vars lvars ; add @@ "\n" ;*)
	   List.iter declare_cvc3_vars svars ; add @@ "\n" ;

		 List.iter (function a -> 
		 match List.exists (function x -> x = a.sign) shared with 
				| true -> 
						List.iter declare_cvc3_vars a.inp ; 
						add @@ "\n" ; 
						List.iter declare_cvc3_vars a.outp ;
						add @@ "\n"
				| false ->  ()) all ; 

		 translate_oneimplication_to_cvc3 symbs enum_types a1 a2 buff typ (lists_intersection shared outa1) shrd_action ;

	Buffer.contents buff
	
	  
let initialize_automaton composite states alph init sems= 
		let nds : (string, node) H.t = H.create 10 in
		let add_node ns s = 
			H.add ns s 
			{  
				reachable = false ;
				illegal = false ; 
				compatible = true ;
		    targets = H.create 10 
			} in
		List.iter (add_node nds) states ;
		let iter_states s nd =
			let add_alphabet nd a = H.add nd.targets a [] in
			List.iter (add_alphabet nd) alph in
		H.iter iter_states nds ;
		{ 
		  is_composite = composite ;
			set_of_states = states ;
			alphabet = alph ;
			initial_state = init ;
			nodes  = nds;
			semantics_ = sems
    }
		
let set_to_empty a = H.clear a.nodes

let is_empty a = H.length a.nodes = 0 


	
	
let add_transition a src label dest =
	let tgt = (H.find a.nodes src).targets in
	let nw_tgts ht l d = 
		H.replace ht l 
							(List.append (try H.find ht l
                						with Not_found -> []) [d])  
	in nw_tgts tgt label dest 
	
	
let remove_transition a src label dest =
  let tgt = (H.find a.nodes src).targets in
  let dests = H.find tgt label in
	let pr_node = H.find a.nodes src in
  H.replace tgt label (lists_diff dests [dest]) ;
	H.replace a.nodes src {
												 	reachable = pr_node.reachable ;
												 	illegal = pr_node.illegal ;
													compatible  = pr_node.compatible ;
												 	targets = tgt
												}
												
let set_reachability a = 
	let rec set_reachability_from_initial_state s =
		let get_node_of_s = try H.find a.nodes s 
												with Not_found -> raise (State_not_found s) in
		begin if get_node_of_s.reachable = false then  
			get_node_of_s.reachable <- true
		end ;
		let set_reachability_one_node lbl dests =
			let set_dest_reach d = 
				begin if (H.find a.nodes d).reachable = false then
					set_reachability_from_initial_state d
				end 
			in List.iter set_dest_reach dests
		in H.iter set_reachability_one_node (H.find a.nodes s).targets
	in set_reachability_from_initial_state a.initial_state


let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)
	

let synchronized_product_semantics a b shared non_shared saout sbout sems symbs enum_types t svars outa all =
	let product_state_a x = function y -> x ^ "." ^ y in
	let product_state_b y = function x -> x ^ "." ^ y in
	let product_states = product_lists a.set_of_states b.set_of_states in
	let convert_couple_state (s1,s2) = s1 ^ "." ^ s2 in
	let states = List.map convert_couple_state product_states in
	let remove_action_annotation a = String.sub a 0 ((String.length a) - 1) in
	let change_to_internal sa = match sa.[(String.length sa) - 1] with
		| '?' | '!' -> String.set sa ((String.length sa) - 1) ';' ; sa
		| _ -> sa in
	let product_alphabet =
		non_shared @> List.map change_to_internal shared  in
	let product_init = a.initial_state ^ "." ^ b.initial_state in
	let product = initialize_automaton true states product_alphabet product_init sems in
	let add_nonshared_trans_a st =
		let tgt = (H.find a.nodes st).targets in
		let apply_for_bstates y =
			let add_ns na ld =
				match List.exists (function act -> act = na) non_shared with
					|  true ->
							let add_dest d =
								add_transition product (product_state_a st y) na (product_state_a d y)
							in List.iter add_dest ld
					| false -> ()
			in H.iter add_ns tgt
		in List.iter 	apply_for_bstates b.set_of_states
	in List.iter add_nonshared_trans_a a.set_of_states ;
	let add_nonshared_trans_b st =
		let tgt = (H.find b.nodes st).targets in
		let apply_for_astates x =
			let add_ns na ld =
				match List.exists (function act -> act = na) non_shared with
					|  true ->
							let add_dest d =
								add_transition product (product_state_b st x) na (product_state_b d x)
							in List.iter add_dest ld
					| false -> ()
			in H.iter add_ns tgt
		in List.iter 	apply_for_astates a.set_of_states
	in List.iter add_nonshared_trans_b b.set_of_states ;
	let add_shared_trans sta =
		let add_shared_trans_bis stb =
			let tgta = (H.find a.nodes sta).targets in
			let tgtb = (H.find b.nodes stb).targets in
			let add_sh sa la =
				let add_sh_bis sb lb =
					match (remove_action_annotation sa) = (remove_action_annotation sb) &&
								List.exists (function act -> act = (remove_action_annotation sa)) shared
								 with
						| true ->
(*					    Printf.printf "$$%s$$\n" (remove_action_annotation sa) ;*)
						(	let buf_pre = Buffer.create 16 in
						  let buf_post = Buffer.create 16 in
							let cvc_implication_pre = add_cvc3header_oneimplication symbs enum_types a b shared svars "pres" outa all (remove_action_annotation sa) in
					    let cvc_implication_post = add_cvc3header_oneimplication symbs enum_types a b shared svars "posts" outa all (remove_action_annotation sa) in
              let pre_file = open_out "/home/smouelhi/workspace_ocaml/lsia/pre_file.cvc" in
							let post_file = open_out "/home/smouelhi/workspace_ocaml/lsia/post_file.cvc" in
							output_string pre_file cvc_implication_pre ;
							output_string post_file cvc_implication_post ;
							close_out pre_file ; close_out post_file ;
							let pre_string = syscall "cvc3 /home/smouelhi/workspace_ocaml/lsia/pre_file.cvc" in
							let post_string = syscall "cvc3 /home/smouelhi/workspace_ocaml/lsia/post_file.cvc" in
							Buffer.add_string buf_pre pre_string;
							Buffer.add_string buf_post post_string ;
							Printf.printf "Satisfiability ... %s" (Buffer.contents buf_pre) ;
							Printf.printf "Satisfiability ... %s" (Buffer.contents buf_post) ; 
							match (Buffer.sub buf_pre 0 5) = "Valid" &&
							       (Buffer.sub buf_post 0 5) = "Valid" 
						   with
								| true  ->
										let add_dest_a da =
												let add_dest_b db =
													add_transition product (convert_couple_state (sta,stb))
																								 (change_to_internal sa)
																								 (convert_couple_state (da,db))
												in List.iter add_dest_b lb
											in List.iter add_dest_a la 
                | false -> () ;
							 Buffer.reset buf_pre ; Buffer.reset buf_post)
						| false -> ()
				in H.iter add_sh_bis tgtb
			in  H.iter add_sh tgta
		in List.iter add_shared_trans_bis b.set_of_states
	in List.iter add_shared_trans a.set_of_states ;  	
	let read_left sta =
		let read_right stb =
			let tgta = (H.find a.nodes sta).targets in
			let tgtb = (H.find b.nodes stb).targets in
			let current_node_product = H.find product.nodes (sta^"."^stb) in
			let check_ill_left sa la =
				let check_ill_right sb lb =
					match (((List.exists (function act -> act = (remove_action_annotation sa)) saout) &&
								(List.length la <> 0) && (List.length lb = 0)) ||
							  ((List.exists (function act -> act = (remove_action_annotation sb)) sbout) &&
								(List.length la = 0) && (List.length lb <> 0))) &&
								(remove_action_annotation sa =  remove_action_annotation sb) with
									| true -> current_node_product.illegal <- true ;
														current_node_product.compatible <- false
									| false ->  
												(let buf_pre = Buffer.create 16 in
											  let buf_post = Buffer.create 16 in
												let cvc_implication_pre = add_cvc3header_oneimplication symbs enum_types a b shared svars "pres" outa all (remove_action_annotation sa) in
												let cvc_implication_post = add_cvc3header_oneimplication symbs enum_types a b shared svars "posts" outa all (remove_action_annotation sa) in
							          let pre_file = open_out "/home/smouelhi/workspace_ocaml/lsia/pre_file.cvc" in
											  let post_file = open_out "/home/smouelhi/workspace_ocaml/lsia/post_file.cvc" in
											  output_string pre_file cvc_implication_pre ;
											  output_string post_file cvc_implication_post ;
												close_out pre_file ; close_out post_file ;
												let pre_string = syscall "cvc3 /home/smouelhi/workspace_ocaml/lsia/pre_file.cvc" in
												let post_string = syscall "cvc3 /home/smouelhi/workspace_ocaml/lsia/post_file.cvc" in
												Buffer.add_string buf_pre pre_string;
												Buffer.add_string buf_post post_string ;
												Printf.printf "Satisfiability_ill ... %s" (Buffer.contents buf_pre) ;
							          Printf.printf "Satisfiability_ill ... %s" (Buffer.contents buf_post) ; 
												match
												  (* Considering semantics *)
													((((List.exists (function act -> act = (remove_action_annotation sa)) saout) &&
														(List.length la <> 0) && (List.length lb <> 0)) ||
							  						((List.exists (function act -> act = (remove_action_annotation sb)) sbout) &&
														(List.length la <> 0) && (List.length lb <> 0))) &&
													((Buffer.sub buf_pre 0 7) = "Invalid" ||
							   					(Buffer.sub buf_post 0 7) = "Invalid"))
													&& (remove_action_annotation sa =  remove_action_annotation sb) with
														| true -> current_node_product.illegal <- true ;
														          current_node_product.compatible <- false
														| false -> ()) 
				in H.iter check_ill_right tgtb
			in  H.iter check_ill_left tgta
		in List.iter read_right b.set_of_states
	in List.iter read_left a.set_of_states ;
  product

	
let synchronized_product a b shared non_shared saout sbout sems = 
	let product_state_a x = function y -> x ^ "." ^ y in
	let product_state_b y = function x -> x ^ "." ^ y in
	let product_states = product_lists a.set_of_states b.set_of_states in
	let convert_couple_state (s1,s2) = s1 ^ "." ^ s2 in 
	let states = List.map convert_couple_state product_states in
	let remove_action_annotation a = String.sub a 0 ((String.length a) - 1) in
	let change_to_internal sa = match sa.[(String.length sa) - 1] with 
		| '?' | '!' -> String.set sa ((String.length sa) - 1) ';' ; sa
		| _ -> sa in
	let product_alphabet =    
		non_shared @> List.map change_to_internal shared  in
	let product_init = a.initial_state ^ "." ^ b.initial_state in
	let product = initialize_automaton true states product_alphabet product_init sems in 
	let add_nonshared_trans_a st =
		let tgt = (H.find a.nodes st).targets in
		let apply_for_bstates y =
			let add_ns na ld =
				match List.exists (function act -> act = na) non_shared with
					|  true ->
							let add_dest d =
								add_transition product (product_state_a st y) na (product_state_a d y)
							in List.iter add_dest ld
					| false -> () 
			in H.iter add_ns tgt
		in List.iter 	apply_for_bstates b.set_of_states
	in List.iter add_nonshared_trans_a a.set_of_states ;
	let add_nonshared_trans_b st =
		let tgt = (H.find b.nodes st).targets in
		let apply_for_astates x =
			let add_ns na ld =
				match List.exists (function act -> act = na) non_shared with
					|  true ->
							let add_dest d =
								add_transition product (product_state_b st x) na (product_state_b d x)
							in List.iter add_dest ld
					| false -> () 
			in H.iter add_ns tgt
		in List.iter 	apply_for_astates a.set_of_states
	in List.iter add_nonshared_trans_b b.set_of_states ;
	let add_shared_trans sta =
		let add_shared_trans_bis stb = 
			let tgta = (H.find a.nodes sta).targets in
			let tgtb = (H.find b.nodes stb).targets in
			let add_sh sa la =
				let add_sh_bis sb lb =
					match (remove_action_annotation sa) = (remove_action_annotation sb) && 
								List.exists (function act -> act = (remove_action_annotation sa)) shared
								 with
						| true -> 
							let add_dest_a da =
								let add_dest_b db = 
									add_transition product (convert_couple_state (sta,stb)) 
																				 (change_to_internal sa) 
																				 (convert_couple_state (da,db))
								in List.iter add_dest_b lb
							in List.iter add_dest_a la
						| false -> ()
				in H.iter add_sh_bis tgtb
			in  H.iter add_sh tgta 
		in List.iter add_shared_trans_bis b.set_of_states
	in List.iter add_shared_trans a.set_of_states ;
	let read_left sta =
		let read_right stb = 
			let tgta = (H.find a.nodes sta).targets in
			let tgtb = (H.find b.nodes stb).targets in
			let current_node_product = H.find product.nodes (sta^"."^stb) in
			let check_ill_left sa la =
				let check_ill_right sb lb =
					match (((List.exists (function act -> act = (remove_action_annotation sa)) saout) && 
								(List.length la <> 0) && (List.length lb = 0)) ||
							  ((List.exists (function act -> act = (remove_action_annotation sb)) sbout) &&
								(List.length la = 0) && (List.length lb <> 0)))  &&
								remove_action_annotation sa =  remove_action_annotation sb with
									| true -> current_node_product.illegal <- true ;
														current_node_product.compatible <- false
									| false ->   ()
				in H.iter check_ill_right tgtb
			in  H.iter check_ill_left tgta 
		in List.iter read_right b.set_of_states
	in List.iter read_left a.set_of_states ;
  product
	
	



let remove_unreachable_states a =
	let if_unreachable s n =
		match n.reachable with
			| true  -> ()
			| false -> let apply_to_all ss nn =
								 	let remove_from_destinations label dests =
										match List.exists (function x  ->  x = s) dests with
											|  false -> ()
											|  true -> H.replace nn.targets label (lists_diff dests [s]) 
								 	in H.iter remove_from_destinations nn.targets
								 in H.iter apply_to_all a.nodes
	in H.iter if_unreachable a.nodes ;
	let remove_unreachable  s n =
			match n.reachable with 
				| true  -> ()
				| false -> a.set_of_states <- lists_diff a.set_of_states [s] ;
								 H.remove a.nodes s 
	in H.iter remove_unreachable a.nodes
	
	
let remove_incompatible_states a =
	let if_incompatible s n =
		match n.compatible with
			| true  -> ()
			| false -> let apply_to_all ss nn =
								 	let remove_from_destinations label dests =
										match List.exists (function x  ->  x = s) dests with
											|  false -> ()
											|  true -> H.replace nn.targets label (lists_diff dests [s]) 
								 	in H.iter remove_from_destinations nn.targets
								 in H.iter apply_to_all a.nodes
	in H.iter if_incompatible a.nodes ;
	let remove_incompatible  s n =
			match n.compatible with 
				| true  -> ()
				| false -> a.set_of_states <- lists_diff a.set_of_states [s] ;
								 H.remove a.nodes s 
	in H.iter remove_incompatible a.nodes


let compute_composition prod =
	let is_illegal s aut = (H.find aut.nodes s).illegal in
	let is_compatible s aut = (H.find aut.nodes s).compatible in
	match prod.is_composite with
		| false -> ()
		| true -> let from_illegal s n =
								let enter_targets a ld =
									let enter_destinations d =
										match (is_illegal d prod, is_compatible d prod) with 
											| (false,true) -> ()
											| _ -> 
												match a.[(String.length a) - 1] with  
													| ';' | '!' -> n.compatible <- false
													| _  -> () 
									in List.iter enter_destinations ld 
								in H.iter enter_targets n.targets
							in H.iter from_illegal prod.nodes ;
							remove_incompatible_states prod ;
							begin if H.mem prod.nodes prod.initial_state = false then
											set_to_empty prod

							end
							


 
