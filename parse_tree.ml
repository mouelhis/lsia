(** ********************************************************************* *)
(** lSIA: Language for implementing Semantical Interface Automata         *)
(**                                                                       *)
(** by Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX                       *)
(**                                                                       *)
(** file : parse_tree.ml : translates source files to ASTs                *)
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


(** Definitions and common operations on the Parse Tree *) 

open Toolkit;;
open Common;;


(** To avoid repeating the exact same treatments on many tree nodes, all binary
operators have been combined into one node. This enumeration specifies which binary operator
the node represents *)
type binary_operator = 
  | BOP_equals | BOP_differs | BOP_less | BOP_greater 
  | BOP_less_eq | BOP_greater_eq | BOP_implies
  | BOP_and | BOP_or | BOP_plus | BOP_minus | BOP_times
  | BOP_divide | BOP_equivalent
  
let string_of_binop = function
  | BOP_equals -> "Equals"
  | BOP_differs -> "Differs"
  | BOP_less -> "Strictly Less"
  | BOP_greater -> "Strictly Greater"
  | BOP_less_eq -> "Less or Equal"
  | BOP_greater_eq -> "Greater or Equal"
  | BOP_implies -> "Implies"
  | BOP_and -> "And"
  | BOP_or -> "Or"
  | BOP_plus -> "Plus"
  | BOP_minus -> "Minus"
  | BOP_times -> "Times"
  | BOP_divide -> "Divide"
  | BOP_equivalent -> "Equivalent"
  
let glyph_of_binop = function
  | BOP_equals -> "="
  | BOP_differs -> "!="
  | BOP_less -> "<"
  | BOP_greater -> ">"
  | BOP_less_eq -> "<="
  | BOP_greater_eq -> ">="
  | BOP_implies -> "==>"
  | BOP_and -> "/\\"
  | BOP_or -> "\\/"
  | BOP_plus -> "+"
  | BOP_minus -> "-"
  | BOP_times -> "*"
  | BOP_divide -> "/"
  | BOP_equivalent -> "<==>"
  
type unary_operator = UOP_not | UOP_minus | UOP_plus

let string_of_unop = function
  | UOP_not -> "Unary Not" 
  | UOP_minus -> "Unary Minus"
  | UOP_plus -> "Unary Plus"
  
let glyph_of_unop = function
  | UOP_not -> "~" 
  | UOP_minus -> "-"
  | UOP_plus -> "+"
  
(** Type of macro; an open macro may have free variables, while a closed macro
  only has bound variables *)
type macro_kind = MAC_open | MAC_closed

let string_of_mackind = function
  | MAC_open -> "}open{" | MAC_closed -> "{closed}"

(** Type of logical condition *)
type semantic = SEM_pre | SEM_post | SEM_transpred


let string_of_semantic = function
  | SEM_pre -> "Precondition" 
  | SEM_post -> "Postcondition" 
  | SEM_transpred -> "Transition predicate"


(** Type of the parse tree: this is the raw output of the parser *)
type t = 
  | Sias of t * t * t * t * t(** enumeration types, macros, shared_vars, primitives, composites *)
  | Locals of t list (** Vars list *)  
  | Init of t (** logical exp *) 
	| Initial of t (** initial state*)
	| Invariant of t (** logical exp *) 
  | Id of string
	| Enumeration_types of t list
	| Enumeration_type of string * t list
  | Symbol of string (** Symbol: enumerated element *)
  | Variable of string * var_type (** name , type *)
  | Primitives of t list
  | Primitive of primitive 
  | Composites of t list
	| Parenthesed_xp of t (** parenthesed expression *)
  | Composite of string * t list
  | Inputs of t list (** id list: primitive inputs *)
  | Outputs of t list (** id list: primitive outputs *)
  | Hiddens of t list (** id list : primitive local actions *)
  | Transitions of t list (** transition list *)
  | Transition of action_style * string * t list * t  * t list (** type, name, arrows, parameters, semantics *)
  | Shared of t list (** by list *)
  | By of t list * t list (** vars , interfaces *)
  | Parameters of t list * t list (** input parameters, output parameters *)
  | Semantic of semantic * t
  | Macros of t list (** macros *)
  | Macro of macro_kind * string * t list * t (** kind, name, bound variables, expression *)
  | Macro_call of string * t list (** name, parameters *)
  | Binary_op of binary_operator * t * t
  | Unary_op of unary_operator * t
  | Conditional of t * t * t (** If x Then y Else z *)
	| Unchanged of t list (** unchanged variables*)
  | True
  | False
  | Natural of int
  | Real of float 
  | State of string (** state as used in expressions *)
  | States of t list (** all state declarations *)
  | Arrow of string * string (** states assoc to a transition *)

and 
(** Record for the interface, as it would be cumbersome to keep it as a tuple *)
primitive = {
  name : string;
  locals : t;
  states : t;
	initial : t;
  init : t;
  inputs : t;
  outputs : t;
  hiddens : t;
	invariant : t ;
  transitions : t;
}

(** Unwrap [Id] or [Symbol] parse tree elements *)
let string_of_id = function Id s -> s | _ -> failwith "string_of_id"
let string_of_symbol = function Symbol s -> s | _ -> failwith "string_of_symbol"

(** Print the parse tree to [stdout] *)

let print ?(prefix="") t = 
  let rec print_rec nb_space t  =
    let succ n = n + 2 in
    let make_spaces n = ps prefix; ps (repeat_pattern " "  n) in
    make_spaces nb_space ;
    let rec_call t = print_rec (succ nb_space)  t in
    let box x = 
      let sp() = make_spaces (succ nb_space) in
      sp(); pl "["; List.iter rec_call x; sp() ; pl "]"
      in match t with 
       | Sias (e,m,s,i,c) -> pl "Sias"; rec_call e; rec_call m; rec_call s; rec_call i; rec_call c
       | Locals l -> pl "Locals"; box l
       | Init t -> pl "Init"; rec_call t
       | Id  i -> pf "Id: " ; pl i
       | Symbol s -> ps "Symbol: `"; pl s
			 | Enumeration_types tl -> pl "Enumeration types: " ; box tl 
			 | Enumeration_type (t, ls) -> ps "Type: " ; ps t ; ps ", list of values:\n" ; box ls
       | Variable (name, var_type) -> ps "Variable: "; ps name ; ps ", type: "; print_var_type var_type
       | Primitives l ->pl "Primitive interfaces "; box l
       | Primitive i -> 
          pl ("Primitive: " ^ i.name);
          rec_call i.locals; rec_call i.states; rec_call i.init;
          rec_call i.inputs; rec_call i.outputs; rec_call i.hiddens; rec_call i.invariant; rec_call i.transitions
       | Inputs l -> pl "Inputs"; box l
       | Outputs l -> pl "Outputs"; box l
       | Hiddens l -> pl "Hiddens"; box l
       | Invariant t -> pl "Invariant"; rec_call t
			 | Initial t -> pl "Initial"; rec_call t
       | Transitions l ->pl "Transitions"; box l
       | Transition (typ, name, arrows, params, l) -> 
          pf "%s: %s\n" (string_of_action_style typ) name; box arrows; rec_call params; box l
       | Shared l -> pl "Shared";box l 
       | By (lv, li) -> pl "By"; box lv ;box li
       | Parameters (li, lo) -> pl "Parameters"; box li ;box lo 
       | Semantic (t, e) -> pl (string_of_semantic t) ; rec_call e
			 | Parenthesed_xp e -> pl "Parenthesed expression" ; rec_call e  
       | Binary_op (op, l, r) -> pl (string_of_binop op) ; rec_call l ; rec_call r
       | Unary_op (op, t) -> pl (string_of_unop op) ; rec_call t
       | Conditional (cond, t, f) -> pl "If:Then/Else"; rec_call cond; rec_call t; rec_call f
			 | Unchanged l -> pl "Unchanged"; box l
       | True -> pl "True"
       | False -> pl "False"
       | Natural nb -> ps "Natural: "; pl (soi nb);
       | Real nb -> ps "Real: "; pl (sof nb)
       | State s -> pf "State: \"%s\"\n" s
       | States sl -> pl "States"; box sl
       | Macros l -> pl "Macros" ; box l
       | Macro (k, n, v, e) -> ps "Macro: "; ps (n^"  "); pl (string_of_mackind k) ; box v ; rec_call e
       | Macro_call (n, p) -> pf "Macro Call: %s\n" n; box p
       | Composites l -> pl "Composite interfaces "; box l
       | Composite (name, l) -> pf "Composite: %s\n" name; box l
       | Arrow (s, s') -> pf "%s -> %s\n" s s'
     in 
        print_rec 0 t
				
				
				(** {6 Macro expanding, Type Checking and other validations} *)

(** Number of errors detected so far *)
let _errors = ref 0

(** Give an error message *)
let error loc = incr _errors; epf "ERROR(%s): " loc; epf 

(** First step: check that macro bodies expansion terminates, ie. that there are no mutually-recusive macros.
    This is a cycle detection in a directed graph. The algorithm used is far from optimal but hey, 
    you should not have thousands of macros... 
*)

(** Get the list of all {i direct} macro dependencies of an expression 
    the function is called by macro_depend *)

let rec get_macro_dep = function
  | Binary_op(_, l, r) -> get_macro_dep l @< get_macro_dep r
  | Unary_op(_, e) -> get_macro_dep  e
  | Conditional (c, t, f) -> get_macro_dep c @< get_macro_dep t @< get_macro_dep f
  | Macro_call (n, el) -> n :: (List.flatten  @@ List.map get_macro_dep el)
  (* flatten all the sublists of get_macro_dep el *)
  | _ -> []


let macro_depend t = 
  let dep = H.create 10 in
  match t with
  | Sias (_, Macros macros, _, _, _) -> 
  (* get direct dependencies  *)
    (* Keys are names of macros and values are expressions *)
    let get_deps1 = function Macro (_, n, _, e) ->  H.replace dep n (get_macro_dep e) |_->()
    in List.iter get_deps1 macros;
    (* compute the transitive closure *)
    let modifs = ref 1 in
    let expand n deps = 
      let _expand l = List.flatten @@ List.map (H.find dep) l in
      let deps' = remove_duplicates @@ deps @< _expand deps in
      modifs := !modifs + (listlen deps') - (listlen deps);
      H.replace dep n deps'
    in while !modifs <> 0 do
      modifs := 0;
      H.iter expand dep
    done;
    (* check that no macro M is such that M ->+ M don't allow recursivity in macros *)
    let check m deps = 
      if List.mem m deps 
      then 
        error "macro_depend" 
              "Macro %s is recursive (directly or not), which is not allowed\n" m
    in H.iter check dep;
    if !_errors > 0 then begin
      pe "Dependency errors have been found: printing dependency table:";
      let print n deps = epf "%10s -> %s\n" n (strof_id_list deps) in
      H.iter print dep
    end
  | _ -> error "macro_depend" "bad tree"


(** Checking that closed macros do not have free variables *)

(** Now that we know macros {i can} be expanded, let's expand them; then we will be able to
expand all expressions without having to worry about anything *)

exception Unknown_macro of string
    
  
let get_macro macros macro = 
  try H.find macros macro
  with Not_found -> raise (Unknown_macro macro)

(** substitute all ids by their corresponding values 
    - the function is called by the expand_1 *)
let substitue_id ids values exp =
  (* [(id1,val1); ...; (idn,valn)] *)
  let corr = List.combine (List.map string_of_id ids) values in
  let rec sub = function
		| Parenthesed_xp e -> Parenthesed_xp (sub e)
    | Binary_op(b, l, r) -> Binary_op(b, sub l, sub r)
    | Unary_op(u, e) -> Unary_op(u, sub e)
    | Conditional (c, t, f) -> Conditional(sub c, sub t, sub f)
    | Macro_call (n, el) -> Macro_call (n, List.map sub el) 
    (* apply the function sub on the set of parameter of the macro call*)
    | Id n -> (try List.assoc n corr with Not_found -> Id n)
    (* when an identifier is retreived, we apply the function corr to associate the identifier with its value *)
    | x -> x
  in sub exp


(** get all the macros as a hashtable name -> (bound vars, body).
    the fuction is called by expand_everything *)
let get_macros t =
  let h = H.create 5 in
  begin match t with  
  | Sias (_, Macros macros, _, _, _) -> (*macros is a list of macro*)
    let add = function Macro(_, n, vars, body) -> H.replace h n (vars, body) |_->() 
    (* make as value of the key (macro n) her vars and body*)
    in List.iter add macros (* macros is a list of macro *)
    (* apply the function add to each macro in macros  *)
    (* List.iter f [a1; ...; an] applies function f in turn to a1; ...; an *)
  | _ -> error "get_macros" "bad tree"
  end; h


(** expand the macros in an expression, once *) 
let expand_1 macros exp = 
  let rec sub = function
	| Parenthesed_xp e -> Parenthesed_xp (sub e) 
  | Binary_op(b, l, r) -> Binary_op(b, sub l, sub r)
  | Unary_op(u, e) -> Unary_op(u, sub e)
  | Conditional (c, t, f) -> Conditional(sub c, sub t, sub f)
  | Macro_call (n, el) -> (* replace the macro call by its code *)
    let vars, body = get_macro macros n in
    substitue_id vars el body
    (* substitute the variables "vars" with their values "el" in the expression "body" *)
  | x -> x 
 in sub exp

let _expand_level = ref 0 
  
let expand_all macros = 
  let f n (v,b) = H.replace macros n (v, expand_1 macros b) in
  for i = 1 to !_expand_level do H.iter f macros done
 
 
let expand_everything t =
  let macros = get_macros t in
  expand_all macros;
  let p n (v,b) = pf "%s -> " n ; print b in
  H.iter p macros
  
(** note: macros are not fully functionnal yet; 
  I'll come back to them later as it is a low-priority thing *)

(** Type-Checking *)

(** get the raw list of local variables of an interface, 
    the function is called by get_symbol_table *)

let get_raw_local_variables_list interf = 
  let lo = interf.locals in 
  let unwrap_lo = function Locals l -> l   | _-> failwith "get_raw_local_variables_list" in
  unwrap_lo lo

(** get the raw list of shared variables,
    the function is called by get_symbol_table*)

let get_raw_shared_variables_list bylst =
    let unwrap_by = function By (vl, _) -> vl   | _-> failwith "get_raw_shared_variables_list" in
    List.flatten @@ List.map unwrap_by (bylst)

(** Unwrap Id *)
let uw_id = function
  | Id i -> i 
  | _ -> failwith "uw_id"

let rec uw_list_ids = function 
  | Id i :: ids_tail -> i :: uw_list_ids ids_tail
  | [] -> []
  | _ -> failwith "uw_list_ids"

(** Add symbols to an existing table of symbols, from a Variables list 
     the function is called by get_symbol_table *)
let pour_symbols loc ht vars = 
  let declare = function
  | Variable (name, typ) ->
    (
     match hfind'o ht name with
      | Some prevtyp -> 
	(* if the same variable was declared previously with a type t1 and then
	   is declared with another type t2*)
	error 
	  "parse_tree.ml : get_symbols_table" 
	  "At %s, variable '%s' was declared once with type %s, and again as %s!\n" 
        loc name (sovt prevtyp) (sovt typ) (* loc : localization of the variable *)
      | None ->
	H.add ht name typ;
    )
  | _ -> failwith "pour_symbols"
  in List.iter declare vars

let shared_variables_of_intr name bylst = 
    let fnd iname = (uw_id iname) = name in
      let unwrap_by_vars = function By (vl, _) -> vl   | _-> failwith "shared_variables_of_intr" in
      let unwrap_by_ints = function By (_, li) -> li   | _-> failwith "shared_variables_of_intr" in
      let in_intlist aby = List.exists fnd (unwrap_by_ints aby) in 
      let get_shvars aby =
	let vars_bylist = function true -> unwrap_by_vars aby | false -> [] in
      vars_bylist (in_intlist aby)
    in List.flatten @@ List.map get_shvars bylst 

(** Build the table of enumeration types *)
let get_enumeration_types enums = 
		let ht = H.create 10 in 
		let get_one_enum = function
			| Enumeration_type (tp, lv) -> H.add ht tp (List.map string_of_symbol lv)
			| _ -> error "get_enumeration_types" "bad tree" 
		in List.iter get_one_enum enums ; ht



let primed_version_of_variables ht =
	let pht = H.create 10 in
	let primed_version var typ =  H.add pht (var^"\'") typ in
	H.iter primed_version ht ; pht
	
	
	
(** Build the table of symbols of an Interface *)
let get_symbols_table = function
  | (Primitive i, Shared bylst) ->
    let ht = H.create 10 in
    let lovars = get_raw_local_variables_list i in 
    let shvars = shared_variables_of_intr i.name bylst in
    pour_symbols ("primitive "^i.name) ht 
		   (lovars @< shvars);  hashtbl_merge ht (primed_version_of_variables ht)
  | _ -> failwith "parse_tree.ml : get_symbols_table"


(** Associate actions with their parameters *)
(*let associate_actions_params = function                           *)
(*	| Sias (_,_,_,Primitives ps, _) ->                              *)
(*		let htb = H.create 10 in                                      *)
(*		let associate = function                                      *)
(*			| Primitive i ->                                            *)
(*				 let hts = H.create 10 in                                 *)
(*				 let all_transitions = function                           *)
(*					| Transitions trs ->                                    *)
(*						let one_transition = function                         *)
(*							| Transition (_, an, _, Parameters(inp,outp), _) -> *)
(*								H.add hts an (inp,outp)                           *)
(*							| _ -> failwith "associate_actions_params : bad AST"*)
(*				   	in List.iter one_transition trs                       *)
(*					| _ -> failwith "associate_actions_params : bad AST"    *)
(*				 in all_transitions i.transitions ;                       *)
(*				 H.add htb i.name hts                                     *)
(*		   | _ -> ()                                                  *)
(*		in List.iter associate ps                                     *)
(*	| _ -> failwith "associate_actions_params : bad AST"            *)


(** Build the table of shared variables of an Interface *)
let get_shared_vars = function
  | (Primitive i, Shared bylst) ->
    let ht = H.create 10 in 
    let shvars = shared_variables_of_intr i.name bylst in
    pour_symbols ("primitive "^i.name) ht shvars; ht
  | _ -> failwith "parse_tree.ml : get_shared_vars"

(** Build the table of symbols of an Interface *)
let get_local_vars = function
  | Primitive i ->
    let ht = H.create 10 in
    let lovars = get_raw_local_variables_list i in 
    pour_symbols ("primitive "^i.name) ht lovars ; ht(*loc is here the interface declaration *)
  | _ -> failwith "parse_tree.ml : get_local_vars"

(** Build the table of symbols of the whole specification *)
let get_symbols_table_spec = function 
   | Sias (_, _, Shared bylst, _, _) -> 
      let ht = H.create 10 in
      let shvars = get_raw_shared_variables_list bylst in
      pour_symbols "shared variables section" ht shvars; 
			hashtbl_merge ht (primed_version_of_variables ht)
   | _ -> failwith "parse_tree.ml : get_symbols_table_spec"


(** Build the set of all components *)
let component_set t table =
		match t with
		| Sias  (_, _, _, Primitives ints, Composites comps) ->
			let get_name = function 
				| Primitive i -> Hashtbl.add table i.name []
				| Composite (name, sc) -> Hashtbl.add table name (List.map uw_id sc)
				| _ -> failwith "parse_tree.ml : component_set"
			in List.iter get_name ints ; List.iter get_name comps
		| _ ->  failwith "parse_tree.ml : bad AST"


(** Build the set of shared variables *)
let shared_variables t table =
		match t with
			| Sias (_, _, Shared bylst,_ ,_) -> 
				let get_variable = function 
					| By (vl, il) -> 
						let add_one_var = function 
							|  Variable (n, _) ->  H.add table n (List.map uw_id il)
							|  _ -> failwith "parse_tree.ml (shared variables):  bad 'by' structure"
						in List.iter add_one_var vl 
					| _ -> failwith "parse_tree.ml (shared variables): bad 'by' structure"
				in List.iter get_variable bylst
			| _ ->  failwith "parse_tree.ml : bad AST" 

(** Apply a transformation to all expressions *)
(** The function f will be replaced by sanitise_logic in the main*)
let transform_expressions f = function
  | Sias (enums, macros, shared_vars, Primitives ints, composites) ->
    let hlp = function  
      | Primitive i -> 
        Primitive {i with 
          (* transform init clause *)
          init = 
            begin match i.init with Init xp -> Init (f xp) 
            | _-> failwith "transform_expressions / on init" end;
					(* transform invariant clause *)
          invariant = 
            begin match i.invariant with Invariant xp -> Invariant (f xp) 
            | _-> failwith "transform_expressions / on invarint" end;
	        (* transform semantic conditions *)
          transitions = 
            let insem = function
              | Semantic(typ, xp) -> Semantic(typ, f xp)
              | _-> failwith "transform_expressions / insem" 
            in let dosems = List.map insem 
            in let intrans = function
              | Transition (t, n, a, p, l) -> Transition (t, n, a, p, dosems l)
              | _-> failwith "transform_expressions / intrans" 
            in begin match i.transitions  with 
            | Transitions transl -> Transitions (List.map intrans transl)
            | _-> failwith "transform_expressions / on transitions" end
        } 
      | _ -> failwith "transform_expressions / hlp"
    in Sias (enums, macros, shared_vars, Primitives (List.map hlp ints), composites)
    | _ -> failwith "transform_expressions"


(** Expression transformer: replaces fancy constructions by simpler ones.
- replaces a <==> b <==> c by a <==> b & b <==> c 
*)

let sanitise_logic exp = 
  let rec sub = function
  (* aRbRcRd ==> aRb & [rec rest] *)
  | Binary_op(BOP_equivalent, a, 
      ((Binary_op(BOP_equivalent, b, 
        Binary_op(BOP_equivalent, c, d))) as rest)) -> 
    Binary_op(BOP_and, Binary_op(BOP_equivalent, sub a, sub b), sub rest)
  (* aRbRd ==> aRb & bRd *)
  | Binary_op(BOP_equivalent, a, 
      Binary_op(BOP_equivalent, b, c)) -> 
    let subb = sub b in
    Binary_op(BOP_and, 
      Binary_op(BOP_equivalent, sub a, subb),
      Binary_op(BOP_equivalent, subb, sub c))
  (* preserve other expressions *)
  | Binary_op(b, l, r) -> Binary_op(b, sub l, sub r)
  | Unary_op(u, e) -> Unary_op(u, sub e)
  | Conditional (c, t, f) -> Conditional(sub c, sub t, sub f)
	| Parenthesed_xp e -> Parenthesed_xp (sub e)
  | x -> x
  in sub exp



	(** Get a compact, prefixed representation of an expression *)
let string_of_xp xp = 
  let rec sub = function
	| Parenthesed_xp e -> spf "(%s)" (sub e) 
  | Binary_op(b, l, r) -> spf "(%s %s %s)" (glyph_of_binop b) (sub l) (sub r) 
  | Unary_op(u, e) ->  spf "%s%s" (glyph_of_unop u) (sub e) 
  | Conditional (c, t, f) -> spf "(if %s %s %s)" (sub c) (sub t) (sub f) 
	| Unchanged l -> spf "(unchanged %s)" (string_of_string_list (List.map uw_id l))
  | Id id -> id
  | Symbol s -> "`" ^ s
  | True -> "#t"
  | False -> "#f"
  | Natural n -> soi n
  | Real r -> sof r
  | State s -> spf "\"%s\"" s
  | _ -> print ~prefix:"string_of_xp error> " xp; "$"
  in sub xp

(** Signals that a typing error has been detected. Increases error count *)
let signal_typerr msg xp = 
  error "*type checking*" "%s\n" msg;
  epf "  In XP: %s\n" (string_of_xp xp)
	
	
	(** Return the type of an expression. Count and print errors as a side effect *)
let type_xp symbs xp enum_types = 
  let rec typ = function
	| Parenthesed_xp e ->  typ e
  | Binary_op(b, l, r) as x -> 
    let tl, tr = typ l, typ r in
    let stl, str = map_pair string_of_var_type (tl, tr) in
    let gb = glyph_of_binop b in
    (* check that operands are compatible *)
    begin if tl <> tr
    then 
			begin
      match tl, tr with
      | VT_enum tl, VT_enum tr -> 
        if tl <> tr then 
	  			signal_typerr (va "incompatible enumerations: (%s, %s)" stl str) x;
      | _ -> signal_typerr (va "mismatched operand types: (%s, %s)" stl str) x;
      end
    end;
    (* Here is the case where the types of l and r are the same *)
    begin match b with
    | BOP_equals | BOP_differs -> 
      VT_bool
      
    | BOP_less | BOP_greater | BOP_less_eq | BOP_greater_eq ->
      begin if tl <> VT_int && tl <> VT_real
      then signal_typerr (va "operator %s expected numericals, got %s" gb stl) x
      end; VT_bool
    
    | BOP_plus | BOP_minus | BOP_times | BOP_divide ->
      begin if tl <> VT_int && tl <> VT_real
      then signal_typerr (va "operator %s expected numericals, got %s" gb stl) x
      end; (match tl with VT_real -> tl | _ -> VT_int)

    | BOP_and | BOP_or | BOP_implies | BOP_equivalent ->
      begin if tl <> VT_bool
      then signal_typerr (va "operator %s expected bool, got %s" gb stl) x
      end; VT_bool
    end

  | Unary_op(u, e) as x -> 
      let te = typ e in
      let ste = string_of_var_type te in
      let gu = glyph_of_unop u in
			begin match u with
			| UOP_not ->
	  			begin if te <> VT_bool
	  						then signal_typerr (va "unary operator ~ expected bool, got %s" ste) x
	 				end; VT_bool 
			| UOP_plus | UOP_minus ->
	  			begin if te <> VT_int && te <> VT_real
	  						then signal_typerr (va "unary operator %s expected a numerical, got %s" gu ste) x
	  			end; te
      end

  | Conditional (c, t, f) as x -> 
      let tt, tf, tc = typ t, typ f, typ c in
      let stt, stf, stc = map_triple string_of_var_type (tt, tf, tc) in
			begin if tc <> VT_bool
						then signal_typerr (va "condition must be boolean, got %s" stc) x
						else if tt <> tf & not (is_enum_type tt && is_enum_type tf)
								 then signal_typerr (va "mismatched conditional types: (%s, %s)" stt stf) x
			end;
			begin match tt , tf with 
				|  VT_enum t , VT_enum f -> 
					if t <> f then
						signal_typerr (va "mismatched conditional enumeration types: (%s, %s)" t f) x
				| _ -> ()
			end ;
			tt
	| Unchanged l -> VT_bool
  | True | False -> VT_bool
  | Natural n -> VT_int
  | Real r -> VT_real
  | Id id -> 
      begin try 
						begin match H.find symbs id with
	  					| VT_interval _ -> VT_int  
							| x -> x 
						end
      			with Not_found -> 
					      error "type_xp" "untyped identifier '%s'; assuming int\n" id; 
					      (*failwith "type_xp / untyped id" *) VT_int
    	end
  (* | State s -> VT_state (* correctness of state affectation will ve checked later on *)*)
  | Symbol s -> 
		let assoc = hassoc enum_types in
		let tp = ref "" in 
		let observe_one_type (t, lv)  = 
			if List.exists (fun x -> x = s) lv then
				tp :=  t in 
		List.iter observe_one_type assoc ; 
		begin if !tp = "" then 
			 error "type_xp" "undefined enumeration value '%s'\n" s
		end  ;
		VT_enum !tp
  | x -> 
      error "type_xp" "unexpected node"; 
      print x ~prefix:"failed type> "; 
      failwith "type_xp / unexpected node"
    in typ xp
		
(** Check that a semantic condition is a correctly-typed boolean expression *)
let check_semantic_xp enum_types symbs xp = 
  if type_xp symbs xp enum_types <> VT_bool
  then signal_typerr "semantic should be a boolean expression" xp


(** Unwrap interface *)
let uw_primitive = function
  | Primitive i -> i
  | _ -> failwith "uw_interface"

let uw_shared = function
  | Shared shvars -> shvars
  | _ -> failwith "uw_shared"
  
(** Unwrap arrow *)
let uw_arrow = function
  | Arrow (o, t) -> (o, t)
  | _ -> failwith "uw_arrow"

(** Unwrap transition *)
let uw_transition = function
  | Transition (t, n, a, p, sems) -> (t, n, a, p, sems)
  | _ -> failwith "uw_transition"

(** Unwrap parameters *)
let uw_parameters = function
  | Parameters (inp,out) -> (inp,out)
  | _ -> failwith "uw_parameters"


(** extract primitive interface from specification *)
let extract_interface iname = function
  | Sias (_, _, _,Primitives is, _) ->
    let sel inter = (uw_primitive inter).name = iname in
    uw_primitive @@ List.find sel is
  | _ -> failwith "extract_interface"

let extract_shared = function
  | Sias (_, _, sharedvars,_ , _) -> sharedvars 
  | _ -> failwith "extract_shared"

(** Unwrap local variables *)
let uw_locals = function
  | Locals l -> l
  | _ -> failwith "uw_locals"
  
(** Unwrap init clause *)
let uw_init = function
  | Init i -> i
  | _ -> failwith "uw_init"

(** Unwrap initial clause *)
let uw_initial = function
  | Initial i -> i
  | _ -> failwith "uw_initial"

(** Unwrap invariant clause *)
let uw_invariant = function
  | Invariant i -> i
  | _ -> failwith "uw_invariant"
  


(** Unwrap state name *)
let uw_state = function
  | State s -> s
  | _ -> failwith "uw_state"
  
(** Unwrap states list *)
let uw_states = function
  | States l -> l
  | _ -> failwith "uw_states"

  
(** Unwrap Inputs/Outputs/Hiddens transition wrappers *)
let uw_transw = function
  | Inputs i | Outputs i | Hiddens i -> i
  | _ -> failwith "uw_transw"
  
(** Unwrap transitions *)
let uw_transitions = function
  | Transitions l -> l
  | _ -> failwith "uw_transitions"

(** Unwrap semantic *)
let uw_semantic = function
  | Semantic (t,xp) -> (t, xp)
  | _-> failwith "uw_semantic"
   

(** Unwrap semantic (get xp) *)
let uw_semantic_xp = function
  | Semantic (_,xp) -> xp
  | _-> failwith "uw_semantic_xp"

(** Unwrap composites *)
let uw_composites = function
  | Composites cl -> cl
  | _-> failwith "uw_composites"

(** Unwrap composite interface name *)
let uw_composite = function
  | Composite (nc,_) -> nc
  | _-> failwith "uw_composite"

(** Unwrap variable name *)
let uw_variable_name = function
  | Variable (n, _) -> n
  | _ -> failwith "uw_variable_name"
	
	
(** Unwrap a variable and its type*)
let uw_vartype = function
  | Variable (id,ty) -> (id, string_of_var_type ty)
  | _ -> failwith "uw_vartype"

(** get a string representing a variable *)
let printvar = function
  | Variable (id, ty) -> spf "%s : %s" id (string_of_var_type ty)
  | _-> failwith "printvar"

let printstr str = spf "%s" str

let typecheck_lvl0 = function 
  | Sias (Enumeration_types enums, _, sharedvars, Primitives primitives, Composites composites) ->
    (* check that types of propositionnal expressions are correct *)
	let type_check_xps primitive = (* basic typechecking *)
	let glosymbs = get_symbols_table (primitive, sharedvars) in
(*	let shared_variables = get_shared_vars  (primitive, sharedvars) in*)
	let local_variables = get_local_vars primitive in
	let chker inps outs = 
	    let tbl = H.copy glosymbs in
		(* pour_symbols for parameters *)
		pour_symbols "parameters" tbl (inps @< outs) ;
		check_semantic_xp (get_enumeration_types enums) tbl
	in
	let check_nonvariable_presence slvars xp =
		let rec sub = function
			| Parenthesed_xp e -> sub e
	    | Binary_op(_, Id l, r) ->
		if H.mem slvars l = false then
		  error "*invariant/init error*" "the identifier '%s' is not a shared or local variable of '%s'\n" 
		  l (uw_primitive primitive).name ;
		  sub r
	    | Binary_op(_, l, Id r)  ->
		sub l ;
		if  H.mem slvars r = false then
		  error "*invariant/init error*" "the identifier '%s' is not a shared or local variable of '%s'\n" 
		  r (uw_primitive primitive).name 
	    | Binary_op(_, l, r) -> sub l; sub r
	    | Unary_op(u, Id e) ->  
		if H.mem slvars e = false then 
		  error "*invariant/init error*" "the identifier '%s' is not a shared or local variable of '%s'\n" 
		  e (uw_primitive primitive).name
	    | Unary_op(_, e) ->  sub e
	    | Conditional (c, t, f) -> sub c; sub t; sub f
	    | _ -> ()
	    in sub xp
	in
	let check_param_presence inps outs typxp xp  =
		let pars = hashset_of_list @@ List.map uw_variable_name (inps @< outs) in
	  let rec sub = function
	    | Binary_op(_, Id l, r) ->
		if H.mem pars l then
		  error "*semantic error*" "the parameter '%s' is used in '%s' in '%s'\n" 
		  l (string_of_semantic typxp) (uw_primitive primitive).name ;
		  sub r 
	    | Binary_op(_, l, Id r)  ->
		sub l ;
		if  H.mem pars r then
		  error "*semantic error*" "the parameter '%s' is used in '%s' in '%s'\n" 
		  r (string_of_semantic typxp) (uw_primitive primitive).name   
	    | Binary_op(_, l, r) -> sub l; sub r
	    | Unary_op(u, Id e) ->  
		if H.mem pars e then 
		  error "*semantic error*" "the parameter '%s' is used in '%s' in '%s'\n" 
		  e (string_of_semantic typxp) (uw_primitive primitive).name
	    | Unary_op(_, e) ->  sub e
	    | Conditional (c, t, f) -> sub c; sub t; sub f
	    | _ -> ()
	    in sub xp
	in
	let check_localvars_presence lvars typxp xp  =
	  let rec sub = function
			| Parenthesed_xp e -> sub e
	    | Binary_op(_, Id l, r) ->
		if H.mem lvars l then
		  error "*semantic error*" "the local variable '%s' is used in '%s' in '%s'\n" 
		  l (string_of_semantic typxp) (uw_primitive primitive).name ;
		  sub r
	    | Binary_op(_, l, Id r)  ->
		sub l ;
		if  H.mem lvars r then
		  error "*semantic error*" "the local variable '%s' is used in '%s' in '%s'\n" 
		  r (string_of_semantic typxp) (uw_primitive primitive).name 
	    | Binary_op(_, l, r) -> sub l; sub r
	    | Unary_op(u, Id e) ->  
		if H.mem lvars e then 
		  error "*semantic error*" "the local variable '%s' is used in '%s' in '%s'\n" 
		  e (string_of_semantic typxp) (uw_primitive primitive).name
	    | Unary_op(_, e) ->  sub e
	    | Conditional (c, t, f) -> sub c; sub t; sub f
	    | _ -> ()
	    in sub xp
	in
(*	let check_sharedvars_presence svars typxp xp  =                                   *)
(*	  let rec sub = function                                                          *)
(*			| Parenthesed_xp e -> sub e                                                   *)
(*	    | Binary_op(_, Id l, r) ->                                                    *)
(*		if H.mem svars l then                                                           *)
(*		  error "*semantic error*" "the shared variable '%s' is used in '%s' in '%s'\n" *)
(*		  l (string_of_semantic typxp) (uw_primitive primitive).name ;                  *)
(*		  sub r                                                                         *)
(*	    | Binary_op(_, l, Id r)  ->                                                   *)
(*		sub l ;                                                                         *)
(*		if  H.mem svars r then                                                          *)
(*		  error "*semantic error*" "the shared variable '%s' is used in '%s' in '%s'\n" *)
(*		  r (string_of_semantic typxp) (uw_primitive primitive).name                    *)
(*	    | Binary_op(_, l, r) -> sub l; sub r                                          *)
(*	    | Unary_op(u, Id e) ->                                                        *)
(*		if H.mem svars e then                                                           *)
(*		  error "*semantic error*" "the shared variable '%s' is used in '%s' in '%s'\n" *)
(*		  e (string_of_semantic typxp) (uw_primitive primitive).name                    *)
(*	    | Unary_op(_, e) ->  sub e                                                    *)
(*	    | Conditional (c, t, f) -> sub c; sub t; sub f                                *)
(*	    | _ -> ()                                                                     *)
(*	    in sub xp                                                                     *)
(*	in                                                                                *)
	let insem inps outs =
	  let chk = chker inps outs in 
	  let chkpp =  check_param_presence inps outs in
		let chklv =  check_localvars_presence local_variables in
(*	  let chksv =  check_sharedvars_presence shared_variables in*)
	  function
	    | Semantic (typ, xp) -> chk xp; 
				(
					match typ with
		  		 	| SEM_transpred ->  chkpp typ xp
		       	| _ -> ()
	      );
				(
					match typ with
		  			| SEM_pre | SEM_post -> 
				        chklv typ xp
						| _ -> ()
	      ); 
(*				(                                                                      *)
(*					match typ with                                                       *)
(*		  			| SEM_preshared | SEM_postshared | SEM_preparam | SEM_postparam -> *)
(*				        chklv typ xp                                                   *)
(*						| _ -> ()                                                          *)
(*	      );                                                                     *)
	    | _ -> failwith "typecheck_lvl0 / insem"
	in let dosems i o = List.iter (insem i o) 
	in  
	let ininvandinit = check_nonvariable_presence glosymbs 
	in
	(* lists of declared transitions *)
	let dinputs, doutputs, dhiddens =
	let i = uw_primitive primitive in
	      map_triple (List.map uw_id) (map_triple uw_transw (i.inputs, i.outputs, i.hiddens))
	in 
	(* check that transition names are not declared several times *)
	let conflicts = remove_duplicates @@ list_duplicates (dinputs @< doutputs @< dhiddens) in
	let signal_conflict trans = 
	    error "*transitions*" "transition name '%s' is declared several times in interface %s\n" 
		  trans (uw_primitive primitive).name
	in List.iter signal_conflict conflicts;
	(* check that transitions have been declared *)
	let used_trans_names = ref [] in
	let chktr i l n = 
	  push n used_trans_names;
	  if not (List.mem n l)
	  then error "*transitions*" "transition '%s' was not declared in interface %s\n" n i
	in
	(* check that used states have been defined *)
	let states = match (uw_primitive primitive).states with States l -> l
	      |_-> failwith "typecheck_lvl0 / check_states" in
	let statess = hashset_of_list @@ List.map uw_state states 
	in
	let check_states states arrows = 
	  let sub = function
	    | Arrow (src, des) ->
	      if not (H.mem states src) then 
		  error "*transitions*" "state \"%s\" is undeclared in the interface '%s'\n" 
		  src ((uw_primitive primitive).name);
	      if not (H.mem states des) then
		  error "*transitions*" "state \"%s\" is undeclared in the interface '%s'\n" 
		  des ((uw_primitive primitive).name)
	    | _-> ()
	  in List.iter sub arrows
	in
	let intrans iname = function
	    | Transition (typ, n, ars, Parameters (i, o), l) ->
		chktr iname (* first parameter of chktr *)
		(match typ with
		  | AS_input -> dinputs
		  | AS_output -> doutputs
		  | AS_hidden -> dhiddens
		) (* second parameter of chktr *)
		n ; (* third parameter of chktr *)
		dosems i o l ;
		check_states statess ars
	    | _-> failwith "typecheck_lvl0 / intrans"
	in 
	begin match (uw_primitive primitive).transitions  with
	| Transitions transl ->
	 let iname = (uw_primitive primitive).name in
	    List.iter (intrans iname) transl;
	    let overused = remove_duplicates @@ list_duplicates !used_trans_names in
	    let chkover name = 
		error "*transitions*" 
		      "transition name '%s' is used several times in interface %s\n" 
		      name iname
	    in List.iter chkover overused
	| _-> failwith "typecheck_lvl0 / on transitions" end; 
	begin match (uw_primitive primitive).invariant  with
	| Invariant inv  -> ininvandinit  inv
	| _-> failwith "typecheck_lvl0 / on invariant" end;	
	begin match (uw_primitive primitive).init  with
	| Init ini  -> ininvandinit  ini
	| _-> failwith "typecheck_lvl0 / on init" end;
	in List.iter type_check_xps primitives ;

(* check composites correctness *)
    
	(** check that composite components names contains subcomponents names that 
	are already defined as composite or primitive *)

  let rec get_subcomps_names = function 
		 | Id ascomp :: tail -> ascomp :: get_subcomps_names tail
		 | _ :: tail -> get_subcomps_names tail
		 | [] -> []  
	in 
	let get_comp_prim_interface_names prims comps = 
	    let itab = H.create 10 in
	    let add_prims = function Primitive i -> 
	      ( 
					match hfind'o itab i.name with
		  		| Some presi -> 
		      		error "*specifiation error*"
			    					"the interface name '%s' is already used.\n" i.name
		  		| None -> H.replace itab i.name []
	      )
	      | _ -> ()
	    in List.iter add_prims prims ;
	    let add_comps = function Composite (name, subcomps) -> 
	      (
					match hfind'o itab name with
		  		| Some presi -> 
		      		error "*specifiation error*"
			    					"the interface name '%s' is already used.\n" name
		  		| None -> H.replace itab name (get_subcomps_names subcomps)
	      )
	      | _-> ()
	    in List.iter add_comps comps ; itab 
	in 
	let ints = get_comp_prim_interface_names primitives composites in
	let allnames = hkeys ints in	
	let check_subcomp_names_onecomp name subcomps = 
	  begin if  not (list_included subcomps allnames) then
				error "*composite consistency*"
		      		"some subcomponent interfaces of '%s' are not defined as primitive or composite:\n" name ;      
				let prnt i = epf "  Interface: %s\n" i
				in List.iter prnt (lists_diff subcomps allnames)
		end
	  in H.iter check_subcomp_names_onecomp ints ;
	let all_subcomps_lists = hvalues ints in
	let check_double_declaration l1 =
		let with_others l2 =
			begin if not (lists_equivalent l1 l2) && List.length (lists_intersection l1 l2) <> 0 then
							let prnt i = epf "  Interface: %s\n" i in 
									error "*composite consistency*"
		          					"some interfaces are declared as subcomponent in several composite interfaces:\n";
		  			      List.iter prnt (lists_intersection l1 l2)
			      end
	  in List.iter with_others all_subcomps_lists
	in List.iter check_double_declaration all_subcomps_lists ;
	(* check that shared variables are well declared *)
	let get_prim_ints ht = 
	let rec prim = function 
	  | (intr, []) :: tail -> intr :: prim tail
	  | (_, sb :: tsb) :: tail -> prim tail
	  | [] -> []
	in prim (hassoc ht)
	in 
	let prim = get_prim_ints ints in 
	let get_by_ints = function By (_, li) -> uw_list_ids li  | _ -> failwith "typecheck_lvl0 / get_by_ints" in
	let get_by_vars = function By (vars, _) -> vars | _ -> failwith "typecheck_lvl0 / get_by_vars" in
	let check_one_by aby = 
	      if not (list_included (get_by_ints aby) prim) then
		error "*shared consistency*" 
		      "%s are shared by non primitive or undeclared interfaces:\n" 
		      (pretty_print_list printvar ", " "[" "]" (get_by_vars aby)) ;
		      let _prnt i = epf "  Interface: %s\n" i
		      in List.iter _prnt (lists_diff (get_by_ints aby) prim)
	in List.iter check_one_by (uw_shared sharedvars) ;

	if !_errors <> 0 then epf "\nTotal: %d errors\n" !_errors
      
  | _ -> failwith "typecheck_lvl0"


(* let tes inps outs = error "kk" "%s\n" (pretty_print_list printstr ", " "[" "]" (List.map uw_variable_name (inps @< outs))) in *)

(** {6 Extractors and high-level manipulation} *)

(** find value of state variable in an expression *)
(*let find_state var xp =                                           *)
(*  let rec sub var = function                                      *)
(*	| Parenthesed_xp e  ->  sub var e                               *)
(*  | Binary_op(BOP_equals, Id i, State s)                          *)
(*  | Binary_op(BOP_equals, State s, Id i) when i = var -> s        *)
(*  | Binary_op(BOP_and, l, r) -> (try sub var l with _-> sub var r)*)
(*  | _ -> failwith ("find_state" ^ (string_of_xp xp))              *)
(*  in sub var xp                                                   *)

(** Take the semantic expression of a given nature from a list of semantics *)
let get_sem typ sems = 
  let isok sem = 
    let t, _ = uw_semantic sem in t = typ
  in uw_semantic_xp @@ List.find isok sems


(** Get origin and target states of a given transition *)
let _state = "state"