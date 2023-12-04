%{

(** ********************************************************************* *)
(** lSIA: Language for implementing Semantical Interface Automata          *)
(**                                                                       *)
(** by Sebti MOUELHI, Vincent HUGOT, Benjamin DREUX                       *)
(**                                                                       *)
(** file : lsiapar.mll : the parser                                        *)
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
open Common;;
open Parse_tree;;

(** The parser for the language *)

let pretty_pos p = 
  spf "%s:%d" p.Lexing.pos_fname p.Lexing.pos_lnum

let pretty_range i j =
  assert (i <= j);
  if i = j 
  then soi i
  else spf "%d-%d" i j

let parse_error s = 
  let lb = (opt_get !Common.the_lexbuf).Lexing.lex_buffer in
  let ss, se = symbol_start(), symbol_end() in
  epf "%s:[%s] %s after `%s'\n%!" 
    (pretty_pos (symbol_start_pos())) 
    (pretty_range ss se) 
    s (snippet (try subb lb ss se with _ -> "$subb error$" ^ lb) 50)

(** Enum types *)
let enum_types = H.create 5

(** Record types *)
let record_types = H.create 5

(** A variable type is used, which has not been previously declared *)
exception Undeclared_type of string

(** Get the enum type, or fail *)
let get_enum_type id = 
  try H.find enum_types id
  with Not_found -> raise (Undeclared_type id)

(** Get the record type, or fail *) 
let get_record_type id = 
  try H.find record_types id
  with Not_found -> raise (Undeclared_type id)

%}

/** Declarations of .mly files must start with % sign */

/** Untyped tokens */

%token EOF COMMA SEMICOLON OUTPUT INPUT HIDDEN PRIMITIVE TRANSITIONS COMPOSITE MACRO
%token PRE POST INVARIANT TRANSPRED STATES LOCAL SHARE BY COMPOSITION_OP CLOSED
%token INPUT_PARAMS OUTPUT_PARAMS INIT INITIAL
%token OPEN CLOSE OPEN_PAREN CLOSE_PAREN
%token AND OR  IMPLIES NOT IMPLIES_CONV ARROW
%token LESS GREATER LESS_EQ GREATER_EQ 
%token EQUALS DIFFERS
%token PLUS MINUS TIMES DIVIDE EQUIVALENT 
%token IN INTEGERS REALS BOOLS ENUM
%token TRUE FALSE IF THEN ELSE UNCHANGED

/** Some tokens must be typed %token < typexpr > constr . . . constr */

%token <int> NATURAL
%token <string> STRING ID SYMBOL
%token <int * int> INTERVAL
%token <float> REAL


/** LESSER PRECEDENCES */

%nonassoc ARROW
%right EQUIVALENT 
%right IMPLIES 
%left IMPLIES_CONV
%left IF_THEN_ELSE
%left OR
%left AND
%left EQUALS DIFFERS
%left LESS_EQ GREATER_EQ LESS GREATER 
%left PLUS MINUS
%left TIMES DIVIDE
%left NOT
%left UMINUS UPLUS
%left COMPOSITION_OP

/* GREATER PRECEDENCES */

%start sias
%type <Parse_tree.t> sias

%%

/** Begining of rules */

sias:
  | enumtype_decls macros shared_vars primitives composites EOF  
	    { Sias (Enumeration_types $1, Macros $2, $3, Primitives $4, Composites $5) }
  | error                                                        { failwith "Parse error" }
;

/* purely side-effect, replaced directly whithin the tree */

enumtype_decls:
  | /* empty */                                         { [] }
  | enumtype_decl enumtype_decls                        { $1 :: $2 }
;

enumtype_decl:
  | ENUM ID OPEN sym_list CLOSE                         { Enumeration_type ($2, $4) }
;




macros:
  | /* empty */                                         { [] } 
  | macro macros                                        { $1 :: $2 }
;


macro:
  | macro_type MACRO ID OPEN_PAREN 
         id_list 
    CLOSE_PAREN EQUALS expression                       { Macro($1, $3, $5, $8) }
;

macro_type:
  | CLOSED                                              { MAC_closed }
  | /* empty */                                         { MAC_open }
;

var_type:
  | BOOLS                                               { VT_bool }
  | INTEGERS                                            { VT_int }
  | REALS                                               { VT_real }
  | INTERVAL                                            { VT_interval $1 }
  | ID                                                  { VT_enum $1 }
;

/* var : type */

vars: 
  | /* empty */                                         { [] }
  | ID IN var_type vars_tail                            { Variable ($1, $3) :: $4 }
;

vars_tail:
  | /* empty */                                         { [] }
  | COMMA ID IN var_type vars_tail                      { Variable ($2, $4) :: $5 }
;


sym_list:
	| SYMBOL COMMA SYMBOL                                 { [Symbol $1 ; Symbol $3] }
  | SYMBOL COMMA sym_list                               { [Symbol $1] @> $3}


composition_list:
	| composition_list COMPOSITION_OP ID                  {$1 @> [Id $3] }
	| ID COMPOSITION_OP ID                                {[Id $1 ; Id $3]}
;   

id_list: 
  | /* empty */                                         { [] }
  | ID id_list_tail                                     { Id $1 :: $2 }
;

id_list_tail:
  | /* empty */                                         { [] }
  | COMMA ID id_list_tail                               { Id $2 :: $3 } 

/* x, y by X, Y; a, b by A, B; */


primitives:
  | /* empty */                                         { [] }
  | primitive primitives                                { $1 :: $2 }
;

composites:
  | /* empty */                                         { [] }
  | composite composites                                { $1 :: $2}
;

composite:
  | COMPOSITE ID OPEN composition_list CLOSE            { Composite($2, $4) }
;

composition_list:
	| composition_list COMPOSITION_OP ID                  {$1 @> [Id $3] }
	| ID COMPOSITION_OP ID                                {[Id $1 ; Id $3]}
;   

local_vars:
  | /* empty */                                         { Locals [] }
  | LOCAL vars                                          { Locals $2 }
;


shared_vars:
  | /* empty */                                         { Shared [] }
  | SHARE share_statement                               { Shared $2 }
;

share_statement:
  | vars BY id_list                                     { [By($1, $3)] }
  | vars BY id_list SEMICOLON share_statement           { By ($1, $3) :: $5 }
;



init_clause:
  | INIT expression                                     { Init $2 }
;

input_actions:
  | INPUT id_list                                       { Inputs $2 }
;

output_actions:
  | OUTPUT id_list                                      { Outputs $2 }
;


hidden_actions:
  | /* empty */                                         { Hiddens [] }
  | HIDDEN id_list                                      { Hiddens $2 }
;

invariant_clause:
	| INVARIANT expression                                { Invariant $2}
;
states_set:
  | STATES states_list                                  { States $2 }
;

states_list:
  | /* empty */                                         { [] }
  | STRING states_list_tail                             { State $1 :: $2}
;

states_list_tail:
  | /* empty */                                         { [] }
  | COMMA STRING states_list_tail                       { State $2 :: $3 }  
;

initial_state:
  | INITIAL STRING                                       {Initial (State $2)}
;

primitive:
  | PRIMITIVE ID OPEN 
        local_vars 
        states_set
				initial_state 
				init_clause
        input_actions output_actions hidden_actions
				invariant_clause
        TRANSITIONS transitions 
    CLOSE

    { Primitive ({
        name = $2; 
        locals = $4;  
        states = $5; 
				initial = $6 ;
        init = $7;
        inputs = $8; 
        outputs = $9; 
        hiddens = $10;
				invariant = $11 ;
        transitions = Transitions $13  
        }) 
    } 
;
  
transitions:
  | /* empty */                                         { [] }
  | transition transitions                              { $1 :: $2 }
;

arrows:
  | /* empty */                                         { [] }
  | arrow arrows                                        { $1 :: $2 }
;

arrow:
  | STRING ARROW STRING                                 { Arrow ($1, $3) }
;

transition:
  | INPUT ID arrows parameters semantics                { Transition (AS_input, $2, $3, $4, $5) }
  | OUTPUT ID arrows parameters semantics               { Transition (AS_output, $2, $3, $4, $5) }
  | HIDDEN ID arrows semantics                          { Transition (AS_hidden, $2, $3, Parameters([],[]), $4) }
;


parameters:
  | /*empty*/                                           { Parameters([],[]) }
  | INPUT_PARAMS vars SEMICOLON OUTPUT_PARAMS vars      { Parameters($2,$5) }
  | INPUT_PARAMS vars 					                        { Parameters($2,[]) }
	| OUTPUT_PARAMS vars                                  { Parameters([],$2) }
;


semantics:
  | /* empty */                                         { [] }
  | semantic semantics                                  { $1 :: $2 }
;

semantic:
  | PRE maybe_expression                                { Semantic (SEM_pre, $2) }
  | POST maybe_expression                               { Semantic (SEM_post, $2) }
	| TRANSPRED maybe_expression                          { Semantic (SEM_transpred, $2) }
;


maybe_expression:
  | expression                                          { $1 }
  | /* empty */                                         { True }
;

/* 
   Note: the expressions are not necessarily coherent; 
   it is up to type-cheking to make sure that they are 
   well-formed (ie. no 3.14 ==> 1.55 etc).
  
   This kind of task can not be done here because expression 
   "ID" could really be {i anything}, and there is no way to know.  
*/

expression:
  | ID                                                  { Id $1 }
  | SYMBOL                                              { Symbol $1 }
  | TRUE                                                { True }
  | FALSE                                               { False }
  | NATURAL                                             { Natural $1 }
  | REAL                                                { Real $1 }
  | OPEN_PAREN expression CLOSE_PAREN                   { Parenthesed_xp $2 }
  | expression AND expression                           { Binary_op (BOP_and, $1, $3) }
  | expression OR expression                            { Binary_op (BOP_or, $1, $3) }
  | NOT expression                                      { Unary_op  (UOP_not, $2) }
  | MINUS expression                                    { Unary_op  (UOP_minus, $2) }       %prec UMINUS
  | PLUS expression                                     { Unary_op  (UOP_plus, $2) }        %prec UPLUS
  | expression IMPLIES expression                       { Binary_op (BOP_implies, $1, $3) }
  | expression IMPLIES_CONV expression                  { Binary_op (BOP_implies, $3, $1) }
  | expression EQUALS expression                        { Binary_op (BOP_equals, $1, $3) }
  | expression LESS expression                          { Binary_op (BOP_less, $1, $3) }
  | expression GREATER expression                       { Binary_op (BOP_greater, $1, $3) }
  | expression LESS_EQ expression                       { Binary_op (BOP_less_eq, $1, $3) }
  | expression GREATER_EQ expression                    { Binary_op (BOP_greater_eq, $1, $3) }
  | expression DIFFERS expression                       { Binary_op (BOP_differs, $1, $3) }
  | expression EQUIVALENT expression                    { Binary_op (BOP_equivalent, $1, $3) }
  | expression PLUS expression                          { Binary_op (BOP_plus, $1, $3) }
  | expression MINUS expression                         { Binary_op (BOP_minus, $1, $3) }
  | expression TIMES expression                         { Binary_op (BOP_times, $1, $3) }
  | expression DIVIDE expression                        { Binary_op (BOP_divide, $1, $3) }
  | IF expression THEN expression ELSE expression       { Conditional ($2, $4, $6) }        %prec IF_THEN_ELSE
	| ID OPEN_PAREN expression_list CLOSE_PAREN           { Macro_call ($1, $3) }
	| UNCHANGED id_list                                   { Unchanged $2}
;

expression_list:
  | /* empty */                                         { [] }
  | expression expression_list_tail                     { $1 :: $2 }
;

expression_list_tail:
  | /* empty */                                         { [] }
  | COMMA expression expression_list_tail               { $2 :: $3 }
;

