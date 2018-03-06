open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let eval_insn config insn =
	match config, insn with
		| (y::x::stack, conf), BINOP op -> ((Syntax.Expr.calc op x y)::stack, conf)
		| (stack, conf), CONST z -> (z::stack, conf)
		| (stack, (s, z::i, o)), READ -> (z::stack, (s, i, o))
		| (z::stack, (s, i, o)), WRITE -> (stack, (s, i, o @ [z]))
		| (stack, (s, i, o)), LD var -> ((s var)::stack, (s, i, o))
		| (z::stack, (s, i, o)), ST var -> (stack, (Syntax.Expr.update var z s, i, o))
		| _, _ -> failwith "Not yet implemented"

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
 let rec eval config prog =
	match config, prog with
		| c, insn::p -> eval (eval_insn c insn) p
		| c, [] -> c 

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o
(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec c_expr = function
	| Syntax.Expr.Const z -> [CONST z]
	| Syntax.Expr.Var var -> [LD var]
	| Syntax.Expr.Binop (op, x, y) -> c_expr x @ c_expr y @ [BINOP op]
  
let rec compile (stmt: Syntax.Stmt.t) : prg =
	match stmt with
		| Syntax.Stmt.Read var -> [READ ; ST var]
		| Syntax.Stmt.Write expr -> c_expr expr @ [WRITE]
		| Syntax.Stmt.Assign (var, expr) -> c_expr expr @ [ST var]
		| Syntax.Stmt.Seq (expr1, expr2) -> compile expr1 @ compile expr2
