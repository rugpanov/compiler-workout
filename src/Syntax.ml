(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

	let get_bool value = if value = 0 then false else true
 
	let calc opstr v1 v2=
		match opstr with 
			| "+" -> v1 + v2
			| "-" -> v1 - v2
			| "*" -> v1 * v2
			| "/" -> v1 / v2
			| "%" -> v1 mod v2
			| "<" -> if v1 < v2 then 1 else 0
			| "<=" -> if v1 <= v2 then 1 else 0
			| ">" -> if v1 > v2 then 1 else 0
			| ">=" -> if v1 >= v2 then 1 else 0
			| "==" -> if v1 = v2 then 1 else 0
			| "!=" -> if v1 <> v2 then 1 else 0
			| "&&" -> if get_bool v1 && get_bool v2 then 1 else 0
			| "!!" -> if get_bool v1 || get_bool v2 then 1 else 0
			| _ -> failwith @@ Printf.sprintf "Unknown op: %s" opstr
	
	let rec eval state expression = 
		match expression with
			| Const (value) -> value
			| Var (value) -> state value
			| Binop (opstr, exp1, exp2) -> let v1 = eval state exp1 and v2 = eval state exp2 in calc opstr v1 v2 
  

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
	let rec eval config stmt =	
		match config, stmt with
			| (s, z::i, o), Read var -> (Expr.update var z s, i, o)
			| (s, i, o), Write expr -> (s, i, o @ [Expr.eval s expr])
			| (s, i, o), Assign (var, expr) -> (Expr.update var (Expr.eval s expr) s, i, o)
			| conf1, Seq (s1, s2) -> eval (eval conf1 s1) s2
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
