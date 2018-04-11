open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let parse_check s e =
  match s with
  | "z"  -> e == 0
  | "nz" -> e <> 0
  | s -> failwith @@ "Unknown condition " ^ s

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' ->
    (match insn with
      | BINOP op -> let y::x::stack' = stack in eval env (cstack, Expr.to_func op x y :: stack', c) prg'
      | READ     -> let z::i'        = i     in eval env (cstack, z::stack, (st, i', o)) prg'
      | WRITE    -> let z::stack'    = stack in eval env (cstack, stack', (st, i, o @ [z])) prg'
      | CONST i  -> eval env (cstack, i::stack, c) prg'
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) prg'
      | ST x     -> let z::stack' = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
      | LABEL _  -> eval env conf prg'
      | JMP   l  -> eval env conf (env#labeled l)
      | CJMP (s, l) ->
        let z::stack' = stack in
          eval env conf (
            if (parse_check s z)
            then (env#labeled l)
            else prg')
      | CALL f   -> eval env ((prg', st)::cstack, stack, c) (env#labeled f)
      | BEGIN (args, locals) ->
        let rec resolve builder args stack = 
        (match args, stack with
          | [], _ -> List.rev builder, stack
          | a::args', s::stack' -> resolve ((a, s)::builder) args' stack') in
        let resolved, stack' = resolve [] args stack in
        let state_to_eval = (List.fold_left (fun s (x, v) -> State.update x v s) (State.enter st (args @ locals)) resolved, i, o) in
        eval env (cstack, stack', state_to_eval) prg'
      | END -> match cstack with
        | (prg', st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) prg'
        | [] -> conf
    ) 

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class env =
	object (self)
		val mutable label = 0
		method get_label = let last_label = label in
			label <- label + 1; Printf.sprintf "L%d" last_label
	end

let rec compile' env p =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  match p with
    | Stmt.Seq (s1, s2)  ->
        let conf = compile' env s1 in
        let conf' = compile' env s2 in
        conf @ conf'
    | Stmt.Read x        -> [READ; ST x]
    | Stmt.Write e       -> expr e @ [WRITE]
    | Stmt.Assign (x, e) -> expr e @ [ST x]
    | Stmt.Skip          -> []
    | Stmt.If (e, s1, s2)->
        let firstL = env#get_label in
        let secondL = env#get_label in
        let c1 = compile' env s1 in
        let c2 = compile' env s2 in
        (expr e @ [CJMP ("z", firstL)] @ c1 @ 
          [JMP secondL; LABEL firstL] @ c2 @ [LABEL secondL])
    | Stmt.While (e, s)  ->
        let firstL = env#get_label in
        let secondL = env#get_label in
        let c1 = compile' env s in
        ([JMP firstL] @ [LABEL secondL] @ c1 @
          [LABEL firstL] @ expr e @ [CJMP ("nz", secondL)])
    | Stmt.Repeat (s, e) ->
        let firstL = env#get_label in
        let c1 = compile' env s in
        ([LABEL firstL] @ c1 @ expr e @ [CJMP ("z", firstL)])
    | Stmt.Call (f, p)    -> List.concat (List.map expr p) @ [CALL f]
    | Stmt.Return None  -> [] @ [END]
    | Stmt.Return Some v -> (expr v) @ [END]

let cproc env (f_name, (args, l_var, body)) =
  [LABEL f_name; BEGIN (args, l_var)] @ compile' env body @ [END]

let compile (defs, prog) = let env = new env in
  let e_label = env#get_label in
  [JMP e_label] @ List.concat (List.map (cproc env) defs)
    @ [LABEL e_label] @ compile' env prog