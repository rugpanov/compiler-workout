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
type config = (prg * State.t) list * int list * Stmt.config

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

let rec eval env ((stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' -> 
    (match insn with
    | BINOP op -> let y::x::stack' = stack in eval env (Expr.to_func op x y :: stack', c) prg'
    | READ     -> let z::i'        = i     in eval env (z::stack, (st, i', o)) prg'
    | WRITE    -> let z::stack'    = stack in eval env (stack', (st, i, o @ [z])) prg'
    | CONST i  -> eval env (i::stack, c) prg'
    | LD x     -> eval env (st x :: stack, c) prg'
    | ST x     -> let z::stack'    = stack in eval env (stack', (Expr.update x z st, i, o)) prg'
    | LABEL _  -> eval env conf prg'
    | JMP   l  -> eval env conf (env#labeled l)
    | CJMP (s, l) ->
      let z::stack' = stack in
        eval env conf (
          if (parse_check s z)
          then (env#labeled l)
          else prg')
    ) 

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
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
    object(self)
        val cnt = 0
        method get_label = "l" ^ string_of_int cnt, {<cnt = cnt + 1>}
    end

let rec compile' env =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  ->
      let env, conf = compile' env s1 in
      let env, conf' = compile' env s2 in
      env, conf @ conf'
  | Stmt.Read x        -> env, [READ; ST x]
  | Stmt.Write e       -> env, expr e @ [WRITE]
  | Stmt.Assign (x, e) -> env, expr e @ [ST x]
  | Stmt.Skip          -> env, []
  | Stmt.If (e, s1, s2)->
      let firstL, env = env#get_label in
      let secondL, env = env#get_label in
      let env, c1 = compile' env s1 in
      let env, c2 = compile' env s2 in
      env, (expr e @ [CJMP ("z", firstL)] @ c1 @ 
        [JMP secondL; LABEL firstL] @ c2 @ [LABEL secondL])
  | Stmt.While (e, s)  ->
      let firstL, env = env#get_label in
      let secondL, env = env#get_label in
      let env, c1 = compile' env s in
      env, ([JMP firstL] @ [LABEL secondL] @ c1 @
        [LABEL firstL] @ expr e @ [CJMP ("nz", secondL)])
  | Stmt.Repeat (s, e) ->
      let firstL, env = env#get_label in
      let env, c1 = compile' env s in
      env, ([LABEL firstL] @ c1 @ expr e @ [CJMP ("z", firstL)])

let compile prg =
  let env, res = compile' (new env) prg in res