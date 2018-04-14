(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}
  
    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}


    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}


    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)

    let enter st xs = {empty with g = st.g; scope = xs}


    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator
      val eval : env -> config -> t -> int * config
      Takes an environment, a configuration and an expresion, and returns another configuration. The 
      environment supplies the following method
      method definition : env -> string -> int list -> config -> config
      which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
      an returns resulting configuration
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
     
    let rec eval env ((st, i, o, r) as conf) expr =      
      match expr with
      | Const n -> n, conf
      | Var   name -> State.eval st name, conf
      | Binop (op, x, y) ->
        let p1, ((st, i, o, r) as conf) = eval env conf x in 
        let p2, ((st, i, o, r) as conf) = eval env conf y in 
        (to_func op) p1 p2, conf
      | Call (funct, params) ->
        let process_with_conf (conf, list) e = (let v, conf = eval env conf e in conf, list @ [v]) in
        let conf, updated_params = List.fold_left process_with_conf (conf, []) params in
        let ((st, i, o, r) as conf) = env#definition env funct updated_params conf in
        (match r with
          | None -> failwith "Void return"
          | Some v -> v
        ), conf

         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr (fun x -> x)
	    (Array.map (fun (a, s) -> a, List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s) 
              [|                
                `Lefta, ["!!"];
                `Lefta, ["&&"];
                `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
                `Lefta, ["+" ; "-"];
                `Lefta, ["*" ; "/"; "%"];
              |] 
	    )
	    primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT p:("(" params:!(Util.list0 parse) ")" {Call (x, params)} | empty {Var x}) {p}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let process_seq p1 p2 =
      match p1, p2 with
      | Skip, p -> p
      | p, Skip -> p
      | p1', p2'  -> Seq (p1', p2')

    let rec eval env ((st, i, o, r) as conf) k stmt = 
      match stmt with
      | Read    x           -> eval env (match i with z::i' -> (State.update x z st, i', o, None) | _ -> failwith "Why is here end of input") Skip k
      | Write   e           -> 
                let value, (st, i, o, _) = Expr.eval env conf e in
                eval env (st, i, o @ [value], None) Skip k
      | Assign (x, e)       ->
                let value, (st, i, o, _) = Expr.eval env conf e in
                eval env (State.update x value st, i, o, None) Skip k
      | Seq    (s1, s2)     -> eval env conf (process_seq s2 k) s1
      | Skip                -> if k = Skip then (st, i, o, None) else eval env conf Skip k
      | If     (e, s1, s2)  -> let value, conf = Expr.eval env conf e in eval env conf k (if value <> 0 then s1 else s2)
      | While  (e, s)       -> (
        let value, conf = Expr.eval env conf e in 
        if (value <> 0)
        then eval env conf (process_seq stmt k) s
        else eval env conf Skip k)
      | Repeat (s, e)       -> eval env conf (process_seq (While ((Expr.Binop ("==", e, Expr.Const 0)), s)) k) s 
      | Call (f, params)    ->
        let process_with_conf (conf, list) e = (let v, conf = Expr.eval env conf e in conf, list @ [v]) in
        let conf, updated_params = List.fold_left process_with_conf (conf, []) params in
        eval env (env#definition env f updated_params conf) Skip k
      | Return Some ex      ->  let v, (st, i, o, _) = Expr.eval env conf ex in (st, i, o, Some v)
      | Return None         -> (st, i, o, None)

    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;

      else_branch:
        %"elif" e:!(Expr.parse) %"then" s1:parse s2:else_branch {If (e, s1, s2)}
      | %"else" s:parse {s}
      | "" {Skip};
      
      stmt:
        "read" "(" x:IDENT ")"                                                {Read x}
      | "write" "(" e:!(Expr.parse) ")"                                       {Write e}
      | x:IDENT ":=" e:!(Expr.parse)                                          {Assign (x, e)}
      | %"skip"                                                               {Skip}
      | %"while" e:!(Expr.parse) %"do" s:parse %"od"                          {While (e, s)}
      | %"for" i:parse "," e:!(Expr.parse) "," s2:parse %"do" s1:parse %"od"  {Seq (i, While (e, Seq (s1, s2)))}
      | %"repeat" s:parse %"until" e:!(Expr.parse)                            {Repeat (s, e)}
      | %"if" e:!(Expr.parse) %"then" s1:parse s2:else_branch %"fi"           {If (e, s1, s2)}
      | %"return" e:!(Expr.parse)?                                            {Return e} 
      | f_name:IDENT "(" args:!(Util.list0)[Expr.parse] ")"                   {Call (f_name, args)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)
    
    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }

    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)

let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
