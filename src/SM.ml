open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

let init n f =
  let rec init' i n f =
    if i >= n then []
    else (f i) :: (init' (i + 1) n f)
  in init' 0 n f
  
(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)   
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
                     
let parse_check s e =
  match s with
  | "z"  -> e == 0
  | "nz" -> e <> 0
  | s -> failwith @@ "Unknown condition " ^ s

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' ->
    (match insn with
      | BINOP op -> let y::x::stack' = stack in
        eval env (cstack, (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)))::stack', c) prg'
      | CONST i  -> eval env (cstack, (Value.of_int i)::stack, c) prg'
      | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) prg'
      | SEXP (t, n) -> let elems, stack' = split n stack in eval env (cstack, (Value.sexp t (List.rev elems)) :: stack', c) prg'
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) prg'
      | ST x     -> let z::stack' = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
      | STA (x, n) -> let v::is, stack' = split (n+1) stack in 
        eval env (cstack, stack', (Stmt.update st x v @@ List.rev is, i, o)) prg'
      | LABEL _  -> eval env conf prg'
      | JMP   l  -> eval env conf (env#labeled l)
      | CJMP (s, l) ->
        let z::stack' = stack in
        eval env (cstack, stack', (st, i, o)) (
        if (parse_check s (Value.to_int z))
        then (env#labeled l)
        else prg')
      | DROP    -> let _::stack' = stack in eval env (cstack, stack', c) prg'
      | DUP     -> let a::_ = stack in eval env (cstack, a::stack, c) prg'
      | SWAP    -> let a::b::stack' = stack in eval env (cstack, b::a::stack', c) prg'
      | TAG s   -> let a::stack' = stack in
        let res = match a with
          | Value.Sexp (t, _) -> Value.of_int @@ if t = s then 1 else 0
          | _ -> Value.of_int 0
        in eval env (cstack, res::stack', c) prg'
      | ENTER xs ->
        let vs, stack' = split (List.length xs) stack in
        let state' = List.fold_left2 (fun s x v -> State.bind x v s) State.undefined xs vs in
        eval env (cstack, stack', (State.push st state' xs, i, o)) prg'
      | LEAVE   -> eval env (cstack, stack, (State.drop st, i, o)) prg'      
      | CALL (f, n, p) ->
        if env#is_label f
        then eval env ((prg', st)::cstack, stack, c) (env#labeled f)
        else eval env (env#builtin conf f n p) prg'
      | BEGIN (_, params, locals) ->
        let s1 = State.enter st (params @ locals) in
        let (st', stack') = List.fold_right (
            fun params (st, x::stack') -> (State.update params x st, stack')  
        ) params (s1, stack) in
        eval env (cstack, stack', (st', i, o)) prg'
      | RET _
      | END -> (match cstack with
        | (prg', st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) prg'
        | [] -> conf)
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

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

let compile (defs, p) =
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lf = function
  | Stmt.Pattern.Wildcard -> false, [DROP]
  | Stmt.Pattern.Ident n -> false, [DROP]
  | Stmt.Pattern.Sexp (t, ps) -> true, [DUP; TAG t; CJMP ("z", lf)] @ (List.concat @@ List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ snd @@ pattern lf p) ps)
  and bindings p =
    let rec inner = function
    | Stmt.Pattern.Ident n      -> [SWAP]
    | Stmt.Pattern.Sexp (_, ps) -> (List.flatten (List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ inner p) ps)) @ [DROP]
    | Stmt.Pattern.Wildcard     -> [DROP]
    in
    inner p @ [ENTER (Stmt.Pattern.vars p)]
  and expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String s         -> [STRING s]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, params) -> call f params false
  | Expr.Array elems      -> List.concat (List.map expr elems) @ [CALL (".array", List.length elems, false)]
  | Expr.Elem (a, i)      -> expr a @ expr i @ [CALL (".elem", 2, false)]
  | Expr.Length a         -> expr a @ [CALL (".length", 1, false)]
  | Expr.Sexp (tag, es)   -> (List.concat @@ List.map expr es) @ [SEXP (tag, List.length es)] 
  in
  let rec compile_stmt l env = function
  | Stmt.Seq (s1, s2)  ->
      let l2, env = env#get_label in
      let env, flag1, cfg = compile_stmt l2 env s1 in
      let env, flag2, cfg' = compile_stmt l env s2 in
      env, flag2, cfg @ (if flag1 then [LABEL l2] else []) @ cfg'
  | Stmt.Assign (x, [], e) -> env, false, expr e @ [ST x]
  | Stmt.Assign (x, is, e) -> env, false, List.concat (List.map expr (is @ [e])) @ [STA (x, List.length is)]
  | Stmt.Skip              -> env, false, []
  | Stmt.If (e, s1, s2)    ->
    let l2, env = env#get_label in
    let env, flag1, then_branch = compile_stmt l env s1 in
    let env, flag2, else_branch = compile_stmt l env s2 in
    env, true, (expr e @ [CJMP ("z", l2)] @ then_branch @ (if flag1 then [] else [JMP l]) @ [LABEL l2] @ else_branch @ (if flag2 then [] else [JMP l])) 
  | Stmt.While (e, s)      ->
    let labelF, env = env#get_label in
    let labelS, env = env#get_label in
    let env, _, compiled_body = compile_stmt labelF env s in
    env, false, ([JMP labelF; LABEL labelS] @ compiled_body @ [LABEL labelF] @ expr e @ [CJMP ("nz", labelS)])
  | Stmt.Repeat (s, e)     ->
    let labelF, env = env#get_label in
    let labelS, env = env#get_label in
    let env, flag, compiled_body = compile_stmt labelF env s in
    env, false, [LABEL labelS] @ compiled_body @ (if flag then [LABEL labelF] else []) @ (expr e) @ [CJMP ("z", labelS)]
  | Stmt.Call (f, args) -> env, false, call f args true
  | Stmt.Return None -> env, false, [RET false]
  | Stmt.Return Some v -> env, false, (expr v) @ [RET true]
  | Stmt.Leave -> env, false, [LEAVE]
  | Stmt.Case (e, [p, s]) ->
    let flag1, body1 = pattern l p in
    let env, flag2, body2 = compile_stmt l env (Stmt.Seq (s, Stmt.Leave))
    in env, flag1 || flag2, expr e @ body1 @ bindings p @ body2 
  | Stmt.Case (e, branches) ->
    let n = List.length branches - 1 in
    let env, _, _, code =
      List.fold_left
        (fun (env, labl, i, cod) (p, s) ->
          let (lfalse, env), jmp = if i = n then (l, env), [] else env#get_label, [JMP l] in
          let _, body1 = pattern lfalse p in
          let env, _, body2 = compile_stmt l env (Stmt.Seq (s, Stmt.Leave)) in
          (env, Some lfalse, i + 1, ((match labl with None -> [] | Some l -> [LABEL l]) @ body1 @ bindings p @ body2 @ jmp) :: cod))
        (env, None, 0, []) branches
    in
    env, true, expr e @ List.concat @@ List.rev code
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 