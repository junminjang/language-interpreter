type exp =
|UNIT
|TRUE
|FALSE
|CONST of int
|ADD of exp * exp
|SUB of exp * exp
|MUL of exp * exp
|DIV of exp * exp
|EQUAL of exp * exp
|LESS of exp * exp
|NOT of exp
|NIL
|CONS of exp * exp
|APPEND of exp * exp
|HEAD of exp
|TAIL of exp
|ISNIL of exp
|VAR of var
|LET of var * exp * exp
|IF of exp * exp * exp
|LETREC of var * var * exp * exp
|LETMREC of (var * var * exp) * (var * var * exp) * exp
|PROC of var * exp
|CALL of exp * exp
|PRINT of exp
|SEQ of exp * exp
and var = string

type value =
  |Unit | Int of int | Bool of bool | List of value list
  |Procedure of var * exp * env
  |RecProcedure of var * var * exp * env
  |MRecProcedure of var * var * exp * var * var * exp * env

and env = (var * value) list

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec apply_env e x =
  match e with
  | [] -> raise (Failure (x ^ " is unbound in Env"))
  | (y,v)::tl -> if x = y then v else apply_env tl x
let rec eval : exp -> env -> value = fun exp env -> match exp with
  |CONST n -> Int n
  |UNIT -> Unit
  |TRUE -> Bool true
  |FALSE -> Bool false
  |VAR x -> apply_env env x
  |ADD (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> Int (n1 + n2)
      |_ -> raise (Failure "Type error"))
  |SUB (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> Int (n1 - n2)
      |_ -> raise (Failure "Type error"))
  |MUL (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> Int (n1 * n2)
      |_ -> raise (Failure "Type error"))
  |DIV (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> if n2 <> 0 then Int(n1/n2) else raise (Failure "division by zero error")
      |_ -> raise (Failure "Type error"))
  |IF (e1, e2, e3) -> (match eval e1 env with
    |Bool true -> eval e2 env
    |Bool false -> eval e3 env
    |_ -> raise (Failure "Type error"))
  |LET (x, e1, e2) -> let v1 = eval e1 env in eval e2 (extend_env (x, v1) env)
  |LETREC (f, x, e1, e2) -> let env' = extend_env (f, RecProcedure(f,x,e1,env)) env in
    eval e2 env'
  |EQUAL (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> if n1 = n2 then Bool(true) else Bool(false)
      |Bool b1, Bool b2 -> if b1 = b2 then Bool(true) else Bool(false)
      |List l1, List l2 -> Bool (List.length l1 = List.length l2 && List.for_all2 (=) l1 l2)
      |_ -> raise (Failure "Type error"))
  |LESS (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> if n1 < n2 then Bool true else Bool false
      |_ -> raise (Failure "Type error"))
  |NOT e -> let v = eval e env in if v = Bool true then Bool false else Bool true
  |NIL -> List []
  |CONS (e1, e2) -> let hd = eval e1 env in let tl = eval e2 env in
    (match tl with
      |List s -> List (hd::s)
      |_ -> raise (Failure "Type error"))
  |APPEND (e1, e2) -> let l1 = eval e1 env in let l2 = eval e2 env in
    (match l1, l2 with
      |List s1, List s2 -> List (s1@s2)
      |_ -> raise (Failure "Type error"))
  |HEAD e -> let l = eval e env in (match l with
    |List s -> if List.length s <> 0 then List.hd s else raise (Failure "Empty list (hd)")
    |_ -> raise (Failure "Type error"))
  |TAIL e -> let l = eval e env in (match l with
    |List s -> if List.length s <> 0 then List(List.tl s) else raise (Failure "Empty list (tl)")
    |_ -> raise (Failure "Type error"))
  |ISNIL e -> let l = eval e env in (match l with
    |List s -> if List.length s <> 0 then Bool false else Bool true
    |_ -> raise (Failure "Type error"))
  |PROC (x, e) -> Procedure (x, e, env)
  |CALL (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1 with
      |Procedure (x, e, env') -> let env' = (extend_env (x, v2) env') in eval e env'
      |RecProcedure (f, x, e, env') -> eval e (extend_env (f, RecProcedure(f, x, e, env')) (extend_env (x, v2) env'))
      |MRecProcedure (f, x, ef, g, y, eg, env') ->
        eval ef (extend_env (f, MRecProcedure(f, x, ef, g, y, eg, env')) (extend_env (g, MRecProcedure(g, y, eg, f, x, ef, env')) (extend_env (x, v2) env')))
      |_ -> raise (Failure "Type error"))
  |LETMREC ((f, x, ef), (g, y, eg), e2) ->
    let val_f = MRecProcedure(f,x,ef,g,y,eg,env) in
    let val_g = MRecProcedure(g,y,eg,f,x,ef,env) in
    let env' = extend_env (f, val_f) (extend_env (g, val_g) env) in
    eval e2 env'
  |PRINT e -> let v = eval e env in
    let rec to_string v = match v with
      |Unit -> "unit"
      |Int n -> string_of_int n
      |Bool b -> string_of_bool b
      |List l -> "[" ^ (String.concat "; " (List.map to_string l)) ^ "]"
      |Procedure _ | RecProcedure _ |MRecProcedure _ -> "<fun>"
      in
      print_endline (to_string v);
      Unit
 |SEQ (e1, e2) -> let _ = eval e1 env in let v2 = eval e2 env in v2

let run: exp -> value = fun pgm -> eval pgm empty_env
