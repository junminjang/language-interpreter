type exp =
|CONST of int
|ADD of exp * exp
|SUB of exp * exp
|VAR of var
|LET of var * exp * exp
|IF of exp * exp * exp
|ISZERO of exp
and var = string

type value = Int of int | Bool of bool
type env = (var * value) list
let empty_env = []
let extend_env (x, v) e = (x, v)::e
let rec apply_env x e = match e with
|[] -> raise (Failure (x ^ " is not found"))
|(y, v)::tl -> if x = y then v else apply_env x tl

let rec eval : exp -> env -> value = fun exp env -> match exp with
  |CONST n -> Int n
  |VAR x -> apply_env x env
  |ADD (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> Int (n1 + n2)
      |_ -> raise (Failure "Type error"))
  |SUB (e1, e2) -> let v1 = eval e1 env in let v2 = eval e2 env in
    (match v1, v2 with
      |Int n1, Int n2 -> Int (n1 - n2)
      |_ -> raise (Failure "Type error"))
  |ISZERO e -> (match eval e env with
    |Int n when n = 0 -> Bool true
    |Int n when n <> 0 -> Bool false
    |_ -> raise (Failure "Type error"))
  |IF (e1, e2, e3) -> (match eval e1 env with
    |Bool true -> eval e2 env
    |Bool false -> eval e3 env
    |_ -> raise (Failure "Type error"))
  |LET (x, e1, e2) -> let v1 = eval e1 env in eval e2 (extend_env (x, v1) env)

let run: exp -> value = fun pgm -> eval pgm empty_env
