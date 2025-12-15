(* explicit reference language *)
type exp =
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | VAR of var
  | LET of var * exp * exp
  | IF of exp * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
  | NEWREF of exp (* memory allocation *)
  | DEREF of exp (* dereference *)
  | SETREF of exp * exp (* assignment *)

and var = string

type value =
  | Unit
  | Int of int
  | Bool of bool
  | List of value list
  | Loc of loc
  | Procedure of var * exp * env
  | RecProcedure of var * var * exp * env
  | MRecProcedure of var * var * exp * var * var * exp * env

and env = (var * value) list
and mem = (loc * value) list
and loc = int

let empty_env = []
let extend_env (x, v) e = (x, v) :: e

let rec apply_env e x =
  match e with
  | [] -> raise (Failure (x ^ " is unbound in Env"))
  | (y, v) :: tl -> if x = y then v else apply_env tl x

let empty_mem = []
let extend_mem (l, v) m = (l, v) :: m

let rec apply_mem m l =
  match m with
  | [] -> raise (Failure (string_of_int l ^ "is unbound in Mem"))
  | (y, v) :: tl -> if l = y then v else apply_mem tl l

let counter = ref 0

let new_location () =
  counter := !counter + 1;
  !counter

let rec eval : exp -> env -> mem -> value * mem =
 fun exp env mem ->
  match exp with
  | CONST n -> (Int n, mem)
  | UNIT -> (Unit, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | VAR x -> (apply_env env x, mem)
  | ADD (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match (v1, v2) with
      | Int n1, Int n2 -> (Int (n1 + n2), mem2)
      | _ -> raise (Failure "Type error"))
  | SUB (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match (v1, v2) with
      | Int n1, Int n2 -> (Int (n1 - n2), mem2)
      | _ -> raise (Failure "Type error"))
  | MUL (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match (v1, v2) with
      | Int n1, Int n2 -> (Int (n1 * n2), mem2)
      | _ -> raise (Failure "Type error"))
  | DIV (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match (v1, v2) with
      | Int n1, Int n2 ->
          if n2 <> 0 then (Int (n1 / n2), mem2)
          else raise (Failure "division by zero error")
      | _ -> raise (Failure "Type error"))
  | IF (e1, e2, e3) -> (
      let v, mem1 = eval e1 env mem in
      match v with
      | Bool true -> eval e2 env mem1
      | Bool false -> eval e2 env mem1
      | _ -> raise (Failure "Type error"))
  | LET (x, e1, e2) ->
      let v1, mem1 = eval e1 env mem in
      eval e2 (extend_env (x, v1) env) mem1
  | LETREC (f, x, e1, e2) ->
      let env' = extend_env (f, RecProcedure (f, x, e1, env)) env in
      eval e2 env' mem
  | EQUAL (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match (v1, v2) with
      | Int n1, Int n2 ->
          if n1 = n2 then (Bool true, mem2) else (Bool false, mem2)
      | Bool b1, Bool b2 ->
          if b1 = b2 then (Bool true, mem2) else (Bool false, mem2)
      | List l1, List l2 ->
          ( Bool (List.length l1 = List.length l2 && List.for_all2 ( = ) l1 l2),
            mem2 )
      | _ -> raise (Failure "Type error"))
  | LESS (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match (v1, v2) with
      | Int n1, Int n2 ->
          if n1 < n2 then (Bool true, mem2) else (Bool false, mem2)
      | _ -> raise (Failure "Type error"))
  | NOT e ->
      let v, mem1 = eval e env mem in
      if v = Bool true then (Bool false, mem1) else (Bool true, mem1)
  | NIL -> (List [], mem)
  | CONS (e1, e2) -> (
      let hd, mem1 = eval e1 env mem in
      let tl, mem2 = eval e2 env mem1 in
      match tl with
      | List s -> (List (hd :: s), mem2)
      | _ -> raise (Failure "Type error"))
  | APPEND (e1, e2) -> (
      let l1, mem1 = eval e1 env mem in
      let l2, mem2 = eval e2 env mem1 in
      match (l1, l2) with
      | List s1, List s2 -> (List (s1 @ s2), mem2)
      | _ -> raise (Failure "Type error"))
  | HEAD e -> (
      let l, mem1 = eval e env mem in
      match l with
      | List s ->
          if List.length s <> 0 then (List.hd s, mem1)
          else raise (Failure "Empty list (hd)")
      | _ -> raise (Failure "Type error"))
  | TAIL e -> (
      let l, mem1 = eval e env mem in
      match l with
      | List s ->
          if List.length s <> 0 then (List (List.tl s), mem1)
          else raise (Failure "Empty list (tl)")
      | _ -> raise (Failure "Type error"))
  | ISNIL e -> (
      let l, mem1 = eval e env mem in
      match l with
      | List s ->
          if List.length s <> 0 then (Bool false, mem1) else (Bool true, mem1)
      | _ -> raise (Failure "Type error"))
  | PROC (x, e) -> (Procedure (x, e, env), mem)
  | CALL (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match v1 with
      | Procedure (x, e, env') ->
          let env' = extend_env (x, v2) env' in
          eval e env' mem2
      | RecProcedure (f, x, e, env') ->
          eval e
            (extend_env
               (f, RecProcedure (f, x, e, env'))
               (extend_env (x, v2) env'))
            mem
      | MRecProcedure (f, x, ef, g, y, eg, env') ->
          eval ef
            (extend_env
               (f, MRecProcedure (f, x, ef, g, y, eg, env'))
               (extend_env
                  (g, MRecProcedure (g, y, eg, f, x, ef, env'))
                  (extend_env (x, v2) env')))
            mem
      | _ -> raise (Failure "Type error"))
  | LETMREC ((f, x, ef), (g, y, eg), e2) ->
      (* closures *)
      let val_f = MRecProcedure (f, x, ef, g, y, eg, env) in
      let val_g = MRecProcedure (g, y, eg, f, x, ef, env) in
      let env' = extend_env (f, val_f) (extend_env (g, val_g) env) in
      eval e2 env' mem
  | PRINT e ->
      let v, mem1 = eval e env mem in
      let rec to_string v =
        match v with
        | Unit -> "unit"
        | Int n -> string_of_int n
        | Bool b -> string_of_bool b
        | List l -> "[" ^ String.concat "; " (List.map to_string l) ^ "]"
        | Procedure _ | RecProcedure _ | MRecProcedure _ -> "<fun>"
        | _ -> raise (Failure "Unimplemented type")
      in
      print_endline (to_string v);
      (Unit, mem1)
  | SEQ (e1, e2) ->
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      (v2, mem2)
  | NEWREF e ->
      let v, mem1 = eval e env mem in
      let l = new_location () in
      (Loc l, extend_mem (l, v) mem1)
  | DEREF e -> (
      let v, mem1 = eval e env mem in
      match v with
      | Loc l ->
          let v1 = apply_mem mem1 l in
          (v1, mem1)
      | _ -> raise (Failure "Type error"))
  | SETREF (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match v1 with
      | Loc l -> (v2, extend_mem (l, v2) mem2)
      | _ -> raise (Failure "Type error"))

let run : exp -> value * mem = fun pgm -> eval pgm empty_env empty_mem
