(* C style imperative language + garbage collection *)
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
  | PROC of var * exp
  | CALL of exp * exp
  | CALLREF of exp * var
  | ASSIGN of var * exp
  | PRINT of exp
  | SEQ of exp * exp
  | EMPTYREC (* {} *)
  | REC of (var * exp) list (* { x := E1, y := E2 }*)
  | FIELD of exp * var (* E.x *)
  | FIELDASSIGN of exp * var * exp (* E1.x := E2 *)
  | NEW of exp (* new E *)
  | ADDROF of var (* &x *)
  | ADDROFREC of exp * var
  | DEREF of exp (* *E  *)
  | STORE of exp * exp (* *E1 := E2 *)

and var = string

type value =
  | Unit
  | Int of int
  | Bool of bool
  | List of value list
  | Loc of loc
  | Record of record
  | Procedure of var * exp * env

and env = (var * loc) list
and mem = (loc * value) list
and loc = int
and record = (var * loc) list

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

let remove_garbage = ref false (* garbage collection on/off *)

let rec remove n lst =
  match lst with
  | [] -> []
  | hd :: tl -> if n = hd then remove n tl else hd :: remove n tl

let rec uniq lst =
  match lst with [] -> [] | hd :: tl -> hd :: remove hd (uniq tl)

let rec reach : env * mem * loc list -> loc list =
 fun (env, mem, locs) ->
  let locs = uniq locs in
  let locs' = locs @ List.map (fun (x, l) -> l) env in
  let locs' =
    List.fold_left
      (fun locs' l ->
        let v = apply_mem mem l in
        match v with
        | Loc l' -> l' :: locs'
        | Record r -> locs' @ List.map (fun (var, loc) -> loc) r
        | Procedure (params, e, env') -> locs' @ reach (env', mem, [])
        | _ -> locs')
      locs' locs'
  in
  let locs' = uniq locs' in
  if List.length locs' > List.length locs then reach (env, mem, locs') else locs

let gc : env * mem -> mem =
 fun (env, mem) ->
  if not !remove_garbage then mem
  else
    let locs = reach (env, mem, []) in
    let mem' = List.filter (fun (l, v) -> List.mem l locs) mem in
    mem'

let rec eval : exp -> env -> mem -> value * mem =
 fun exp env mem ->
  let mem = gc (env, mem) in
  match exp with
  | CONST n -> (Int n, mem)
  | UNIT -> (Unit, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | VAR x ->
      let l = apply_env env x in
      (apply_mem mem l, mem)
  | ASSIGN (x, e) ->
      let v1, mem1 = eval e env mem in
      (v1, extend_mem (apply_env env x, v1) mem1)
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
      | Bool false -> eval e3 env mem1
      | _ -> raise (Failure "Type error"))
  | LET (x, e1, e2) ->
      let v1, mem1 = eval e1 env mem in
      let l = new_location () in
      eval e2 (extend_env (x, l) env) (extend_mem (l, v1) mem1)
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
          let l = new_location () in
          eval e (extend_env (x, l) env') (extend_mem (l, v2) mem2)
      | _ -> raise (Failure "Type error"))
  | CALLREF (e, y) -> (
      let v1, mem1 = eval e env mem in
      let l = apply_env env y in
      match v1 with
      | Procedure (x, ef, env') ->
          let v2, mem2 = eval ef (extend_env (x, l) env') mem1 in
          (v2, mem2)
      | _ -> raise (Failure "Type error"))
  | PRINT e ->
      let v, mem1 = eval e env mem in
      let rec to_string v =
        match v with
        | Unit -> "unit"
        | Int n -> string_of_int n
        | Bool b -> string_of_bool b
        | List l -> "[" ^ String.concat "; " (List.map to_string l) ^ "]"
        | Procedure _ -> "<fun>"
        | _ -> raise (Failure "Unimplemented type")
      in
      print_endline (to_string v);
      (Unit, mem1)
  | SEQ (e1, e2) ->
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      (v2, mem2)
  | EMPTYREC -> (Unit, mem)
  | REC ves ->
      let rev_record_env, final_mem =
        List.fold_left
          (fun (acc, curr_mem) (x, e) ->
            let v, next_mem = eval e env curr_mem in
            let l = new_location () in
            let new_mem = extend_mem (l, v) next_mem in
            ((x, l) :: acc, new_mem))
          ([], mem) ves
      in
      (Record (List.rev rev_record_env), final_mem)
  | FIELD (e, x) -> (
      let v, mem1 = eval e env mem in
      match v with
      | Record r -> (apply_mem mem1 (apply_env r x), mem1)
      | _ -> raise (Failure "Unimplemented"))
  | FIELDASSIGN (e1, x, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match v1 with
      | Record r ->
          let mem3 = extend_mem (apply_env r x, v2) mem2 in
          (v2, mem3)
      | _ -> raise (Failure "Type error"))
  | NEW e ->
      let v, mem1 = eval e env mem in
      let l = new_location () in
      (Loc l, extend_mem (l, v) mem1)
  | ADDROF x -> (Loc (apply_env env x), mem)
  | ADDROFREC (e, x) -> (
      let v, mem1 = eval e env mem in
      match v with
      | Record r -> (Loc (apply_env r x), mem1)
      | _ -> raise (Failure "Unimplemented"))
  | DEREF e -> (
      let v, mem1 = eval e env mem in
      match v with
      | Loc l ->
          let v1 = apply_mem mem1 l in
          (v1, mem1)
      | _ -> raise (Failure "Type error"))
  | STORE (e1, e2) -> (
      let v1, mem1 = eval e1 env mem in
      let v2, mem2 = eval e2 env mem1 in
      match v1 with
      | Loc l -> (v2, extend_mem (l, v2) mem2)
      | _ -> raise (Failure "Unimplemented"))

let run : exp -> bool -> bool -> value * mem =
 fun pgm gc print_mem_size ->
  let _ = remove_garbage := gc in
  let v, mem = eval pgm empty_env empty_mem in
  if print_mem_size then
    print_endline (Printf.sprintf "Fianl mem size: %d" (List.length mem));
  (v, mem)
