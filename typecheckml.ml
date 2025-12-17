(* type checker for subset of miniML *)
type exp =
  | TRUE
  | FALSE
  | CONST of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | VAR of var
  | LET of var * exp * exp
  | IF of exp * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp

and var = string

type value =
  | Unit
  | Int of int
  | Bool of bool
  | Loc of loc
  | Procedure of var * exp * env
  | RecProcedure of var * var * exp * env

and env = (var * value) list
and mem = (loc * value) list
and loc = int

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string

let tyvar_num = ref 0

let fresh_tyvar () =
  tyvar_num := !tyvar_num + 1;
  TyVar ("t" ^ string_of_int !tyvar_num)

module TEnv = struct
  type t = var -> typ

  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x, t) tenv = fun y -> if x = y then t else tenv y
  let find tenv x = tenv x
end

module Subst = struct
  type t = (tyvar * typ) list (* subst list type *)

  let empty = []
  let find x subst = List.assoc x subst

  let rec apply : typ -> t -> typ =
   fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool
    | TyFun (t1, t2) ->
        TyFun (apply t1 subst, apply t2 subst) (* recursively substitute *)
    | TyVar x -> ( try find x subst with _ -> typ)

  let extend tv ty subst =
    (tv, ty) :: List.map (fun (x, t) -> (x, apply t [ (tv, ty) ])) subst
end

type typ_eqn = (typ * typ) list

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn =
 fun tenv e ty ->
  match e with
  | CONST _ -> [ (ty, TyInt) ]
  | TRUE | FALSE -> [ (ty, TyBool) ]
  | VAR x -> [ (ty, TEnv.find tenv x) ]
  | ADD (e1, e2) | SUB (e1, e2) | MUL (e1, e2) | DIV (e1, e2) ->
      ((ty, TyInt) :: gen_equations tenv e1 TyInt) @ gen_equations tenv e2 TyInt
  | IF (e1, e2, e3) ->
      gen_equations tenv e1 TyBool
      @ gen_equations tenv e2 ty @ gen_equations tenv e3 ty
  | ISZERO e -> [ (ty, TyBool) ] @ gen_equations tenv e TyInt
  | LET (x, e1, e2) ->
      let t_x = fresh_tyvar () in
      gen_equations tenv e1 t_x
      @ gen_equations (TEnv.extend (x, t_x) tenv) e2 ty
  | LETREC (f, x, e1, e2) ->
      let t_x = fresh_tyvar () in
      let t_y = fresh_tyvar () in
      let t_f = TyFun (t_x, t_y) in
      gen_equations (TEnv.extend (x, t_x) (TEnv.extend (f, t_f) tenv)) e1 t_y
      @ gen_equations (TEnv.extend (f, t_f) tenv) e2 ty
  | PROC (x, e) ->
      let t_x = fresh_tyvar () in
      let t_y = fresh_tyvar () in
      (ty, TyFun (t_x, t_y)) :: gen_equations (TEnv.extend (x, t_x) tenv) e t_y
  | CALL (e1, e2) ->
      let t_x = fresh_tyvar () in
      gen_equations tenv e1 (TyFun (t_x, ty)) @ gen_equations tenv e2 t_x

let solve : typ_eqn -> Subst.t =
 fun eqn ->
  let rec unify ty1 ty2 subst =
    let ty1 = Subst.apply ty1 subst in
    let ty2 = Subst.apply ty2 subst in
    if ty1 = ty2 then subst
    else
      match (ty1, ty2) with
      | TyVar x, _ ->
          if cycle_check x ty2 then raise (Failure "Type Error: Cycle detected")
          else Subst.extend x ty2 subst
      | _, TyVar x ->
          if cycle_check x ty1 then raise (Failure "Type Error: Cycle deteced")
          else Subst.extend x ty1 subst
      | TyFun (t1, t2), TyFun (t3, t4) ->
          let subst' = unify t1 t3 subst in
          unify t2 t4 subst'
      | _ -> raise (Failure "Type Error: Mismatch")
  and cycle_check x ty =
    match ty with
    | TyVar y -> x = y
    | TyFun (t1, t2) -> cycle_check x t1 || cycle_check x t2
    | _ -> false
  in
  List.fold_left (fun subst (t1, t2) -> unify t1 t2 subst) Subst.empty eqn

let typecheck : exp -> typ =
 fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let subst = solve eqns in
  let ty = Subst.apply new_tv subst in
  ty
