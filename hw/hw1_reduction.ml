open Hw1;;

(* Вернуть список имён свободных переменных *)
(* val free_vars: lambda -> string list *)

module StringSet = Set.Make (String);;
module StringMap = Map.Make (String);;

let free_vars lmbd = 
  let rec free_vars_rec lmbd blocked = match lmbd with
      | Var a            -> if StringSet.mem a blocked then 
                             StringSet.empty 
                           else StringSet.singleton a
      | Abs(a, lm)       -> free_vars_rec lm (StringSet.add a blocked)
      | App(left, right) -> StringSet.union (free_vars_rec left blocked) (free_vars_rec right blocked)
  in StringSet.elements (free_vars_rec lmbd StringSet.empty);;

(* Проверить свободу для подстановки. Параметры:
 что подставляем, где подставляем, вместо чего подставляем *)
(* val free_to_subst: lambda -> lambda -> string -> bool *)

let free_to_subst theta lmbd x =
  let free_set = StringSet.of_list (free_vars theta) in
  let rec is_free lmbd x blocked = match lmbd with
      | Var a            -> if a = x then
                              ((StringSet.inter free_set blocked) = StringSet.empty) 
                            else true 
      | Abs(a, lm)       -> if a = x then
                              true
                            else is_free lm x (StringSet.add a blocked)
      | App(left, right) -> (is_free left x blocked) && (is_free right x blocked)
    in is_free lmbd x StringSet.empty;;


(* Проверить, находится ли лямбда-выражение в нормальной форме *)
(* val is_normal_form: lambda -> bool *)

let rec is_normal_form lmbd = match lmbd with
  | Var a             -> true
  | App(Abs(a, b), c) -> false
  | Abs(a, lm)        -> is_normal_form lm
  | App(left, right)  -> (is_normal_form left) && (is_normal_form right);;

(* Проверить, альфа-эквивалентны ли лямбда-выражения *)
(* val is_alpha_equivalent: lambda -> lambda -> bool *)

let unique_name = Stream.from (fun i -> Some ("var_" ^ string_of_int i));;

let rec subst theta lmbd x = match lmbd with
  | Var a            -> if a = x then 
                          theta
                        else lmbd
  | Abs(a, lm)       -> if a = x then 
                          lmbd
                        else Abs(a, subst theta lm x)
  | App(left, right) ->  App(subst theta left x, subst theta right x);;

let is_alpha_equivalent left right =
  let rec is_alpha_equivalent_rec left right =
    match (left, right) with
    | (Var a, Var b)               -> a = b
    | (App (x1, y1), App (x2, y2)) -> (is_alpha_equivalent_rec x1 x2 && is_alpha_equivalent_rec y1 y2)
    | (Abs (x1, y1), Abs (x2, y2)) -> let new_var = Var (Stream.next unique_name) in
                                        is_alpha_equivalent_rec (subst new_var y1 x1) (subst new_var y2 x2)
    | _                            -> false
  in is_alpha_equivalent_rec left right;;

(* Выполнить один шаг бета-редукции, используя нормальный порядок *)
(* val normal_beta_reduction: lambda -> lambda *)

let rec change_vars lmbd map = match lmbd with
  | Var a            -> if StringMap.mem a map then 
                          Var (StringMap.find a map) 
                        else lmbd
  | Abs(a, lm)       -> let new_var = (Stream.next unique_name) in
                          Abs(new_var, change_vars lm (StringMap.add a new_var map))
  | App(left, right) -> App(change_vars left map, change_vars right map);;


let normal_beta_reduction lmbd =
  let rec reduction_rec lmbd = match lmbd with
    | Var a             ->  (false, lmbd)
    | Abs(a, lm)        ->  let (helper, new_lm) = reduction_rec lm in
                              (helper, Abs(a, new_lm))
    | App(Abs(a, b), c) ->  (true, subst c b a)
    | App(left, right)  ->  let (helper, new_left) = reduction_rec left in
                              if helper then 
                                (helper, App(new_left, right))
                              else let (helper, new_right) = reduction_rec right in
                                (helper, App(left, new_right))
  in
  let (helper, ans) = reduction_rec (change_vars lmbd StringMap.empty) in
  ans;;

(* Свести выражение к нормальной форме с использованием нормального
 порядка редукции; реализация должна быть эффективной: использовать 
 мемоизацию *)
(* val reduce_to_normal_form: lambda -> lambda *)

type lambda_ref = Varref of string | Absref of (string * lambda_ref ref)| Appref of (lambda_ref ref * lambda_ref ref);;
  
let rec lambda_to_lambda_ref lmbd = match lmbd with
  | Var a            -> ref (Varref a)
  | Abs(a, lm)       -> ref (Absref (a, lambda_to_lambda_ref lm))
  | App(left, right) -> ref (Appref (lambda_to_lambda_ref left, lambda_to_lambda_ref right));;
  
let rec lambda_ref_to_lambda lmbdref = match !lmbdref with
  | Varref a            -> Var a
  | Absref(a, lm)       -> Abs (a, lambda_ref_to_lambda lm)
  | Appref(left, right) -> App (lambda_ref_to_lambda left, lambda_ref_to_lambda right);;
  
let rec subst_ref thetaref lmbdref z = match !lmbdref with
  | Varref a     -> if a = z then 
                      lmbdref := !thetaref
  | Absref(a, b) -> if a <> z then 
                      subst_ref thetaref b z
  | Appref(a, b) -> subst_ref thetaref a z; 
                    subst_ref thetaref b z;;


let rec reduce_to_normal_form lmbd = 
  let lmbdref = lambda_to_lambda_ref (change_vars lmbd StringMap.empty) in
  
  let rec reduce lmbdref = match !lmbdref with
    | Varref a            -> None
    | Absref(a, lm)       -> (match reduce lm with
        | Some ans -> Some lmbdref
        | None     -> None
        )
    | Appref(left, right) -> (match !left with         
        | Absref(x, y) -> let new_name = (Stream.next unique_name) in
                            lmbdref := !(lambda_to_lambda_ref (change_vars (lambda_ref_to_lambda y) (StringMap.singleton x new_name)));
                            subst_ref right lmbdref new_name;
                            Some lmbdref
        | _            -> match reduce left with
            | Some ans -> Some lmbdref
            | None     -> match reduce right with
                | Some ans -> Some lmbdref
                | None     -> None
    )       
  in let rec get_ans lmbdref = match reduce lmbdref with
    | Some ans -> get_ans ans
    | None     -> lmbdref
  in lambda_ref_to_lambda (get_ans lmbdref);;