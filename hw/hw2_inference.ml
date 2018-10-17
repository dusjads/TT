open Hw1
open Hw1_reduction
open Hw2_unify

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

module StringMap = Map.Make(String);;
module StringSet = Set.Make(String);;

let unique_type = Stream.from (fun i -> Some ("type_" ^ string_of_int i));;
let unique_var = Stream.from (fun i -> Some ("var_" ^ string_of_int i));;

exception NoSolution of string;;  


(* val infer_simp_type : lambda -> ((string * simp_type list) * simp_type) option *)
let infer_simp_type lambda =
  let rec simp_type_to_term = (function
    | S_Elem v       -> Var v
    | S_Arrow (a, b) -> Fun("->", [ (simp_type_to_term a); (simp_type_to_term b) ])) in 
  let rec term_to_simp_type = (function
    | Var v                          -> S_Elem v
    | Fun(f, [ l; r ]) when f = "->" -> S_Arrow (term_to_simp_type l, term_to_simp_type r)
    | _                              -> failwith "Term is not representing a simple type") in
  let equation_of_types (l, r) = (simp_type_to_term l, simp_type_to_term r) in
  let new_type() = S_Elem (Stream.next unique_type) in
  let add_type_to_map map t = StringMap.add t (new_type()) map in
  let rec get_system lambda types =
    match (lambda : lambda) with
      | Var v                  -> ([], StringMap.find v types)
      | App (lambda1, lambda2) ->
          let (system1, t1) = get_system lambda1 types in
          let (system2, t2) = get_system lambda2 types in
          let new_t = new_type() in
          (system1 @ system2 @ [(t1, S_Arrow(t2, new_t))], new_t)
      | Abs (v, l)             ->
          let new_map = add_type_to_map types v in
          let (system1, t1) = get_system l new_map in
          (system1, S_Arrow(StringMap.find v new_map, t1))
  in
  let free = free_vars lambda in
  let types = List.fold_left add_type_to_map StringMap.empty free in
  let (system, t) = get_system lambda types in
  match solve_system (List.map equation_of_types system) with
    | None          -> None
    | Some solution ->
        let lambda_type_term = apply_substitution solution (simp_type_to_term t) in
        let to_type_list = List.map (fun (a, b) -> (a, term_to_simp_type b)) in
        Some (to_type_list solution, term_to_simp_type lambda_type_term);;


(* val algorithm_w : hm_lambda -> ((string * hm_type list) * hm_type) option *)
let algorithm_w hm_lambda =
  let rec hm_type_to_term = function
    | HM_Elem a       -> Var a
    | HM_Arrow (a, b) -> Fun ("->", [ (hm_type_to_term a); (hm_type_to_term b) ])
    | _               -> failwith "Forall quantifier cannot be represented as a term"
  in
  let rec term_to_hm_type = function
    | Var a                        -> HM_Elem a
    | Fun (f, [l;r]) when f = "->" -> HM_Arrow(term_to_hm_type l, term_to_hm_type r)
    | _                            -> failwith "Term is not representing a simple type"
  in
  let rec free_vars = function
    | HM_Var a          -> StringSet.singleton a
    | HM_App (a, b)     -> StringSet.union (free_vars a) (free_vars b)
    | HM_Abs (a, b)     -> StringSet.remove a (free_vars b)
    | HM_Let (a, b, c)  ->
      let free_vars_c = StringSet.remove a (free_vars c) in
      StringSet.union (free_vars b) free_vars_c
  in
  let rec free_types = function
    | HM_Elem a         -> StringSet.singleton a
    | HM_Arrow (a, b)   -> StringSet.union (free_types a) (free_types b)
    | HM_ForAll (a, b)  -> StringSet.remove a (free_types b)
  in
  let rec apply_type_subst subst = function
    | HM_Elem a when StringMap.mem a subst  -> StringMap.find a subst
    | HM_Elem a                             -> HM_Elem a
    | HM_Arrow (a, b)                       -> HM_Arrow (apply_type_subst subst a, apply_type_subst subst b)
    | HM_ForAll (a, b)                      -> HM_ForAll (a, apply_type_subst (StringMap.remove a subst) b)
  in
  let compose_subst subst1 subst2 =
    let get_some key v1 v2 = match (v1, v2) with
      | (None,    None)    -> None
      | (Some v,  None)    -> Some v
      | (None,    Some v)  -> Some v
      | (Some v1, Some v2) -> Some v2
    in
    let subst2 = StringMap.map (apply_type_subst subst1) subst2 in
      StringMap.merge get_some subst1 subst2
  in
  let apply_subst_to_env subst type_env = StringMap.map (apply_type_subst subst) type_env
  in
  let generalize type_env hm_type =
    let add_free_types key value = StringSet.union (free_types value) in
    let free_hm_types = free_types hm_type in
    let free_env_types = StringMap.fold add_free_types type_env StringSet.empty in
    let new_forall_vars = StringSet.diff free_hm_types free_env_types in
    let add_quantifier var hm_type = HM_ForAll (var, hm_type) in
    StringSet.fold add_quantifier new_forall_vars hm_type
  in
  let rec instantiate hm_type =
    match hm_type with
      | HM_ForAll (a, b) ->
        let subst = StringMap.singleton a (HM_Elem (Stream.next unique_var)) in
        apply_type_subst subst (instantiate b)
      | _                -> hm_type 
  in
  let error message = raise (NoSolution message) in
  let rec algorithm_w_rec type_env = function
    | HM_Var a when StringMap.mem a type_env -> (StringMap.empty, instantiate (StringMap.find a type_env))
    | HM_Var a                               -> error "Free variable found"
    | HM_App (a, b)                          ->
        (let (s1, t1) = algorithm_w_rec type_env a in
         let (s2, t2) = algorithm_w_rec (apply_subst_to_env s1 type_env) b in
         let new_type = HM_Elem (Stream.next unique_var) in
         let left = apply_type_subst s2 t1 in
         let right = HM_Arrow (t2, new_type) in
         let equation = (hm_type_to_term left, hm_type_to_term right) in
         match solve_system [equation] with
           | None         -> error "Couldn't solve the system"
           | Some answer  ->
              let add_subst (str, term) = StringMap.add str (term_to_hm_type term) in
              let v = List.fold_right add_subst answer StringMap.empty in
              let unifier = compose_subst v (compose_subst s2 s1) in
              (unifier, apply_type_subst unifier new_type))
    | HM_Abs (a, b)                          ->
        let new_type = HM_Elem (Stream.next unique_var) in
        let type_env = StringMap.add a new_type (StringMap.remove a type_env) in
        let (s1, t1) = algorithm_w_rec type_env b in
        (s1, HM_Arrow (apply_type_subst s1 new_type, t1))
    | HM_Let (a, b, c)                       ->
        let (s1, t1) = algorithm_w_rec type_env b in
        let a_type = generalize (apply_subst_to_env s1 type_env) t1 in
        let type_env = apply_subst_to_env s1 (StringMap.remove a type_env) in
        let type_env = StringMap.add a a_type type_env in
        let (s2, t2) = algorithm_w_rec type_env c in
        (compose_subst s2 s1, t2)
  in
  let free = free_vars hm_lambda in
  let bound_to_unique v = StringMap.add v (HM_Elem (Stream.next unique_var)) in
  let type_environment = StringSet.fold bound_to_unique free StringMap.empty in
  try
    let (unifier, hm_type) = algorithm_w_rec type_environment hm_lambda in
    Some (StringMap.bindings unifier, hm_type)
  with (NoSolution e) -> None;;