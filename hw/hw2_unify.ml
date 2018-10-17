type algebraic_term = Var of string | Fun of string * (algebraic_term list)

let unique_name = Stream.from (fun i -> Some ("var_" ^ string_of_int i));;
exception No_solution of string;;
module StringSet = Set.Make (String);;

(* По списку уравнений вернуть одно уравнение *)
(* val system_to_equation: (algebraic_term * algebraic_term) list -> (algebraic_term * algebraic_term) *)

let system_to_equation system =
let new_name = Stream.next unique_name in
let (left, right) = List.split system in
(Fun (new_name, left), Fun (new_name, right));;

(* Применить подстановку к системе *)
(* val apply_substitution: (string * algebraic_term) list -> algebraic_term -> algebraic_term *)

let apply_substitution substitution_list term = 
  let rec apply substitution term =
  let (key, new_term) = substitution in
  match term with
  | Var v            -> if (key = v) then 
                          new_term 
                        else term
  | Fun (name, args) -> Fun (name, List.map (apply substitution) args)
  in List.fold_right apply substitution_list term;;

(* Проверить решение *)
(* val check_solution: (string * algebraic_term) list -> (algebraic_term * algebraic_term) list -> bool *)

let check_solution substitution_list system =
  let (l, r) = system_to_equation system in
  let substitute = apply_substitution substitution_list in
  substitute l = substitute r;;

(* Решить систему; если решения нет -- вернуть None *)
(* val solve_system: (algebraic_term * algebraic_term) list -> (string * algebraic_term) list option *)

let apply_substitution_to_system subst system = 
  let rec apply system ans = match system with
    | []                    -> ans
    | (left, right) :: tail -> 
        apply tail (List.append ans (((apply_substitution subst left), (apply_substitution subst right)) :: []))
  in apply system [];; 
  
let rec equal_terms term1 term2 = match (term1, term2) with
  | (Var a, Var b) -> a = b
  | (Fun(f, list1), Fun(g, list2)) -> f = g && equal_lists list1 list2 
  | _ -> false
  and 
  equal_lists list1 list2 = match (list1, list2) with
    | ([], []) -> true
    | (head1 :: tail1), (head2 :: tail2) -> (equal_terms head1 head2) && (equal_lists tail1 tail2) 
    | _ -> false;;

let solve_system system = 
  let rec contains x term = match term with
    | (Var a) -> if a = x then 1 else 0
    | (Fun (f, lst)) -> (contains_lst x lst) lor (if f = x then 2 else 0)
  and 
  contains_lst x lst = match lst with
    | [] -> 0
    | (head :: tail) -> (contains x head) lor (contains_lst x tail)
  in
  let rec third_rule list1 list2 new_system = 
    match (list1, list2) with
      | ([], [])                         -> new_system
      | (head1 :: tail1, head2 :: tail2) -> third_rule tail1 tail2 ((head1, head2) :: new_system) 
      | _ -> raise (No_solution "Function arguments are incorrect.")
  in
  let rec robinson system answer = 
    if StringSet.cardinal answer = List.length system then 
      system
    else match system with
      | []                    -> raise (No_solution "System ubexpectedly empty.")
      | (left, right) :: tail -> 
          if equal_terms left right then 
            robinson tail answer
          else match (left, right) with
            | (Var a, right)                 -> 
              if contains a right land 1 <> 0 then 
                raise (No_solution "\"x\" both in lhs and rhs")
              else let answer = StringSet.add a answer in
                robinson (List.append (apply_substitution_to_system [a, right] tail) [(left, right)]) answer
            | (left, Var a)                  -> robinson (List.append tail [(right, left)]) answer
            | Fun(f, terms1), Fun(g, terms2) -> 
                if f <> g || List.length terms1 <> List.length terms2 then 
                  raise (No_solution "Arguments mismatch.")
                else robinson (List.append tail (third_rule terms1 terms2 [])) answer 
  in
  let rec get_answer answer new_ans = match answer with
    | [] -> new_ans
    | ((Var a, right) :: tail) -> get_answer tail ((a, right) :: new_ans) 
    | _ -> failwith "System is incorrect." 
  in
  try 
    let ans = robinson system StringSet.empty in
    (Some (get_answer (ans) []))
  with (No_solution error) -> None;;
