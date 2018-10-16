type peano = Z | S of peano;; (* типы необходимо копировать в реализацию *)
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int x = if x == 0 then Z else S (peano_of_int (x - 1))

(*val int_of_peano: peano -> int;; *)
let rec int_of_peano p = match p with
  | Z -> 0
  | S x -> 1 + int_of_peano x;;

(*val inc: peano -> peano;;*)
let inc x = S x;;

exception Dec_zero;;

let dec x = match x with
  Z -> raise Dec_zero
  | S p -> p;;

let rec add x y = match y with
  Z -> x
  | S p -> S (add x p);;   

let rec sub x y = match y with
  Z -> x
  | S p -> dec (sub x p);;

let rec mul x y = match y with
  Z -> Z
  | S Z -> x
  | S p -> add (mul x p) x;;

let rec power x y = match y with
  Z -> S Z
  | S Z -> x
  | S p -> mul (power x p) x;;

(*--------------------list-------------------------*)

let rec append arr x = match arr with
  [] -> [x]
  | h::tail -> h:: append tail x;;

let rec rev arr = match arr with
  [] -> []
  | h::tail -> append (rev tail) h;;

(*---------------------merge sort------------------*)

let rec split = function
  | [] -> ([], [])
  | h::tail -> let (part1, part2) = split tail in 
               (h::part2, part1);;

let rec merge l1 l2 = match (l1, l2) with
  | ([], x) -> x
  | (x, []) -> x
  | (h1::t1, h2::t2) -> if h1 < h2
                        then h1 :: merge t1 l2
                        else h2 :: merge l1 t2;;

let rec merge_sort = function 
   | [] -> []
   | [x] -> [x]
   | arr -> let (part1, part2) = split arr in 
            merge (merge_sort part1) (merge_sort part2);;

(*---------------------lambda and string----------------------------*)

let rec string_of_lambda l = 
  match l with
    Var(x) -> x
  | App(a, b) -> "(" ^ string_of_lambda a ^ " " ^ string_of_lambda b ^ ")"
  | Abs(s, e) -> "(\\" ^ s ^ "." ^ string_of_lambda e ^ ")";;

let lambda_of_string str = 
  let str = str ^ ";" in
  let cur = ref 0 in
  let cur_char() = str.[!cur] in
  let inc_cur() = 
    if !cur < String.length str - 1 then 
      cur := !cur + 1 
    else failwith "Out of range" in
  let pass_next x =
    if cur_char() != x then 
      failwith ("Expected " ^ (String.make 1 x) ^  ", found " ^ (String.make 1 (cur_char()))) 
    else (inc_cur()) in
  
  let var_name_part x = (('a' <= x) && (x <= 'z')) || (('0' <= x) && (x <= '9')) || (x = '\'') in
  let parse_var() = 
    let rec get_full_name acc =
      if var_name_part (cur_char()) then
        let next = cur_char() in
          inc_cur();
          get_full_name (acc ^ (String.make 1 next))
        else acc in
    get_full_name "" in
  let create_var() = Var(parse_var()) in
  
  let rec parse_abs() = 
    pass_next '\\';
    let var = parse_var() in
    pass_next '.';
    let lmbd = parse_lambda() in
    Abs(var, lmbd)

  and parse_part left = 
    if ((!cur = String.length str - 1) || (cur_char() = ')')) then
      left
    else (
      if cur_char() == ' ' then
        pass_next ' ';
      match cur_char() with
      | '\\' -> (let right = parse_abs() in
                parse_part (App(left, right)))
      | '('  -> (pass_next '(';
                let right = parse_lambda() in
                pass_next ')';
                parse_part (App(left, right)))
      | _    -> (let right = create_var() in
                parse_part (App(left, right)))
    )

  and parse_lambda() = 
    match cur_char() with
    | '\\' -> (let left = parse_abs() in
              parse_part left)
    | '('  -> (pass_next '(';
              let left = parse_lambda() in
              pass_next ')';
              parse_part left)
    | _    -> (let left = create_var() in
              parse_part left) in 

  parse_lambda();;

(*----------------------helper-------------------------------------*)

let rec print_array arr =
  match arr with
  | [] -> print_endline ""
  | head::tail -> print_int head; print_string " "; print_array tail;;


