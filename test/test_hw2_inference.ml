open Hw2_unify;;
open Hw2_inference;;
open Test;;

(** Converts Hindley-Milner type to algebraic term using `->` as a function *)
let rec term_of_hm_type hm_type =
  let to_term = term_of_hm_type in
  match hm_type with
  | HM_Elem a  -> Var a
  | HM_Arrow (a, b) -> Fun ("->", [ (to_term a); (to_term b) ])
  | _ -> failwith "Forall quantifier cannot be represented as a term";;

(** Converts algebraic term with `->` functions to Hindley-Milner type *)
let rec hm_type_of_term term =
  let to_type = hm_type_of_term in
  match term with
  | Var a  -> HM_Elem a
  | Fun (f, [l;r]) when f = "->" -> HM_Arrow(to_type l, to_type r)
  | _ -> failwith "Term is not representing a simple type";;

let rec string_of_hm_type hm_type =
  let term = term_of_hm_type hm_type in
  let rec string_of_term term =
    match term with
    | Var v -> v
    | Fun (f, (Fun (_, _) as t1)::t2::[]) -> "(" ^ (string_of_term t1) ^ ") -> " ^ (string_of_term t2)
    | Fun (f, t1::t2::[]) -> (string_of_term t1) ^ " -> " ^ (string_of_term t2)
    | _ -> failwith "Impossible state for hm_type"
  in
  string_of_term term;;



let test123 t =
  let ans1 = algorithm_w t in
  match ans1 with
  | Some (l, s) ->
    print_endline (string_of_hm_type s)
  | None -> print_string "";;


let test1 = HM_Abs("x", HM_Var("x"));;
let test2 = HM_Let("w", HM_Abs("f", HM_Abs("x", HM_App(HM_Var("f"), HM_App(HM_Var("f"), HM_Var("x"))))), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_Var("w"))))))))))))));;
let test3 = HM_Let ("id", HM_Abs ("x", HM_Var "x"), HM_Var "id");;
let test4 = HM_Let ("id", HM_Abs ("x", HM_Var "x"), HM_App (HM_Var "id", HM_Var "id"));;
let test5 = HM_Let ("id", HM_Abs ("x", HM_Let ("y", HM_Var "x", HM_Var "y")), HM_App (HM_Var "id", HM_Var "id"));;
let test6 = HM_Let ("id", HM_Abs ("x", HM_Let ("y", HM_Var "x", HM_Var "y")), HM_App (HM_App (HM_Var "id", HM_Var "id"), HM_Var "int"));;
let test7 = HM_Let ("id", HM_Abs ("x", HM_App (HM_Var "x", HM_Var "x")), HM_Var "id");;
let test8 = HM_Abs ("m", HM_Let ("y", HM_Var "m", HM_Let ("x", HM_App (HM_Var "y", HM_Var "bool"), HM_Var "x")));;

test "algorithm_w"
  ~tester: (fun hm_lambda -> match algorithm_w hm_lambda with
      | Some (s, t) -> string_of_hm_type t
      | None -> "")
  (*~compare: system_to_equation_compare*)
  ~string_of: (fun a -> a)
  (Stream.of_list [
      { input = test1; output = "var0 -> var0" };
      { input = test2; output = "(var17 -> var17) -> var17 -> var17" };
      { input = test3; output = "var31 -> var31" };
      { input = test4; output = "var34 -> var34" };
      { input = test5; output = "var38 -> var38" };
      { input = test6; output = "var45" };
      { input = test7; output = "" };
      { input = test8; output = "(var48 -> var50) -> var50" };
    ]);;
