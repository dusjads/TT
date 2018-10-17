open Hw2_unify;;
open Test;;

(* TODO: update tests*)

let rec string_of_term x =
  match x with
  | Var v -> v
  | Fun (f, t) -> f ^ "(" ^ (String.concat ", " (List.map string_of_term t)) ^ ")";;

let rec string_of_equation (l, r) =
  string_of_term l ^ " = " ^ string_of_term r;;

let term_of_string input =
  let stream = Stream.of_string (input ^ "=") in
  let tokens = Genlex.make_lexer [","; "("; ")"; "="] stream in
  let next() = Stream.next tokens in
  let peek() = Stream.peek tokens in
  let check c err value = if (next() <> Genlex.Kwd c) then failwith err else value in
  let check_parenthesis = check ")" "Parenthesis not closed" in

  let rec parse_term() =
    match next() with
    | Genlex.Ident name -> check_fun name
    | Genlex.Kwd "(" -> let t = parse_term() in check_parenthesis t
    | _ -> failwith "Unexpected symbol"

  and check_fun name =
    match peek() with
    | Some (Genlex.Kwd "(") -> let _ = next() in parse_fun name []
    | Some (Genlex.Kwd _) -> Var name
    | _ -> failwith "Unexpected end of string"

  and parse_fun name args =
    let args = (parse_term()) :: args in
    match next() with
    | Genlex.Kwd "," -> parse_fun name args
    | Genlex.Kwd ")" -> Fun (name, List.rev args)
    | _ -> failwith "Unexpected symbol"
  in parse_term();;

test "string_of_term"
  ~tester: string_of_term
  ~string_of: (fun x -> x)
  (Stream.of_list [
      { input = Fun ("f", [Var "x"; Var "y"; Fun ("z", [Var "abc"; Var "def"]); Var "x"]); output = "f(x, y, z(abc, def), x)" };
    ]);;

test "term_of_string"
  ~tester: term_of_string
  ~string_of: string_of_term
  (Stream.of_list [
      { input = "f(x,(y),z(abc,def),x)"; output = Fun ("f", [Var "x"; Var "y"; Fun ("z", [Var "abc"; Var "def"]); Var "x"]) };
    ]);;

let sym1 = [
  (Fun ("x", [Var "p1"]), Fun ("x", [Var "p2"]));
  (Fun ("y", [Var "p3"]), Fun ("y", [Var "p4"]));
  (Fun ("z", [Var "p5"]), Fun ("z", [Var "p6"]));
];;

let sol1 = [
  ("p5", Var "p6");
  ("p3", Var "p4");
  ("p1", Var "p2");
];;

let sym2 = [
  (Fun("x", [Var "p1"]), Fun("x", [Var "p2"]));
  (Fun("m", [Var "p1"]), Fun("y", [Var "p4"]));
  (Fun("z", [Var "p5"]), Fun("z", [Var "p6"]));
];;

let sym3 = [
  (Fun("x", [Var "p1"]), Fun("x", [Var "p2"]));
  (Fun("y", [Var "p1"]), Fun("y", [Var "p4"]));
  (Fun("z", [Var "p1"]), Fun("z", [Var "p6"]));
];;

let sym4 = [
  (Fun("a", [Var "tx"; Fun("a", [Var "ty"; Fun("a", [Var "tz";Var "t2"])])]), Fun("a", [Fun("a", [Var "ta"; Fun("a", [Var "tb"; Var "ta"])]); Var "t1"]));
  (Var("ty"), Fun("a", [Var "tz"; Var "t4"]));
  (Var("tx"), Fun("a", [Var "tz"; Var "t3"]));
  (Var("t3"), Fun("a", [Var "t4"; Var "t2"]));
];;

let sym5 = [
  (Fun ("x", [Var "p1"]), Fun ("x", [Var "p2"]));
  (Fun ("y", [Var "p2"]), Fun ("y", [Var "p4"]));
  (Fun ("z", [Var "p5"]), Fun ("z", [Var "p6"]));
];;

let sol5 = [
  ("p5", Var "p6");
  ("p2", Var "p4");
  ("p1", Var "p4");
];;

let sym6 = [
  (Fun ("x", [Var "p1"]), Fun ("x", [Var "p1"]));
];;

let sol6 = [];;

let substitution = [
  ("p1", Var "s1");
  ("p2", Var "s2");
  ("p3", Var "s3");
];;

let system_to_equation_compare (exp1, exp2) (res1, res2) =
  match (exp1, exp2, res1, res2) with
  | (Fun (exp_n1, exp_a1), Fun (exp_n2, exp_a2), Fun (res_n1, res_a1), Fun (res_n2, res_a2)) ->
    exp_n1 = exp_n2 && res_n1 = res_n2 && exp_a1 = res_a1 && exp_a2 = res_a2
  | _ -> false;;

test "system_to_equation"
  ~tester: system_to_equation
  ~compare: system_to_equation_compare
  ~string_of: string_of_equation
  (Stream.of_list [
      { input = sym1; output = (term_of_string "temp(x(p1), y(p3), z(p5))", term_of_string "temp(x(p2), y(p4), z(p6))") };
      { input = sym2; output = (term_of_string "temp(x(p1), m(p1), z(p5))", term_of_string "temp(x(p2), y(p4), z(p6))") };
      { input = sym3; output = (term_of_string "temp(x(p1), y(p1), z(p1))", term_of_string "temp(x(p2), y(p4), z(p6))") };
      { input = sym4; output = (term_of_string "temp(a(tx, a(ty, a(tz, t2))), ty, tx, t3)", term_of_string "temp(a(a(ta, a(tb, ta)), t1), a(tz, t4), a(tz, t3), a(t4, t2))") };
    ]);;

test "apply_substitution"
  ~tester: (fun (x, y) -> apply_substitution x y)
  ~string_of: string_of_term
  (Stream.of_list [
      { input = (substitution, term_of_string "temp(x(p1), y(p2), z(p5))"); output = term_of_string "temp(x(s1), y(s2), z(p5))" };
      { input = (substitution, term_of_string "temp(x(p2), y(p4), z(p6))"); output = term_of_string "temp(x(s2), y(p4), z(p6))" };
    ]);;

test "check_solution"
  ~tester: (fun (x, y) -> check_solution x y)
  ~string_of: string_of_bool
  (Stream.of_list [
      { input = (sol1, sym1); output = true };
      { input = (sol5, sym5); output = true };
      { input = (substitution, sym1); output = false };
    ]);;

let string_of_solution solution =
  match solution with
  | Some s -> String.concat "; " (List.map (fun (v, t) -> v ^ " = " ^ (string_of_term t)) s)
  | None -> "No solution";;

test "solve_system"
  ~tester: solve_system
  ~string_of: string_of_solution
  (Stream.of_list [
      { input = sym1; output = Some sol1
          };
      { input = sym2; output = None };
      { input = sym3; output = Some [
            ("p4", Var "p6");
            ("p2", Var "p6");
            ("p1", Var "p6");
          ] };
      { input = sym4; output = Some [
            ("t4", term_of_string "tb");
            ("t2", term_of_string "ta");
            ("t1", term_of_string "a(a(ta, tb), a(ta, ta))");
            ("t3", term_of_string "a(tb, ta)");
            ("tx", term_of_string "a(ta, a(tb, ta))");
            ("ty", term_of_string "a(ta, tb)");
            ("tz", term_of_string "ta");
          ] };
      { input = sym5; output = Some sol5 };
      { input = sym6; output = Some sol6 };
    ]);;
