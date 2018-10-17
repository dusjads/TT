open Hw1;;

print_int (Hw1.int_of_peano (S(S (S (Z)))));;
print_endline "";;

print_endline (Hw1.string_of_lambda (Hw1.lambda_of_string "\\x.\\y.x"));;

let b = [];;
let b = Hw1.append b 2;;
let b = Hw1.append b 4;;
let b = Hw1.append b 3;;

let la = Hw1.App(Hw1.Var("y"), Hw1.Abs("x", Hw1.Var("x")));;

print_int (Hw1.int_of_peano Z);;
print_endline "\npeano_of_int";;
print_int (Hw1.int_of_peano (Hw1.peano_of_int 7));;
print_endline "\nstring_of_lambda";;
print_endline (Hw1.string_of_lambda la);;
Hw1.print_array (Hw1.merge_sort [3;2;6;1;4;5;3]);;
Hw1.print_array (Hw1.rev (Hw1.merge_sort [3;2;6;1;4;5;3]))