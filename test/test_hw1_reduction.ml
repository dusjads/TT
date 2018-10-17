open Test;;
open Hw1;;
open Hw1_reduction;;

test "free_to_subst"
  ~tester: (fun (src, dest, key) -> free_to_subst src dest key)
  ~string_of: string_of_bool
  (Stream.of_list [
      { input = (lambda_of_string "x", lambda_of_string "\\x.y", "y"); output = false };
      { input = (lambda_of_string "x", lambda_of_string "\\x.x", "y"); output = true };
      { input = (lambda_of_string "x", lambda_of_string "(x) (\\x.y)", "y"); output = false };
      { input = (lambda_of_string "x y \\z.z", lambda_of_string "\\x.a", "a"); output = false };
      { input = (lambda_of_string "x y \\z.z", lambda_of_string "\\y.a", "a"); output = false };
      { input = (lambda_of_string "x y \\z.z", lambda_of_string "\\z.a", "a"); output = true };
      { input = (lambda_of_string "x y \\z.z", lambda_of_string "a (\\z.a)", "a"); output = true };
      { input = (lambda_of_string "x y \\z.z", lambda_of_string "\\x.b", "a"); output = true };
    ]);;

test "free_vars"
  ~tester: free_vars
  ~string_of: (String.concat "; ")
  (Stream.of_list [
      { input = lambda_of_string "x"; output = ["x"] };
      { input = lambda_of_string "\\x.x"; output = [] };
      { input = lambda_of_string "(x) (\\x.y)"; output = ["x";"y"] };
    ]);;

test "is_normal_form"
  ~tester: is_normal_form
  ~string_of: string_of_bool
  (Stream.of_list [
      { input = lambda_of_string "x"; output = true };
      { input = lambda_of_string "\\x.x"; output = true };
      { input = lambda_of_string "(x) (\\x.y)"; output = true };
    ]);;

test "is_alpha_equivalent"
  ~tester: (fun (x, y) -> is_alpha_equivalent x y)
  ~string_of: string_of_bool
  (Stream.of_list [
      { input = (lambda_of_string "(x)", lambda_of_string "(y)"); output = false };
      { input = (lambda_of_string "x y", lambda_of_string "x y"); output = true };
      { input = (lambda_of_string "\\x.x y", lambda_of_string "\\y.y y"); output = false };
      { input = (lambda_of_string "\\x1.x1", lambda_of_string "\\y1.y1"); output = true };
      { input = (lambda_of_string "(\\x.x)(z)(w)", lambda_of_string "(\\y.y)(z)(w)"); output = true };
      { input = (lambda_of_string "\\x1.\\x2.\\x3.\\x4.x1 x2 x3 x4", lambda_of_string "\\y1.\\y2.\\y3.\\y4.y1 y2 y3 y4"); output = true };
      { input = (lambda_of_string "\\x1.\\x2.\\x3.\\x4.x4 x2 x3 x1", lambda_of_string "\\y1.\\y2.\\y3.\\y4.y1 y2 y3 y4"); output = false };
      { input = (lambda_of_string "\\x1.\\x2.x1 x2", lambda_of_string "\\y1.\\y2.y2 y1"); output = false };
      { input = (lambda_of_string "\\x.x", lambda_of_string "\\a.x"); output = false };
      { input = (lambda_of_string "\\b.\\a.a", lambda_of_string "\\x.\\x.x"); output = true};
    ]);;

test "normal_beta_reduction"
  ~tester: normal_beta_reduction
  ~string_of: string_of_lambda
  ~compare: is_alpha_equivalent
  (Stream.of_list [
      { input = (lambda_of_string "x"); output = lambda_of_string "x" };
      { input = (lambda_of_string "\\x.x"); output = lambda_of_string "\\x.x" };
      { input = (lambda_of_string "(x) (\\x.y)"); output = lambda_of_string "(x) (\\x.y)" };
      { input = (lambda_of_string "(\\x.y) x"); output = lambda_of_string "y" };
      { input = (lambda_of_string "(\\x.x) a"); output = lambda_of_string "a" };
      { input = (lambda_of_string "a ((\\y.\\z.y) (\\p.p))"); output = lambda_of_string "a \\z.\\p.p" };
      { input = (lambda_of_string "(\\x.x) (\\y.y) (\\z.z))"); output = lambda_of_string "((\\y.y) (\\z.z))" };
      { input = (lambda_of_string "\\z.((\\x.x) y)"); output = lambda_of_string "\\z.y" };
      { input = (lambda_of_string "((\\x.\\y.x)(\\z.y)) k"); output = lambda_of_string "((\\y1.(\\z.y)) k)" };
    ]);;


test "reduce_to_normal_form"
  ~tester: reduce_to_normal_form
  ~string_of: string_of_lambda
  ~compare: is_alpha_equivalent
  (Stream.of_list [
      { input = (lambda_of_string "(\\x.\\y.y)((\\z.z z)(\\z.z z))"); output = lambda_of_string "\\y.y"};
      { input = (lambda_of_string "a ((\\y.\\z.y) (\\p.p))"); output = lambda_of_string "a \\z.\\p.p"};
      { input = (lambda_of_string "(\\x.x) (\\y.y) (\\z.z))"); output = lambda_of_string "(\\z.z)"};
      { input = (lambda_of_string "(\\n.\\f.\\x.f (n f x)) (\\f.\\x.f x)"); output = lambda_of_string "\\f.\\x.f (f x)"};
      { input = (lambda_of_string "(\\x.x x)(\\a.\\b.b b b)"); output = lambda_of_string "\\b.b b b"};
      { input = (lambda_of_string "(\\x.x x x)((\\x.x)(\\x.x))"); output = lambda_of_string "\\x.x"};
      { input = (lambda_of_string "(\\x.\\y.x)(\\x.x)((\\x.x x)(\\x.x x))"); output = lambda_of_string "\\x.x"};
      { input = (lambda_of_string "(\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)) (\\f.\\x.f (f (f x)))"); output = lambda_of_string "(\\f.(\\x.(f (f x))))"};
      { input = (lambda_of_string "((\\x.\\y.x)(\\z.y)) k"); output = lambda_of_string "\\z.y"};
      { input = (lambda_of_string "(\\x.\\y.x) k"); output = lambda_of_string "\\y.k"};
      { input = (lambda_of_string "(\\y.\\m.y (\\f.\\n.(\\s.(s (\\x.\\a.\\b.b) (\\a.\\b.a)) (\\f.\\x.x) (f s)) (m n)) (\\f.\\x.f (f (f x)))) (\\f.(\\x.f (x x)) (\\x.f (x x))) ((\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)))"); output = lambda_of_string "(\\t.(\\t1.t1))"};
      { input = (lambda_of_string "(\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)) (\\f.\\x.f (f (f x)))"); output = lambda_of_string "\\x1.\\x2.(x1 (x1 x2))"};
      { input = (lambda_of_string "((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((l13 (\\l14.(\\l15.(l14 (l14 l15))))) (\\l14.(\\l15.(l14 (l14 (l14 l15))))))) (\\l13.(\\l14.(((l0 (\\l15.(\\l16.(\\l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (\\l18.(\\l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (\\l12.(\\l13.(\\l14.((l12 l13) (l13 l14))))))) (\\l11.(\\l12.(\\l13.(((l11 (\\l14.(\\l15.(l15 (l14 l12))))) (\\l14.l13)) (\\l14.l14))))))) (\\l10.((l10 (\\l11.l3)) l2)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))"); output = lambda_of_string "\\x1.(\\x2.(x1 (x1 (x1 (x1 (x1 (x1 (x1 (x1 (x1 x2))))))))))"};
      { input = (lambda_of_string "(\\s.\\k.\\i.(((s ((s (k s)) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s ((s (k s)) ((s (k (s (k (s ((s ((s ((s i) (k (k (k i))))) (k ((s (k k)) i)))) (k ((s ((s (k s)) ((s (k k)) i))) (k i))))))))) ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k (s (k ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k k)) i))))) (k ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) (k ((s (k k)) i)))))))) ((s (k k)) ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) (k (k ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) ((s ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i))))) ((s ((s (k s)) ((s (k (s (k s)))) ((s ((s (k s)) ((s (k (s (k s)))) ((s (k (s (k k)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s (k (s i))))) ((s (k (s (k k)))) ((s (k (s i))) ((s (k k)) i)))))))))) (k (k ((s (k k)) i))))))) (k (k (k i))))) (\\x.\\y.\\z.x z (y z)) (\\x.\\y.x) (\\x.x)"); output = lambda_of_string "(\\t9.(\\t2.(t9 (t9 (t9 (t9 (t9 (t9 t2))))))))"}
    ]);;