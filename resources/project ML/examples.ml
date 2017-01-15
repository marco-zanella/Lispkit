(*******************************************************************************
 * Dependencies.
*******************************************************************************)
use "SECD.ml";



(*******************************************************************************
 * Examples for part V of the project.
*******************************************************************************)

(* Given by the teacher. *)
val C = "letrec FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else X * FACT( X -"^
        " 1 ) and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car"^
        "( L ) ), G ( H, cdr ( L ) ) ) in G ( FACT, cons(1 ,cons(2, cons(3, nil"^
        "))) ) end $";

(* Given by the teacher. *)
val S = "let x= 5 and y= 6 in x*3 + y * 2* x + x*y end $";

(* Very simple test. Expected output is 42. *)
val very_simple = "let x = 42 in x end $";

(* Simple test. Expected output is 1017. *)
val simple = "let x = 42 and y = 24 in x*y + 9 - y/x * (x+y/x - x/y) end $";

(* Test with functions. Expected output is ~32. *)
val functions = "let foo = lambda(x) x*2+5 and bar = lambda(x y) (x+y) * (x-y) in bar(foo(1),foo(2)) end $";

(* Test with nested stuffs. Expected output is 5. *)
val nested = "let foo = lambda(x y) let z = x+y in z end in foo(2, 3) end $";

(* Test with lists. Expected output is a list [a, b]. *)
val lists = "let lst = cons(\"a\", cons(\"b\", nil)) in lst end $";

(* More on lists. Expected output is [1, 2, 3]. *)
val more_lists = "let lst = cons(1, cons(2, cons(3, nil))) in cons(car(lst), cdr(lst)) end $";

(* Test on equality and inequality. Expected output is ~1. *)
val truth = "let x=2 in if eq(x, 3) then 0 else if leq(x, 3) then ~1 else 1 end $";

(* Test on recursion. *)
val recursion = "letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X "^
"- 1 ) and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car( L ) )"^ 
",G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $";