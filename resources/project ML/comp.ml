(*******************************************************************************
 * Project of Programming Languages 2013-14
 * Part V - Compiler
 * Author:  Giilberto File`
 * Student: Marco Zanella, mat. 1079762
*******************************************************************************)



(*******************************************************************************
 * Dependencies.
*******************************************************************************)
use "synt.ml"; 



(*******************************************************************************
 * Datatypes.
*******************************************************************************)

(* Expression for the SECD machine. *)
datatype secdexpr = Var of string
                  | Add
                  | Sub
                  | Mult
                  | Div
                  | Rem
                  | Eq
                  | Leq
                  | Car
                  | Cdr
                  | Cons
                  | Atom
                  | Join
                  | Rtn
                  | Stop
                  | Push
                  | Ap
                  | Rap
                  | Ld of int*int
                  | Ldc of LKC
                  | Sel of secdexpr list * secdexpr list
                  | Ldf of secdexpr list
                  ;



(*******************************************************************************
 * Auxiliary functions used to compute the address of a variable within the
 * environment.
*******************************************************************************)

(* Position of given identifier is computed. *)
fun position(x : string, LKC_VAR(w)::a : LKC list) : int =
      if x = w then 0 else 1 + position(x, a)
  | position(x : string, _             : LKC list) : int =
      0
;



(* Predicate which tells whenever a given LKC list contains an identifier x. *)
fun member(x : string, LKC_VAR(w)::l : LKC list) : bool =
      if x = w then true else member(x, l)
  | member(x : string, _             : LKC list) : bool =
      false
;



(* Location of given identifier is computed. *)
fun location(x : string, ct : int, n : LKC list list) : int * int =
      if member(x, hd(n)) then
        (ct, position(x, hd(n)))
      else
        location(x, ct + 1, tl(n))
;



(* Given list is reversed. *)
fun sexpr_reverse([])   = []
  | sexpr_reverse(a::l) = sexpr_reverse(l @ [a])
;



(* Variables are removed from a list of binders. *)
fun vars(nil)      = []
  | vars((x,y)::R) = x::vars(R)
;



(* Expressions are removed from a list of binders.*)
fun exprs(nil)      = []
  | exprs((x,y)::R) = y::exprs(R)
;



(* ??? *)
fun complist(nil  : LKC list, n : (LKC list) list, c : secdexpr list) : secdexpr list =
      (Ldc LKC_Nil)::c
  | complist(x::y : LKC list, n : (LKC list) list, c : secdexpr list) : secdexpr list =
      complist(y, n, COMP(x, n, Cons::c))



(* Compiler. Two auxiliary fields are used to make the recursion easier. *)
and COMP(e : LKC, n : (LKC list) list, c : secdexpr list) : secdexpr list =
      case e
        of LKC_VAR(x)       => Ld(location(x, 0, n))::c
         | LKC_NM(x)        => Ldc(LKC_NM(x))::c
         | LKC_BOOL(x)      => Ldc(LKC_BOOL(x))::c
         | LKC_STR(x)       => Ldc(LKC_STR(x))::c
         | LKC_Nil          => Ldc(LKC_Nil)::c
         | LKC_ADD(x, y)    => COMP(y, n, COMP(x, n, Add::c))
         | LKC_SUB(x, y)    => COMP(y, n, COMP(x, n, Sub::c))
         | LKC_MUL(x, y)    => COMP(y, n, COMP(x, n, Mult::c))
         | LKC_DIV(x, y)    => COMP(y, n, COMP(x, n, Div::c))
        (* | LKC_REM(x, y)    => COMP(y, n, COMP(x, n, Rem::c))*)
         | LKC_EQ(x, y)     => COMP(y, n, COMP(x, n, Eq::c))
         | LKC_LEQ(x, y)    => COMP(y, n, COMP(x, n, Leq::c))
         | LKC_CAR(x)       => COMP(x, n, Car::c)
         | LKC_CDR(x)       => COMP(x, n, Cdr::c)
         | LKC_CONS(x, y)   => COMP(y, n, COMP(x, n, Cons::c))
         | LKC_ATOM(x)      => COMP(x, n, Atom::c)
         | LKC_IF(x, y, z)  => let
                                 val thenp = COMP(y, n, [Join])
                                 and elsep = COMP(z, n, [Join])
                               in
                                 COMP(x, n, Sel(thenp, elsep)::c)
                               end
         | LKC_LAMBDA(x, y) => Ldf(COMP(y, x::n, [Rtn]))::c
         | LKC_LET(x, y)    => let
                                 val var_list = vars(y)
                                 val exp_list = exprs(y)
                               in
                                 complist(exp_list, n, [Ldf(COMP(x, var_list::n, [Rtn]))] @ [Ap] @ c)
                               end
         | LKC_LETREC(x, y) => let
                                 val var_list = vars(y)
                                 val exp_list = exprs(y)
                               in
                                 complist(exp_list, var_list::n, [Ldf(COMP(x, var_list::n, [Rtn]))] @ [Rap] @ c)
                               end
         | LKC_CALL(x, y)   => complist(y, n, COMP(x, n, Ap::c))
;



(*******************************************************************************
 * Actual compiler.
*******************************************************************************)

(* Exception handler. *)
fun compHandler(field : string) =
      let
        val msg = print("Compiler terminated due to a " ^ field ^ " error.\n")
      in
        []
      end
;

(* Compiler function. *)
fun comp(program : string) : secdexpr list =
      COMP(synt(lexi(explode(program))), [], [])
        handle LexicalException   => compHandler("lexical")
             | SyntacticException => compHandler("syntactic")
;

