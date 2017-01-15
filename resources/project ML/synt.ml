(*******************************************************************************
 * Project of Programming Languages 2013-14
 * Part IV - Syntactic Analyzer and translator
 * Author:  Giilberto File`
 * Student: Marco Zanella, mat. 1079762
 *
 * The grammar used to implement this syntactic analyzer is represented by:
 * Prog    ::= let Bind in Exp end
 *           | letrec Bind in Exp end
 * Bind    ::= var = Exp X
 * X       ::= and Bind
 *           | e
 * Exp     ::= Prog
 *           | lambda ( Seq_Var ) Exp
 *           | ExpA
 *           | OPP ( Seq_Exp )
 *           | if Exp then Exp else Exp
 * ExpA    ::= T E1
 * E1      ::= OPA T E1
 *           | e
 * T       ::= F T1
 * T1      ::= OPM F T1
 *           | e
 * F       ::= var Y
 *           | exp_const
 *           | ( ExpA )
 * Y       ::= ( Seq_Exp )
 *           | e
 * OPA     ::= +
 *           | -
 * OPM     ::= *
 *           | /
 * OPP     ::= cons
 *           | car
 *           | cdr
 *           | eq
 *           | leq
 *           | atom
 * Seq_Exp ::= Exp Lst_Exp
 *           | e
 * Lst_Exp ::= , Seq_Exp
 *           | e
 * Seq_Var ::= var Seq_Var
 *           | e
 * This context free grammar is LL(1) (Look-ahead, Left-derivation).
 * The algorithm here implemented aims to be as more 'functional-like' as
 * possible, defining a certain number of functions, one for each symbol
 * (either terminal or non-terminal( in the context free, LL(1) grammar and
 * applying composition of functions.
 * The right composition of functions to use is selected looking at the first
 * terminal symbol on top of the token list and at the parsing table of the
 * grammar (this is possible due to the fact that the grammar is LL(1)).
 * The Syntactic Analyzer also translates the program to an intermediate format
 * called LkC ("LispKit Concreto").
*******************************************************************************)


(*******************************************************************************
 * Dependencies.
*******************************************************************************)
use "lexi.ml";


(*******************************************************************************
 * Exceptions.
*******************************************************************************)

(* A constant expression was expected but not found. *)
exception NOCONST of token list;

(* Unexpected end of token list was reached. *)
exception unexpEOF;

(* A token was expected, but something else was found. *)
exception expButFound of string * string * token list;

(* General syntactic exception. *)
exception SyntacticException;



(*******************************************************************************
 * Data types.
*******************************************************************************)

(* Type used to represent an LKC tree. *)
datatype LKC = LKC_VAR    of string
             | LKC_NM     of int
             | LKC_BOOL   of B
             | LKC_STR    of string
             | LKC_Nil
             | LKC_ADD    of LKC * LKC
             | LKC_SUB    of LKC * LKC
             | LKC_MUL    of LKC * LKC
             | LKC_DIV    of LKC * LKC
             | LKC_EQ     of LKC * LKC
             | LKC_LEQ    of LKC * LKC
             | LKC_CAR    of LKC
             | LKC_CDR    of LKC
             | LKC_CONS   of LKC * LKC
             | LKC_ATOM   of LKC
             | LKC_IF     of LKC * LKC * LKC
             | LKC_LAMBDA of LKC list * LKC
             | LKC_CALL   of LKC * LKC list
             | LKC_LET    of LKC * (LKC * LKC) list
             | LKC_LETREC of LKC * (LKC * LKC) list
             ;



(*******************************************************************************
 * Support functions.
*******************************************************************************)

(* The string value associated to the given token is returned. *)
fun tokenToString(KEYWORD(s) : token) : string = s
  | tokenToString(ID(s)      : token) : string = s
  | tokenToString(OP(s)      : token) : string = s
  | tokenToString(SYM(s)     : token) : string = s
  | tokenToString(STR(s)     : token) : string = s
  | tokenToString(NM(n)      : token) : string = "NM"
  | tokenToString(BOOL(b)    : token) : string = "BOOL"
  | tokenToString(Nil        : token) : string = "Nil"
  ;

(* The given list of token is converted to a string. *)
fun tokenListToString(tkn::tkn_list : token list) : string =
      tokenToString(tkn) ^ " " ^ tokenListToString(tkn_list)
  | tokenListToString(nil           : token list) : string =
      ""
  ;

(* Top element of a token list is compared to a given string. If there is not
   correspondency, an exception is thrown. *)
fun tokenCmp(str : string, tkn::tkn_lst : token list) : token list =
      let
        val tkn_str = tokenToString(tkn)
      in
        if str = tkn_str then
          tkn_lst
        else
          raise expButFound(str, tkn_str, tkn::tkn_lst)
      end
  | tokenCmp(str : string, nil : token list) : token list =
          raise unexpEOF
  ;



(*******************************************************************************
 * Syntactic Analyzer.
*******************************************************************************)

(* Using 'let' creates a kind of namespace, avoiding name conficlts among
   functions defined in different parts of the program. *)
val PROG = let
  (****************************************************************************)
  (* Functions used to consume Terminal Symbols. *)
  
  (* Terminal Symbol 'let'. *)
  fun LET(c : token list) : token list = tokenCmp("let", c)
  
  (* Terminal Symbol 'letrec'. *)
  and LETREC(c : token list) : token list = tokenCmp("letrec", c)
  
  (* Terminal Symbol 'in'. *)
  and IN(c : token list) : token list = tokenCmp("in", c)
  
  (* Terminal Symbol 'end'. *)
  and END(c : token list) : token list = tokenCmp("end", c)
  
  (* Terminal Symbol '=', which stands for 'assignement'. *)
  and ASSIGN(c : token list) : token list = tokenCmp("=", c)
  
  (* Terminal Symbol 'and'. *)
  and AND(c : token list) : token list = tokenCmp("and", c)
  
  (* Terminal Symbol 'lambda'. *)
  and LAMBDA(c : token list) : token list = tokenCmp("lambda", c)
  
  (* Terminal Symbol 'if'. *)
  and IF(c : token list) : token list = tokenCmp("if", c)
  
  (* Terminal Symbol 'then'. *)
  and THEN(c : token list) : token list = tokenCmp("then", c)
  
  (* Terminal Symbol 'else'. *)
  and ELSE(c : token list) : token list = tokenCmp("else", c)
  
  (* Terminal Symbol 'exp_const', which may be one of NM, Nil, BOOL or STR. *)
  and EXP_CONST(NM(n)::c   : token list) : token list = c
    | EXP_CONST(Nil::c     : token list) : token list = c
    | EXP_CONST(BOOL(b)::c : token list) : token list = c
    | EXP_CONST(STR(s)::c  : token list) : token list = c
    | EXP_CONST(nil        : token list) : token list = raise unexpEOF
    | EXP_CONST(t          : token list) : token list = raise NOCONST(t)
  
  (* Terminal Symbol '(', which stands for left parenthesys, 'LPAR'. *)
  and LPAR(c : token list) : token list = tokenCmp("(", c)
  
  (* Terminal Symbol ')', which stands for right parenthesys, 'RPAR'. *)
  and RPAR(c : token list) : token list = tokenCmp(")", c)
  
  (* Terminal Symbol '+', which stands for 'PLUS'. *)
  and PLUS(c : token list) : token list = tokenCmp("+", c)
  
  (* Terminal Symbol '-', which stands for 'MINUS'. *)
  and MINUS(c : token list) : token list = tokenCmp("-", c)
  
  (* Terminal Symbol '*', which stands for 'DOT'. *)
  and DOT(c : token list) : token list = tokenCmp("*", c)
  
  (* Terminal Symbol '/', which stands for 'DIV'. *)
  and DIV(c : token list) : token list = tokenCmp("/", c)
  
  (* Terminal Symbol 'cons'. *)
  and CONS(c : token list) : token list = tokenCmp("cons", c)
  
  (* Terminal Symbol 'car'. *)
  and CAR(c : token list) : token list = tokenCmp("car", c)
  
  (* Terminal Symbol 'cdr'. *)
  and CDR(c : token list) : token list = tokenCmp("cdr", c)
  
  (* Terminal Symbol 'eq'. *)
  and EQ(c : token list) : token list = tokenCmp("eq", c)
  
  (* Terminal Symbol 'leq'. *)
  and LEQ(c : token list) : token list = tokenCmp("leq", c)
  
  (* Terminal Symbol 'atom'. *)
  and ATOM(c : token list) : token list = tokenCmp("atom", c)
  
  (* Terminal Symbol ',', which stands for 'comma'. *)
  and COMMA(c : token list) : token list = tokenCmp(",", c)
  
  (* Terminal Symbol 'var', which is an identifier. *)
  and VAR(ID(i)::c     : token list) : token list = c
    | VAR(tkn::tkn_lst : token list) : token list =
        raise expButFound("identifier", tokenToString(tkn), tkn::tkn_lst)
    | VAR(nil          : token list) : token list = raise unexpEOF
  
  (* Terminal Symbol '$', which stands for End Of Program (EOP). *)
  and EOP(c : token list) : token list = tokenCmp("$", c)
  
  
        
  (****************************************************************************)
  (* Functions used to consume Non-Terminal Symbols. *)
  
  (* Production for the Non-Terminal 'Prog'. *)
  and Prog(t::c : token list) : LKC * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "let"     => 
                 let
                   val bind = Bind(LET(tkn_list))
                   val exp  = Exp(IN(#2bind))
                   val nxt  = END(#2exp)
                 in
                   (LKC_LET(#1exp, #1bind), nxt)
                 end
             | "letrec"  =>
                 let
                   val bind = Bind(LETREC(tkn_list))
                   val exp  = Exp(IN(#2bind))
                   val nxt  = END(#2exp)
                 in
                   (LKC_LETREC(#1exp, #1bind), nxt)
                 end
             | _         => raise expButFound("let | letrec", nxt_term, tkn_list)
        end
     | Prog(nil : token list) : LKC * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'Bind' *)
  and Bind(ID(a)::c : token list) : (LKC * LKC) list * token list = 
        let
          val bind = Exp(ASSIGN(VAR(ID(a)::c)))
          val nxt  = X(#2bind)
        in
          ((LKC_VAR(a), #1bind) :: #1(nxt), #2nxt)
        end
    | Bind(t::c     : token list) : (LKC * LKC) list * token list =
        raise expButFound("identifier", tokenToString(t), t::c)
    | Bind(nil      : token list) : (LKC * LKC) list * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'X'. *)
  and X(t::c : token list) : (LKC * LKC) list * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "in"  => ([], tkn_list)
             | "and" => Bind(AND(tkn_list))
             | _     => raise expButFound("in | and", nxt_term, tkn_list)
        end
    | X(nil  : token list) : (LKC * LKC) list * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'Exp'. *)
  and Exp(ID(t)::c   : token list) : LKC * token list = ExpA(ID(t)::c)
    | Exp(NM(n)::c   : token list) : LKC * token list = ExpA(NM(n)::c)
    | Exp(Nil::c     : token list) : LKC * token list = ExpA(Nil::c)
    | Exp(BOOL(b)::c : token list) : LKC * token list = ExpA(BOOL(b)::c)
    | Exp(STR(s)::c  : token list) : LKC * token list = ExpA(STR(s)::c)
    | Exp(t::c       : token list) : LKC * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "let"    => Prog(tkn_list)
             | "letrec" => Prog(tkn_list)
             | "lambda" =>
                 let
                   val seq_var = Seq_Var(LPAR(LAMBDA(tkn_list)))
                   val exp     = Exp(RPAR(#2seq_var))
                 in
                   (LKC_LAMBDA(#1seq_var, #1exp), #2exp)
                 end
             | "if"     =>
                 let
                   val guard       = Exp(IF(tkn_list))
                   val then_branch = Exp(THEN(#2guard))
                   val else_branch = Exp(ELSE(#2then_branch))
                 in
                   (LKC_IF(#1guard, #1then_branch, #1else_branch), #2else_branch)
                 end
             | "("      => ExpA(tkn_list)
             | "cons"   => 
                 let
                   val exp1 = Exp(LPAR(OPP(tkn_list)))
                   val exp2 = Exp(COMMA(#2exp1))
                   val nxt  = RPAR(#2exp2)
                 in
                   (LKC_CONS(#1exp1, #1exp2), nxt)
                 end
             | "car"    => 
                 let
                   val exp = Exp(LPAR(OPP(tkn_list)))
                   val nxt = RPAR(#2exp)
                 in
                   (LKC_CAR(#1exp), nxt)
                 end
             | "cdr"    =>
                 let
                   val exp = Exp(LPAR(OPP(tkn_list)))
                   val nxt = RPAR(#2exp)
                 in
                   (LKC_CDR(#1exp), nxt)
                 end
             | "eq"     =>
                 let
                   val exp1 = Exp(LPAR(OPP(tkn_list)))
                   val exp2 = Exp(COMMA(#2exp1))
                   val nxt  = RPAR(#2exp2)
                 in
                   (LKC_EQ(#1exp1, #1exp2), nxt)
                 end
             | "leq"    =>
                 let
                   val exp1 = Exp(LPAR(OPP(tkn_list)))
                   val exp2 = Exp(COMMA(#2exp1))
                   val nxt  = RPAR(#2exp2)
                 in
                   (LKC_LEQ(#1exp1, #1exp2), nxt)
                 end
             | "atom"   =>
                 let
                   val exp = Exp(LPAR(OPP(tkn_list)))
                   val nxt = RPAR(#2exp)
                 in
                   (LKC_ATOM(#1exp), nxt)
                 end
             | _        => raise expButFound(
                             "let | letrec | lambda | if | ( | cons | car | " ^
                             "cdr | eq | leq | atom | identifier | constant " ^
                             "expression",
                             nxt_term,
                             tkn_list
                           )
        end
    | Exp(nil        : token list) : LKC * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'ExpA'. *)
  and ExpA(ID(t)::c   : token list) : LKC * token list = E1(T(ID(t)::c))
    | ExpA(NM(n)::c   : token list) : LKC * token list = E1(T(NM(n)::c))
    | ExpA(Nil::c     : token list) : LKC * token list = E1(T(Nil::c))
    | ExpA(BOOL(b)::c : token list) : LKC * token list = E1(T(BOOL(b)::c))
    | ExpA(STR(s)::c  : token list) : LKC * token list = E1(T(STR(s)::c))
    | ExpA(t::c       : token list) : LKC * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "(" => E1(T(tkn_list))
             | _   => raise expButFound(
                        "constant expression | ( | identifier",
                         nxt_term,
                         tkn_list
                       )
        end
    | ExpA(nil        : token list) : LKC * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'E1'. *)
  and E1(first_op : LKC, t::c : token list) : LKC * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "in"   => (first_op, tkn_list)
             | "end"  => (first_op, tkn_list)
             | "and"  => (first_op, tkn_list)
             | "then" => (first_op, tkn_list)
             | "else" => (first_op, tkn_list)
             | ")"    => (first_op, tkn_list)
             | "+"    =>
                 let
                   val t = T(OPA(tkn_list))
                 in
                   E1(LKC_ADD(first_op, #1t), #2t)
                 end
             | "-"    =>
                 let
                   val t = T(OPA(tkn_list))
                 in
                   E1(LKC_SUB(first_op, #1t), #2t)
                 end
             | ","    => (first_op, tkn_list)
             | _      => raise expButFound(
                           "in | end | and | then | else | ) | + | - | ,",
                           nxt_term,
                           tkn_list
                         )
        end
    | E1(_        : LKC, nil  : token list) : LKC * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'T' *)
  and T(ID(t)::c   : token list) : LKC * token list = T1(F(ID(t)::c))
    | T(NM(n)::c   : token list) : LKC * token list = T1(F(NM(n)::c))
    | T(Nil::c     : token list) : LKC * token list = T1(F(Nil::c))
    | T(BOOL(b)::c : token list) : LKC * token list = T1(F(BOOL(b)::c))
    | T(STR(s)::c  : token list) : LKC * token list = T1(F(STR(s)::c))
    | T(t::c       : token list) : LKC * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "(" => T1(F(tkn_list))
             | _   => raise expButFound(
                        "constant expression | ( | identifier",
                        nxt_term,
                        tkn_list
                      )
        end
    | T(nil        : token list) : LKC * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'T1'. *)
  and T1(first_op : LKC, t::c : token list) : LKC * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "in"   => (first_op, tkn_list)
             | "end"  => (first_op, tkn_list)
             | "and"  => (first_op, tkn_list)
             | "then" => (first_op, tkn_list)
             | "else" => (first_op, tkn_list)
             | ")"    => (first_op, tkn_list)
             | "+"    => (first_op, tkn_list)
             | "-"    => (first_op, tkn_list)
             | "*"    =>
                 let
                   val f = F(OPM(tkn_list))
                 in
                   T1(LKC_MUL(first_op, #1f), #2f)
                 end
             | "/"    =>
                 let
                   val f = F(OPM(tkn_list))
                 in
                   T1(LKC_DIV(first_op, #1f), #2f)
                 end
             | ","    => (first_op, tkn_list)
             | _      => raise expButFound(
                           "in | end | and | then | else | ) | + | - | * | / | ,",
                           nxt_term,
                           tkn_list
                         )
        end
    | T1(_        : LKC, nil  : token list) : LKC * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'F'. *)
  and F(ID(t)::c   : token list) : LKC * token list =
        let
          val y = Y(VAR(ID(t)::c))
        in
          if "(" = tokenToString(hd(c)) then
            (LKC_CALL(LKC_VAR(t), #1y), #2y)
          else
            (LKC_VAR(t), c)
        end
    | F(NM(n)::c   : token list) : LKC * token list =
        (LKC_NM(n), EXP_CONST(NM(n)::c))
    | F(Nil::c     : token list) : LKC * token list =
        (LKC_Nil, EXP_CONST(Nil::c))
    | F(BOOL(b)::c : token list) : LKC * token list =
        (LKC_BOOL(b), EXP_CONST(BOOL(b)::c))
    | F(STR(s)::c  : token list) : LKC * token list =
        (LKC_STR(s), EXP_CONST(STR(s)::c))
    | F(t::c       : token list) : LKC * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "(" => 
                 let
                   val expa = ExpA(LPAR(tkn_list))
                   val nxt  = RPAR(#2expa)
                 in
                   (#1expa, nxt)
                 end
             | _   => raise expButFound(
                        "identifier | constant_expression | )",
                        nxt_term,
                        tkn_list
                      )
        end
    | F(nil       : token list) : LKC * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'Y'. *)
  and Y(t::c : token list) : LKC list * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "in"   => (nil, tkn_list)
             | "end"  => (nil, tkn_list)
             | "and"  => (nil, tkn_list)
             | "then" => (nil, tkn_list)
             | "else" => (nil, tkn_list)
             | "("    =>
                 let
                   val seq_exp = Seq_Exp(LPAR(t::c))
                   val nxt     = RPAR(#2seq_exp)
                 in
                   (#1seq_exp, nxt)
                 end
             | ")"    => (nil, tkn_list)
             | "+"    => (nil, tkn_list)
             | "-"    => (nil, tkn_list)
             | "*"    => (nil, tkn_list)
             | "/"    => (nil, tkn_list)
             | ","    => (nil, tkn_list)
             | _      => raise expButFound(
                           "in | end | and | then | else | ( | ) | + | - | * " ^
                           "/ | ,",
                           nxt_term,
                           tkn_list
                         )
        end
    | Y(nil  : token list) : LKC list * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal OPA.  *)
  and OPA(t::c : token list) : token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "+" => PLUS(tkn_list)
             | "-" => MINUS(tkn_list)
             | _   => raise expButFound("+ | -", nxt_term, tkn_list)
        end
    | OPA(nil  : token list) : token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal OPM.  *)
  and OPM(t::c : token list) : token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "*" => DOT(tkn_list)
             | "/" => DIV(tkn_list)
             | _   => raise expButFound("* | /", nxt_term, tkn_list)
        end
    | OPM(nil  : token list) : token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal OPP.  *)
  and OPP(t::c : token list) : token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "cons" => CONS(tkn_list)
             | "car"  => CAR(tkn_list)
             | "cdr"  => CDR(tkn_list)
             | "eq"   => EQ(tkn_list)
             | "leq"  => LEQ(tkn_list)
             | "atom" => ATOM(tkn_list)
             | _   => raise expButFound(
                        "cons | car | cdr | eq | leq | atom",
                        nxt_term,
                        tkn_list
                      )
        end
    | OPP(nil  : token list) : token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'Seq_Exp'. *)
  and Seq_Exp(ID(t)::c   : token list) : LKC list * token list =
        let
          val exp     = Exp(ID(t)::c)
          val lst_exp = Lst_Exp(#2exp)
        in
          (#1exp:: #1lst_exp, #2lst_exp)
        end
    | Seq_Exp(NM(n)::c   : token list) : LKC list * token list =
        let
          val exp     = Exp(NM(n)::c)
          val lst_exp = Lst_Exp(#2exp)
        in
          (#1exp:: #1lst_exp, #2lst_exp)
        end
    | Seq_Exp(Nil::c     : token list) : LKC list * token list =
        let
          val exp     = Exp(Nil::c)
          val lst_exp = Lst_Exp(#2exp)
        in
          (#1exp:: #1lst_exp, #2lst_exp)
        end
    | Seq_Exp(BOOL(b)::c : token list) : LKC list * token list =
        let
          val exp     = Exp(BOOL(b)::c)
          val lst_exp = Lst_Exp(#2exp)
        in
          (#1exp:: #1lst_exp, #2lst_exp)
        end
    | Seq_Exp(STR(s)::c  : token list) : LKC list * token list =
        let
          val exp     = Exp(STR(s)::c)
          val lst_exp = Lst_Exp(#2exp)
        in
          (#1exp:: #1lst_exp, #2lst_exp)
        end
    | Seq_Exp(t::c       : token list) : LKC list * token list = 
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of "let"    =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "letrec" =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "lambda" =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "if"     =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "("      =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | ")"      => (nil, tkn_list)
             | "cons"   =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "car"    =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "cdr"    =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "eq"     =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "leq"    =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | "atom"   =>
                 let
                   val exp     = Exp(tkn_list)
                   val lst_exp = Lst_Exp(#2exp)
                 in
                   (#1exp:: #1lst_exp, #2lst_exp)
                 end
             | _        => raise expButFound(
                             "let | letrec | lambda | if | ( | ) | cons | car "^
                             "| cdr | eq | leq | atom | identifier | constant "^
                             "expression",
                             nxt_term,
                             tkn_list
                           )
        end
    | Seq_Exp(nil       : token list) : LKC list * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'Lst_Exp'. *)
  and Lst_Exp(t::c : token list) : LKC list * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of ")" => (nil, tkn_list)
             | "," => Seq_Exp(COMMA(tkn_list))
             | _   => raise expButFound(") | ,", nxt_term, tkn_list)
        end
    | Lst_Exp(nil  : token list) : LKC list * token list = raise unexpEOF
  
  
  (* Production for the Non-Terminal 'Seq_Var'. *)
  and Seq_Var(ID(t)::c : token list) : LKC list * token list =
        let
          val seq_var = Seq_Var(VAR(ID(t)::c))
        in
          (LKC_VAR(t):: #1seq_var, #2seq_var)
        end
    | Seq_Var(t::c     : token list) : LKC list * token list =
        let
          val nxt_term = tokenToString(t)
          val tkn_list = t::c
        in
          case nxt_term
            of ")" => (nil, tkn_list)
             | _   => raise expButFound("identifier | )", nxt_term, tkn_list)
        end
    | Seq_Var(nil      : token list) : LKC list * token list = raise unexpEOF
  
  
  in
    Prog
  end
;



(******************************************************************************)
(* Syntactic exceptions handlers. *)

(* Unexpected end of token list handler. *)
fun syntExcEOF() =
      let
        val msg = print("[Syntactic Analyzer]: Unexpected end of token list.\n")
      in
        raise SyntacticException
      end

(* Non constant expression found handler. *)
and syntExcNoconst(tkn_list : token list) =
      let
        val msg = print(
                   "[Syntactic Analyzer]: Non constant expression found near '"^
                   tokenListToString(tkn_list) ^ "'.\n"
                  )
      in
        raise SyntacticException
      end

(* A symbol X was expected, but Y was found instead (Expected But Found). *)
and syntExcEBF(exp : string, fnd : string, tkn_list : token list) =
      let
        val msg = print(
                    "[Syntactic Analyzer]: '" ^ exp ^ "' expected, but '" ^ fnd ^
                    "' was found near '" ^ tokenListToString(tkn_list) ^ "'.\n"
                  )
      in
        raise SyntacticException
      end
;



(******************************************************************************)
(* Main function for the Syntactic Analizer. *)
fun synt(prog : token list) =
  let
    val q = PROG(prog)
      handle unexpEOF                        => syntExcEOF()
           | NOCONST(tkn_list)               => syntExcNoconst(tkn_list)
           | expButFound(exp, fnd, tkn_list) => syntExcEBF(exp, fnd, tkn_list)
  in
    case #2q
      of [SYM("$")] => #1q
       | _          => #1q
  end
;

val L = lexi(explode("let x  = 2 in x - 5 + 4 end $"));
