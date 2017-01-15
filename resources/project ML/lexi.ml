(*******************************************************************************
 * Project of Programming Languages 2013-14
 * Part I - Lexical Analyzer
 * Author:  Gilberto File`
 * Student: Marco Zanella, mat. 1079762 
*******************************************************************************)


(*******************************************************************************
 * Datatypes.
*******************************************************************************)

(* Boolean type. *)
datatype B = T 
           | F
           ;

(* Token type. *)
datatype token = KEYWORD of string
               | OP of string
               | ID of string
               | SYM of string
               | NM of int 
               | STR of string 
               | BOOL of B
               | Nil
               ;



(*******************************************************************************
 * Exceptions.
*******************************************************************************)

(* Unrecognized characted was found. *)
exception NotValidChar of char;

(* Input string terminates, but an input was expected. *)
exception UnexpectedEndOfString;

(* Lexical analyzer terminated due to an exception. *)
exception LexicalException;



(*******************************************************************************
 * Lexical analyzer.
*******************************************************************************)

(* Support functions. *)

(* Predicate which tells if a character is legit to start an identifier, an
   operator or a keyword. *)
fun IsAlphaChar(c: char) : bool =
  (c >= (#"a") andalso c <= (#"z")) orelse (c >= (#"A") andalso c <= (#"Z"))
;

(* Predicate which tells if a character is a (decimal) digit. *)
fun IsDigitChar(c : char) : bool =
  c >= (#"0") andalso c <= (#"9")
;

(* Predicate which tells if a caracter is legit to use to compose an identifier,
   an operator or a keyword (not considering the first character). *)
fun IsIdChar(c: char) : bool =
  IsAlphaChar(c) orelse IsDigitChar(c)
;

(* Predicate which tells if a character is a separator. *)
fun IsSeparator(c :char ) : bool =
  c = (#"(") orelse c = (#")") orelse c = (#"=") orelse c = (#"$") orelse c = (#",")
;

(* Predicate which tells if a character is a space or a newline. *)
fun IsSpace(c : char) : bool =
  c = (#" ") orelse c = (#"\n") orelse c = (#"\f") orelse c = (#"\r")
;

(* Predicate which tells if a character is an operator. *)
fun IsOp(c : char) : bool =
  c = (#"+") orelse c = (#"-") orelse c = (#"*") orelse c = (#"/")
;


(* A given string X is compared with the keywords and the operators of LispKit.
   If it belongs to them, the couple token-lexema is returned. Otherwise, it is
   considered an identifier, and the couple (ID, STRING(X)) is returned. *)
fun extractWord("let"    : string) : token = KEYWORD("let")
  | extractWord("in"     : string) : token = KEYWORD("in")
  | extractWord("end"    : string) : token = KEYWORD("end")
  | extractWord("letrec" : string) : token = KEYWORD("letrec")
  | extractWord("and"    : string) : token = KEYWORD("and")
  | extractWord("nil"    : string) : token = Nil
  | extractWord("true"   : string) : token = BOOL(T)
  | extractWord("false"  : string) : token = BOOL(F)
  | extractWord("eq"     : string) : token = OP("eq")
  | extractWord("leq"    : string) : token = OP("leq")
  | extractWord("car"    : string) : token = OP("car")
  | extractWord("cdr"    : string) : token = OP("cdr")
  | extractWord("cons"   : string) : token = OP("cons")
  | extractWord("atom"   : string) : token = OP("atom")
  | extractWord("if"     : string) : token = KEYWORD("if")
  | extractWord("then"   : string) : token = KEYWORD("then")
  | extractWord("else"   : string) : token = KEYWORD("else")
  | extractWord("lambda" : string) : token = KEYWORD("lambda")
  | extractWord(s        : string) : token = ID(s)
  ;



(* Functions used to implement the finite states of the automata.
 * There are not recursive calls. Transitions from the main state I are
 * implemented as an invocation. The control always returns to I, so the
 * regular return from the function is enough.
 *)

(* State N use to recognize numbers. *)
fun N(nil  : char list, n : int, b : bool) : token * char list =
      raise UnexpectedEndOfString
  | N(c::l : char list, n : int, b : bool) : token * char list =
      if IsDigitChar(c) then
        let
          val x = ord(c)-ord(#"0")
        in 
          N(l, n*10+x, b)
        end
      else if b = true then
        (NM(~n), c::l)
      else
        (NM(n), c::l)
  ;

(* State SC used to recognize strings between quotes. *)
fun SC(#"\""::l : char list, result : char list) : token * char list =
     (STR(implode(result)), l)
  | SC(c::l : char list, result : char list) = SC(l, result@[c])
  | SC(nil  : char list, result : char list) = raise UnexpectedEndOfString
  ;

(* State S used to collect strings which can be identifiers, prefix operators or
   keywords. *)
fun S(c::l : char list, result : char list) : token * char list =
      if IsIdChar(c) then
        S(l, result@[c])
      else 
        (extractWord(implode(result)), c::l)
  | S(nil : char list, result : char list) : token * char list =
      raise UnexpectedEndOfString
  ;    

(* State I used as main state.
   It recognizes the current input character and calls the appropriate 
   state function. *)
fun I(nil : char list) : token list = raise UnexpectedEndOfString
  | I(c::L : char list) : token list =
      (* $ means end of program. *)
      if c = #"$" then
        [SYM(str(c))]
      
      (* Numbers starting with a digit or ~. *)
      else if c = #"~" then 
        let
          val n = N(L, 0, true)
        in
          #1n::I(#2n)
        end
      else if IsDigitChar(c) then
        let
          val n = N(c::L, 0, false)
        in
          #1n::I(#2n)
        end
      
      (* Identifiers. *)
      else if IsAlphaChar(c) then
        let
          val s = S(c::L, [])
        in
          #1s::I(#2s)
        end
      
      (* Space are skipped. *)
      else if IsSpace(c) then
        I(L)
      
      (* Separator symbols. *)
      else if IsSeparator(c) then
        SYM(str(c))::I(L)
      
      (* Operation symbols. *)
      else if IsOp(c) then
        OP(str(c))::I(L)
      
      (* Quoted strings. *)
      else if c = #"\"" then
        let
          val sc = SC(L, [])
        in
          #1sc::I(#2sc)
        end
      
      (* Otherwise: non valid input. *)
      else
       raise NotValidChar(c);
    ;



(* Function used to handle lexical exceptions. 
   A LexicalException exception is raised. *)
fun lexiException(err_msg : string) =
  let
    val msg = print("[Lexical Analyzer]: " ^ err_msg ^ "\n")
  in
    raise LexicalException
  end
;



(* Main function for the lexical analysis. *)
fun lexi(s : char list) : token list =
  I(s) handle NotValidChar(c) =>lexiException("An unrecognized character was found: " ^ str(c) ^ ".")
            | UnexpectedEndOfString => lexiException("Unexpected end of string was encountered.")
;

