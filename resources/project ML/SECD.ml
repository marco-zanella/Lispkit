(*******************************************************************************
 * Project of Programming Languages 2013-14
 * Part V - Interpreter.
 * Author:  Giilberto File`
 * Student: Marco Zanella, mat. 1079762
*******************************************************************************)



(*******************************************************************************
 * Dependencies.
*******************************************************************************)

use "comp.ml";



(*******************************************************************************
 * Datatypes.
*******************************************************************************)

(* Type used to model R-values of variables. Those values are meant to be stored
   in the stack S and in the dynamic environment E. Moreover, CLO models the
   clousures.
 *)
datatype Valore = V of LKC
                | OGA
                | CLO of secdexpr list * (unit -> Valore list list)
                | VLISTA of Valore list
                ;

(* Datatype of the values of Dump. *)
datatype Dump = CONTR of secdexpr list
              | TRIPLA of Valore list * Valore list list * secdexpr list
              | DUMMY
              ;



(*******************************************************************************
 * Exceptions.
*******************************************************************************)
exception Error of string; 
exception Vuota_Hd;
exception Vuota_Tl;



(*******************************************************************************
 * Auxiliary functions.
*******************************************************************************)

(* The first element of the given list is returned, if any. *)
fun HA([]   : 'a list) : 'a = raise Vuota_Hd
  | HA(a::l : 'a list) : 'a = a
;

(* The tail of a the given list is returned, if any. *)
fun TA([]   : 'a list) : 'a list = raise Vuota_Tl
  | TA(a::l : 'a list) : 'a list = l
;

(* funz che crea l'ambiente dinamico ricorsivo necessario per il trattamento 
   della ricorsione. Serve nel caso Rap *)
fun LazyE([],   _) : Valore list = []
  | LazyE(a::b, A) : Valore list = LazyClo(a, A)::LazyE(b, A)

and LazyClo(CLO(a, b), A) = 
      let 
        val w = b() 
      in 
        CLO(a, fn() => LazyE(A, A)::w) 
      end
  | LazyClo(V(x), A)      = V(x) 
  | LazyClo(VLISTA(x), A) = VLISTA(x)
  | LazyClo(_, _)         = raise Error("LazyClo trova valore non possibile")
;



(* Functions used to search the R-values, given their addresses (used by Ld). *)
fun index(n : int, s : 'a list) : 'a =
      if n = 0 then HA(s) else index(n-1, TA(s))
;  


fun locate((a,b) : int*int, e : Valore list list) : Valore=
      index(b, index(a, e))
;
      
val extract_int = fn V(LKC_NM(x)) => x 
                | _               => raise Error("trovato altro da intero")
;



(* Functions used to manipulate list of Valori VLISTA. *)
val Vhd = fn VLISTA(a::b) => a
        | Q               => raise Error("Vhd fallisce")
;

fun Vtl(VLISTA(a::b)) = VLISTA(b)
  | Vtl(_)            = raise Error("Vtl fallisce")
;

fun Vatom(a : Valore) : Valore =
      case a
        of V(K) => V(LKC_BOOL(T))
         | Q1   => V(LKC_BOOL(F))
;

fun bool2s_espressione(b : bool): LKC =
      if b then LKC_BOOL(T) else LKC_BOOL(F)
;



(* Equality test for type Valore, it auto-react to the type of the parameters it
   is invoked with.*)
fun EqValore(a, b) =
      case a 
        of V(_)      => EqV(a,b)
         | VLISTA(_) => EqVLISTA(a,b)
         | _         => raise Error("uguaglianza tra chiusure")

and EqVLISTA(VLISTA([]), VLISTA([]))     = true
  | EqVLISTA(VLISTA(a::b), VLISTA(c::d)) = EqValore(a,c) andalso EqVL(b,d)
  | EqVLISTA(x,y)                        = false

and EqV(V(a), x) : bool =
      (case x
        of V(b) => (a=b)
         | _    => false
      )
  | EqV(a,b) = false

and EqVL([],[])      = true
  | EqVL(a::b ,c::d) = (EqValore(a,c) andalso EqVL(b,d))
  | EqVL(_, _)       = false
;



(******************************************************************************)
(* Main interpreter function. *)
fun interprete(S: Valore list, E: Valore list list, C: secdexpr list, D: Dump list) : Valore =  
      case HA(C)
        of Ld(b,n) =>
             let
               val x = locate((b,n),E) handle VuotoHd => raise Error("in locate")
             in
               interprete(x::S,E,TA(C),D)
             end 
        | Ldc(k) => 
            (case k
               of LKC_Nil => interprete(VLISTA([])::S, E, TA(C), D)
                | x       => interprete(V(k)::S, E, TA(C), D)
            )
        | Add =>
            let
              val operand1 = extract_int(HA(S));
              val operand2 = extract_int(HA(TA(S)));
            in
              interprete(V(LKC_NM(operand1 + operand2))::TA(TA(S)),E,TA(C),D)
            end
        | Sub =>
            let
              val operand1 = extract_int(HA(S)handle VuotoHd =>(print("SUB1");V(LKC_Nil)));
              val operand2 = extract_int(HA(TA(S))handle VuotoHd =>(print("SUB2");V(LKC_Nil)));	 
            in
              interprete(V(LKC_NM(operand1 - operand2))::TA(TA(S)),E,TA(C),D)
            end
        | Mult =>
            let
              val operand1 = extract_int(HA(S)handle VuotoHd =>(print("MULT1");V(LKC_Nil)));
              val operand2 = extract_int(HA(TA(S))handle VuotoHd =>(print("MULT2");V(LKC_Nil)));
            in  
              interprete(V(LKC_NM(operand1*operand2))::TA(TA(S)),E,TA(C),D)
            end
        | Div =>
            let
              val operand1 = extract_int(HA(S));
              val operand2 = extract_int(HA(TA(S)));
            in
              interprete(V(LKC_NM(operand1 div operand2))::TA(TA(S)),E,TA(C),D)
            end
        | Rem =>
            let
              val operand1 = extract_int(HA(S));
              val operand2 = extract_int(HA(TA(S)));
            in
              interprete(V(LKC_NM(operand1 mod operand2))::TA(TA(S)),E,TA(C),D)
            end
        | Leq =>
            let 
              val operand1 = extract_int(HA(S));
              val operand2 = extract_int(HA(TA(S)));
            in  
              interprete(V(bool2s_espressione(operand1 <= operand2))::TA(TA(S)),E,TA(C),D)
            end
        | Eq =>
            (case S
               of w1::w2::w3 => interprete(V(bool2s_espressione(EqValore(w1,w2)))::w3,E,TA(C),D)
                | _=> raise Error("manca un argomento in Eq")
            )
        | Car =>
            interprete(Vhd(HA(S)handle VuotoHd =>(print("CAR");V(LKC_Nil)))::TA(S),E,TA(C),D) 
        | Cdr =>
            interprete(Vtl(HA(S)handle VuotoHd =>(print("CDR");V(LKC_Nil)))::TA(S),E,TA(C),D)
        | Cons =>
            (case HA(TA(S))handle VuotoHd =>(print("CONS");V(LKC_Nil))
               of VLISTA([]) =>
                    interprete(VLISTA([HA(S)handle VuotoHd =>(print("CONS2");V(LKC_Nil))])::TA(TA(S)),E,TA(C),D)
                | VLISTA(vl2) =>
                    interprete(VLISTA((HA(S)handle VuotoHd =>(print("CONS3");V(LKC_Nil)))::vl2)::TA(TA(S)),E,TA(C),D)| 
                _ => raise Error("CONS: il secondo argomento non e' una lista")
            )
        | Atom => interprete(Vatom(HA(S))::TA(S),E,TA(C),D)
        | Sel(sl1,sl2) =>                 
            (case HA(S)handle VuotoHd =>(print("SEL");V(LKC_Nil))
               of V(LKC_BOOL(T)) => interprete(TA(S), E, sl1,CONTR(TA(C))::D)
                | V(LKC_BOOL(F)) => interprete(TA(S), E, sl2, CONTR(TA(C))::D)
                | _ =>  raise Error("SEL: non trovato bool su S")
            )
        | Join =>
            (case HA(D)handle VuotoHd =>(print("JOIN");DUMMY)
               of CONTR(C1) => interprete(S,E,C1,TA(D))
                | _=> raise Error("JOIN: il dump non contiene controllo")
            )
        | Ldf(sl) => interprete(CLO(sl,fn()=>E)::S,E,TA(C),D)
        | Ap =>
            (case HA(S) handle VuotoHd =>(print("AP");V(LKC_Nil))
               of CLO(c1,e1)=> 
                    (case HA(TA(S))handle VuotoHd =>(print("AP2");V(LKC_Nil))
                       of VLISTA([]) => interprete([],[]::e1(), c1,TRIPLA(TA(TA(S)),E,TA(C))::D)
                        | VLISTA(vl2) => interprete([],vl2::e1(), c1,TRIPLA(TA(TA(S)),E,TA(C))::D)
                        | X => raise Error("AP: non ci sono i parametri attuali")
                    )
                | _ => raise Error("AP: non trovata chiusura su S")
            )
        | Rtn =>
            (case HA(D)handle VuotoHd =>(print("RTN");DUMMY)
               of TRIPLA(s1,e1,c1) => interprete(HA(S)::s1,e1,c1,TA(D))
                | _ =>  raise Error("RTN: non trovata TRIPLA su dump")
            )
				| Rap =>
					  (case HA(S)
						  of CLO (cl, el) =>
							  (case HA(TA(S))
								  of VLISTA(vl2) => interprete([], LazyE(vl2, vl2)::(el()), cl, TRIPLA(TA(TA(S)), E, TA(C))::D)
									 | _ => raise Error("RAP: non trovo i parametri attuali dell'invocazione")
								)
								| _ => raise Error("Rap: non trovata chiusura su S")
						)
        | Push => interprete(S, [OGA]::E,TA(C),D)
        | Stop => HA(S)
        | _ => (print("operazione non riconosciuta"); V(LKC_Nil))
;



(******************************************************************************)
(* Actual interpreter. *)
fun SECD(O : secdexpr list) : Valore = interprete([], [], O @ [Stop], []);

