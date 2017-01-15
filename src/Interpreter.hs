{- | Module   : Interpreter
  Description : Complete SECD interpreterr
  Mantainer   : marco.zanella.9@studenti.unipd.it
  
  SECD interpreter receives an input from the compiler and executes it
  within the SECD machine.
-}
module Interpreter(execute, Value) where
import Compiler
import Parser



------------------------------------------------------------------------
-- Datatypes.

-- | Type modelling R-values of variables.
-- Those value will be put into stack S and dynamic environment E.
data Value
  = V LKC                    -- ^ Value
  | VLIST [Value]            -- ^ List
  | CLO [Secdexpr] [[Value]] -- ^ Closure
  | OGA                      -- ^ Placeholder for recursive environments
  deriving (Show, Eq)



-- | Values for dump.
data Dump
  = CONTR [Secdexpr]         -- ^ Control
  | TRIPLE [Value] [[Value]] [Secdexpr] -- ^ Stack, environment, control
  deriving (Show, Eq)



------------------------------------------------------------------------
-- Support functions.

-- | Creates a dynamic recursive environment.
-- Such environment is necessary to handle recursions.
lazyE :: [Value] -> [Value] -> [Value]
lazyE [] _      = []
lazyE (a : b) c = lazyClo a c : lazyE b c


-- | Creates a closure.
lazyClo :: Value -> [Value] -> Value
lazyClo (CLO f x) c = CLO f (lazyE c c : x)
lazyClo (V v) _     = V v
lazyClo (VLIST l) _ = VLIST l
lazyClo x _         = error ("LazyClo: bad value " ++ show x)


-- | Returns n-esim element of given list.
index :: Integer -> [a] -> a
index 0 l = head l
index n l = index (n - 1) (tail l)


-- | Returns element (i, j) from given environment (list of lists).
locate :: (Integer, Integer) -> [[Value]] -> Value
locate (i, j) e = index j (index i e)


-- | Extracts a constant integer value.
extractInt :: Value -> Integer
extractInt (V (NUM n)) = n
extractInt x           = error ("Expected integer, found: " ++ show x)


-- | Returns first element of a list.
vhd :: Value -> Value
vhd (VLIST (a : _)) = a
vhd (VLIST [])      = error "hd: empty list was found"
vhd _               = error "hd: list not found"


-- | Returns tail of a list.
vtl :: Value -> Value
vtl (VLIST (_ : l)) = VLIST l
vtl (VLIST [])      = error "tl: empty list was found";
vtl _               = error "tl: list not found"


-- | Tells whether value is not a list nor closure.
vatom :: Value -> Value
vatom (V _) = V (BOO True)
vatom _     = V (BOO False)


-- | Converts a boolean value into an LKC (boolean) value.
bool2LKC :: Bool -> LKC
bool2LKC b = if b then BOO True else BOO False


-- | Tests whether two values are equal.
eqValue :: Value -> Value -> Bool
eqValue a @ (V _) b     = eqV a b
eqValue a @ (VLIST _) b = eqVLIST a b
eqValue a b             = error ("Equality between closures: "
                                ++ show a ++ ", " ++ show b)


-- | Tests whether two lists are equal.
eqVLIST :: Value -> Value -> Bool
eqVLIST (VLIST []) (VLIST [])           = True
eqVLIST (VLIST (a : b)) (VLIST (c : d)) = eqValue a c
                                       && eqVLIST (VLIST b) (VLIST d)
eqVLIST _ _                             = False


-- | Tests whether two (non-list) values are equal.
eqV :: Value -> Value -> Bool
eqV (V a) (V b) = a == b
eqV _ _         = False



------------------------------------------------------------------------
-- Actual interpreter.

-- | Interpretes given SECD program.
interpreter :: [Value] -> [[Value]] -> [Secdexpr] -> [Dump] -> Value
interpreter s e c d = case head c of 
  Ld (i, j) -> let
                 v = locate (i, j) e
               in
                 interpreter (v : s) e (tail c) d
  
  Ldc NIL   -> interpreter (VLIST [] : s) e (tail c) d
  Ldc v     -> interpreter (V v : s) e (tail c) d
  
  Add  -> let
            op1 = extractInt . head $ s
            op2 = extractInt . head . tail $ s
            r   = V . NUM $ (op1 + op2)
            s'  = tail . tail $ s
            c'  = tail c
          in
            interpreter (r : s') e c' d
  
  Sub  -> let
            op1 = extractInt . head $ s
            op2 = extractInt . head . tail $ s
            r   = V . NUM $ (op1 - op2)
            s'  = tail . tail $ s
            c'  = tail c
          in
            interpreter (r : s') e c' d
  
  Mult -> let
            op1 = extractInt . head $ s
            op2 = extractInt . head . tail $ s
            r   = V . NUM $ (op1 * op2)
            s'  = tail . tail $ s
            c'  = tail c
          in
            interpreter (r : s') e c' d
  
  Div  -> let
            op1 = extractInt . head $ s
            op2 = extractInt . head . tail $ s
            r   = V . NUM $ (op1 `div` op2)
            s'  = tail . tail $ s
            c'  = tail c
         in
            interpreter (r : s') e c' d
  
  Rem  -> let
            op1 = extractInt . head $ s
            op2 = extractInt . head . tail $ s
            r   = V . NUM $ (op1 `mod` op2)
            s'  = tail . tail $ s
            c'  = tail c
         in
            interpreter (r : s') e c' d
  
  Leq  -> let
            op1 = extractInt . head $ s
            op2 = extractInt . head . tail $ s
            r   = V . bool2LKC $ (op1 <= op2)
            s'  = tail . tail $ s
            c'  = tail c
         in
           interpreter (r : s') e c' d
  
  Eq   -> let
            op1 = head s
            op2 = head . tail $ s
            r   = V . bool2LKC $ eqValue op1 op2
            s'  = tail . tail $ s
            c'  = tail c
          in
            interpreter (r : s') e c' d
  
  Car  -> interpreter (vhd(head s) : tail s) e (tail c) d
  
  Cdr  -> interpreter (vtl(head s) : tail s) e (tail c) d
  
  Cons -> case head . tail $ s of
    (VLIST l) -> interpreter (VLIST (head s:l) : tail (tail s)) e (tail c) d
    _         -> error "CONS: second argument is not a list"
  
  Atom ->  let
             r  = vatom . head $ s
             s' = tail s
             c' = tail c
           in
             interpreter (r : s') e c' d
  
  Sel slT slF -> let
                   s' = tail s
                   d' = (CONTR . tail $ c) : d
                 in case head s of
    (V (BOO True))  -> interpreter s' e slT d'
    (V (BOO False)) -> interpreter s' e slF d'
    _               -> error "Bad boolean value"
  
  Join -> case head d of
    (CONTR c') -> interpreter s e c' (tail d)
    _          -> error "Join: cannot give control to dump"
  
  Ldf sl -> interpreter (CLO sl e : s) e (tail c) d
  
  Ap   -> case head s of
    (CLO c' e') -> case head (tail s) of
      VLIST l -> interpreter [] (l:e') c' (TRIPLE(tail(tail s)) e (tail c):d)
      _       -> error "Missing parameter list in a function call"
    _           -> error "Calling something which is not a function"
  
  Rtn  -> case head d of
    (TRIPLE s' e' c') -> interpreter (head s : s') e' c' (tail d)
    _                 ->  error  "RTN: cannot restore dump"
  
  Rap  -> case head s of
    (CLO c1 e1) ->  case e1 of
      ([OGA]:re) -> case head (tail s) of
        (VLIST vl2) -> interpreter [] (lazyE vl2 vl2:re) c1 (TRIPLE (tail (tail s)) (tail e) (tail c):d)
        _ -> error "manca lista dei parametri dopo OGA";
      _ -> error "manca [OGA] sull'ambiente di chiusura ric"
    _  -> error "RAP: non trovata chiusura su s"
  
  Push -> interpreter s ([OGA] : e) (tail c) d
  
  Stop -> head s



-- | Calls the interpreter.
execute :: [Secdexpr] -> Value
execute se = interpreter [] [] (se ++ [Stop]) []
