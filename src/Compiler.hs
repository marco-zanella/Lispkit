{- | Module   : Compiler
  Description : SECD compiler
  Mantainer   : marco.zanella.9@studenti.unipd.it
  
  Complete SECD compiler for LispKit programming language.
-}
module Compiler(
  Secdexpr(..),
  compile
)
where
import Parser



-- | Command for a SECD machine.
data Secdexpr
  = Add                      -- ^ Addition
  | Sub                      -- ^ Subtraction
  | Mult                     -- ^ Multiplication
  | Div                      -- ^ Integer division
  | Rem                      -- ^ Remainder of integer division
  | Eq                       -- ^ Equality test
  | Leq                      -- ^ Less then or equal to comparison
  | Car                      -- ^ Head of a list
  | Cdr                      -- ^ Tail of a list
  | Cons                     -- ^ Constructor of a list
  | Atom                     -- ^ Tells whether its argument is a value
  | Join                     -- ^ Join after a branch
  | Rtn                      -- ^ Return after a function
  | Stop                     -- ^ Stop SECD machine
  | Push                     -- ^ Pushes a placeholder into environment
  | Ap                       -- ^ Apply
  | Rap                      -- ^ Recursive apply
  | Ld (Integer, Integer)    -- ^ Load a value from environment
  | Ldc LKC                  -- ^ Load a constant value
  | Sel [Secdexpr] [Secdexpr] -- ^ Branching
  | Ldf [Secdexpr]           -- ^ Defines a function
  deriving (Show, Eq)


-- | Returns index of given variable within the list.
position :: String -> [LKC] -> Integer
position _ []          = error "position: variable not found"
position x (VAR z : y) = if z == x then 0 else 1 + position x y
position _ _           = error "position: found bad variable"


-- | Tells whether a variable is defined.
member :: String -> [LKC] -> Bool
member _ []          = False 
member x (VAR z : y) = (x == z) || member x y
member _ _           = error "member: found bad variable"


-- | Returns index of a variable within the environment.
location :: String -> Integer -> [[LKC]] -> (Integer, Integer) 
location x _ []       = error ("location non trova VAR"++ x)
location x ct (n : m) = if member x n
                        then (ct, position x n)
                        else location x (ct + 1) m
 

-- | Removes expressions from a list of binders.
vars :: [(a, b)] -> [a]
vars []           = [] 
vars ((x, _) : r) = x : vars r


-- | Removes variables from a list of binders.
exprs :: [(a, b)] -> [b]
exprs []           = [] 
exprs ((_, y) : r) = y : exprs r


-- | Compiles instructions to build a list.
complist :: [LKC] -> [[LKC]] -> [Secdexpr] -> [Secdexpr]
complist [] _ c      = Ldc NIL : c
complist (x : l) e c = complist l e (comp x e (Cons : c))


-- | Compiles a LispKit program.
-- An LKC is translated to a sequence of SECD commands, using given
-- environment and adding commands to those already present.
comp :: LKC -> [[LKC]] -> [Secdexpr] -> [Secdexpr]
comp e n c =  case e of
  (VAR x)       -> Ld (location x 0 n) : c
  (NUM x)       -> Ldc (NUM x) : c
  (BOO x)       -> Ldc (BOO x) : c
  (STRI x)      -> Ldc (STRI x) : c
  NIL           -> Ldc NIL : c
  (ADD x y)     -> comp y n (comp x n ( Add : c))
  (SUB x y)     -> comp y n (comp x n ( Sub : c))
  (MULT x y)    -> comp y n (comp x n (Mult : c))
  (DIV x y)     -> comp y n (comp x n ( Div : c))
  (REM x y)     -> comp y n (comp x n ( Rem : c))
  (EQC x y)     -> comp y n (comp x n (  Eq : c))
  (LEQC x y)    -> comp y n (comp x n ( Leq : c))
  (CONSC x y)   -> comp y n (comp x n (Cons : c))
  (CARC x)      -> comp x n ( Car : c)
  (CDRC x)      -> comp x n ( Cdr : c)
  (ATOMC x)     -> comp x n (Atom : c)
  (IFC x y z)   -> let
                     thenp = comp y n [Join]
                     elsep = comp z n [Join]
                   in
                     comp x n (Sel thenp elsep : c)
  (LAMBDAC x y)  -> Ldf (comp y (x : n) [Rtn]) : c
  (LETC i e')    -> let
                      var_list = vars e'
                      exp_list = exprs e'
                    in
                      complist exp_list
                               n
                               (Ldf (comp i (var_list : n) [Rtn]) : Ap : c)
  (LETRECC i e') -> let
                      var_list = vars e'
                      exp_list = exprs e'
                      e''      = var_list : n
                    in
                      Push : complist exp_list
                                      e''
                                      (Ldf(comp i e'' [Rtn]) : Rap : c)
  (CALL f y)    -> complist y n (comp f n (Ap : c))
  _             -> []


-- | Compiles a LispKit program.
compile :: LKC -> [Secdexpr]
compile program = comp program [] []
