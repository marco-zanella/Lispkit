{- | Module   : Parser
  Description : Parser module
  Mantainer   : marco.zanella.9@studenti.unipd.it
  
  The parser receives an iput from the lexical analyzer, that is, a list
  of tokens, and has to build the abstract syntax tree representing the
  program.
-}
module Parser(
  LKC(..),
  parse
)
where
import Lexer
import Prelude hiding (EQ, exp, id)



------------------------------------------------------------------------
-- Tools to handle exceptions.

-- | Type representing an exception.
data Exc a
  = Raise Exception          -- ^ An exception has occurred
  | Return a                 -- ^ Regular return


-- | Exceptions carry a string message
type Exception = String


-- | Shows an exception (or return).
instance Show a => Show (Exc a) where
  show (Raise e)  = "Exception: " ++ e
  show (Return x) = "Reached: " ++ show x


-- | Monadic behaviour for exceptions (and returns).
instance Monad Exc where
  return = Return
  (Raise e)  >>= _  = Raise e
  (Return x) >>= q  = q x 


-- | A token was expected, but something else was found.
wrongToken :: String -> Token -> Exc a
wrongToken expected found = Raise $ "Expected '" ++ expected ++ "', but "
                         ++ show found ++ " was found."


-- | Unexpected end of token list.
unexpectedEnd :: String -> Exc a
unexpectedEnd expected = Raise $ "Unexpected end of token list: '"
                      ++ expected ++ "' was expected."



------------------------------------------------------------------------
-- | LispKit Concreto type.
data LKC
  = ETY                      -- ^ Indicates epsilon-production
  | VAR String               -- ^ Name of an identifier
  | NUM Integer              -- ^ Constant numerical value
  | STRI String              -- ^ Constant string
  | BOO Bool                 -- ^ Constant boolean value
  | NIL                      -- ^ Empty list
  | ADD LKC LKC              -- ^ Addition
  | SUB LKC LKC              -- ^ Subtraction
  | MULT LKC LKC             -- ^ Multiplication
  | REM LKC LKC              -- ^ Remainder of integer division
  | DIV LKC LKC              -- ^ Integer division
  | EQC LKC LKC              -- ^ Equality test
  | LEQC LKC LKC             -- ^ Less then or equal to test
  | CARC LKC                 -- ^ Head of a list
  | CDRC LKC                 -- ^ Tail of a list
  | CONSC LKC LKC            -- ^ Constructor of a list
  | ATOMC LKC                -- ^ Tells whether its argument is a value
  | IFC LKC LKC LKC          -- ^ If-then-else statement
  | LAMBDAC [LKC] LKC        -- ^ Function declaration
  | CALL LKC [LKC]           -- ^ Function invocation
  | LETC LKC [(LKC,LKC)]     -- ^ Block declaration
  | LETRECC LKC [(LKC, LKC)] -- ^ Recursive block declaration
  deriving (Show, Eq)


------------------------------------------------------------------------
-- Parsing functions which recognize terminal symbols.

-- | Recognizes 'let' and 'letrec' keywords.
recKey :: [Token] -> Exc [Token]
recKey (Keyword LET : l)    = Return l
recKey (Keyword LETREC : l) = Return l
recKey (t : _)              = wrongToken "let | letrec" t
recKey []                   = unexpectedEnd "let | letrec"


-- | Recognizes 'in' keyword.
recIn :: [Token] -> Exc [Token]
recIn (Keyword IN : l) = Return l
recIn (t : _)          = wrongToken "in" t
recIn []               = unexpectedEnd "in"


-- | Recognizes 'end' keyword.
recEnd :: [Token] -> Exc [Token]
recEnd (Keyword END : l) = Return l
recEnd (t : _)           = wrongToken "end" t
recEnd []                = unexpectedEnd "end"


-- | Recognizes 'then' keyword.
recThen :: [Token] -> Exc [Token]
recThen (Keyword THEN : l) = Return l
recThen (t : _)            = wrongToken "then" t
recThen []                 = unexpectedEnd "then"


-- | Recognizes 'else' keyword.
recElse :: [Token] -> Exc [Token]
recElse (Keyword ELSE : l) = Return l
recElse (t : _)            = wrongToken "else" t
recElse []                 = unexpectedEnd "else"


-- | Recognizes '(' symbol.
recLp :: [Token] -> Exc [Token]
recLp (Symbol LPAREN : l) = Return l
recLp (t : _)             = wrongToken "(" t
recLp []                  = unexpectedEnd "("


-- | Recognizes ')' symbol.
recRp :: [Token] -> Exc [Token]
recRp (Symbol RPAREN : l) = Return l
recRp (t : _)             = wrongToken ")" t
recRp []                  = unexpectedEnd ")"


-- | Recognizes ',' symbol.
recComma :: [Token] -> Exc [Token]
recComma (Symbol COMMA : l) = Return  l
recComma (t : _)            = wrongToken "," t
recComma []                 = unexpectedEnd ","


-- | Recognizes "=" symbol.
recEquals :: [Token] -> Exc [Token]
recEquals (Symbol EQUALS : l) = Return l
recEquals (t : _)             = wrongToken "=" t
recEquals []                  = unexpectedEnd "="



------------------------------------------------------------------------
-- Parsing function which recognize non terminal symbols.

-- | Recognizes a program.
prog :: [Token] -> Exc ([Token], LKC)
prog tokens @ (t : _) = do 
  x          <- recKey tokens
  (y, binds) <- bind x
  z          <- recIn y
  (w, body)  <- exp z
  s          <- recEnd w
  case t of
    Keyword LET    -> Return (s, LETC body binds)
    Keyword LETREC -> Return (s, LETRECC body binds)
    _              -> wrongToken "let | letrec" t
prog [] = unexpectedEnd "let | letrec"


-- | Recognizes a binding.
bind :: [Token] -> Exc([Token], [(LKC, LKC)])
bind (Id id : l) =  do
  x          <- recEquals l
  (y, value) <- exp x
  (s, binds) <- funx y
  Return (s, (VAR id, value) : binds)
bind (t : _) = wrongToken "identifier" t
bind []      = unexpectedEnd "indentifier"


-- | Recognizes continuation of a binding ('and bind...').
funx :: [Token] -> Exc ([Token], [(LKC, LKC)])
funx (Keyword AND : l)    = bind l
funx s @ (Keyword IN : _) = Return (s, [])
funx (t : _)              = wrongToken "and | in" t
funx []                   = unexpectedEnd "and | in"


-- | Recognizes an expression.
exp :: [Token] -> Exc ([Token], LKC)
exp s @ (Keyword LET : _)    = prog s
exp s @ (Keyword LETREC : _) = prog s

exp (Keyword LAMBDA : l) = do
  x          <- recLp l
  (y, vars)  <- seqVar x
  (s, value) <- exp y
  Return (s, LAMBDAC vars value)

exp (Operator CONS : l) = do
  x       <- recLp l
  (y, hd) <- exp x
  z       <- recComma y
  (w, tl) <- exp z
  s       <- recRp w
  Return (s, CONSC hd tl)

exp (Operator CAR : l) = do
  (s, list) <- exp l
  Return (s, CARC list)

exp (Operator CDR : l) = do
  (s, list) <- exp l
  Return (s, CDRC list)

exp (Operator ATOM : l) = do
  (s, list) <- exp l
  Return (s, ATOMC list)

exp (Keyword IF : l) = do
  (x, guard)    <- exp l
  y             <-recThen x
  (z, ttBranch) <- exp y
  w             <-recElse z
  (s, ffBranch) <- exp w
  Return (s, IFC guard ttBranch ffBranch)

exp (Operator LEQ : l) = do
  x            <- recLp l
  (y, leftOp)  <- exp x
  z            <- recComma y
  (w, rightOp) <- exp z
  s            <- recRp w
  Return (s, LEQC leftOp rightOp)

exp (Operator EQ : l) = do
  x            <- recLp l
  (y, leftOp)  <- exp x
  z            <- recComma y
  (w, rightOp) <- exp z
  s            <- recRp w
  Return (s, EQC leftOp rightOp)

exp tokens = expa tokens


-- | Recognizes an arithmetic expression.
expa :: [Token] -> Exc ([Token], LKC)
expa l = do
  (x, operand) <- funt l
  (s, more)    <- fune1 x operand
  if more == ETY
  then Return (s, operand)
  else Return (s, more)


-- | Recognizes additions and substractions.
fune1 :: [Token] -> LKC -> Exc ([Token], LKC)
fune1 (Symbol PLUS : l) op = do
  (x, operand) <- funt l
  (s, more)    <- fune1 x operand
  if more == ETY
  then Return (s, ADD op operand)
  else Return (s, ADD op more)

fune1 (Symbol MINUS : l) op = do
  (x, operand) <- funt l
  (s, more)    <- fune1 x operand
  if more == ETY
  then Return (s, SUB op operand)
  else Return (s, SUB op more)

fune1 s _ = Return (s, ETY)


-- | Recognizes part of an arithmetic expression.
funt :: [Token] -> Exc ([Token], LKC)
funt l = do
  (x, operand) <- funf l
  (s, more)    <- funt1 x operand
  if more == ETY
  then Return (s, operand)
  else Return (s, more)


-- | Recognizes multiplication and division.
funt1 :: [Token] -> LKC -> Exc ([Token], LKC)
funt1 (Symbol TIMES : l) op = do
  (x, operand) <- funf l
  (s, more)    <- funt1 x operand
  if more == ETY
  then Return (s, MULT op operand)
  else Return (s, MULT op more)

funt1 (Symbol DIVISION : l) op = do
  (x, operand) <- funf l
  (s, more)    <- funt1 x operand
  if more == ETY
  then Return (s, DIV op operand)
  else Return (s, DIV op more)

funt1 s _ = Return (s, ETY)


-- | Recognizes variables, constants and expression between parenthesis.
funf :: [Token] -> Exc ([Token], LKC)
funf (Id var : l) = do
  (s, value) <- funy l (VAR var)
  Return (s, value)

funf (Symbol LPAREN : l) = do
  (x, value) <- expa l
  s          <- recRp x
  Return (s, value)

funf (String s : l) = Return (l, STRI s)
funf (Number n : l) = Return (l, NUM n)
funf (Bool b : l)   = Return (l, BOO b)
funf (Nil : l)      = Return (l, NIL)
funf (t : _)        = wrongToken "identifier | constant | (" t
funf []             = unexpectedEnd "identifier | constant | ("


-- | Recognizes sequences of expressions between parenthesis.
funy :: [Token] -> LKC -> Exc ([Token], LKC)
funy (Symbol LPAREN : l) var =  do
  (x, exps) <- seqExp l
  s         <- recRp x
  Return (s, CALL var exps)
funy x var = Return (x, var)


-- | Recognizes sequences of expressions.
seqExp :: [Token] -> Exc ([Token], [LKC])
seqExp s @ (Symbol RPAREN : _) = Return (s, [])
seqExp tokens = do
  (x, value) <- exp tokens
  (s, list)  <- lstExp x
  Return (s, value : list)


-- | Recognizes continuations of sequences of expressions (', exp...').
lstExp :: [Token] -> Exc ([Token], [LKC])
lstExp (Symbol COMMA : l)      = seqExp l
lstExp s @ (Symbol RPAREN : _) = Return (s, [])
lstExp (t : _)                 = wrongToken ", | )" t
lstExp []                      = unexpectedEnd ", | )"


-- | Recognizes a sequence of varibles.
seqVar :: [Token]-> Exc ([Token], [LKC])
seqVar (Id id : l) = do
  (x, vars) <- seqVar l
  Return (x, VAR id : vars)
seqVar (Symbol RPAREN : l) = Return (l, [])
seqVar (t : _)             = wrongToken "identifier | )" t
seqVar []                  = unexpectedEnd "identifier | )"


------------------------------------------------------------------------
-- | Parses given token list.
parse :: [Token] -> LKC
parse l  = case prog l of
  Return ([Symbol DOLLAR], ast) -> ast
  Return (_, _)                 -> error "Program is not $-terminating"
  Raise e                       -> error . show $ e
