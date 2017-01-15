{- | Module   : Lexer
  Description : Lexical analyzer module
  Mantainer   : marco.zanella.9@studenti.unipd.it
  
  The lexical analyzer receives as input a LispKit program, that is,
  a list of characters, and has to recognize the atomic components of
  the language as well as translating into a easy-to-handle shape for
  the next step of syntactic analysis.
  For instance, constant values (integer numbers, true, etc.), keywords,
  identifiers, operators and symbols must be recognized.
  Each component of these must be represented by a value whose type is
  Token.
-}
module Lexer(
  Token(..),
  SymbolT(..),
  OperatorT(..),
  KeywordT(..),
  lexi
)
where
import Prelude hiding (EQ)



-- | Type representing keywords.
data KeywordT
  = LET           -- ^ Keyword used to declare a binding block
  | LETREC        -- ^ Keyword used to declare a recursive binding block
  | IN            -- ^ Keyword indicating the body of a function
  | END           -- ^ Keyword indicating the end of a function
  | AND           -- ^ Used to concatenate bindings
  | IF            -- ^ Part of the if-then-else branch
  | THEN          -- ^ Part of the if-then-else branch
  | ELSE          -- ^ Part of the if-theb-else branch
  | LAMBDA        -- ^ Keyword used to declare a function
  deriving (Show, Eq)



-- | Type representing operators.
data OperatorT
  = EQ             -- ^ Equality test
  | LEQ            -- ^ Less or equal test
  | CAR            -- ^ Operator returning the list head
  | CDR            -- ^ Operator returning the list tail
  | CONS           -- ^ Constructor of a list
  | ATOM           -- ^ Tells whether its argument is a value
  deriving (Show, Eq)



-- | Type representing symbols (parenthesis, comma...).
data SymbolT 
  = LPAREN         -- ^ Left parenthesis
  | RPAREN         -- ^ Right parenthesis
  | EQUALS         -- ^ Equality symbol
  | PLUS           -- ^ Sum symbol
  | MINUS          -- ^ Difference symbol
  | TIMES          -- ^ Multiplication symbol
  | DIVISION       -- ^ Division symbol
  | COMMA          -- ^ Comma symbol, used to separate actual parameters
  | DOLLAR         -- ^ Dollar symbol, meaning end of input
  deriving (Show, Eq)



-- | Type representing a token.
data Token 
  = Keyword KeywordT    -- ^ A keyword of the language
  | Operator OperatorT  -- ^ An operator
  | Id String           -- ^ The name of an identifier
  | Symbol SymbolT      -- ^ A symbol
  | Number Integer      -- ^ An integer number
  | String String       -- ^ A string
  | Bool Bool           -- ^ A boolean value
  | Nil                 -- ^ The empty list
  deriving (Show, Eq)



------------------------------------------------------------------------
-- Support functions.

-- | Tells whether character is alphanumeric.
isAlphaChar :: Char -> Bool
isAlphaChar c = c `elem` (['a' .. 'z'] ++ ['A' .. 'Z'])


-- | Tells whether character is a digit.
isDigitChar :: Char -> Bool
isDigitChar c = c `elem` ['0' .. '9']


-- | Tells whether character is suitable for componing an identifier,
-- operator or keyword (with exception for the first character).
isIdChar :: Char -> Bool
isIdChar c = isAlphaChar c || isDigitChar c


-- | Tells whether character is a space character.
isSpace :: Char -> Bool
isSpace c = c `elem` " \n\f\r\t"


-- | Tells whether character is a symbol.
isSymbol :: Char -> Bool
isSymbol c = c `elem` "()=+-*/,"




--  | Compares string with LispKit keywords and operators and returns
-- corresponding token.
-- If no corresponding token is found, string is considered an identifier
-- and the couple (ID, string) is returned.
extractWord :: String -> Token
extractWord w = case w of
  "let"    -> Keyword LET
  "in"     -> Keyword IN
  "end"    -> Keyword END
  "letrec" -> Keyword LETREC
  "and"    -> Keyword AND
  "if"     -> Keyword IF
  "then"   -> Keyword THEN
  "else"   -> Keyword ELSE
  "lambda" -> Keyword LAMBDA
  
  "eq"     -> Operator EQ
  "leq"    -> Operator LEQ
  "car"    -> Operator CAR
  "cdr"    -> Operator CDR
  "cons"   -> Operator CONS
  "atom"   -> Operator ATOM
  
  "true"   -> Bool True
  "false"  -> Bool False
  
  "nil"    -> Nil
  
  _        -> Id w



-- | Converts character to the corresponding symbol.
toSymbol :: Char -> SymbolT
toSymbol c = case c of
  '(' -> LPAREN
  ')' -> RPAREN
  '+' -> PLUS
  '-' -> MINUS
  '*' -> TIMES
  '/' -> DIVISION
  '=' -> EQUALS
  ',' -> COMMA
  _   -> error "Not a symbol"
    


------------------------------------------------------------------------
-- Functions used to implement the finite states of the automata.
-- There are not recursive calls. Transitions from the main state I are
-- implemented as an invocation. The control always returns to I, so the
-- regular return from the function is enough.

-- | Recognizes a number.
n :: String -> Bool -> (Token, String)
n input is_negative =
  let
    read_num "" _ = error "Unexpected end of string"
    read_num input_str @ (c : l) num 
      | isDigitChar c = read_num l (num * 10 + read [c] :: Integer)
      | otherwise     = (num, input_str)
    (number, unused_input) = read_num input 0
  in
    (Number(number * (if is_negative then -1 else 1)), unused_input)



-- | Recognizes strings between quotes.
sc :: String -> (Token, String)
sc input =
  let
    read_string "" _             = error "Unexpected end of string"
    read_string ('"' : l) string = (String string, l)
    read_string (c : l)   string = read_string l (string ++ [c])
  in
    read_string input ""



-- | Collects strings which may be identifiers, prefix operators or
-- keywords.
s :: String -> (Token, String)
s input =
  let
    read_string "" _ = error "Unexpected end of string"
    read_string input_str @ (c : l) string
      | isIdChar c = read_string l (string ++ [c])
      | otherwise  = (extractWord string, input_str)
  in
    read_string input ""



-- | Recognizes current input character and calls the appropriate
-- state function.
i :: String -> [Token]
i ""  = error "Unexpected end of string"
i "$" = [Symbol DOLLAR]
i input @ (f : l)
  | isSpace  f = i l
  | isSymbol f = (Symbol $ toSymbol f) : i l
  | otherwise  =
    let
      call :: Char -> (Token, String)
      call '"' = sc l
      call '~' = n l True
      call c
        | isDigitChar c = n input False
        | isAlphaChar c = s input
      call _ = error ("Lexical error starting with \"" ++ input ++ "\"")
      (token, next_input) = call f
    in
      token : i next_input



-- | Main function for the lexical analysis.
-- Scans string representing the source code of the program and converts
-- it into a list of tokens.
lexi :: String -> [Token]
lexi = i
