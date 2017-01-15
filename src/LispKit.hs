{- | Module   : Main
  Description : LispKit interpreter
  Mantainer   : marco.zanella.9@studenti.unipd.it
  
  LispKit is a basic functional programming language, yet complex
  enough to show many interesting aspects of the programming languages
  discussed during the course. In LispKit there are no types, however
  integer values, boolean values, constant strings and list can be
  handled.
-}
module Main(main) where
import System.Environment
import Lexer
import Parser
import Compiler
import Interpreter



-- | Content of a program is read from the given file, if any, otherwise
-- it is read from the standard input.
-- The end-of-file character is removed.
getProgram :: IO String
getProgram = do
  args <- getArgs
  content <- if null args
    then getContents
    else readFile . head $ args
  return . init $ content



-- | Entry point of the program.
-- Source code of the program is load, parsed, compiled and executed.
main :: IO ()
main = do
  source <- getProgram
  print . execute . compile . parse . lexi $ source
