import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Expr
import Text.Megaparsec.String
import qualified Text.Megaparsec.Lexer as L
import Miranda (DecV, DecP, Aexp(N, V, Mult, Add, Sub), Bexp(TRUE, FALSE, Neg, And, Eq, Le), Stm(Ass, Skip, Comp, If, While, Block, Call))
import Miranda(pretty_print, s_dynamic, baseState)
import Data.List

{---------Lexer---------}

-- Space consumer (and comment consumer)
sc :: Parser ()
sc = L.space (void spaceChar) lineCmnt blockCmnt
  where lineCmnt  = L.skipLineComment "//"
        blockCmnt = L.skipBlockComment "/*" "*/"

-- Parses a lexeme and any trailing whitespace
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- Parses a string and any trailing whitespace
symbol :: String -> Parser String
symbol = L.symbol sc

-- Parses a thing between parenthesis
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- Parses an integer
integer :: Parser Integer
integer = lexeme L.integer

-- Parses a semicolon
semi :: Parser String
semi = symbol ";"

-- Check that a parsed string is not a reserved word
rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> sc

-- List of reserved words
rws :: [String]
rws = ["if","then","else","while","do","skip","true","false","begin","end","call","proc","is","var"]

-- Check if variable name is in reserved word list
identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many alphaNumChar
    check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x

{-----------------Parser------------------}
-- Evaluate an input program as a string, return a pretty list of final state variables
evaluate :: String -> String
evaluate s = pretty_print $ s_dynamic (parseString s) baseState

-- Convert an input string to a Stm using procParser
parseString :: String -> Stm
parseString str =
  case parse procParser "" str of
    Left e  -> error $ show e
    Right r -> r

-- Parse the proc language
procParser :: Parser Stm
procParser = between sc eof stm

-- Parse a statement or composition of statements
stm :: Parser Stm
stm = parens stm <|> stmComp

-- Parse a single statment, or multiple if parenthesis are used
singleStm :: Parser Stm
singleStm = parens stmComp <|> stm'

-- Convert list of statements to Comp data structure
listToComp :: [Stm] -> Stm
listToComp l
  | length l == 1 = head l -- if there's only one stmt return it without using 'Comp'
  | otherwise     = Comp (head l) (listToComp (tail l))

-- Parse a composition of statements
stmComp :: Parser Stm
stmComp = listToComp <$> sepEndBy1 stm' semi

-- Parse some specific statments
stm' :: Parser Stm
stm' = blockStm <|> callStm <|> ifStm <|> whileStm <|> skipStm <|> assignStm

-- Parse a block (begin .. end)
blockStm :: Parser Stm
blockStm = between (rword "begin") (rword "end") block

-- Parse a block with or without parenthesis
block :: Parser Stm
block = parens block <|> block'

-- Parse the internal structure of a block
block' :: Parser Stm
block' = do
  vs <- decVs
  ps <- decPs
  stm1 <- stm
  return (Block vs ps stm1)

-- Parse 0 or more proc declarations in a block
decPs :: Parser DecP
decPs = concat <$> sepEndBy decP semi

-- Parse a single proc declaration
decP :: Parser DecP
decP = do
  void (rword "proc")
  name <- identifier
  void (rword "is")
  stm1 <- singleStm
  return ([(name, stm1)])

-- Parse 0 or more variable declarations
decVs :: Parser DecV
decVs = concat <$> sepEndBy decV semi

-- Parse a single variable declaration
decV :: Parser DecV
decV = do
  void (rword "var")
  var <- identifier
  void (symbol ":=")
  expr <- aExp
  return ([(var, expr)])

-- Parse a statement
callStm :: Parser Stm
callStm = do
  rword "call"
  name <- identifier
  return (Call name)

-- Parse an if statement
ifStm :: Parser Stm
ifStm = do
  rword "if"
  cond <- bExp
  rword "then"
  stm1 <- stm
  rword "else"
  stm2 <- stm
  return (If cond stm1 stm2)

-- Parse a while statement
whileStm :: Parser Stm
whileStm = do
  rword "while"
  cond <- bExp
  rword "do"
  stm1 <- stm
  return (While cond stm1)

-- Parse an assign statement
assignStm :: Parser Stm
assignStm = do
  var  <- identifier
  void (symbol ":=")
  expr <- aExp
  return (Ass var expr)

-- Parse a skip statement
skipStm :: Parser Stm
skipStm = Skip <$ rword "skip"

-- Parse an arithmetic expression using makeExprParser
aExp :: Parser Aexp
aExp = makeExprParser aTerm aOperators

-- Parse a boolean expression using makeExprParser
bExp :: Parser Bexp
bExp = makeExprParser bTerm bOperators

-- Table of operators for arithmetic expressions
aOperators :: [[Operator Parser Aexp]]
aOperators =
  [ [ InfixL (Mult <$ symbol "*") ]
  , [ InfixL (Add  <$ symbol "+")
    , InfixL (Sub  <$ symbol "-")
    ]
  ]

-- Table of operators for boolean expressions
bOperators :: [[Operator Parser Bexp]]
bOperators =
  [ [Prefix (Neg <$ symbol "!") ]
  , [InfixL (And <$ symbol "&") ]
  ]

-- Parse an arithmetic expression
aTerm :: Parser Aexp
aTerm = parens aExp
  <|> V <$> identifier -- variable
  <|> N <$> integer    -- number

-- Parse a boolean expression
bTerm :: Parser Bexp
bTerm =  parens bExp
  <|> (rword "true"  *> pure TRUE)
  <|> (rword "false" *> pure FALSE)
  <|> eqExp
  <|> leExp

-- Parse a boolean equals expression
eqExp :: Parser Bexp
eqExp = do
  a1 <- aExp
  op <- symbol "="
  a2 <- aExp
  return (Eq a1 a2)

-- Parse a boolean less than expression
leExp :: Parser Bexp
leExp = do
  a1 <- aExp
  op <- symbol "<"
  a2 <- aExp
  return (Le a1 a2)
