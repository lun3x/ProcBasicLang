module CW2 where

import Prelude hiding (Num)
import Data.List
import Control.Monad (void)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Expr
import Text.Megaparsec.String
import qualified Text.Megaparsec.Lexer as L

-- Defining basic datatypes
type Num = Integer
type Var = String

type Z = Integer
type T = Bool

type Pname = String
type DecV = [(Var, Aexp)]
type DecP = [(Pname, Stm)]

type EnvP = Pname -> Stm
type State = Var -> Z

data Aexp = N Num
          | V Var
          | Mult Aexp Aexp
          | Add Aexp Aexp
          | Sub Aexp Aexp
          deriving (Show, Eq, Read)

data Bexp = TRUE
          | FALSE
          | Neg Bexp
          | And Bexp Bexp
          | Eq Aexp Aexp
          | Le Aexp Aexp
          | Imp Bexp Bexp
          deriving (Show, Eq, Read)

data Stm = Ass Var Aexp
         | Skip
         | Comp Stm Stm -- Compose
         | If Bexp Stm Stm
         | While Bexp Stm
         | Block DecV DecP Stm
         | Call Pname
         deriving (Show, Eq, Read)

n_val :: Num -> Z
n_val x = x

a_val_d :: Aexp -> State -> Z
a_val_d (N n) s        = n_val n
a_val_d (V v) s        = s v
a_val_d (Mult e1 e2) s = (a_val_d e1 s) * (a_val_d e2 s)
a_val_d (Add e1 e2) s  = (a_val_d e1 s) + (a_val_d e2 s)
a_val_d (Sub e1 e2) s  = (a_val_d e1 s) - (a_val_d e2 s)

b_val_d :: Bexp -> State -> T
b_val_d TRUE s  = True
b_val_d FALSE s = False
b_val_d (Neg e) s
  | (b_val_d e s) == True = False
  | otherwise           = True
b_val_d (And e1 e2) s
  | ((b_val_d e1 s) == True) && ((b_val_d e2 s) == True) = True
  | otherwise                                        = False
b_val_d (Eq e1 e2) s
  | (a_val_d e1 s) == (a_val_d e2 s) = True
  | otherwise                    = False
b_val_d (Le e1 e2) s
  | (a_val_d e1 s) < (a_val_d e2 s) = True
  | otherwise                   = False
b_val_d (Imp e1 e2) s
  | ((b_val_d e1 s) == True) && ((b_val_d e2 s) == False) = False
  | otherwise                                         = True

updateState :: State -> Z -> Var -> State
updateState s i v = s' where          -- equals updated state
  s' v'               -- where in the updated state
   | v' == v   = i    -- the relevant variable equals the new integer
   | otherwise = s v' -- the other variables stay the same

cond :: (a->T, a->a, a->a) -> (a->a)
cond (test, func1, func2) state
  | test state = func1 state
  | otherwise  = func2 state

fix :: ((State->State) -> (State->State)) -> (State->State)
fix ff = ff (fix ff)

-- Resets any variables that have had new ones declared with the same name to their original state
-- (Preserves scoping)
resetVars :: State -> State -> DecV -> State
resetVars s s' [] = s'
resetVars s s' d  = resetVars s (updateState s' (s (fst (head d))) (fst (head d))) (tail d)

-- Recurse through all procedure declarations to update environment
-- upd_p
updateEnvPs :: EnvP -> DecP -> EnvP
updateEnvPs env [] = env
updateEnvPs env ps = updateEnvPs (updateEnvP env ps) (tail ps)

-- Update environment with first declaration in DecP
updateEnvP :: EnvP -> DecP -> EnvP
updateEnvP env decP = env'
                where env' pName
                         | pName == (fst (head decP)) = snd (head decP)
                         | otherwise                  = env pName

-- ->_D
updateDecVs_d :: State -> DecV -> State
updateDecVs_d s []   = s
updateDecVs_d s decV = updateDecVs_d (updateDecV_d s decV) (tail decV)

updateDecV_d :: State -> DecV -> State
updateDecV_d s decV = updateState s (a_val_d (snd (head decV)) s) (fst (head decV))

-- Update the current state given a statement and the environment
s_ds_dynamic :: Stm -> EnvP -> State -> State
s_ds_dynamic Skip e s                  = s
s_ds_dynamic (Ass v exp0) e s          = updateState s (a_val_d exp0 s) v
s_ds_dynamic (Comp stm1 stm2) e s      = s_ds_dynamic stm2 e (s_ds_dynamic stm1 e s)
s_ds_dynamic (If test stm1 stm2) e s   = cond (b_val_d test, s_ds_dynamic stm1 e, s_ds_dynamic stm2 e) s
s_ds_dynamic (While test stm) e s      = fix f s
                                       where f g = cond (b_val_d test, g . (s_ds_dynamic stm e), s_ds_dynamic Skip e)
s_ds_dynamic (Block decV decP stm) e s = resetVars s (s_ds_dynamic stm e' s') decV
                                                                 where e' = updateEnvPs e decP
                                                                       s' = updateDecVs_d s decV
s_ds_dynamic (Call n) e s              = s_ds_dynamic (e n) e s

baseEnvP :: EnvP
baseEnvP _ = Skip

baseState :: State
baseState _ = 0

-- Testing wrapper function
s_dynamic :: Stm -> State -> State
s_dynamic stm state = s_ds_dynamic stm baseEnvP state

--------------------------------------------------------------------------------------------------------------------------------------
---------------------------- Mixed ------------------------------------------------------------------------------------

newtype MEnvP = MEnvP (Pname -> (Stm, MEnvP))

updateMEnvP_m :: MEnvP -> Pname -> Stm -> MEnvP
updateMEnvP_m (MEnvP e) pName stm = MEnvP e' where
  e' pName'
   | pName' == pName = (stm, MEnvP e)
   | otherwise       = e pName'

assignDecPs_m :: MEnvP -> DecP -> MEnvP
assignDecPs_m e [] = e
assignDecPs_m e (dp:dps) = assignDecPs_m (assignDecP_m e dp) dps

assignDecP_m :: MEnvP -> (Pname, Stm) -> MEnvP
assignDecP_m e (pName, stm) = updateMEnvP_m e pName stm

assignDecVs_m :: State -> DecV -> State
assignDecVs_m s []     = s
assignDecVs_m s (dv:dvs) = assignDecVs_m (assignDecV_m s dv) dvs

assignDecV_m :: State -> (Var, Aexp) -> State
assignDecV_m s (v, expr) = updateState s (a_val_d expr s) v

s_ds_mixed :: Stm -> MEnvP -> State -> State
s_ds_mixed Skip e s                  = s
s_ds_mixed (Ass v expr) e s          = updateState s (a_val_d expr s) v
s_ds_mixed (Comp stm1 stm2) e s      = s_ds_mixed stm2 e (s_ds_mixed stm1 e s)
s_ds_mixed (If test stm1 stm2) e s   = cond (b_val_d test, s_ds_mixed stm1 e, s_ds_mixed stm2 e) s
s_ds_mixed (While test stm) e s      = fix f s where
                                           f g = cond (b_val_d test, g . (s_ds_mixed stm e), s_ds_mixed Skip e)
s_ds_mixed (Block decV decP stm) e s = resetVars s (s_ds_mixed stm e' s') decV where
                                                                   e' = assignDecPs_m e decP
                                                                   s' = assignDecVs_m s decV
s_ds_mixed (Call pName) (MEnvP env) state = state' where
  state' = s_ds_mixed stmt (updateMEnvP_m env' pName stmt) state where
     (stmt, env') = env pName

baseMEnvP :: MEnvP
baseMEnvP = MEnvP baseMEnvP'

baseMEnvP' :: Pname -> (Stm, MEnvP)
baseMEnvP' _ = (Skip, baseMEnvP)

s_mixed :: Stm -> State -> State
s_mixed stm state = s_ds_mixed stm baseMEnvP state

--------------------------------------------------------------------------------------------------------------------------------------
---------------------------- Static ------------------------------------------------------------------------------------

newtype SEnvP = SEnvP (Pname -> (Stm, EnvV, SEnvP))

data ConfigD = InterD DecV DecP Stm Store
             | FinalD DecV DecP Store

data ConfigP = InterP Stm Store
             | FinalP Store

type Loc = Z
data Loc' = Loc' Loc
          | Next

type Store = Loc' -> Z
type EnvV = Var -> Loc

-- Evaluate variable in store
getFromStore :: EnvV -> Store -> Var -> Z
getFromStore e s x = s (Loc' (e x))

getStoreFromConfig :: ConfigP -> Store
getStoreFromConfig (FinalP sto) = sto
getStoreFromConfig (InterP stm sto) = sto

-- Evaluate arithmetic expression
a_val_s :: Aexp -> EnvV -> Store -> Z
a_val_s (N n) eV s              = n_val n
a_val_s (V v) eV s              = getFromStore eV s v
a_val_s (Mult expr1 expr2) eV s = (a_val_s expr1 eV s) * (a_val_s expr2 eV s)
a_val_s (Add expr1 expr2) eV s  = (a_val_s expr1 eV s) + (a_val_s expr2 eV s)
a_val_s (Sub expr1 expr2) eV s  = (a_val_s expr1 eV s) - (a_val_s expr2 eV s)

-- Evaluate boolean expression
b_val_s :: Bexp -> EnvV -> Store -> T
b_val_s TRUE eV s  = True
b_val_s FALSE eV s = False
b_val_s (Neg expr) eV s
  | (b_val_s expr eV s) == True = False
  | otherwise                 = True
b_val_s (And expr1 expr2) eV s
  | ((b_val_s expr1 eV s) == True) && ((b_val_s expr2 eV s) == True) = True
  | otherwise                                                    = False
b_val_s (Eq expr1 expr2) eV s
  | (a_val_s expr1 eV s) == (a_val_s expr2 eV s) = True
  | otherwise                                = False
b_val_s (Le expr1 expr2) eV s
  | (a_val_s expr1 eV s) < (a_val_s expr2 eV s) = True
  | otherwise                               = False
b_val_s (Imp expr1 expr2) eV s
  | ((b_val_s expr1 eV s) == True) && ((b_val_s expr2 eV s) == False) = False
  | otherwise                                                     = True

-- Defining storewise functions

new :: Loc -> Loc
new = (+ 1)

updateSEnvP_s :: EnvV -> SEnvP -> Pname -> Stm -> SEnvP
updateSEnvP_s eV (SEnvP e) pName stm = SEnvP e' where
  e' pName'
   | pName' == pName = (stm, eV, SEnvP e)
   | otherwise       = e pName'

assignDecPs :: DecP -> EnvV -> SEnvP -> SEnvP
assignDecPs [] eV eP       = eP
assignDecPs (dp:dps) eV eP = assignDecPs dps eV (assignDecP dp eV eP)

assignDecP :: (Pname, Stm) -> EnvV -> SEnvP -> SEnvP
assignDecP (pName, stm) eV eP = updateSEnvP_s eV eP pName stm

updateEnvV :: EnvV -> Var -> Loc -> EnvV
updateEnvV eV v loc = eV' where
  eV' v'
    | v' == v   = loc
    | otherwise = eV v'

assignDecVs :: EnvV -> Store -> DecV -> (EnvV, Store)
assignDecVs eV sto []       = (eV, sto)
assignDecVs eV sto (dv:dvs) = assignDecVs eV' sto' dvs where
  (eV', sto') = assignDecV eV sto dv

assignDecV :: EnvV -> Store -> (Var, Aexp) -> (EnvV, Store)
assignDecV eV sto (v, expr) = (eV', sto') where
  eV' = updateEnvV eV v l
  sto' = incStoreNext (updateStore sto l (a_val_s expr eV sto))
  l = sto Next

incStoreNext :: Store -> Store
incStoreNext sto = sto' where
  sto' Next = new (sto Next)
  sto' l    = sto l

updateStore :: Store -> Loc -> Z -> Store
updateStore sto loc i = sto' where
  sto' (Loc' loc')
     | loc' == loc = i
     | otherwise   = sto (Loc' loc')
  sto' Next = sto Next

updateStore' :: EnvV -> Store -> Var -> Z -> Store
updateStore' e s x i = s' where
  s' (Loc' loc)
         | loc == e x = i
         | otherwise  = s (Loc' (e x))
  s' Next = s Next

-- ns_decV :: EnvV -> ConfigD -> ConfigD
-- ns_decV eV (InterD dVs dPs stm sto) = FinalD dVs dPs (snd (assignDecVs eV sto dVs))

ns_stm :: EnvV -> SEnvP -> ConfigP -> ConfigP
ns_stm eV eP (InterP (Ass v a) sto) = FinalP (updateStore' eV sto v (a_val_s a eV sto))
ns_stm eV eP (InterP (Skip) sto) = FinalP sto
ns_stm eV eP (InterP (Comp stm1 stm2) sto) = FinalP sto'' where
  FinalP sto'  = ns_stm eV eP (InterP stm1 sto)
  FinalP sto'' = ns_stm eV eP (InterP stm1 sto)
ns_stm eV eP (InterP (If test stm1 stm2) sto) = FinalP sto' where
  FinalP sto'
    | b_val_s test eV sto == True = ns_stm eV eP (InterP stm1 sto)
    | otherwise                 = ns_stm eV eP (InterP stm2 sto)
ns_stm eV eP (InterP (While test stm) sto) = FinalP sto'' where
  FinalP sto''
    | b_val_s test eV sto == True = FinalP loop_store
    | otherwise                 = FinalP sto
  FinalP loop_store  = ns_stm eV eP (InterP (While test stm) inter_store)
  FinalP inter_store = ns_stm eV eP (InterP stm sto)
ns_stm eV eP (InterP (Block decV decP stm) sto) = FinalP sto'' where
  FinalP sto'' = ns_stm eV' eP' (InterP stm sto')
  (eV', sto') = assignDecVs eV sto decV
  eP'         = assignDecPs decP eV' eP
ns_stm eV (SEnvP eP) (InterP (Call pName) sto) = FinalP sto' where
  FinalP sto' = ns_stm eV' (updateSEnvP_s eV' eP' pName stmt) (InterP stmt sto)
  (stmt, eV', eP') = eP pName

-- Wrapper for static

createState :: EnvV -> Store -> State
createState eV sto = s where
  s x = sto (Loc' (eV x))

s_static :: Stm -> State -> State
s_static stm s = createState eV sto'
  where
    FinalP sto' = (ns_stm eV baseSEnvP (InterP stm sto))
    (eV, sto) = initialEnvV stm s

getVars :: Stm -> [Var]
getVars (Ass v a)       = [v]
getVars (Skip)          = []
getVars (Comp s1 s2)    = (getVars s1) ++ (getVars s2)
getVars (If b s1 s2)    = (getVars s1) ++ (getVars s2)
getVars (While b stm)   = (getVars stm)
getVars (Block v p stm) = (getDecVVs v) ++ (getDecPVs p) ++ (getVars stm)
getVars (Call name)     = []

getDecVVs :: DecV -> [Var]
getDecVVs []           = []
getDecVVs ((v, a):dvs) = v : getDecVVs dvs

getDecPVs :: DecP -> [Var]
getDecPVs []             = []
getDecPVs ((p, stm):dps) = getDecPVs dps ++ getVars stm

baseStore :: Store
baseStore Next = 1
baseStore _    = 0

initialEnvV :: Stm -> State -> (EnvV, Store)
initialEnvV stm s = setUpEnv (nub (getVars stm)) baseEnvV baseStore s

convertVsStateToDecVs :: [Var] -> State -> DecV -> DecV
convertVsStateToDecVs [] s dVs     = dVs
convertVsStateToDecVs (v:vs) s dVs = (convertVStateToDecV v s):(convertVsStateToDecVs vs s dVs)

convertVStateToDecV :: Var -> State -> (Var, Aexp)
convertVStateToDecV v s = (v, (N (s v)))

setUpEnv :: [Var] -> EnvV -> Store -> State -> (EnvV, Store)
setUpEnv vs eV sto s = assignDecVs eV sto (convertVsStateToDecVs vs s [])

baseSEnvP :: SEnvP
baseSEnvP = SEnvP baseSEnvP'

baseSEnvP' :: Pname -> (Stm, EnvV, SEnvP)
baseSEnvP' _ = (Skip, baseEnvV, baseSEnvP)

baseEnvV :: EnvV
baseEnvV _ = 0

pretty_print :: State -> String
pretty_print s = "x: " ++ show (s "x") ++ " y: " ++ show (s "y") ++ " z: " ++ show (s "z")

scopeTestStm :: Stm
scopeTestStm = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))

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
eval_dynamic :: String -> String
eval_dynamic s = pretty_print $ s_dynamic (parseString s) baseState

-- Evaluate an input program as a string, return a pretty list of final state variables
eval_mixed :: String -> String
eval_mixed s = pretty_print $ s_mixed (parseString s) baseState

eval_static :: String -> String
eval_static s = pretty_print $ s_static (parseString s) baseState

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
