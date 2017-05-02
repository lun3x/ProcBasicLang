import Prelude hiding (Num)
import Data.List

-- Defining basic datatypes
type Num = Integer
type Var = String

type Z = Integer
type T = Bool

type Pname = String
type DecV = [(Var, Aexp)]
type DecP = [(Pname, Stm)]

newtype MEnvP = MEnvP (Pname -> (Stm, MEnvP))

type State = Var -> Z

data Config = Inter Stm State
            | Final State

data ConfigD = InterD DecV DecP Stm State
             | FinalD DecV DecP State

data ConfigP = InterP Stm Store
             | FinalP Store

type Loc = Z
data Loc' = Loc' Loc
          | Next

type Store = Loc' -> Z
type EnvV = Var -> Loc

-- Defining data constructors
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

-- Defining base eval functions
-- Evaluate number
n_val :: Num -> Z
n_val x = x

-- Evaluate variable in store
getFromStore :: EnvV -> Store -> Var -> Z
getFromStore e s x = s (Loc' (e x))

-- Evaluate arithmetic expression
a_val :: Aexp -> EnvV -> Store -> Z
a_val (N n) eV s              = n_val n
a_val (V v) eV s              = getFromStore eV s v
a_val (Mult expr1 expr2) eV s = (a_val expr1 eV s) * (a_val expr2 eV s)
a_val (Add expr1 expr2) eV s  = (a_val expr1 eV s) + (a_val expr2 eV s)
a_val (Sub expr1 expr2) eV s  = (a_val expr1 eV s) - (a_val expr2 eV s)

-- Evaluate boolean expression
b_val :: Bexp -> EnvV -> Store -> T
b_val TRUE eV s  = True
b_val FALSE eV s = False
b_val (Neg expr) eV s
  | (b_val expr eV s) == True = False
  | otherwise                 = True
b_val (And expr1 expr2) eV s
  | ((b_val expr1 eV s) == True) && ((b_val expr2 eV s) == True) = True
  | otherwise                                                    = False
b_val (Eq expr1 expr2) eV s
  | (a_val expr1 eV s) == (a_val expr2 eV s) = True
  | otherwise                                = False
b_val (Le expr1 expr2) eV s
  | (a_val expr1 eV s) < (a_val expr2 eV s) = True
  | otherwise                               = False
b_val (Imp expr1 expr2) eV s
  | ((b_val expr1 eV s) == True) && ((b_val expr2 eV s) == False) = False
  | otherwise                                                     = True

-- Defining storewise functions

new :: Loc -> Loc
new = (+ 1)

updateMEnvP :: MEnvP -> Pname -> Stm -> MEnvP
updateMEnvP (MEnvP e) pName stm = MEnvP e' where
  e' pName'
   | pName' == pName = (stm, MEnvP e)
   | otherwise       = e pName'

assignDecPs :: MEnvP -> DecP -> MEnvP
assignDecPs e [] = e
assignDecPs e (dp:dps) = assignDecPs (assignDecP e dp) dps

assignDecP :: MEnvP -> (Pname, Stm) -> MEnvP
assignDecP e (pName, stm) = updateMEnvP e pName stm

-- assignDecVs :: EnvV -> Store -> DecV -> Store
-- assignDecVs s []     = s
-- assignDecVs s (dv:dvs) = assignDecVs (assignDecV s dv) dvs
--
-- assignDecV :: EnvV -> (Var, Aexp) -> EnvV
-- assignDecV s (v, expr) = updateStore s (a_val expr s) v

-- ns_decV :: ConfigD -> ConfigD
-- ns_decV (InterD dVs dPs stm state) = FinalD dVs dPs (assignDecVs state dVs)

updateStore :: EnvV -> Store -> Var -> Z -> Store
updateStore e s x i = s' where
  s' (Loc' loc)
         | loc == e x = i
         | otherwise  = s (Loc' (e x))

ns_stm :: EnvV -> MEnvP -> ConfigP -> ConfigP
ns_stm eV eP (InterP (Ass v a) sto) = FinalP (updateStore eV sto v (a_val a eV sto))
ns_stm eV eP (InterP (Skip) sto) = FinalP sto
ns_stm eV eP (InterP (Comp stm1 stm2) sto) = FinalP sto'' where
  FinalP sto'  = ns_stm eV eP (InterP stm1 sto)
  FinalP sto'' = ns_stm eV eP (InterP stm1 sto)
ns_stm eV eP (InterP (If test stm1 stm2) sto) = FinalP sto' where
  FinalP sto'
    | b_val test eV sto == True = ns_stm eV eP (InterP stm1 sto)
    | otherwise                 = ns_stm eV eP (InterP stm2 sto)
ns_stm eV eP (InterP (While test stm) sto) = FinalP sto'' where
  FinalP sto''
    | b_val test eV sto == True = FinalP loop_store
    | otherwise                 = FinalP sto
  FinalP loop_store  = ns_stm eV eP (InterP (While test stm) inter_store)
  FinalP inter_store = ns_stm eV eP (InterP stm sto)
ns_stm eV eP (Inter (Block decV decP stm) sto) 
