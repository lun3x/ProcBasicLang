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

newtype MEnvP = MEnvP (Pname -> (Stm, EnvV, MEnvP))

type State = Var -> Z

data ConfigD = InterD DecV DecP Stm Store
             | FinalD DecV DecP Store

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

updateMEnvP :: EnvV -> MEnvP -> Pname -> Stm -> MEnvP
updateMEnvP eV (MEnvP e) pName stm = MEnvP e' where
  e' pName'
   | pName' == pName = (stm, eV, MEnvP e)
   | otherwise       = e pName'

assignDecPs :: DecP -> EnvV -> MEnvP -> MEnvP
assignDecPs [] eV eP       = eP
assignDecPs (dp:dps) eV eP = assignDecPs dps eV (assignDecP dp eV eP)

assignDecP :: (Pname, Stm) -> EnvV -> MEnvP -> MEnvP
assignDecP (pName, stm) eV eP = updateMEnvP eV eP pName stm

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
  sto' = incStoreNext (updateStore sto l (a_val expr eV sto))
  l = sto Next

incStoreNext :: Store -> Store
incStoreNext sto = sto' where
  sto' Next = new (sto Next)

updateStore :: Store -> Loc -> Z -> Store
updateStore sto loc i = sto' where
  sto' (Loc' loc')
     | loc' == loc = i
     | otherwise   = sto (Loc' loc')

updateStore' :: EnvV -> Store -> Var -> Z -> Store
updateStore' e s x i = s' where
  s' (Loc' loc)
         | loc == e x = i
         | otherwise  = s (Loc' (e x))

-- ns_decV :: EnvV -> ConfigD -> ConfigD
-- ns_decV eV (InterD dVs dPs stm sto) = FinalD dVs dPs (snd (assignDecVs eV sto dVs))

ns_stm :: EnvV -> MEnvP -> ConfigP -> ConfigP
ns_stm eV eP (InterP (Ass v a) sto) = FinalP (updateStore' eV sto v (a_val a eV sto))
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
ns_stm eV eP (InterP (Block decV decP stm) sto) = FinalP sto'' where
  FinalP sto'' = ns_stm eV' eP' (InterP stm sto')
  (eV', sto') = assignDecVs eV sto decV
  eP'         = assignDecPs decP eV' eP
ns_stm eV (MEnvP eP) (InterP (Call pName) sto) = FinalP sto' where
  FinalP sto' = ns_stm eV' (updateMEnvP eV' eP' pName stmt) (InterP stmt sto)
  (stmt, eV', eP') = eP pName
