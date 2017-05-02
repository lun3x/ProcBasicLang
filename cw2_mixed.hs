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

n_val :: Num -> Z
n_val x = x

a_val :: Aexp -> State -> Z
a_val (N n) s        = n_val n
a_val (V v) s        = s v
a_val (Mult e1 e2) s = (a_val e1 s) * (a_val e2 s)
a_val (Add e1 e2) s  = (a_val e1 s) + (a_val e2 s)
a_val (Sub e1 e2) s  = (a_val e1 s) - (a_val e2 s)

b_val :: Bexp -> State -> T
b_val TRUE s  = True
b_val FALSE s = False
b_val (Neg e) s
  | (b_val e s) == True = False
  | otherwise           = True
b_val (And e1 e2) s
  | ((b_val e1 s) == True) && ((b_val e2 s) == True) = True
  | otherwise                                        = False
b_val (Eq e1 e2) s
  | (a_val e1 s) == (a_val e2 s) = True
  | otherwise                    = False
b_val (Le e1 e2) s
  | (a_val e1 s) < (a_val e2 s) = True
  | otherwise                   = False
b_val (Imp e1 e2) s
  | ((b_val e1 s) == True) && ((b_val e2 s) == False) = False
  | otherwise                                         = True

cond :: (a->T, a->a, a->a) -> (a->a)
cond (test, func1, func2) state
  | test state = func1 state
  | otherwise  = func2 state

fix :: ((State->State) -> (State->State)) -> (State->State)
fix ff = ff (fix ff)

updateState :: State -> Z -> Var -> State
updateState s i v = s' where          -- equals updated state
  s' v'               -- where in the updated state
   | v' == v   = i    -- the relevant variable equals the new integer
   | otherwise = s v' -- the other variables stay the same

updateMEnvP :: MEnvP -> Pname -> Stm -> MEnvP
updateMEnvP (MEnvP e) pName stm = MEnvP e' where
  e' pName'
   | pName' == pName = (stm, MEnvP e)
   | otherwise       = (fst (e pName), MEnvP e)

resetVars :: State -> State -> DecV -> State
resetVars s s' [] = s'
resetVars s s' d  = resetVars s (updateState s' (s (fst (head d))) (fst (head d))) (tail d)

assignDecPs :: MEnvP -> DecP -> MEnvP
assignDecPs e [] = e
assignDecPs e (dp:dps) = assignDecPs (assignDecP e dp) dps

assignDecP :: MEnvP -> (Pname, Stm) -> MEnvP
assignDecP e (pName, stm) = updateMEnvP e pName stm

assignDecVs :: State -> DecV -> State
assignDecVs s []     = s
assignDecVs s (dv:dvs) = assignDecVs (assignDecV s dv) dvs

assignDecV :: State -> (Var, Aexp) -> State
assignDecV s (v, expr) = updateState s (a_val expr s) v

s_ds_mixed :: Stm -> MEnvP -> State -> State
s_ds_mixed Skip e s                  = s
s_ds_mixed (Ass v expr) e s          = updateState s (a_val expr s) v
s_ds_mixed (Comp stm1 stm2) e s      = s_ds_mixed stm2 e (s_ds_mixed stm1 e s)
s_ds_mixed (If test stm1 stm2) e s   = cond (b_val test, s_ds_mixed stm1 e, s_ds_mixed stm2 e) s
s_ds_mixed (While test stm) e s      = fix f s where
                                           f g = cond (b_val test, g . (s_ds_mixed stm e), s_ds_mixed Skip e)
s_ds_mixed (Block decV decP stm) e s = resetVars s (s_ds_mixed stm e' s') decV where
                                                                   e' = assignDecPs e decP
                                                                   s' = assignDecVs s decV
s_ds_mixed (Call pName) (MEnvP env) state = state' where
  state' = s_ds_mixed stmt env' state where
     (stmt, env') = env pName

baseMEnvP :: MEnvP
baseMEnvP = MEnvP baseMEnvP'

baseMEnvP' :: Pname -> (Stm, MEnvP)
baseMEnvP' _ = (Skip, baseMEnvP)

baseState :: State
baseState _ = 0

scopeTestStm :: Stm
scopeTestStm = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))

pretty_print :: State -> String
pretty_print s = "x: " ++ show (s "x") ++ " y: " ++ show (s "y") ++ " z: " ++ show (s "z")
