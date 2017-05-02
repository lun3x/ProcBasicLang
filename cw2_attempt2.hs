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

type EnvP = Pname -> EnvP'
data EnvP' = EnvP' Stm EnvP

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

-- Evaluate arithmetic expression
a_val :: Aexp -> State -> Z
a_val (N n) s        = n_val n
a_val (V v) s        = s v
a_val (Mult e1 e2) s = (a_val e1 s) * (a_val e2 s)
a_val (Add e1 e2) s  = (a_val e1 s) + (a_val e2 s)
a_val (Sub e1 e2) s  = (a_val e1 s) - (a_val e2 s)

-- Evaluate boolean expression
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

-- Defining statewise functions
-- Update given variable in given state with new given value
update :: State -> Z -> Var -> State
update s i v = s' where          -- equals updated state
               s' v'               -- where in the updated state
                | v' == v   = i    -- the relevant variable equals the new integer
                | otherwise = s v' -- the other variables stay the same

-- Conditionally choose between two functions based on a given boolean test
cond :: (a->T, a->a, a->a) -> (a->a)
cond (test, func1, func2) state
  | test state = func1 state
  | otherwise  = func2 state

-- Fix point of transition function
fix :: ((State->State) -> (State->State)) -> (State->State)
fix ff = ff (fix ff)

-- Resets any variables that have had new ones declared with the same name to their original state
-- (Preserves scoping)
resetVars :: State -> State -> DecV -> State
resetVars s s' [] = s'
resetVars s s' d  = resetVars s (update s' (s (fst (head d))) (fst (head d))) (tail d)

new :: Loc -> Loc
new = (+ 1)

-- ->_D
updateDecVs :: State -> DecV -> State
updateDecVs s []   = s
updateDecVs s decV = updateDecVs (updateDecV s decV) (tail decV)

updateDecV :: State -> DecV -> State
updateDecV s decV = update s (a_val (snd (head decV)) s) (fst (head decV))

ns_decV :: ConfigD -> ConfigD
ns_decV (InterD dVs dPs stm state) = FinalD dVs dPs (updateDecVs state dVs)

getFromStore :: EnvV -> Store -> Var -> Z
getFromStore e s x = s (Loc' (e x))

updateStore :: EnvV -> Store -> Var -> Z -> Store
updateStore e s x i = s' where
  s' Loc' loc
        | loc == e x = i
        | otherwise  = s (Loc' (e x))

ns_stm :: EnvV -> EnvP -> ConfigP -> ConfigP
ns_stm eV eP (Inter (Ass x a) sto) = Final (update s (a_val a s) x)
ns_stm eV eP (Inter (Skip) s) = Final s
ns_stm eV eP (Inter (Comp stm1 stm2) s) = Final s'' where
  Final s'  = ns_stm (Inter stm1 s)
  Final s'' = ns_stm (Inter stm1 s)
ns_stm eV eP (Inter (If test stm1 stm2) s) = Final s' where
  Final s'
    | b_val test s == True = ns_stm (Inter stm1 s)
    | otherwise            = ns_stm (Inter stm2 s)
ns_stm eV eP (Inter (While test stm) s) = Final s'' where
  Final s''
    | b_val test s == True = Final loop_state
    | otherwise            = Final s
  Final loop_state  = ns_stm (Inter (While test stm) inter_state)
  Final inter_state = ns_stm (Inter stm s)
