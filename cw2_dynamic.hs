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

type EnvP = Pname -> Stm
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

pretty_state :: State -> String
pretty_state s = "x: " ++ show (s "x") ++ " y: " ++ show (s "y") ++ " z: " ++ show (s "z")

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

-- Testing wrapper function
s_dynamic :: Stm -> State -> State
s_dynamic stm state = s_ds_dynamic stm baseEnvP state

scopeTestStm :: Stm
scopeTestStm = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))

baseEnvP :: EnvP
baseEnvP _ = Skip

baseState :: State
baseState _ = 0
