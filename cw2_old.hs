module CW2 where

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

pretty_print :: State -> String
pretty_print s = "x: " ++ show (s "x") ++ " y: " ++ show (s "y") ++ " z: " ++ show (s "z")

n_val :: Num -> Z
n_val x = x

baseState :: State
baseState _ = 0

s :: State
s "x" = 1
s "y" = 2
s "z" = 3
s  _  = 0

a :: Aexp
--a = Mult (Add (V "x") (V "y")) (Sub (V "z") (N 1))
a = ((V "x") `Add` (V "x")) `Mult` ((V "z") `Sub` (N 1))

mult2 :: Aexp -> Aexp
mult2 x = (N 2) `Mult` x

mult3 :: Aexp -> Aexp
mult3 x = (N 3) `Mult` x

a_val :: Aexp -> State -> Z
a_val (N n) s        = n_val n
a_val (V v) s        = s v
a_val (Mult e1 e2) s = (a_val e1 s) * (a_val e2 s)
a_val (Add e1 e2) s  = (a_val e1 s) + (a_val e2 s)
a_val (Sub e1 e2) s  = (a_val e1 s) - (a_val e2 s)

b :: Bexp
b = Neg (Eq (Add (V "x") (V "y")) (N 4))

c :: Bexp
c = Imp b TRUE

d :: Bexp -> Bexp
d x = Neg x

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

afv_aexp :: Aexp -> [Var]
afv_aexp (N n) = []
afv_aexp (V v) = [v]
afv_aexp (Mult e1 e2) = (afv_aexp e1) ++ (afv_aexp e2)
afv_aexp (Add e1 e2)  = (afv_aexp e1) ++ (afv_aexp e2)
afv_aexp (Sub e1 e2)  = (afv_aexp e1) ++ (afv_aexp e2)

fv_aexp :: Aexp -> [Var]
fv_aexp e = nub (afv_aexp e)

subst_aexp :: Aexp -> Var -> Aexp -> Aexp
subst_aexp (N n) _ _ = (N n)
subst_aexp (V v1) v2 a2
  | v1 == v2 = a2
  | otherwise = (V v1)
subst_aexp (Mult e1 e2) v a2 = Mult (subst_aexp e1 v a2) (subst_aexp e2 v a2)
subst_aexp (Add e1 e2) v a2  = Add (subst_aexp e1 v a2) (subst_aexp e2 v a2)
subst_aexp (Sub e1 e2) v a2  = Sub (subst_aexp e1 v a2) (subst_aexp e2 v a2)

-- Example statement
stmt0 :: Stm
stmt0 = "y" `Ass` (N 1)

stmt1 :: Stm
stmt1 = "y" `Ass` ((V "y") `Mult` (V "x"))

stmt2 :: Stm
stmt2 = "x" `Ass` ((V "x") `Sub` (N 1))

condit :: Bexp
condit = Neg (Eq (V "x") (N 1))

p :: Stm
p = stmt0 `Comp` (While condit (stmt1 `Comp` stmt2))

p2 :: Stm
p2 = While (Le (V "x") (N 5)) ("x" `Ass` ((V "x") `Add` (N 1)))

update :: State -> Z -> Var -> State
update s i v = s' where          -- equals updated state
               s' v'               -- where in the updated state
                | v' == v   = i    -- the relevant variable equals the new integer
                | otherwise = s v' -- the other variables stay the same

s' :: State
s' = update s 10 "x"

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
resetVars s s' d  = resetVars s (update s' (s (fst (head d))) (fst (head d))) (tail d)

baseEnvP :: EnvP
baseEnvP _ = Skip

baseEnvV :: EnvV
baseEnvV _ = -1

baseStore :: Store
baseStore _ = 0

upd_p :: DecP -> EnvSP -> EnvV -> EnvSP
upd_p dp envSP envV = updateEnvSPs envSP dp

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

updateEnvSPs :: EnvSP -> DecP -> EnvSP
updateEnvSPs env [] = env
updateEnvSPs env ps = updateEnvSPs (updateEnvSP env ps) (tail ps)

updateEnvSP :: EnvSP -> DecP -> EnvSP
updateEnvSP env decP = env'
                 where env' pName
                          | pName == (fst (head decP)) = EnvSP' (snd (head decP)) env
                          | otherwise                  = env pName

-- ->_D
updateDecVs :: State -> DecV -> State
updateDecVs s []   = s
updateDecVs s decV = updateDecVs (updateDecV s decV) (tail decV)

updateDecV :: State -> DecV -> State
updateDecV s decV = update s (a_val (snd (head decV)) s) (fst (head decV))

-- Update the current state given a statement and the environment
s_ds_dynamic :: Stm -> EnvP -> State -> State
s_ds_dynamic Skip e s                  = s
s_ds_dynamic (Ass v exp0) e s          = update s (a_val exp0 s) v
s_ds_dynamic (Comp stm1 stm2) e s      = s_ds_dynamic stm2 e (s_ds_dynamic stm1 e s)
s_ds_dynamic (If test stm1 stm2) e s   = cond (b_val test, s_ds_dynamic stm1 e, s_ds_dynamic stm2 e) s
s_ds_dynamic (While test stm) e s      = fix f s
                                       where f g = cond (b_val test, g . (s_ds_dynamic stm e), s_ds_dynamic Skip e)
s_ds_dynamic (Block decV decP stm) e s = resetVars s (s_ds_dynamic stm e' s') decV
                                                                 where e' = updateEnvPs e decP
                                                                       s' = updateDecVs s decV
s_ds_dynamic (Call n) e s              = s_ds_dynamic (e n) e s

-- Testing wrapper function
s_dynamic :: Stm -> State -> State
s_dynamic stm state = s_ds_dynamic stm baseEnvP state

scopeTestStm :: Stm
scopeTestStm = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))
