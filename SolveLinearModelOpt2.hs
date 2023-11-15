import Debug.Trace
import Data.List
import Data.Char

data Typ = TTop | TBot | TInt | Fun Typ Typ | Var String | Nominal String deriving (Eq)

data Work = Exists Typ String Typ | Sub Typ Typ 

type WorkList = [Work]

type NominalEnv = [(String, Maybe String)]

instance Show Typ where
   show TInt          = "I"
   show TTop          = "T"
   show TBot          = "B"
   show (Fun a b)     = "(" ++ show a ++ ") -> " ++ show b
   show (Var s )      = "^" ++ s
   show (Nominal s)   = s

showWork (Sub t1 t2)        = show t1 ++ " <: " ++ show t2
showWork (Exists t1 s t2)   = show t1 ++ " <: ^" ++ s ++ " <: " ++ show t2

instance {-# OVERLAPPING #-} Show WorkList where
   show []      = "."
   show [x]     = showWork x
   show (x:xs)  = show xs ++ ", " ++ showWork x

subst :: NominalEnv -> String -> Typ -> Bool -> WorkList -> Maybe WorkList
subst e i t b o@(Sub t1 t2 : ws) = do ws' <- subst e i t b ws
                                      return (Sub t1 t2 : ws')
subst e i t b (Exists t1 s t2 : ws)
   | i == s && b       = do t2' <- glb e t t2
                            return (Exists t1 s t2' : ws)
   | i == s && (not b) = do t1' <- lub e t t1
                            return (Exists t1' s t2 : ws)
   | otherwise           =  -- not fully correct as I ignore dependencies (but we know how to deal with this)
       do ws' <- subst e i t b ws
          return (Exists t1 s t2 : ws')

lub :: NominalEnv -> Typ -> Typ -> Maybe Typ
lub e TBot t                     = Just t
lub e t TBot                     = Just t
lub e TInt TInt                  = Just TInt
lub e (Nominal n1) (Nominal n2)
   | n1 == n2 || subN n1 n2 e    = Just (Nominal n2)
   | subN n2 n1 e                = Just (Nominal n1)
lub e (Fun a b) (Fun c d)        =
   do t1 <- glb e a c
      t2 <- lub e b d
      return (Fun t1 t2)
lub e _ _                        = Nothing

glb :: NominalEnv -> Typ -> Typ -> Maybe Typ
glb e TTop t                     = Just t
glb e t TTop                     = Just t
glb e TInt TInt                  = Just TInt
glb e (Nominal n1) (Nominal n2)
   | n1 == n2 || subN n1 n2 e    = Just (Nominal n1)
   | subN n2 n1 e                = Just (Nominal n2)
glb e (Fun a b) (Fun c d)        =
   do t1 <- lub e a c
      t2 <- glb e b d
      return (Fun t1 t2)
glb e _ _                        = Nothing

-- I know that the two nominal types are different

subN :: String -> String -> NominalEnv -> Bool
subN n1 n2 []             = False
subN n1 n2 ((n3,Nothing):es)
   | n1 /= n3 && n2 /= n3 = subN n1 n2 es
   | otherwise            = False
subN n1 n2 ((n3,Just n4):es)
   | n1 == n3 && n2 == n4 = True
   | otherwise            = subN (if n1 == n3 then n4 else n1) n2 es

-- I will need this, if I use Top and Bot in places other than the bound
mono :: Typ -> Bool
mono TTop       = False
mono TBot       = False
mono (Fun a b)  = mono a && mono b
mono _          = True

-- run = maybe False id

solvable' e = maybe False (solvable e)

solvable :: NominalEnv -> WorkList -> Bool
solvable _ []                                    = True
-- Subtyping
solvable e o@(Sub a TTop : ws)                   = trace (show o) $ solvable e ws
solvable e o@(Sub TBot a : ws)                   = trace (show o) $ solvable e ws
solvable e o@(Sub TInt TInt : ws)                = trace (show o) $ solvable e ws 
solvable e o@(Sub (Fun t1 t2) (Fun t3 t4) : ws)  = trace (show o) $ solvable e (Sub t3 t1 : Sub t2 t4 : ws)
-- cases for non-mono are missing
solvable e o@(Sub (Var i) t1 : ws) | mono t1     = trace (show o) $ solvable' e (subst e i t1 True ws)
solvable e o@(Sub t1 (Var i) : ws) | mono t1     = trace (show o) $ solvable' e (subst e i t1 False ws)
solvable e o@(Sub (Nominal n1) (Nominal n2) : ws)
   | n1 == n2 || subN n1 n2 e = trace (show o) $ solvable e ws
   | otherwise                = trace (show o) $ False
-- Existentials
solvable e o@(Exists t1 s t2 : ws)               = trace (show o) $ solvable e (Sub t1 t2 : ws) 
solvable e o                                     = trace (show o) $ False


nomEnv = [("Grad", Just "Student"), ("Student", Just "Person"), ("Person", Nothing), ("Oak",Just "Tree"), ("Tree",Just "Plant"), ("Plant",Nothing)]

solve = solvable nomEnv

w1 = [Sub TInt TInt, Exists TBot "a" TTop]

w2 = [Sub (Var "a") TInt, Exists TBot "a" TTop]

w3 = [Sub (Var "a") (Fun TInt TInt), Sub (Var "a") TInt, Exists TBot "a" TTop]

w4 = [Sub (Fun (Var "a") (Var "a")) (Fun (Fun TInt TInt) (Fun TInt TInt)), Sub (Fun (Var "a") (Var "a")) (Fun TInt TInt) , Exists TBot "a" TTop]

w5 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Student")), Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Exists TBot "a" TTop]


w6 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Student")), Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Student") (Nominal "Person")), Exists TBot "a" TTop]

w7 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Sub (Fun (Nominal "Student") (Nominal "Person")) (Fun (Var "a") (Var "a")), Exists TBot "a" TTop]

w8 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Sub (Fun (Nominal "Person") (Nominal "Student")) (Fun (Var "a") (Var "a")), Exists TBot "a" TTop]

w9 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Sub (Fun (Nominal "Person") (Nominal "Grad")) (Fun (Var "a") (Var "a")), Exists TBot "a" TTop]


{-
w7 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Student") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Person") (Nominal "Person")] [], Exists [] []]

w8 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Grad")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Student") (Nominal "Person")] [], Exists [] []]

main = do putStrLn (show $ solvable nomEnv w1)
          putStrLn "\n"  
          putStrLn (show $ solvable nomEnv w2)
          putStrLn "\n"
          putStrLn (show $ solvable nomEnv w3)
          putStrLn "\n"
          putStrLn (show $ solvable nomEnv w4)
          putStrLn "\n"
          putStrLn (show $ solvable nomEnv w5)
          putStrLn "\n"
          putStrLn (show $ solvable nomEnv w6)
          putStrLn "\n"
          putStrLn (show $ solvable nomEnv w7)
          putStrLn "\n"
          putStrLn (show $ solvable nomEnv w8)
-}