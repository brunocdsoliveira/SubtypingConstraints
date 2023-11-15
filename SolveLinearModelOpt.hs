import Debug.Trace
import Data.List
import Data.Char

data Typ = TTop | TBot | TInt | Fun Typ Typ | Var String | Nominal String deriving (Eq)

data Work = Exists Typ String Typ | Sub Typ Typ | LUB Typ Typ (Typ -> WorkList) | GLB Typ Typ (Typ -> WorkList)

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
showWork (GLB t1 t2 f)      = "GLB(" ++ show t1 ++ ", " ++ show t2 ++ ")"
showWork (LUB t1 t2 f)      = "LUB(" ++ show t1 ++ ", " ++ show t2 ++ ")"

instance {-# OVERLAPPING #-} Show WorkList where
   show []      = "."
   show [x]     = showWork x
   show (x:xs)  = show xs ++ ", " ++ showWork x

subst :: String -> Typ -> Bool -> WorkList -> WorkList -> WorkList
subst i t b o@(Sub t1 t2 : ws) ws'   = subst i t b ws (Sub t1 t2 : ws')  
subst i t b (Exists t1 s t2 : ws) ws'
   | i == s         = if b then GLB t t2 (\t2' -> reverse (Exists t1 s t2' : ws')) : ws else LUB t t1 (\t1' -> reverse (Exists t1' s t2 : ws')) : ws
   | otherwise      = subst i t b ws (Exists t1 s t2 : ws')   -- not fully correct as I ignore dependencies (but we know how to deal with this)
-- subst i t b o ws' = trace 

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

solvable :: NominalEnv -> WorkList -> Bool
solvable _ []                                    = True
-- Subtyping
solvable e o@(Sub a TTop : ws)                   = trace (show o) $ solvable e ws
solvable e o@(Sub TBot a : ws)                   = trace (show o) $ solvable e ws
solvable e o@(Sub TInt TInt : ws)                = trace (show o) $ solvable e ws 
solvable e o@(Sub (Fun t1 t2) (Fun t3 t4) : ws)  = trace (show o) $ solvable e (Sub t3 t1 : Sub t2 t4 : ws)
-- cases for non-mono are missing
solvable e o@(Sub (Var i) t1 : ws) | mono t1     = trace (show o) $ solvable e (subst i t1 True ws [])
solvable e o@(Sub t1 (Var i) : ws) | mono t1     = trace (show o) $ solvable e (subst i t1 False ws [])
solvable e o@(Sub (Nominal n1) (Nominal n2) : ws)
   | n1 == n2 || subN n1 n2 e = trace (show o) $ solvable e ws
   | otherwise                = trace (show o) $ False
-- LUB
solvable e o@(LUB TBot t k : ws)                = trace (show o) $ solvable e (k t ++ ws)
solvable e o@(LUB t TBot k : ws)                = trace (show o) $ solvable e (k t ++ ws)
solvable e o@(LUB TInt TInt k : ws)             = trace (show o) $ solvable e (k TInt ++ ws)
solvable e o@(LUB (Nominal n1) (Nominal n2) k : ws)  -- can be further optimized.
   | n1 == n2 || subN n1 n2 e = trace (show o) $ solvable e (k (Nominal n2) ++ ws)
   | subN n2 n1 e             = trace (show o) $ solvable e (k (Nominal n1) ++ ws)
   | otherwise                = trace (show o) $ False 
solvable e o@(LUB (Fun a b) (Fun c d) k : ws)    = trace (show o) $ solvable e (GLB a c (\t1 -> [LUB b d (\t2 -> k (Fun t1 t2))]) : ws)  
-- GLB
solvable e o@(GLB TTop t k : ws)                 = trace (show o) $ solvable e (k t ++ ws)
solvable e o@(GLB t TTop k : ws)                 = trace (show o) $ solvable e (k t ++ ws)
solvable e o@(GLB TInt TInt k : ws)              = trace (show o) $ solvable e (k TInt ++ ws)
solvable e o@(GLB (Nominal n1) (Nominal n2) k : ws)  -- can be further optimized.
   | n1 == n2 || subN n1 n2 e = trace (show o) $ solvable e (k (Nominal n1) ++ ws)
   | subN n2 n1 e             = trace (show o) $ solvable e (k (Nominal n2) ++ ws)
   | otherwise                = trace (show o) $ False 
solvable e o@(GLB (Fun a b) (Fun c d) k : ws)    = trace (show o) $ solvable e (LUB a c (\t1 -> [GLB b d (\t2 -> k (Fun t1 t2))]) : ws)
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