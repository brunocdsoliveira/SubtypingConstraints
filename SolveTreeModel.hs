import Debug.Trace
import Control.Applicative

data Typ = TInt | Fun Typ Typ | Var Int | Nominal String deriving (Eq)

data Work = Exists [Typ] [Typ] | Sub Typ Typ

type WorkList = [Work]

type NominalEnv = [(String, Maybe String)]

instance Show Typ where
   show TInt          = "I"
   show (Fun a b)     = "(" ++ show a ++ ") -> " ++ show b
   show (Var i)       = "^" ++ show i
   show (Nominal s)   = s

showWork (Sub t1 t2)       _  = show t1 ++ " <: " ++ show t2
showWork (Exists ts1 ts2)  i  = show ts1 ++ " <: ^" ++ show i ++ " <: " ++ show ts2

instance {-# OVERLAPPING #-} Show WorkList where
   show []      = "."
   show [x]     = showWork x 0
   show (x:xs)  = show xs ++ ", " ++ showWork x (length xs)

subst :: Int -> Typ -> Bool -> WorkList -> WorkList
subst i t b o@(Sub t1 t2 : ws)       =  Sub t1 t2 : subst i t b ws  
subst i t b (Exists ts1 ts2 : ws)
   | i == length ws = if b then Exists ts1 (t:ts2) : ws else Exists (t:ts1) ts2 : ws
   | otherwise      = Exists ts1 ts2 : subst i t b ws   -- not fully correct as I ignore dependencies (but we know how to deal with this)

-- For the 3 definitions below, I assume that the two nominal types are different

subN :: String -> String -> NominalEnv -> Bool
subN n1 n2 []             = False
subN n1 n2 ((n3,Nothing):es)
   | n1 /= n3 && n2 /= n3 = subN n1 n2 es
   | otherwise            = False
subN n1 n2 ((n3,Just n4):es)
   | n1 == n3 && n2 == n4 = True
   | otherwise            = subN (if n1 == n3 then n4 else n1) n2 es

glb :: String -> String -> NominalEnv -> Maybe Typ
glb n1 n2 [] = Nothing
glb n1 n2 ((n3,Nothing):es)
   | n1 /= n3 && n2 /= n3 = glb n1 n2 es
   | otherwise            = Nothing  
glb n1 n2 ((n3,Just n4):es)
   | (n1 == n3 && n2 == n4) || (n1 == n4 && n2 == n3) = Just (Nominal n4)
   | n1 == n3                                         = glb n4 n2 es
   | n2 == n3                                         = glb n1 n4 es
   | otherwise                                        = glb n1 n2 es

lub' :: String -> String -> NominalEnv -> Maybe Typ
lub' n1 n2 [] = Nothing
lub' n1 n2 ((n3,Nothing):es) = lub' n1 n2 es 
lub' n1 n2 ((n3,Just n4):es)
   | (n1 == n3 && n2 == n4) || (n1 == n4 && n2 == n3) = Just (Nominal n3)
   | n1 == n4                                         = lub' n3 n2 es <|> lub' n1 n2 es
   | n2 == n4                                         = lub' n1 n3 es <|> lub' n1 n2 es 
   | otherwise                                        = lub' n1 n2 es 

lub :: String -> String -> NominalEnv -> Maybe Typ
lub n1 n2 e = lub' n1 n2 (reverse e)

-- Can be optimized to avoid non-branching supertypes
{-
candidates :: String -> NominalEnv -> [Typ] 
candidates n [] = []
candidates n ((n', m) : es)
   | n == n'    = Nominal n : case m of {Nothing -> []; Just n'' -> candidates n'' es}
   | otherwise  = candidates n es
-}

super :: String -> NominalEnv -> Maybe Typ
super n []      = Nothing
super n ((n',m) : es)
   | n == n'    = fmap Nominal m
   | otherwise  = super n es

solvable :: NominalEnv -> WorkList -> Bool
solvable _ []                                      = True
-- Subtyping
solvable e o@(Sub TInt TInt : ws)                  = trace (show o) $ solvable e ws
solvable e o@(Sub (Fun t1 t2) (Fun t3 t4) : ws)    = trace (show o) $ solvable e (Sub t3 t1 : Sub t2 t4 : ws)
solvable e o@(Sub (Var i) t1 : ws)                 = trace (show o) $ solvable e (subst i t1 True ws)
solvable e o@(Sub t1 (Var i) : ws)                 = trace (show o) $ solvable e (subst i t1 False ws)
solvable e o@(Sub (Nominal n1) (Nominal n2) : ws)
   | n1 == n2 || subN n1 n2 e = trace (show o) $ solvable e ws
   | otherwise                = False
-- Existentials
-- Processing stuff on the left
solvable e o@(Exists (Nominal n1:Nominal n2:ts1) ts2 : ws) 
   | n1 == n2              = trace (show o) $ solvable e (Exists (Nominal n1:ts1) ts2 : ws)
   | Just t <- glb n1 n2 e = trace (show o) $ solvable e (Exists (t:ts1) ts2 : ws)
   | otherwise             = False
solvable e o@(Exists (Var i : Nominal n : ts1) ts2 : ws) =  -- A brute force solution to the incompleteness problem
   trace (show o) (solvable e (subst i (Nominal n) True ws)) ||
   trace "Backtrack: " (solvable e (subst i (Nominal n) False ws)) ||
   case super n e of
      Nothing -> False
      (Just t) -> trace "Backtrack: " $ solvable e (Exists (Var i : t : ts1) ts2 : ws)
-- Symmetric case to the previous case is missing, so still incomplete for that 
solvable e o@(Exists (t1:t2:ts1) ts2 : ws)         = trace (show o) $
   solvable e (Sub t1 t2 : Exists (t2:ts1) ts2 : ws) || (trace "Backtrack: " $ solvable e (Sub t2 t1 : Exists (t1:ts1) ts2 : ws))
-- Processing stuff on the right
solvable e o@(Exists ts1 (Nominal n1:Nominal n2:ts2) : ws) 
   | n1 == n2              = trace (show o) $ solvable e (Exists ts1 ((Nominal n1):ts2) : ws)
   | Just t <- lub n1 n2 e = trace (show o) $ solvable e (Exists ts1 (t:ts2) : ws)
   | otherwise             = False
solvable e o@(Exists ts1 (t1:t2:ts2) : ws)         = trace (show o) $
   solvable e (Sub t1 t2 : Exists ts1 (t1:ts2) : ws) ||  (trace "Backtrack: " $ solvable e (Sub t2 t1 : Exists ts1 (t2:ts2) : ws))
-- After everything has been processed
solvable e o@(Exists [t1] [t2] : ws)               = trace (show o) $ solvable e (Sub t1 t2 : ws) 
solvable e o@(Exists _ _ : ws)                     = trace (show o) $ solvable e ws
solvable e o                                       = trace (show o) $ False

w1 = [Sub TInt TInt, Exists [] []]

w2 = [Sub (Var 0) TInt, Exists [] []]

w3 = [Sub (Var 0) (Fun TInt TInt), Sub (Var 0) TInt, Exists [] []]

w4 = [Exists [Fun (Var 0) (Var 0), Fun (Fun TInt TInt) (Fun TInt TInt)] [], Exists [Fun (Var 0) (Var 0),Fun TInt TInt] [], Exists [] []]

nomEnv = [("Grad", Just "Student"),("Employee", Just "Person"), ("Student", Just "Person"), ("Person", Nothing)]

w5 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Person") (Nominal "Person")] [], Exists [] []]

w6 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Student") (Nominal "Person")] [], Exists [] []]

w7 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Student") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Person") (Nominal "Person")] [], Exists [] []]

w8 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Person") (Nominal "Employee")] [], Exists [] []]

w9 = [Exists [Var 0, (Nominal "Student")] [], Exists [Var 0,(Nominal "Employee")] [], Exists [] []]

w10 = [Exists [Var 0,(Nominal "Employee")] [], Exists [Nominal "Student"] [Nominal "Student"]]

w11 = [Exists [Var 0,(Nominal "Person")] [], Exists [Nominal "Student"] [Nominal "Student"]]

w12 = [Exists [Nominal "Employee",(Nominal "Student")] []]

w13 = [Exists [] [Var 0, (Nominal "Grad")], Exists [] [Var 0,(Nominal "Person")], Exists [] []]

w14 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Grad")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Student") (Nominal "Person")] [], Exists [] []]

w15 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Grad")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Student") (Nominal "Employee")] [], Exists [] []]

w16 = [Exists [Var 0,(Nominal "Employee")] [], Exists [] [Nominal "Student"]]

w17 = [Exists [Var 0,(Nominal "Employee")] [], Exists [Nominal "Student"] []]

w18 = [Exists [Var 0,(Nominal "Employee")] [], Exists [] []]

-- forall a. Employee -> a -> a <: (forall b. b -> a )

{-

In S1, when you talk about recursive types currently in CP, perhaps you wish 
cite Yaoda's work, saying that there has been some work already on modelling
classic iso-recursive types. Maybe in:

The current iso-recursive type systems \cite{yaoda} ...


Now, instead of allowing --> Instead of allowing    (drop "Now")

modify the codes --> modify the code

the finally tagless pattern --> finally tagless encodings 
Also, besides [5], the actual first paper that talked about 
this kind of encodings being extensible was:

@incollection{emgm,
  title = "Extensible and Modular Generics for the Masses",
  author = "Bruno C. d. S. Oliveira, Ralf Hinze and Andres Loeh",
  year = "2007",
  booktitle = "Trends in Functional Programming",
  editor = "Henrik Nilsson",
  note = "Best student paper award",
}

So, perhaps you can cite [5] together with the above.

-}