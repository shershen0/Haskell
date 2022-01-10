{-# LANGUAGE FlexibleContexts #-}
import Control.Monad.Except
import Data.List 

type Symb = String 
infixl 2 :@
infix 1 `alphaEq`
infix 1 `betaEq`

data Expr = Var Symb         -- var 
          | Expr :@ Expr     -- application
          | Lam Symb Expr    -- abstraction
          deriving (Eq, Read, Show)

freeVars :: Expr -> [Symb]  
freeVars (Var x)   = [x]
freeVars (m :@ n)  = freeVars m `union` freeVars n
freeVars (Lam name body) = freeVars body \\ [name]
    

subst :: Symb -> Expr -> Expr -> Expr 
subst n m (Var v) | v == n = m
                  | otherwise = (Var v)
subst n m (x :@ y) = (subst n m x) :@ (subst n m y)
subst n m (Lam name body) | name == n = Lam name body
                          | elem name (freeVars m) = subst n m (Lam nameN bodyN)
                          | otherwise = Lam name $ subst n m body 
    where nameN = name ++ "'"
          bodyN = subst name (Var nameN) body



alphaEq :: Expr -> Expr -> Bool
alphaEq (Var x) (Var y) | x == y = True 
                        | otherwise = False
alphaEq fst@(lx :@ rx) snd@(ly :@ ry) 
    | alphaEq lx ly = alphaEq rx ry 
    | otherwise = False

alphaEq (Lam nameF bodyF) (Lam nameS bodyS) 
    | nameF == nameS = alphaEq bodyF bodyS
    | (nameF `notElem` freeVars bodyS) && alphaEq (subst nameS (Var nameF) bodyS) bodyF = True 
    | otherwise = False
alphaEq _ _ = False


reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var x) = Nothing 
reduceOnce ((Lam name body) :@ arg) = Just $ subst name arg body

reduceOnce (x :@ y) = case reduceOnce x of 
    Just x' -> Just $ x' :@ y
    Nothing -> case reduceOnce y of 
        Just y' -> Just $ x :@ y'
        Nothing -> Nothing

reduceOnce (Lam name body) = case reduceOnce body of 
    Just x' -> Just $ Lam name x'
    Nothing -> Nothing 

nf :: Expr -> Expr 
nf expr = case reduceOnce expr of 
    Just x -> nf x
    Nothing -> expr


betaEq :: Expr -> Expr -> Bool 
betaEq expr1 expr2 = alphaEq (nf expr1) (nf expr2) 

