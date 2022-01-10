{-# LANGUAGE FlexibleContexts #-}
import Control.Monad.Except
import Data.List 
import Data.List (union,group) -- нужно для проверки, не убирайте!
import Control.Monad.Except
import Control.Monad.State


infixl 4 :@
infixr 3 :->

type Symb = String 

-- Терм
data Expr = Var Symb 
          | Expr :@ Expr
          | Lam Symb Expr
   deriving (Eq,Show)

-- Тип
data Type = TVar Symb 
          | Type :-> Type
   deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
   deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
    deriving (Eq,Show)

freeVars :: Expr -> [Symb]  
freeVars (Var x)   = [x]
freeVars (m :@ n)  = freeVars m `union` freeVars n
freeVars (Lam name body) = freeVars body \\ [name]


freeTVars :: Type -> [Symb] 
freeTVars (TVar x)  = [x]
freeTVars (s :-> t) = freeTVars s `union` freeTVars t

extendEnv :: Env -> Symb -> Type -> Env 
extendEnv (Env env) name ttype  = case lookup name env of
    Just _ -> Env env
    Nothing -> Env $ (name, ttype) : env

freeTVarsEnv :: Env -> [Symb] 
freeTVarsEnv (Env env) = nub $ concatMap (\(_,t) -> freeTVars t) env

appEnv :: MonadError String m => Env -> Symb -> m Type
appEnv (Env xs) v = case lookup v xs of 
    Just ttype -> pure ttype 
    Nothing -> throwError $ "There is no variable " <> show v <> " in the enviroment."

appSubsTy :: SubsTy -> Type -> Type
appSubsTy (SubsTy sbs) (TVar v) = case lookup v sbs of 
    Just ttype -> ttype 
    Nothing -> TVar v        
appSubsTy sbs (s :-> t) = appSubsTy sbs s :-> appSubsTy sbs t 

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv sbs (Env env) = Env $ map (fmap $ appSubsTy sbs) env

instance Semigroup SubsTy where 
    (<>) = composeSubsTy
instance Monoid SubsTy where 
    mempty = SubsTy []

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy left@(SubsTy s1) right@(SubsTy s2) = let 
    carrier pairs = fst $ unzip pairs
    result = carrier s1 `union` carrier s2 
    in SubsTy $ map (\symb -> (symb, appSubsTy left $ appSubsTy right $ TVar symb)) result

unify :: MonadError String m => Type -> Type -> m SubsTy
unify (TVar v1)  (TVar v2)    = if v1 == v2 then return $ SubsTy []
                                else return $ SubsTy [(v1, TVar v2)]
unify (TVar v) t              = do
    let list = freeTVars t
    let f = find (==v) list
    case f of 
      Just _ -> throwError $ "Can't unify (" ++ show t ++ ") with (" ++ show v ++ ")!"
      Nothing -> return $ SubsTy [(v, t)]
unify arrow@(s1 :-> s2) (TVar v)  = unify (TVar v) arrow
unify (s1 :-> s2) (t1 :-> t2)     = do
    u2 <- unify s2 t2
    let first =  appSubsTy u2 s1 
    let second = appSubsTy u2 t1
    smth <- unify first second
    return $  composeSubsTy smth u2 

getFreshTVar :: MonadState Integer m => m Type 
getFreshTVar = do
    n <- get 
    put $ n + 1
    return $ TVar $ "t_" ++ show n      

equations :: MonadError String m => Env -> Expr -> Type -> m [(Type,Type)]
equations env term t = evalStateT (equations'' env term t) 1

equations'' :: MonadError String m => Env -> Expr -> Type -> StateT Integer m [(Type,Type)]
equations'' env (Var x) t = do
    t' <- appEnv env x 
    return [(t, t')]
equations'' env (m :@ n) t = do
    alpha <- getFreshTVar
    eqs1 <- equations'' env m (alpha :-> t)
    eqs <- equations'' env n alpha
    return $ eqs1 `union` eqs
equations'' (Env env) (Lam v m) t = do
    alpha <- getFreshTVar
    betha <- getFreshTVar
    eqs1 <- equations'' (Env $ env `union` [(v, alpha)]) m betha
    let eqs2 = [(alpha :-> betha, t)]
    return $ eqs1 `union` eqs2


-- system of equasions into one 
flattenEqs :: [(Type, Type)] -> (Type, Type)
flattenEqs [(a,b)] = (a, b)
flattenEqs ((a,b):xs) = (a :-> x, b :-> y)
    where (x, y) = flattenEqs xs


makeList :: MonadState Integer m => Int -> m [Type]
makeList n | n == 0 = return []
           | otherwise  = do 
    ll <- makeList $ n-1
    v <- getFreshTVar
    return $ v : ll 

--main pair
principlePair :: MonadError String m =>  Expr -> m (Env,Type)
principlePair expr = evalStateT (principlePair'' expr) 1

principlePair'' :: (MonadError String m, MonadState Integer m) => Expr -> m (Env, Type)
principlePair'' expr = do 
    let list   = freeVars expr
    vars <- makeList $ length list
    let pairs  = zip list vars
    let var = TVar "firsty"
    eq <- equations (Env pairs) expr var
    let (f, s) = flattenEqs eq
    uni <- unify f s  -- or throws an exception
    return (appSubsEnv uni (Env pairs), appSubsTy uni var)

