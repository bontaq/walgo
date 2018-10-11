module Main where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import qualified Text.PrettyPrint as PP

-- Start by defining the abstract syntax
data Exp = EVar String
         | ELit Lit
         | EApp Exp Exp
         | EAbs String Exp
         | ELet String Exp Exp
         deriving (Eq, Ord)
data Lit = LInt Integer
         | LBool Bool
         deriving (Eq, Ord)
data Type = TVar String
          | TInt
          | TBool
          | TFun Type Type
          deriving (Eq, Ord, Show)
data Scheme = Scheme [String] Type

-- Rules for determinging free type (ftv) and Substitution (Subst)
class Types a where
  ftv   :: a -> Set.Set String
  apply :: Subst -> a -> a

instance Types Type where
  ftv (TVar n)     = Set.singleton n
  ftv TInt         = mempty
  ftv TBool        = mempty
  ftv (TFun t1 t2) = Set.union (ftv t1) (ftv t2)

  apply s (TVar n)     = case Map.lookup n s of
    Nothing -> TVar n
    Just t  -> t
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply s t            = t
instance Types Scheme where
  ftv (Scheme vars t)     = Set.difference (ftv t) (Set.fromList vars)
  apply s (Scheme vars t) = Scheme vars (apply (foldr Map.delete s vars) t)

-- helper
instance Types a => Types [a] where
  apply s = map (apply s)
  ftv l   = foldr Set.union mempty (map ftv l)

-- substitutions
type Subst = Map.Map String Type

nullSubst :: Subst
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = (Map.map (apply s1) s2) `Map.union` s1

-- Type environment and operations on it
newtype TypeEnv = TypeEnv (Map.Map String Scheme)

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (Map.elems env)
  apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

-- abstract a type over all type variables which are free in the type
-- but not free in the given type environment
generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where vars = Set.toList $ Set.difference (ftv t) (ftv env)

-- handling the generation of newly introduced type variables
data TIEnv = TIEnv {}
data TIState = TIState { tiSupply :: Int
                       , tiSubst  :: Subst }
type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a
-- neat, it could produce errors
runTI :: TI a -> IO (Either String a, TIState)
runTI t = do
  (res, st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState
  return (res, st)
  where
    initTIEnv = TIEnv {}
    initTIState = TIState { tiSupply = 0
                          , tiSubst  = mempty }

newTyVar :: String -> TI Type
newTyVar prefix = do
  s <- get
  put s { tiSupply = tiSupply s + 1 }
  return (TVar (prefix ++ show (tiSupply s)))

-- replace all bound type variables in a scheme with fresh type vars
instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\_ -> newTyVar "a") vars
  let s = Map.fromList (zip vars nvars)
  return $ apply s t

-- oh shit the unification function! (for types)
-- here he come
mgu :: Type -> Type -> TI Subst
mgu (TFun l r) (TFun l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  return (s1 `composeSubst` s2)
mgu (TVar u) t  = varBind u t
mgu t (TVar u)  = varBind u t
mgu TInt TInt   = return nullSubst
mgu TBool TBool = return nullSubst
mgu t1 t2       = throwError $ "types do not unify" -- todo

varBind :: String -> Type -> TI Subst
varBind u t | t == TVar u         = return nullSubst
            | u `Set.member` ftv t = throwError $ "occur check fails: "
              ++ u ++ " vs. " -- ++ show t
            | otherwise            = return (Map.singleton u t)

-- inference
-- for literals
tiLit :: TypeEnv -> Lit -> TI (Subst, Type)
tiLit _ (LInt _)  = return (nullSubst, TInt)
tiLit _ (LBool _) = return (nullSubst, TBool)

-- for expressions
ti :: TypeEnv -> Exp -> TI (Subst, Type)
ti (TypeEnv env) (EVar n) =
  case Map.lookup n env of
    Nothing    -> throwError $ "unbound variable: " ++ n
    Just sigma -> do
      t <- instantiate sigma
      return (nullSubst, t)
ti env (ELit l) = tiLit env l
ti env (EAbs n e) = do
  tv <- newTyVar "a"
  let TypeEnv env' = remove env n
      env''        = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
  (s1, t1) <- ti env'' e
  return (s1, TFun (apply s1 tv) t1)
ti env (EApp e1 e2) = do
  tv <- newTyVar "a"
  (s1, t1) <- ti env e1
  (s2, t2) <- ti (apply s1 env) e2
  s3 <- mgu (apply s2 t1) (TFun t2 tv)
  return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
ti env (ELet x e1 e2) = do
  (s1, t1) <- ti env e1
  let TypeEnv env' = remove env x
      t' = generalize (apply s1 env) t1
      env'' = TypeEnv (Map.insert x t' env')
  (s2, t2) <- ti (apply s1 env'') e2
  return (s1 `composeSubst` s2, t2)

-- finally, the main entry point
typeInference :: Map.Map String Scheme -> Exp -> TI Type
typeInference env e = do
  (s, t) <- ti (TypeEnv env) e
  return (apply s t)

test :: Exp -> IO ()
test e = do
  (res, _) <- runTI (typeInference Map.empty e)
  putStrLn . show $ res

main :: IO ()
main = do
  let e0 = ELet "id" (EAbs "x" (EVar "x")) (EVar "id")
  mapM_ test [e0]
  putStrLn "hello world"
