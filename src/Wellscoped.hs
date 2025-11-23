{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

module Wellscoped where

import Syntax

import Control.Monad.Reader
import Control.Applicative ((<|>))
import Control.Monad       (guard)

import Data.List (elemIndex)

-- Raw syntax -----------------------------------------------------------------

data Raw
    = RVar String
    | RU Int
    | RNat 
    | RZero 
    | RSucc Raw
    | RPi String Raw Raw        
    | RFun Raw Raw              
    | RSigma String Raw Raw     
    | RTimes Raw Raw            
    | RLet String Raw Raw Raw   
    | RLam String Raw           
    | RPair Raw Raw             
    | RFst Raw                  
    | RSnd Raw                  
    | RApp Raw Raw              
    | REql Raw Raw Raw          
    | RRefl
    | RContra Raw
    | RInd Int Raw Raw Raw Raw      
    | RJ Raw Raw Int Raw Raw Raw Raw
    | RHole String              
    deriving Show

-- Wellscopdness checking -----------------------------------------------------

data ScopeCtx = ScopeCtx 
    { scLocals  :: [String],
      scGlobals :: GNames }

type SC = ReaderT ScopeCtx (Either String)

runSC :: GNames -> SC a -> Either String a
runSC globs m = runReaderT m (ScopeCtx { scLocals = [], scGlobals = globs })

wsI :: Raw -> SC IExp
wsI = \case
    RU i              -> pure $ U (Ul i)
    RNat              -> pure Nat
    RZero             -> pure Zero
    RPi x a b         -> Pi    (LName x) <$> wsI a <*> withVar x   (wsI b)
    RFun a b          -> Pi    "_"       <$> wsI a <*> withVar "_" (wsI b) 
    RSigma x a b      -> Sigma (LName x) <$> wsI a <*> withVar x   (wsI b) 
    RTimes a b        -> Sigma "_"       <$> wsI a <*> withVar "_" (wsI b) 
    RFst t            -> Fst <$> wsI t
    RSnd t            -> Snd <$> wsI t
    RInd l p z s n    -> Ind (Ul l) <$> wsC p <*> wsC z <*> wsC s <*> wsC n
    REql t a b        -> Eql <$> wsI t <*> wsC a <*> wsC b
    RJ a x l p q y e  -> J   <$> wsI a <*> wsC x <*> pure (Ul l) 
                             <*> wsC p <*> wsC q <*> wsC y <*> wsC e
    RLet x t v b      -> LetI (LName x) <$> wsC v <*> wsI t <*> withVar x (wsI b)
    RSucc t           -> Succ <$> wsC t
    t@(RApp _ _)      -> wsS t
    t@(RVar _)        -> wsS t
    RHole n           -> lift $ Left $ "Cannot infer type of hole ?" ++ n
    t                 -> lift $ Left $ "Cannot infer type: " ++ show t

wsC :: Raw -> SC CExp
wsC = \case
    RLam x b      -> Lam (LName x)  <$> withVar x (wsC b)
    RLet x t v b  -> LetC (LName x) <$> wsC v <*> wsI t <*> withVar x (wsC b)
    RPair a b     -> Pair   <$> wsC a <*> wsC b
    RContra t     -> Contra <$> wsC t
    RRefl         -> pure Refl
    RHole n       -> pure $ Hole $ HName n
    t             -> Inf <$> wsI t

wsS :: Raw -> SC IExp
wsS = fmap Spine . roll
  where roll = \case
            RApp f a -> App  <$> roll f <*> (Locl <$> wsC a)
            RVar x   -> Head <$> resolve x
            t        -> lift $ Left $ "Spine head must be variable, found: " ++ show t

resolve :: String -> SC (Glob Ix)
resolve n = asks lookupName >>= maybe reportError pure
  where reportError    = lift $ Left $ "Variable not in scope: " ++ n
        lookupName ctx = (Locl . Ix <$> elemIndex n (scLocals ctx)) <|> (Glob (GName n) <$ guard (GName n `elem` scGlobals ctx))

withVar :: String -> SC a -> SC a
withVar x = local $ \ctx -> ctx { scLocals = x : scLocals ctx }