{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Wellscoped where

import Control.Monad.Reader
import Control.Applicative ((<|>))
import Control.Monad (guard)

import Data.List (elemIndex)

import Syntax
import Utils
import Pretty (ppRaw)

data ScopeCtx
  = ScopeCtx { scLocals  :: [String], -- come from arguments of Raw syntax
               scGlobals :: RNames }
    
type SC = ReaderT ScopeCtx (Either String)

runSC :: RNames -> SC a -> Either String a
runSC globs m = runReaderT m (ScopeCtx { scLocals = [], scGlobals = globs })

ws :: forall m. (HasMode m, Valid Syn m) => Raw -> SC (Sy m)
ws raw = case raw of
    RU     i       -> pure $ U (Ul i)
    RNat           -> pure Nat
    RZero          -> pure Zero
    RSucc    t     -> Succ <$> ws @Check t
    RPi    x a b   -> Pi  (LName x) <$> ws @Infer a <*> withVar x (ws @Infer b)
    RFun     a b   -> Pi  "_"       <$> ws @Infer a <*> withVar "_" (ws @Infer b)
    RSigma x a b   -> Sig (LName x) <$> ws @Infer a <*> withVar x (ws @Infer b)
    RTimes   a b   -> Sig "_"       <$> ws @Infer a <*> withVar "_" (ws @Infer b)
    REql   t a b   -> Eql           <$> ws @Infer t <*> ws @Check a <*> ws @Check b
    RLet   x t v b -> Let (LName x) <$> ws @Check v <*> ws @Infer t <*> withVar x (ws @m b)
    RVar   x       -> resolve x

    RApp f a -> withS f $ \s -> do
        arg  <- ws @Check a
        case view s of { VLocal -> pure $ Use $ App s arg; VGlobal -> pure $ Use $ App s arg; }
        
    RFst t -> withS t $ \s -> 
        pure $ Use (App (Head Fst) s)

    RSnd t -> withS t $ \s -> 
        pure $ Use (App (Head Snd) s)

    RInd l p z s n -> do
        cn <- ws @Check n; cp <- ws @Check p; cz <- ws @Check z; cs <- ws @Check s
        pure $ Use (App (Head (Ind (Ul l) cp cz cs)) cn)

    RJ a x l p q y e -> do
        ca <- ws @Infer a; cx <- ws @Check x; cp <- ws @Check p
        cq <- ws @Check q; cy <- ws @Check y; ce <- ws @Check e
        pure $ Use (App (Head (J ca cx (Ul l) cp cq cy)) ce)

    RContra t -> case mode @m of 
        SCheck -> withS t $ \s -> pure $ Use (App (Head Contra) s)
        _      -> wsErr

    RLam x b -> case mode @m of 
        SCheck -> Lam (LName x) <$> withVar x (ws @Check b)
        _      -> wsErr

    RPair a b -> case mode @m of 
        SCheck -> Pair <$> ws @Check a <*> ws @Check b
        _      -> wsErr

    RRefl -> case mode @m of 
        SCheck -> pure Refl
        _      -> wsErr

    RHole n -> case mode @m of 
        SCheck -> pure $ Use (Head (Hole (HName n)))
        _      -> wsErr
    
    where wsErr = lift . Left $ "Cannot infer expression: " ++ ppRaw raw
    
          withS :: Raw -> (forall l. Spine Syn Infer (Node l) Check -> SC a) -> SC a
          withS t k = ws @Infer t >>= \case
              Use s -> k s 
              _     -> lift $ Left "Expected a spine (variable, reference, or application), but got a canonical term."

          -- Left for locals, Right for globals
          lookupName name ctx = (Left <$> elemIndex name (scLocals ctx)) <|> (Right (RName name) <$ guard (RName name `elem` scGlobals ctx))
            
          resolve :: String -> SC (Sy m)
          resolve n = asks (lookupName n) >>= \case
              Nothing        -> lift $ Left $ "Var not in scope: " ++ n
              Just (Left i)  -> pure $ var (Ix i)
              Just (Right r) -> pure $ Use (Head (Ref r))
           
          withVar :: String -> SC a -> SC a
          withVar x = local \c -> c { scLocals = x : scLocals c }
