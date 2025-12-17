{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Control.Monad          (foldM, void)
import Control.Monad.Except   (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)

import Data.Map.Strict (empty, insert)

import System.Environment (getArgs)

import Syntax
import Eval
import Pretty
import Readback
import Typechecker
import Wellscoped
import Parser

-- Monad ----------------------------------------------------------------------

data State = State 
    { stREnv  :: REnv,
      stRTys  :: RTys,
      stNames :: [RName] }

type Typechecker = ExceptT () IO

emptyState :: State
emptyState = State empty empty []

-- Execution ------------------------------------------------------------------

main :: IO ()
main = getArgs >>= \case
    []    -> putStrLn "Usage: ns <file_0> <file_1> ... <file_n>"
    files -> void $ runExceptT $ foldM processFile emptyState files

-- For debugging in REPL
checkDefs :: String -> IO ()
checkDefs = void . runExceptT . processBlock "GHCi" emptyState

processFile :: State -> FilePath -> Typechecker State
processFile state path = do
    liftIO $ putStrLn $ "--- Typecheckering " ++ path ++ " ---" -- I don't want to add the transformers library to cabal project. That's why it's liftIO.
    content <- liftIO $ readFile path 
    processBlock path state content

processBlock :: String -> State -> String -> Typechecker State
processBlock sourceName state input = do
    defs <- liftError ("Parse Error in " ++ sourceName) (parseRDefs input)
    foldM processDef state defs

processDef :: State -> (String, Raw, Raw) -> Typechecker State
processDef st (rName, rTy, rV) = do
    let name = RName rName
    
    (ty, e) <- liftError ("Scope Error [" ++ rName ++ "]") $ runSC (stNames st) ((,) <$> ws @Infer rTy <*> ws @Check rV)

    let ctx = Ctx 
            { ctxREnv  = stREnv st,
              ctxRTys  = stRTys st,
              ctxEnv   = [],
              ctxTys   = [],
              ctxNames = [],
              ctxLv    = 0 }

    _ <- runTypechecker ctx rName "Annotation" (tc ty)

    let vTy = eval (stREnv st) [] ty

    runTypechecker ctx rName "Body" (tc e vTy)

    let v = eval (stREnv st) [] e

    --let nTy = rb (stREnv st) 0 vTy
    let n   = rb (stREnv st) 0 v
    
    liftIO $ putStrLn $ rName ++ " : " ++ pp [] ty {-nTy-} ++ " ≔ " ++ pp [] n
    
    return $ st 
        { stREnv  = insert name v    (stREnv st),
          stRTys  = insert name vTy  (stRTys st),
          stNames = stNames st ++ [name] }

liftError :: String -> Either String a -> Typechecker a
liftError prefix = either (logError . ((prefix ++ ": ") ++)) return
    where logError = (>> throwError ()) . liftIO . putStrLn

runTypechecker :: Ctx -> String -> String -> TC a -> Typechecker a
runTypechecker ctx name stage action = do
    let (res, logs) = runTC ctx action
    liftIO $ mapM_ putStrLn logs
    liftError ("Type Error (" ++ stage ++ ") [" ++ name ++ "]") res
