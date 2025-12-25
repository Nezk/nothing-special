{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Control.Monad          ((>=>))
import Control.Monad.Except   (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State    (StateT, execStateT, get, modify)

import Data.Foldable   (traverse_)
import Data.Functor    ((<&>))
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

type Holes  = [String]
type Output = [String]

data State = State
    { stREnv   :: REnv,
      stRTys   :: RTys,
      stNames  :: [RName],
      stReport :: Either Holes Output }

type Typechecker = StateT State (ExceptT () IO)

-- Execution ------------------------------------------------------------------

main :: IO ()
main = getArgs >>= \case
    []    -> putStrLn "Usage: ns <file_0> <file_1> ... <file_n>"
    files -> runExceptT (execStateT (traverse_ processFile files) emptySt) >>=
             either (const $ pure ())
                    (putStr . unlines . either id id . stReport)
    where emptySt = State empty empty [] (Right [])

processFile :: FilePath -> Typechecker ()
processFile path = do
    modify \st -> st { stReport = (++ ["--- Typechecking " ++ path ++ " ---"]) <$> stReport st }
    liftIO (readFile path) >>= processBlock path

processBlock :: String -> String -> Typechecker ()
processBlock src = orErr src . parseRDefs >=> traverse_ processDef

processDef :: (String, Raw, Maybe Raw) -> Typechecker ()
processDef (name, rty, def) = do
    vty <-                 typecheck name "Annotation" rty (ws @Infer)   tc
    v   <- traverse (\d -> typecheck name "Body"       d   (ws @Check) (`tc` vty)) def
    register name vty v

orErr :: String -> Either String a -> Typechecker a
orErr prefix = either ((>> throwError ()) . liftIO . putStrLn . ((prefix ++ ": ") ++)) pure

typecheck :: String -> String -> Raw -> (Raw -> SC (Sy m)) -> (Sy m -> TC a) -> Typechecker Vl
typecheck name stage raw scope check = do
    st <- get
    t  <- orErr ("Scope Error [" ++ name ++ "]") (runSC (stNames st) (scope raw))
    
    let ctx          =  Ctx (stREnv st) (stRTys st) [] [] [] 0
    let (res, holes) =  runTC ctx (check t)
    _                <- orErr ("Type Error (" ++ stage ++ ") [" ++ name ++ "]") res
    
    -- isn't evaluated if stReport st' is Left due to lazyness
    let newHoles = (("\n[" ++ name ++ "]\n") ++) <$> holes
    
    modify \st' -> st' { stReport = either (Left . (++ newHoles)) 
                                           (if null newHoles then Right else const (Left newHoles)) 
                                           (stReport st') }
    
    pure (eval (stREnv st) [] t)

register :: String -> Vl -> Maybe Vl -> Typechecker ()
register name vty body = 
    modify \st ->
        let rname = RName name
            renv  = stREnv st
            renv' = (maybe id (insert rname) body) renv
            rtys' = insert rname vty (stRTys st)
            ppv   = pp [] . rb renv 0            
            ppty  = ppv vty
            out   = maybe ("postulate: " ++ name ++ " : " ++ ppty)
                          (((               name ++ " : " ++ ppty ++ " ≔ ") ++) . ppv)
                          body
        in State { stREnv   = renv',
                   stRTys   = rtys',
                   stNames  = stNames  st ++ [rname],
                   stReport = stReport st <&> \outs -> outs ++ [out] }
