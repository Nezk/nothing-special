{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}

module Main where

import Control.Monad          (foldM, void)
import Control.Monad.Except   (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)

import qualified Data.Map.Strict as M
import           System.Environment (getArgs)

import Syntax
import Eval
import Pretty
import Typechecker
import Wellscoped
import Parser

-- Monad ----------------------------------------------------------------------

data State = State 
    { env   :: GEnv,
      tys   :: GTys,
      names :: GNames }

type Check = ExceptT () IO

initState :: State
initState = State M.empty M.empty []

-- Execution ------------------------------------------------------------------

main :: IO ()
main = getArgs >>= \case
    []    -> putStrLn "Usage: ns <file_0> <file_1> ... <file_n>"
    files -> void $ runExceptT $ foldM processFile initState files

-- For debugging in REPL
checkDefs :: String -> IO ()
checkDefs = void . runExceptT . processBlock "GHCi" initState

processFile :: State -> FilePath -> Check State
processFile state path = do
    liftIO $ putStrLn $ "--- Checking " ++ path ++ " ---"
    content <- liftIO $ readFile path
    processBlock path state content

processBlock :: String -> State -> String -> Check State
processBlock sourceName state input = do
    defs <- liftError ("Parse Error in " ++ sourceName) (parseRDefs input)
    foldM processDef state defs

processDef :: State -> (String, Raw, Raw) -> Check State
processDef st (rName, rTy, rV) = do
    let name = GName rName
    
    -- Scope Check
    (ty, e) <- liftError ("Scope Error [" ++ rName ++ "]") $ runSC (names st) ((,) <$> wsI rTy <*> wsC rV)

    let ctx = emptyCtx (env st) (tys st)

    -- Check annotation
    _ <- runCheck ctx rName "Annotation" (inferI ty)

    -- Evaluate type
    let vTy = evalI (env st) [] ty

    -- Check body
    runCheck ctx rName "Body" (checkC e vTy)

    -- Evaluate body
    let v = evalC (env st) [] e

    -- Readback
    let nTy = rbV (env st) 0 vTy
    let n   = rbV (env st) 0 v
    
    liftIO $ putStrLn $ rName ++ " : " ++ pp [] nTy ++ " ≔ " ++ pp [] n
    
    -- State update
    return $ st 
        { env   = M.insert name v    (env st)
        , tys   = M.insert name vTy  (tys st)
        , names = names st ++ [name] 
        }

liftError :: String -> Either String a -> Check a
liftError prefix = either (logError . ((prefix ++ ": ") ++)) return
    where logError = (>> throwError ()) . liftIO . putStrLn

runCheck :: Ctx -> String -> String -> TC a -> Check a
runCheck ctx name stage action = do
    let (res, logs) = runTC ctx action
    liftIO $ mapM_ putStrLn logs
    liftError ("Type Error (" ++ stage ++ ") [" ++ name ++ "]") res