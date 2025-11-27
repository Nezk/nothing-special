{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Typechecker where

import Control.Monad.Except
import Control.Monad.Writer.Strict
import Control.Monad.Reader

import Syntax
import Eval
import Pretty

-- TC Monad -------------------------------------------------------------------

data Ctx = Ctx 
    { ctxGEnv  :: GEnv,
      ctxGTys  :: GTys,
      ctxEnv   :: Env,
      ctxTys   :: Env,
      ctxNames :: LNames,
      ctxLv    :: Lv } 

-- todo: think of better name? It's not log in a sense of debug log, but place where holes information is stored
type Log = [String]

newtype TC a 
    = TC { unTC :: ReaderT Ctx (ExceptT String (Writer Log)) a }
    deriving (Functor, Applicative, Monad, MonadError String, MonadWriter Log, MonadReader Ctx)

runTC :: Ctx -> TC a -> (Either String a, Log)
runTC ctx = runWriter . runExceptT . flip runReaderT ctx . unTC

emptyCtx :: GEnv -> GTys -> Ctx
emptyCtx ge gt = Ctx ge gt [] [] [] 0

withBind :: LName -> Val -> TC a -> TC a
withBind name ty = local \c -> c 
    { ctxEnv   = fresh (ctxLv c) : ctxEnv c,
      ctxTys   = ty              : ctxTys c,
      ctxNames = name            : ctxNames c,
      ctxLv    = ctxLv c + 1 
    }

withDef :: LName -> Val -> Val -> TC a -> TC a
withDef name val ty = local \c -> c
    { ctxEnv   = val  : ctxEnv c,
      ctxTys   = ty   : ctxTys c,
      ctxNames = name : ctxNames c,
      ctxLv    = ctxLv c + 1
    }

inCtx :: (GEnv -> Env -> a) -> TC a
inCtx f = do
    ge  <- asks ctxGEnv
    env <- asks ctxEnv
    return $ f ge env

ppV :: Val -> TC String
ppV v = do
    ge    <- asks ctxGEnv
    l     <- asks ctxLv
    names <- asks ctxNames
    return $ pp names (rbV ge l v)

-- Conversion -----------------------------------------------------------------

convV :: Val -> Val -> TC ()
convV u v = do 
    ge <- asks ctxGEnv
    case (u, v) of
        (VU i,         VU j)         | i == j -> return ()        
        (VPi _ a b,    VPi _ a' b')           -> convV a a' >> convF (app ge b) (app ge b')
        (VSigma _ a b, VSigma _ a' b')        -> convV a a' >> convF (app ge b) (app ge b')
        (VPair a b,    VPair a' b')           -> convV a a' >> convV b b'  
        (VPair _ _,    _)                     -> convV (vfst u) (vfst v) >> convV (vsnd u) (vsnd v)
        (_,            VPair _ _)             -> convV (vfst u) (vfst v) >> convV (vsnd u) (vsnd v)
        (VNat,         VNat)                  -> return ()
        (VZero,        VZero)                 -> return ()
        (VSucc n,      VSucc n')              -> convV n n'
        (VEql a x y,   VEql a' x' y')         -> convV a a' >> convV x x' >> convV y y'
        (VRefl,        VRefl)                 -> return ()
        (VNeut n,      VNeut n')              -> convN n n'      
        (VLam _ cl,    VLam _ cl')            -> convF (app  ge cl) (app  ge cl')
        (VLam _ cl,    f)                     -> convF (app  ge cl) (vapp ge f)
        (f,            VLam _ cl)             -> convF (vapp ge f)  (app  ge cl)        
        _                                   -> do { pu <- ppV u; pv <- ppV v; throwError $ "Mismatch: " ++ pu ++ " /= " ++ pv }
  where convF :: (Val -> Val) -> (Val -> Val) -> TC ()
        convF f f' = do
            l <- asks ctxLv
            let fr = fresh l
            local (\c -> c { ctxLv = l + 1 }) $ convV (f fr) (f' fr)

convN :: Neutral Lv Val -> Neutral Lv Val -> TC ()
convN ne ne' = case (ne, ne') of
    (Head h,  Head h')   -> convH h h'
    (App f x, App f' x') -> convN f f' >> convG x x'
    _                    -> throwError $ "Spine mismatch: " ++ show ne ++ " /= " ++ show ne' -- TODO: rb/pp in error messages
    where convH h h' = case (h, h') of
            (NVar i,            NVar i')    | i == i' -> return ()
            (NHole n,           NHole n')   | n == n' -> return ()
            (NFst n,            NFst n')              -> convN n n'
            (NSnd n,            NSnd n')              -> convN n n'
            (NInd k p z s n,    NInd k' p' z' s' n')  | k == k' ->
                convV p p' >> convV z z' >> 
                convV s s' >> convN n n'
            (NJ a x k p q y e,  NJ a' x' k' p' q' y' e') | k == k' ->
                convV a a' >> convV x x' >> convV p p' >> 
                convV q q' >> convV y y' >> convN e e'
            (NContra n,         NContra n')           -> convN n n'
            _                                         -> throwError $ "Neutral head mismatch: " ++ show h ++ " " ++ show h'

convG :: Glob Val -> Glob Val -> TC ()
convG g g' = do
    ge <- asks ctxGEnv
    case (g, g') of
        (Glob n,  Glob n') | n == n' -> return ()
        (Glob n,  Glob n')           -> convV (ge !:? n) (ge !:? n')
        (Glob n,  Locl v)            -> convV (ge !:? n) v
        (Locl v,  Glob n)            -> convV v          (ge !:? n)
        (Locl v,  Locl v')           -> convV v          v'

-- Type Checking --------------------------------------------------------------

checkG :: Glob CExp -> Val -> TC ()
checkG g ty = elimGlob (\n -> asks ((!:? n) . ctxGTys) >>= flip convV ty) (`checkC` ty) g

inferS :: Spine (Glob Ix) (Glob CExp) -> TC Val
inferS = \case
    Head h -> elimGlob (\n -> asks ((!:? n) . ctxGTys)) (\i -> asks ((!! unIx i) . ctxTys)) h
    App f x -> do
        (dom, cl) <- inferS f >>= asPi
        checkG x dom
        vx <- elimGlob (\n -> inCtx \ge _ -> ge !:? n) (\e -> inCtx \ge env -> evalC ge env e) x
        inCtx \ge _ -> app ge cl vx

reportHole :: HName -> Val -> TC ()
reportHole n ty = do
    ge    <- asks ctxGEnv
    tys   <- asks ctxTys
    lv    <- asks ctxLv
    names <- asks ctxNames
    
    let normGoal      = rbV ge lv ty
    let ppEntry ty' i = unLName (names !! i) ++ " : " ++ pp names ty'
    let ctxEntries    = zipWith ppEntry (map (rbV ge lv) tys) [0..]
    
    tell ["\nHole: ?" ++ unHName n ++ "\n\nContext:\n\n" 
          ++ unlines (map ("  " ++) (reverse ctxEntries)) 
          ++ "\nGoal: " ++ pp names normGoal ++ "\n"]

isType :: IExp -> String -> TC Ul
isType e msg = inferI e >>= \case { VU l -> return l; _ -> throwError msg }

asPi :: Val -> TC (Val, Cl)
asPi = \case { VPi _ d c -> return (d, c); v -> throwError $ "Expected function type, got: " ++ show v }

inferI :: IExp -> TC Val
inferI expr = do
    case expr of
        U i -> return (VU (i + 1))
        
        Pi x a b -> do
            l  <- isType a "Pi dom"
            va <- inCtx $ \ge env -> evalI ge env a
            l' <- withBind x va $ isType b "Pi cod"
            return (VU (max l l')) 
            
        LetI x e ty body -> do
            _   <- isType ty "Let annot"
            vTy <- inCtx $ \ge env -> evalI ge env ty
            checkC e vTy
            v   <- inCtx $ \ge env -> evalC ge env e
            withDef x v vTy $ inferI body
            
        Spine s -> inferS s
        
        Sigma x a b -> do
            l1 <- isType a "Sigma fst"
            va <- inCtx $ \ge env -> evalI ge env a
            l2 <- withBind x va $ isType b "Sigma snd"
            return (VU (max l1 l2))
        Fst e      -> 
            inferI e >>= \case { VSigma _ a _ -> return a; _ -> throwError "Fst on non-sigma" }
        Snd e      -> 
            inferI e >>= \case
                VSigma _ _ cl -> do
                    ve <- inCtx $ \ge env -> evalI ge env e
                    inCtx       $ \ge _   -> app ge cl (vfst ve)
                _           -> throwError "Snd on non-sigma"
                
        Nat           -> return (VU 0)
        Zero          -> return VNat
        Succ n        -> checkC n VNat >> return VNat
        Ind l p z s n -> do
            vp  <- inCtx $ \ge env -> evalC ge env p

            _ <- inCtx $ \_ env -> checkC p (VPi "_" VNat (Cl env (Inf (U l)))) 
            
            zTy <- inCtx $ \ge _ -> vapp ge vp VZero
            checkC z zTy

            -- Oh god…
            
            let ix  k = Head (Locl (Ix k))
            let var k = Inf (Spine (ix k))
            
            -- Domain: P n
            -- Context: [n : Nat, P : Nat -> U l, ...] 
            -- Indices:  0        1         
            let dom = Spine (App (ix 1) (Locl (var 0)))
            
            -- Codomain: P (Succ n)
            -- Context: [hyp : P n, n : Nat, P : Nat -> U l, ...]
            -- Indices:  0          1        2
            let cod = Spine (App (ix 2) (Locl (Inf (Succ (var 1)))))
            
            let body = Inf (Pi "_" dom cod)

            --                                        Closure with motive in env
            _ <- inCtx $ \_ env -> let sTy = VPi "_" VNat (Cl (vp : env) body) in checkC s sTy
            
            checkC n VNat            
            vn <- inCtx $ \ge env -> evalC ge env n

            -- Result type is p n
            inCtx $ \ge _ -> vapp ge vp vn
        Eql a x y       -> do
            l  <- isType a "Eql type"
            va <- inCtx $ \ge env -> evalI ge env a
            checkC x va >> checkC y va >> return (VU l)
        J a x l p q y e -> do
            _  <- isType a "J: A not a type"
            va <- inCtx $ \ge env -> evalI ge env a
            
            checkC x va
            vx <- inCtx $ \ge env -> evalC ge env x
            
            let var k = Spine (Head (Locl (Ix k)))

            -- Eql A x y
            -- Context: [y : A,  x : A, A : U k, ...]
            -- indices: 0       1       2
            let eqTy = Eql (var 2) (Inf (var 1)) (Inf (var 0))

            -- Eql A x y -> U l
            let body = Inf (Pi "_" eqTy (U l))

                                                 -- A : U k, x : A |- (y : A) -> Eql A x y -> U l
            _ <- inCtx $ \_ env -> let motiveTy = VPi "_" va (Cl (vx : va : env) body) in checkC p motiveTy
            vp <- inCtx $ \ge env -> evalC ge env p

            qTy <- inCtx $ \ge _ -> vapp ge (vapp ge vp vx) VRefl
            checkC q qTy
            
            checkC y va
            vy <- inCtx $ \ge env -> evalC ge env y
            
            checkC e (VEql va vx vy)
            
            v <- inCtx $ \ge env -> evalC ge env e
            -- Return type is p y e
            inCtx $ \ge _ -> vapp ge (vapp ge vp vy) v

isHole :: Neutral i e -> Bool
isHole = \case
    (Head (NHole _)) -> True
    (App s _)        -> isHole s
    _                -> False

checkC :: CExp -> Val -> TC ()
checkC expr ty = case (expr, ty) of
    (Hole n, ty') -> reportHole n ty'
        
    (_, VNeut s) | isHole s -> return ()

    (Lam x body, VPi _ dom cl) -> do
        l <- asks ctxLv
        withBind x dom $ do
            bodyTy <- inCtx $ \ge _ -> app ge cl (fresh l)
            checkC body bodyTy
    
    (Inf i, _) -> inferI i >>= convV ty
    
    (LetC x e ty' b, _) -> do
        _    <- isType ty' "Let annot"
        vty' <- inCtx $ \ge env -> evalI ge env ty'
        checkC e vty'
        ve <- inCtx $ \ge env -> evalC ge env e
        withDef x ve vty' $ checkC b ty
        
    (Pair a b, VSigma _ dom cl) -> do
        checkC a dom
        va  <- inCtx $ \ge env -> evalC ge env a
        bTy <- inCtx $ \ge _ -> app ge cl va
        checkC b bTy
        
    (Refl, VEql _ x y) -> convV x y 

    (Contra c, _) -> checkC c (VEql VNat VZero (VSucc VZero))
    
    _ -> do
        pTy <- ppV ty
        throwError $ "Check mismatch: " ++ show expr ++ " vs " ++ pTy