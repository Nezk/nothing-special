{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Typechecker where

import Control.Monad.Except
import Control.Monad.Writer.Strict
import Control.Monad.Reader
import Control.Monad               (join)

import GHC.TypeLits (TypeError, ErrorMessage(..))

import Data.Kind       (Constraint)
import Data.Map.Strict ((!))
import Data.Either     (isRight)

import Syntax
import Eval
import Readback (rb)
import Utils

import qualified Pretty as P

-- Context and Monad ----------------------------------------------------------

data Ctx =
  Ctx { ctxREnv :: REnv,
        ctxRTys :: RTys,

        ctxEnv :: Env,
        ctxTys :: Tys,

        ctxNames :: LNames,

        ctxLv :: Lv }

type Log = [String]

newtype TC a
    = TC { unTC :: ReaderT Ctx (ExceptT String (Writer Log)) a }
    deriving (Functor, Applicative, Monad, MonadError String, MonadWriter Log, MonadReader Ctx)

runTC :: Ctx -> TC a -> (Either String a, Log)
runTC ctx = runWriter . runExceptT . flip runReaderT ctx . unTC

withBind :: LName -> Vl -> TC a -> TC a
withBind name ty = local \c -> c
    { ctxEnv   = var c.ctxLv             : c.ctxEnv,
      ctxTys   = ty                      : c.ctxTys,
      ctxNames = P.fresh name c.ctxNames : c.ctxNames,
      ctxLv    = c.ctxLv + 1 }

withDef :: LName -> Vl -> Vl -> TC a -> TC a
withDef name val ty = local \c -> c
    { ctxEnv   = val                     : c.ctxEnv,
      ctxTys   = ty                      : c.ctxTys,
      ctxNames = P.fresh name c.ctxNames : c.ctxNames,
      ctxLv    = c.ctxLv + 1 }

mismatch :: String -> (LNames -> a -> String) -> a -> (LNames -> b -> String) -> b -> TC c
mismatch msg ppA a ppB b = asks ctxNames >>= \names -> throwError $ msg ++ ": " ++ ppA names a ++ " /= " ++ ppB names b

expected :: String -> (LNames -> a -> String) -> a -> TC b
expected e ppA a = asks ctxNames >>= \names -> throwError $ "Expected " ++ e ++ ", got: " ++ ppA names a

-- Unfolding ------------------------------------------------------------------

expand :: Spine Sem None Rigid Check -> (Vl -> TC a) -> TC a -> TC a
expand s f n = asks ctxREnv >>= \renv -> maybe n f (unfold renv s)

force :: Vl -> TC Vl
force = \case
  (Use s) -> expand s force (pure (Use s))
  v       -> pure v

-- Conversion Checking --------------------------------------------------------

conv :: Vl -> Vl -> TC ()
conv u v = case (u, v) of
    (U i,       U j) | i == j -> pure ()
    (Nat,       Nat)          -> pure ()
    (Zero,      Zero)         -> pure ()
    (Succ n,    Succ m)       -> conv n m
    (Pi  _ a b, Pi  _ a' b')  -> conv a a' >> convBind b b'
    (Sig _ a b, Sig _ a' b')  -> conv a a' >> convBind b b'
    (Pair  a b, Pair  a' b')  -> conv a a' >> conv b b'
    (Pair _ _,  _)            -> convProj u v
    (_,         Pair _ _)     -> convProj u v
    (Lam _ b,   Lam _ b')     -> convBind b b'
    (Lam _ b,   f)            -> convEta b f
    (f,         Lam _ b)      -> convEta b f
    (Eql a x y, Eql a' x' y') -> conv a a' >> conv x x' >> conv y y'
    (Refl,      Refl)         -> pure ()
    (Use s,     Use s')       -> convS s s'
    (Use s,     _)            -> tryUnfold s v
    (_,         Use s)        -> tryUnfold s u
    _                         -> mismatch "Mismatch" P.pp u P.pp v
  where convGen   f          f'           = asks ctxLv   >>= \l    -> local (\c -> c { ctxLv = l + 1 })    $  join (liftA2 conv (f (var l)) (f' (var l)))
        convProj  p          p'           = asks ctxREnv >>= \renv -> conv  (doFst renv p) (doFst renv p') >> conv (doSnd renv p) (doSnd renv p')
        convBind  (Cl env b) (Cl env' b') = convGen (\a -> asks \c -> eval c.ctxREnv (a : env) b) (\a -> asks \c -> eval c.ctxREnv (a : env') b')
        convEta   (Cl env b) f            = convGen (\a -> asks \c -> eval c.ctxREnv (a : env) b) (\a -> asks \c -> app  c.ctxREnv f a)
        tryUnfold s          x            = expand s (`conv` x) (mismatch "Mismatch" (P.ppS 0) s P.pp x)

convS :: Spine Sem None s arg -> Spine Sem None s' arg' -> TC ()
convS s s' = catchError match delta
  where match = case (s, s') of
          (Head h,   Head h')   -> convH h h'
          (App l r,  App l' r') -> convS l l' >> convArgs (view l) (view l') r r'
          _                     -> mismatch "Shape mismatch" (P.ppS 0) s (P.ppS 0) s'
        convArgs :: View s a -> View s' a' -> Choice Sem s a -> Choice Sem s' a' -> TC ()
        convArgs v v' a a' = case (v, v') of
          (VRigid,  VRigid)  -> conv  a a'
          (VStrict, VStrict) -> convS a a'
          (VFlex,   VFlex)   -> convS a a'
          _                  -> mismatch "View mismatch" (P.ppS 0) s (P.ppS 0) s'
        delta err = case (view s, view s') of -- both spines are rigid because of Use
          (VRigid, VRigid) -> expand s  (`conv` Use s') -- Trying to unfold the left  spine, applying conv if it succeeds
                            $ expand s' (conv  (Use s)) -- Trying to unfold the right spine
                            $ throwError err
          _                -> throwError err

convH :: Head Sem None s a -> Head Sem None s' a' -> TC ()
convH h h' = case (h, h') of
    (Var i,         Var j)               | i == j  -> pure ()
    (Hole n _,      Hole m _)            | n == m  -> pure ()
    (Ref n,         Ref m)               | n == m  -> pure ()
    (Fst,           Fst)                           -> pure ()
    (Snd,           Snd)                           -> pure ()
    (Contra,        Contra)                        -> pure ()
    (Ind k p z s,   Ind k' p' z' s')     | k == k' -> conv p p' >> conv z z' >> conv s s'
    (J a x k p q y, J a' x' k' p' q' y') | k == k' -> conv a a' >> conv x x' >> conv p p' >> conv q q' >> conv y y'
    _                                              -> mismatch "Head mismatch" P.ppH h P.ppH h' -- delta in convS already unfolds cases when convH fails

-- Typechecking ---------------------------------------------------------------

reportHole :: HName -> Maybe (Inf Syn) -> Vl -> TC ()
reportHole n t ty = ask >>= \ctx -> do
    let normGoal      = rb ctx.ctxREnv ctx.ctxLv ty
        ppEntry ty' i = unLName (ctx.ctxNames !! i) ++ " : " ++ P.pp ctx.ctxNames ty'
        normTys       = map (rb ctx.ctxREnv ctx.ctxLv) ctx.ctxTys
        ctxEntries    = zipWith ppEntry normTys [0..]

    extra <- maybe (pure "") reportAnn t -- TODO: something better than this?

    tell ["\nHole: ?" ++ unHName n ++ "\n\nContext:\n\n" ++ unlines (map ("  " ++) (reverse ctxEntries)) ++ extra ++
         "\nGoal: "  ++ P.pp ctx.ctxNames normGoal ++ "\n"]
  where reportAnn t' = catchError
          (do ty'     <- tc @Infer t'
              norm    <- force ty' >>= \v -> asks \c -> rb c.ctxREnv c.ctxLv v
              matches <- isRight <$> tryError (conv ty' ty) -- TODO: print the error instead of converting it to bool?
              names   <- asks ctxNames 
              pure $ "\nType: " ++ P.pp names norm ++ if matches then " [Matches Goal]" else " [Type Mismatch]")
          (pure . ("\nError: " ++))

isType :: Inf Syn -> TC Ul
isType e = do
    ty  <- tc e
    ty' <- force ty
    case ty' of
        U l -> pure l
        v   -> expected "Universe" P.pp v

asPi :: Vl -> TC (Vl, Cl)
asPi v = force v >>= \case
    Pi  _ d c -> pure (d, c)
    Use   s   -> expected "function (stuck)" (P.ppS 0) s
    v'        -> expected "function"          P.pp     v'

asSig :: Vl -> TC (Vl, Cl)
asSig v = force v >>= \case
    Sig _ d c -> pure (d, c)
    Use   s   -> expected "product (stuck)" (P.ppS 0) s
    v'        -> expected "product"          P.pp     v'

-- Ensures we don’t try to use a checking term in inference position
type family Flow (i :: Mode) (o :: Mode) :: Constraint where
    Flow Check Infer = TypeError (Text "Directionality Error: Cannot infer type for a term that requires checking mode.")
    Flow _     _     = ()

type family TcTy (m :: Mode) where
    TcTy Infer = TC Vl
    TcTy Check = Vl -> TC ()

class HasMode m => Typing m where
    yield :: Vl                                 -> TcTy m
    bind  :: TC (TcTy m)                        -> TcTy m
    scope :: (forall a. TC a -> TC a) -> TcTy m -> TcTy m

instance Typing Infer where
    yield   = pure
    bind    = join
    scope f = f

instance Typing Check where
    yield        = conv
    bind    m ty = m >>= \k -> k ty -- m :: TC (Vl -> TC ())
    scope f m ty = f (m ty)

inst :: forall m. Typing m => TC Vl -> TcTy m
inst op = bind @m (yield @m <$> op)

tc :: forall m. Typing m => Exp Syn m -> TcTy m
tc = \case
    Use s -> tcS @m s

    Lam x b -> \ty -> do
        (dom, Cl env body) <- asPi ty
        vBodyTy            <- asks \c -> eval c.ctxREnv (var c.ctxLv : env) body
        withBind x dom $ tc b vBodyTy

    Pair a b -> \ty -> do
        (dom, Cl env body) <- asSig ty
        tc a dom
        va      <- asks \c -> eval c.ctxREnv c.ctxEnv a
        vBodyTy <- asks \c -> eval c.ctxREnv (va : env) body
        tc b vBodyTy

    Refl -> \ty -> do
        ty' <- force ty
        case ty' of
            Eql _ x y -> conv x y
            _         -> expected "Eql type" P.pp ty'

    U i  -> yield @m $ U $ Ul $ unUl i + 1
    Nat  -> yield @m $ U 0
    Zero -> yield @m $ Nat

    Succ k -> inst @m $ do
        tc k Nat
        pure Nat

    Pi x a b -> inst @m $ do
        l  <- isType a
        va <- asks \c -> eval c.ctxREnv c.ctxEnv a
        l' <- withBind x va $ isType b
        pure $ U $ max l l'

    Sig x a b -> inst @m $ do
        l1 <- isType a
        va <- asks \c -> eval c.ctxREnv c.ctxEnv a
        l2 <- withBind x va $ isType b
        pure $ U $ max l1 l2

    Eql a x y -> inst @m $ do
        l <- isType a
        va <- asks \c -> eval c.ctxREnv c.ctxEnv a
        tc x va
        tc y va
        pure $ U l

    Let @m' x d b -> bind @m $ do
        (v, vty) <- case mode @m' of
            SInfer -> flip (,) <$> tc d         <*> asks (\c ->  eval c.ctxREnv c.ctxEnv d)
            SCheck -> let (e, t) = d in isType t >> asks (\c ->  eval c.ctxREnv c.ctxEnv t)
                      >>= \vty' -> tc e vty'     >> asks (\c -> (eval c.ctxREnv c.ctxEnv e, vty'))
        pure $ scope @m (withDef x v vty) (tc b)

tcS :: forall m m'. (Valid Syn m', Flow m' m, Typing m) => Spine Syn m' Rigid Check -> TcTy m
tcS = \case
    Head h    -> tcH @m h
    App s arg -> case view s of
        VRigid  -> tcApp @m (tcS @Infer) s arg
        VFlex   -> tcApp @m tcFlex       s arg
        VStrict -> case s of Head h -> tcAppStrict @m h arg

tcH :: forall m m'. (Valid Syn m', Flow m' m, Typing m) => Head Syn m' Rigid Check -> TcTy m
tcH = \case
    Var i     -> inst @m $ asks    \c -> c.ctxTys !! unIx i
    Ref r     -> inst @m $ ask >>= \c -> pure $ c.ctxRTys ! r
    Hole h t  -> case mode @m of SCheck -> reportHole h t

tcFlex :: Valid Syn m => Spine Syn m Flex Check -> TC Vl
tcFlex (Head h) = case h of
    Ind u p z s -> do
        tc p $ Pi "_" Nat (Cl [] (U u :: Exp Syn Infer))
        vp   <- asks \c -> eval c.ctxREnv c.ctxEnv p

        zTy <- asks \c -> app c.ctxREnv vp Zero
        tc z zTy

        -- Domain: P n
        -- Context: [n : Nat, P : Nat -> U l, ...]
        -- Indices:  0        1
        let dom = Use $ App (Head (Var 1)) (var 0)
        -- Context: [hyp : P n, n : Nat, P : Nat -> U l, ...]
        -- Indices:  0          1        2
        let cod = Use $ App (Head (Var 2)) (Succ (var 1))

        let body :: Exp Syn Infer = Pi "_" dom cod
        let sTy  = Pi "_" Nat (Cl [vp] body)

        tc s sTy

        let resTy :: Exp Syn Infer = Use $ App (Head (Var 1)) (var 0)
        pure $ Pi "n" Nat (Cl [vp] resTy)

    J a x u p q y -> do
        _ <- isType a
        va <- asks \c -> eval c.ctxREnv c.ctxEnv a

        tc x va
        vx <- asks \c -> eval c.ctxREnv c.ctxEnv x

        -- Eql A x y -> U l
        -- Context: [y : A,  x : A, A : U k, ...]
        -- Indices:  0       1      2
        let body :: Exp Syn Infer = Pi "_" (Eql (var 2) (var 1) (var 0)) (U u)
        let pTy                   = Pi "_" va (Cl [vx, va] body)
        tc p pTy
        vp <- asks \c -> eval c.ctxREnv c.ctxEnv p

        qTy <- asks \c -> app c.ctxREnv (app c.ctxREnv vp vx) Refl
        tc q qTy

        tc y va
        vy <- asks \c -> eval c.ctxREnv c.ctxEnv y

        -- (e : Eql A x y) -> P y e
        let dom = Eql va vx vy
        -- P y e
        -- Indices: 0 -> e, 1 -> vy, 2 -> vp
        let cod :: Exp Syn Infer = Use $ App (App (Head (Var 2)) (var 1)) (var 0)
        pure $ Pi "_" dom (Cl [vy, vp] cod)

tcApp :: forall m a. Typing m => (a -> TC Vl) -> a -> Chk Syn -> TcTy m
tcApp infer s arg = inst @m $ do
    fTy               <- infer s
    (dom, Cl env cod) <- asPi fTy
    tc arg dom
    varg <- asks \c -> eval c.ctxREnv c.ctxEnv arg
    asks \c -> eval c.ctxREnv (varg : env) cod

tcAppStrict :: forall m m' arg. (Valid Syn m', Flow m' m, Typing m) => Head Syn m' Strict arg -> Spine Syn arg Rigid Check -> TcTy m
tcAppStrict h arg = case h of
    Fst -> inst @m $ do
        ty       <- tcS @Infer arg
        (dom, _) <- asSig ty
        pure dom
    Snd -> inst @m $ do
        ty              <- tcS @Infer arg
        (_, Cl env cod) <- asSig ty
        varg <- asks \c -> evalS c.ctxREnv c.ctxEnv arg
        asks \c -> eval c.ctxREnv (doFst c.ctxREnv varg : env) cod
    Contra -> case mode @m of
        SCheck -> \_ -> do
            ty  <- tcS @Infer arg
            ty' <- force ty
            case ty' of
                Eql _ Zero (Succ Zero) -> pure ()
                _                      -> throwError "Contra: Argument must be a proof of equality"
