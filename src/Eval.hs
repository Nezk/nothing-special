{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Eval where

import qualified Data.Map.Strict as M

import Syntax
import Utils

type family Res (s :: Status) (arg :: Mode) where
    Res Rigid    _   = Vl
    Res Strict   arg = Spine Sem None Strict arg
    Res Flex     arg = Spine Sem None Flex   Check

eval :: REnv -> Env -> Sy m -> Vl
eval renv env = \case
    U         l   -> U l
    Nat           -> Nat
    Zero          -> Zero
    Succ      k   -> Succ      (eval renv env k)
    Pi  x     a b -> Pi   x    (eval renv env a)      (Cl        env b)
    Lam x       b -> Lam  x    (Cl        env b)
    Sig x     a b -> Sig  x    (eval renv env a)      (Cl        env b)
    Pair      a b -> Pair      (eval renv env a)      (eval renv env b)
    Eql     t a b -> Eql       (eval renv env t)      (eval renv env a) (eval renv env b)
    Refl          -> Refl
    Let _   d   b -> let v = either (eval renv env) (eval renv env . fst) d
                     in eval renv (v : env) b
    Use       s   -> evalS renv env s

evalS :: REnv -> Env -> Spine Syn m s arg -> Res s arg
evalS renv env = \case
    Head h     -> evalH renv env h
    App  s arg ->
        let f = evalS renv env s
        in case view s of
            VRigid  -> app        renv f (eval  renv env arg)
            VStrict -> elimStrict renv f (evalS renv env arg)
            VFlex   -> elimFlex   renv f (eval  renv env arg)

evalH :: REnv -> Env -> Head Syn m s arg -> Res s arg
evalH renv env = \case
    Var  i        -> env !! unIx i
    Hole h t      -> Use $ Head $ Hole h $ eval renv env <$> t
    Ref  r        -> Use $ Head $ Ref r -- lazy
    Fst           -> Head Fst
    Snd           -> Head Snd
    Contra        -> Head Contra
    Ind   u p z s -> Head $ Ind u (eval renv env p) (eval renv env z)   (eval renv env s)
    J a x u p q y -> Head $ J     (eval renv env a) (eval renv env x) u (eval renv env p)
                                  (eval renv env q) (eval renv env y)

-- The current implementation of unfold is highly inefficient.
-- For every useful unfolding of a global reference,
-- a lot of attempts are made to unfold spines headed by local variables.
unfold :: REnv -> Spine Sem None Rigid Check -> Maybe Vl
unfold renv = \case
    Head h -> case h of
        Ref r -> M.lookup r renv -- unfolding is impossible if it's a postulate
        _     -> Nothing
    App s a -> case view s of
        VRigid -> unfold renv s >>= \f -> pure (app renv f a)
        _      -> Nothing

app :: REnv -> Vl -> Vl -> Vl
app renv f a = case f of
    Lam _ (Cl env b) -> eval renv (a : env) b
    Use s            -> Use $ App s a
    _                -> internalErr "app: Ill-typed application"

-- TODO: Merge these to functions for projections?
doFst :: REnv -> Vl -> Vl
doFst renv = \case
    Pair a _ -> a
    Use  s   -> maybe (Use (App (Head Fst) s)) (doFst renv) (unfold renv s)
    _        -> internalErr "doFst: not a pair"

doSnd :: REnv -> Vl -> Vl
doSnd renv = \case
    Pair _ b -> b
    Use  s   -> maybe (Use (App (Head Snd) s)) (doSnd renv) (unfold renv s)
    _        -> internalErr "doSnd: not a pair"

elimStrict :: REnv -> Spine Sem None Strict arg -> Vl -> Vl
elimStrict renv sp arg = case sp of
    Head Fst    -> doFst renv arg
    Head Snd    -> doSnd renv arg
    Head Contra -> 
        case arg of
            Use s -> Use (App sp s)
            _     -> internalErr "elimStrict: not a spine"

elimFlex :: REnv -> Spine Sem None Flex Check -> Vl -> Vl
elimFlex renv sp arg = case (sp, arg) of
    (Head (Ind _ _     z _), Zero)   -> z
    (Head (Ind _ _ _     s), Succ k) -> app renv (app renv s k) (elimFlex renv sp k)
    (Head (J   _ _ _ _ q _), Refl)   -> q
    (_,                      Use s)  -> maybe (Use (App sp s)) (elimFlex renv sp) (unfold renv s)
    _                                -> internalErr "elimFlex: wrong spine/arg"
