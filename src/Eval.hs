{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Eval where

import qualified Data.Map.Strict as M

import Syntax
import Utils

-- It is not possible to use `Choice` here because of the `Strict` and `Flex` cases.
-- In `Choice`, these heads accept `Rigid` spines (Neutrals) as arguments.
-- Here, evaluation returns the `Strict` or `Flex` spine itself — using `Op` pattern
type family Res (s :: Status) (arg :: Mode) where
    Res Rigid    _   = Vl
    Res Strict   arg = Spine Sem None Strict arg
    Res Flex     arg = Spine Sem None Flex   Check

eval :: REnv -> Env -> Sy m -> Vl
eval renv env = \case
    U         l   -> U l
    Nat           -> Nat
    Zero          -> Zero
    Succ      k   -> Succ   (eval renv env k)
    Pi  x     a b -> Pi   x (eval renv env a) (Cl        env b)
    Lam x       b -> Lam  x (Cl        env b)
    Sig x     a b -> Sig  x (eval renv env a) (Cl        env b)
    Pair      a b -> Pair   (eval renv env a) (eval renv env b)
    Eql     t a b -> Eql    (eval renv env t) (eval renv env a) (eval renv env b)
    Refl          -> Refl
    Let _   d   b -> let v = either (eval renv env) (eval renv env . fst) d
                     in eval renv (v : env) b
    Use       s   -> evalS renv env s

evalS :: REnv -> Env -> Spine Syn m s arg -> Res s arg
evalS renv env (Spine h args) = -- (h a b c)
  case args of
    Nil     -> evalH renv env h
    as :> a -> -- evalS … (h a b), because it's a snoc lsit
      let f = evalS renv env (Spine h as)
      in case viewA h as of
        VRigid  -> app        renv f (eval  renv env a)
        VStrict -> elimStrict renv f (evalS renv env a)
        VFlex   -> elimFlex   renv f (eval  renv env a)

evalH :: REnv -> Env -> Head Syn m s arg -> Res s arg
evalH renv env = \case
    Var  i        -> env !! unIx i
    Hole h t      -> Use $ Op $ Hole h $ eval renv env <$> t
    Ref  r        -> Use $ Op $ Ref r
    Fst           -> Op Fst
    Snd           -> Op Snd
    Contra        -> Op Contra
    Ind   u p z s -> Op $ Ind u (eval renv env p) (eval renv env z)   (eval renv env s)
    J a x u p q y -> Op $ J     (eval renv env a) (eval renv env x) u (eval renv env p)
                                (eval renv env q) (eval renv env y)

unfold :: REnv -> Spine Sem None Rigid Check -> Maybe Vl
unfold renv (Spine h args) = case h of
    Ref r -> M.lookup r renv >>= \v -> pure $ appA renv v args
    _     -> Nothing

appA :: REnv -> Vl -> Args Sem None s arg mh Rigid argh -> Vl
appA renv v = \case
  Nil     -> v
  as :> a -> case as of -- TODO: write a comment about this (and not only this) pattern matching (constraints, yada yada)
    Nil       -> app renv (appA renv v as) a
    _   :> _  -> app renv (appA renv v as) a

app :: REnv -> Vl -> Vl -> Vl
app renv f a = case f of
    Lam _ (Cl env b) -> eval renv (a : env) b
    Use s            -> Use $ sapp s a
    _                -> internalErr "app: Ill-typed application"

-- TODO: Merge these to functions for projections?
doFst :: REnv -> Vl -> Vl
doFst renv = \case
    Pair a _ -> a
    Use  s   -> maybe (Use (sapp (Op Fst) s)) (doFst renv) (unfold renv s)
    _        -> internalErr "doFst: not a pair"

doSnd :: REnv -> Vl -> Vl
doSnd renv = \case
    Pair _ b -> b
    Use  s   -> maybe (Use (sapp (Op Snd) s)) (doSnd renv) (unfold renv s)
    _        -> internalErr "doSnd: not a pair"

elimStrict :: REnv -> Spine Sem None Strict arg -> Vl -> Vl
elimStrict renv s arg = case s of
    Op Fst    -> doFst renv arg
    Op Snd    -> doSnd renv arg
    Op Contra -> 
        case arg of
            Use s' -> Use (sapp s s')
            _      -> internalErr "elimStrict: not a spine"
    _         -> internalErr "elimStrict: unknown strict head"

elimFlex :: REnv -> Spine Sem None Flex Check -> Vl -> Vl
elimFlex renv s arg = case (s, arg) of
    (Op (Ind _ _     z  _), Zero)   -> z
    (Op (Ind _ _ _     su), Succ k) -> app renv (app renv su k) (elimFlex renv s k)
    (Op (J   _ _ _ _ q  _), Refl)   -> q 
    (_,                     Use s') -> maybe (Use (sapp s s')) (elimFlex renv s) (unfold renv s') -- elim. applied to neutral var/glob ref
    _                               -> internalErr "elimFlex: wrong spine/arg"
