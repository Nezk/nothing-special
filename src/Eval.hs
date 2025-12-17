{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Eval where

import Data.Map.Strict ((!))

import Syntax
import Utils

type family Res (s :: Status) (arg :: Mode) where
    Res (Node l) _   = Vl
    Res Strict   arg = Spine Sem None Strict arg
    Res Flex     arg = Spine Sem None Flex   Check

eval :: REnv -> Env -> Sy m -> Vl
eval renv env = \case
    U l         -> U l
    Nat         -> Nat
    Zero        -> Zero
    Succ k      -> Succ      (eval renv env k)
    Pi x a b    -> Pi   x    (eval renv env a)      (Cl        env b)
    Lam x b     -> Lam  x    (Cl        env b)
    Sig x a b   -> Sig  x    (eval renv env a)      (Cl        env b)
    Pair a b    -> Pair      (eval renv env a)      (eval renv env b)
    Eql a x y   -> Eql       (eval renv env a)      (eval renv env x) (eval renv env y)
    Refl        -> Refl
    Let _ v _ b -> eval renv (eval renv env v : env) b
    Use s       -> case view s of 
        VLocal  -> evalS renv env s
        VGlobal -> evalS renv env s

evalS :: REnv -> Env -> Spine Syn m s arg -> Res s arg
evalS renv env = \case
    Head h     -> evalH renv env h
    App s arg -> 
        let f = evalS renv env s
        in case view s of
            VLocal  -> app        renv f (eval  renv env arg)
            VGlobal -> app        renv f (eval  renv env arg)
            VStrict -> elimStrict      f (evalS renv env arg)
            VFlex   -> elimFlex   renv f (eval  renv env arg)

evalH :: REnv -> Env -> Head Syn m s arg -> Res s arg
evalH renv env = \case
    Var ix        -> env !! unIx ix
    Hole h        -> Use $ Head $ Hole h
    Ref r         -> renv ! r
    Fst           -> Head Fst
    Snd           -> Head Snd
    Contra        -> Head Contra
    Ind u p z s   -> Head $ Ind u (eval renv env p) (eval renv env z)   (eval renv env s)
    J a x u p q y -> Head $ J     (eval renv env a) (eval renv env x) u (eval renv env p)
                                  (eval renv env q) (eval renv env y)

app :: REnv -> Vl -> Vl -> Vl
app renv f a = case f of
    Lam _ (Cl env b) -> eval renv (a : env) b
    Use s            -> case view s of
        VLocal  -> Use $ App s a
        VGlobal -> internalErr "Global ref in Sem app head"
    _                -> internalErr "app: Ill-typed application"

doFst :: Vl -> Vl
doFst = \case
    Pair a _ -> a
    Use  s   -> case view s of
        VLocal  -> Use $ App (Head Fst) s
        VGlobal -> internalErr "Global ref in doFst"
    _        -> internalErr "doFst: not a pair"

doSnd :: Vl -> Vl
doSnd = \case
    Pair _ b -> b
    Use  s   -> case view s of
        VLocal  -> Use $ App (Head Snd) s
        VGlobal -> internalErr "Global ref in doSnd"
    _        -> internalErr "doSnd: not a pair"

elimStrict :: Spine Sem None Strict arg -> Vl -> Vl
elimStrict = \case
    Head Fst -> doFst
    Head Snd -> doSnd
    -- e. g. Contra
    s        -> \case 
      Use s' -> case view s' of
         VLocal  -> Use $ App s s'
         VGlobal -> internalErr "Global ref in strict elim arg"
      _      -> internalErr "Stuck strict elim"     

elimFlex :: REnv -> Spine Sem None Flex Check -> Vl -> Vl
elimFlex renv sp arg = case (sp, arg) of
    (Head (Ind _ _     z _), Zero)   -> z
    (Head (Ind _ _ _     s), Succ k) -> app renv (app renv s k) (elimFlex renv sp k)
    (Head (J   _ _ _ _ q _), Refl)   -> q
    (_,   Use spArg)                 -> case view spArg of
        VLocal  -> Use $ App sp spArg
        VGlobal -> internalErr "Global ref in flex elim arg"
    _                                -> internalErr "Stuck flex elim"
