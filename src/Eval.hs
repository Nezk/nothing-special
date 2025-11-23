{-# LANGUAGE LambdaCase #-}

module Eval where

import Data.Bifunctor  (bimap)
import Data.Maybe      (fromMaybe)
import Data.Map.Strict (Map, (!?))

import Syntax

internalErr :: String -> a
internalErr err = error $ "Internal error: " ++ err

-- Well-scopedness is guaranteed for global references; therefore, such errors are considered bugs
infixl 9 !:? -- todo: or maybe I should just use `(!)` without "fancy" error message
(!:?) :: Map GName a -> GName -> a
(!:?) ge n = fromMaybe (internalErr $ "Global missing: " ++ unGName n) (ge !? n)

app :: GEnv -> Cl -> Val -> Val
app ge (Cl env body) arg = evalC ge (arg : env) body

vapp :: GEnv -> Val -> Val -> Val
vapp ge v arg = case v of
    (VLam _ cl) -> app ge cl arg
    (VNeut s)   -> VNeut (App s (Locl arg)) 
    _           -> internalErr "vapp: applying non-function"

vfst, vsnd :: Val -> Val
vfst = \case { VPair u _ -> u; VNeut ne -> VNeut (Head (NFst ne)); _ -> internalErr "fst error" }
vsnd = \case { VPair _ v -> v; VNeut ne -> VNeut (Head (NSnd ne)); _ -> internalErr "snd error" }

-- Eval -----------------------------------------------------------------------

evalC :: GEnv -> Env -> CExp -> Val
evalC ge env = \case
    Lam x b      -> VLam x (Cl env b)
    Inf i        -> evalI ge env i
    LetC _ e _ b -> evalC ge (evalC ge env e : env) b
    Pair u v     -> VPair    (evalC ge env u) (evalC ge env v)
    Refl         -> VRefl
    Contra e     -> case evalC ge env e of
                        VNeut ne -> VNeut (Head (NContra ne))
                        v        -> internalErr $ "contra applied to non-neutral: " ++ show v
    Hole n       -> VNeut (Head (NHole n))

evalI :: GEnv -> Env -> IExp -> Val
evalI ge env = \case
    U i             -> VU i
    Pi x ty body    -> VPi x    (evalI ge env ty) (Cl env (Inf body))
    LetI _ e _ body -> evalI ge (evalC ge env e : env) body
    Spine s         -> evalS ge env s
    Sigma x ty body -> VSigma x (evalI ge env ty) (Cl env (Inf body))
    Fst e           -> vfst   (evalI ge env e)
    Snd e           -> vsnd   (evalI ge env e)
    Nat             -> VNat
    Zero            -> VZero
    Succ n          -> VSucc (evalC ge env n)
    Eql a x y       -> VEql  (evalI ge env a) (evalC ge env x) (evalC ge env y)
    Ind l p z s n   -> ind (evalC ge env p) (evalC ge env z) (evalC ge env s) (evalC ge env n)
        where ind vp vz vs = \case -- todo: helpers are not both in evalI scope `where` block because of univ. level
                VZero      -> vz   -- maybe I should move them?
                VSucc vn   -> vapp ge (vapp ge vs vn) (ind vp vz vs vn)
                VNeut ne   -> VNeut (Head (NInd l vp vz vs ne))
                v          -> internalErr $ "ind applied to non-Nat: " ++ show v
    J a x l p q y e -> j (evalI ge env a) (evalC ge env x) (evalC ge env p)
                         (evalC ge env q) (evalC ge env y) (evalC ge env e)
        where j va vx vp vq vy = \case
                VRefl      -> vq 
                VNeut ne   -> VNeut (Head (NJ va vx l vp vq vy ne))
                v          -> internalErr $ "J applied to non-equality: " ++ show v

evalS :: GEnv -> Env -> Spine (Glob Ix) (Glob CExp) -> Val
evalS ge env = \case 
    Head h    -> elimGlob (ge !:?) (\i -> env !! unIx i) h
    App f arg -> 
        let vf   = evalS ge env f
            vArg = fmap (evalC ge env) arg -- is ony evaluated if local
        in case vf of
            VLam _ cl -> let val = elimGlob (ge !:?) id vArg in app ge cl val
            VNeut s'  -> VNeut (App s' vArg)
            _         -> internalErr "vapp: applying non-function"

fresh :: Lv -> Val
fresh = VNeut . Head . NVar

-- Readback -------------------------------------------------------------------

lv2Ix :: Lv -> Lv -> Ix
lv2Ix (Lv l) (Lv x) = Ix $ l - x - 1

rbV :: GEnv -> Lv -> Val -> NExp
rbV ge l = \case
    VU i          -> NU i
    VPi    x a cl -> NPi    x (rbV ge l a) (rbCl cl)
    VLam   x   cl -> NLam   x (rbCl cl)
    VSigma x a cl -> NSigma x (rbV ge l a) (rbCl cl)
    VPair a b     -> NPair (rbV ge l a) (rbV ge l b)
    VNeut ne      -> NNeut (rbN ge l ne)
    VNat          -> NNat
    VZero         -> NZero
    VSucc n       -> NSucc (rbV ge l n)
    VEql a x y    -> NEql  (rbV ge l a) (rbV ge l x) (rbV ge l y)
    VRefl         -> NRefl
    where rbCl cl = rbV ge (l + 1) (app ge cl (fresh l))

rbN :: GEnv -> Lv -> Neutral Lv Val -> Neutral Ix NExp
rbN ge l = bimap rbH (fmap (rbV ge l))
    where rbH = \case
            NVar i            -> NVar (lv2Ix l i)
            NHole h           -> NHole h
            NFst n            -> NFst (rbN ge l n)
            NSnd n            -> NSnd (rbN ge l n)
            NInd k p z s n    -> NInd k (rbV ge l p) (rbV ge l z) (rbV ge l s) (rbN ge l n)
            NJ a x k p q y e  -> NJ (rbV ge l a) (rbV ge l x) k (rbV ge l p) (rbV ge l q) (rbV ge l y) (rbN ge l e)
            NContra n         -> NContra (rbN ge l n)