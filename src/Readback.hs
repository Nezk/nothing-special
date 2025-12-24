{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Readback where

import Syntax
import Eval (eval)
import Utils

rb :: REnv -> Lv -> Exp Sem None -> Nm
rb renv lv = \case
    U l        -> U l
    Nat        -> Nat
    Zero       -> Zero
    Succ k     -> Succ  (rb renv lv k)
    Pi   x a b -> Pi  x (rb renv lv a)    (rbBind renv lv b)
    Lam  x b   -> Lam x (rbBind renv lv b)
    Sig  x a b -> Sig x (rb renv lv a)    (rbBind renv lv b)    
    Pair a b   -> Pair  (rb renv lv a)    (rb renv lv b)
    Eql  a x y -> Eql   (rb renv lv a)    (rb renv lv x)    (rb renv lv y)
    Refl       -> Refl
    Use  s     -> Use   (rbS renv lv s)

rbBind :: REnv -> Lv -> Cl -> Nm
rbBind renv lv (Cl env b) = rb renv (lv + 1) (eval renv (var lv : env) b)

rbS :: REnv -> Lv -> Spine Sem None s arg -> Spine Nrm None s arg
rbS renv lv = \case
    Head h  -> Head (rbH renv lv h)
    App s a -> case view s of
            VRigid  -> App s' (rb  renv lv a)
            VStrict -> App s' (rbS renv lv a)
            VFlex   -> App s' (rbS renv lv a)
            where s' = rbS renv lv s

rbH :: REnv -> Lv -> Head Sem None s arg -> Head Nrm None s arg
rbH renv lv = \case
    Var  l           -> Var   (lvl2ix lv l)
    Hole n t         -> Hole n $ rb renv lv <$> t
    Ref  r           -> Ref r    
    Ind  u a b c     -> Ind u (rb renv lv a) (rb renv lv b)   (rb renv lv c)
    J    a p u x d y -> J     (rb renv lv a) (rb renv lv p) u (rb renv lv x) (rb renv lv d) (rb renv lv y)
    Fst              -> Fst
    Snd              -> Snd
    Contra           -> Contra

lvl2ix :: Lv -> Lv -> Ix
lvl2ix (Lv x) (Lv d) = Ix $ x - d - 1
