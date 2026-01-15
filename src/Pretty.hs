{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeAbstractions #-}

module Pretty where

import Data.List (intercalate)

import Syntax
import Utils

parens :: Bool -> String -> String
parens b s = if b then "(" ++ s ++ ")" else s

sub :: Int -> String
sub = map (toEnum . (+ 0x2050) . fromEnum) . show

ppVar :: forall p. HasPhase p => LNames -> V p -> String
ppVar ctx v = unLName $ ctx !! idx
  where idx = case phase @p of { SSem -> length ctx - unLv v - 1; SSyn -> unIx v; SNrm -> unIx v }

ppBind :: forall p m. HasPhase p => Int -> LNames -> Bind p m -> String
ppBind p = case phase @p of { SSem -> ppCl; SSyn -> pp' p; SNrm -> pp' p }

ppCl :: LNames -> Cl -> String
ppCl = \case
    []          -> \_             -> internalErr "ppCl: Empty context"
    ctx@(x : _) -> \(Cl env body) ->
        let envNames    = [ LName ("#" ++ show i) | i <- [0..length env - 1] ]
            bodyPP      = pp' 0 (x : envNames) body
            dumpVal i v = "#" ++ show i ++ " = " ++ pp' 0 ctx v 
        in bodyPP ++ " { " ++ intercalate ", " (zipWith dumpVal [(0 :: Int)..] env) ++ " }"

pp :: forall p m. HasPhase p => LNames -> Exp p m -> String
pp = pp' 0

pp' :: forall p m. HasPhase p => Int -> LNames -> Exp p m -> String
pp' p ctx = \case
    U         i   -> "U" ++ sub (unUl i)
    Nat           -> "ℕ"
    Zero          -> "Z"
    Succ      n   -> parens (p > 3) $ "S " ++ pp' 4 ctx n
    Pi  x     a b -> ppBinder 0 1 "→" p x a b
    Sig x     a b -> ppBinder 2 3 "×" p x a b
    Lam x       b -> parens (p > 0) $ withFresh ctx x $ \x' ctx' -> 
                     "λ" ++ unLName x'  ++ ". " ++ ppBind @p @Check 0 ctx' b
    Pair      a b -> "(" ++ pp' 0 ctx a ++ ", " ++ pp' 0 ctx b ++ ")"
    Eql     t a b -> parens (p > 1) $ unwords [pp' 2 ctx a, "=", pp' 2 ctx b, "@", pp' 3 ctx t]
    Refl          -> "refl"    
    Use       s   -> ppS p ctx s
    Let x   d   b -> parens (p > 0) $ withFresh ctx x $ \x' ctx' ->
                     let d' = either (\e      -> unwords [unLName x',                   ":=", pp' 0 ctx e])
                                     (\(e, t) -> unwords [unLName x', ":", pp' 0 ctx t, ":=", pp' 0 ctx e]) d
                     in unwords ["let", d', "in", pp' 0 ctx' b]
    where ppBinder thP argP op prec x a b = parens (prec > thP) $ withFresh ctx x $ \x' ctx' -> unwords [ppDomain argP x x' a, op, ppBind @p @Infer 0 ctx' b]
          ppDomain argP x x' a            = if unLName x == "_" then pp' argP ctx a else "(" ++ unLName x' ++ " : " ++ pp' 0 ctx a ++ ")"         

ppS :: forall p m s arg. HasPhase p => Int -> LNames -> Spine p m s arg -> String
ppS p ctx (Spine h args) = case args of -- (h x y a)
    Nil     -> ppH ctx h
    as :> a -> -- (h x y | a)
        case Spine h as of
            Op Fst -> ppArg ++ ".1"
            Op Snd -> ppArg ++ ".2"
            s      -> parens (p > 3) $ unwords [ppS 3 ctx s, ppArg]
        where ppArg = case viewA h as of
                         VRigid  -> pp' 4 ctx a
                         VStrict -> case phase @p of
                             SSyn -> ppS 4 ctx a
                             SSem -> ppS 4 ctx a
                             SNrm -> ppS 4 ctx a
                         VFlex   -> case phase @p of
                             SSyn -> pp' 4 ctx a
                             SSem -> ppS 4 ctx a
                             SNrm -> ppS 4 ctx a

ppH :: forall p m s arg. HasPhase p => LNames -> Head p m s arg -> String
ppH ctx = \case
    Var      i                -> ppVar @p ctx i
    Hole   h t                -> "?" ++ unHName h ++ maybe "" (\t' -> "{" ++ pp' 4 ctx t' ++ "}") t
    Ref    r                  -> unRName r    
    Contra                    -> "contra"
    Ind          (Ul k) p z s -> unwords ["ind",                           "{" ++ show k ++ "}", pp' 4 ctx p, pp' 4 ctx z, pp' 4 ctx s]
    J        a x (Ul k) p q y -> unwords ["J",   pp' 4 ctx a, pp' 4 ctx x, "{" ++ show k ++ "}", pp' 4 ctx p, pp' 4 ctx q, pp' 4 ctx y]    
    Fst                       -> "fst"
    Snd                       -> "snd"

withFresh :: LNames -> LName -> (LName -> LNames -> res) -> res
withFresh ctx x k = let x' = fresh x ctx in k x' (x' : ctx)

fresh :: LName -> LNames -> LName
fresh n ctx | n == "_" || n `notElem` ctx = n
            | otherwise                   = fresh (LName (unLName n ++ "'")) ctx

ppRaw :: Raw -> String
ppRaw = ppRaw' 0

ppRaw' :: Int -> Raw -> String
ppRaw' p = \case
    RVar   x            -> x
    RU     i            -> "U" ++ sub i
    RNat                -> "ℕ"
    RZero               -> "Z"
    RSucc    t          -> parens (p > 3) $ "S " ++ ppRaw' 4 t
    RPi    "_" a b      -> ppArrow p a b
    RPi    x   a b      -> parens (p > 0) $ unwords ["(" ++ x ++ " :", ppRaw' 0 a ++ ")", "→", ppRaw' 0 b]
    RFun       a b      -> ppArrow p a b
    RSigma "_" a b      -> ppTimes p a b
    RSigma x   a b      -> parens (p > 0) $ unwords ["(" ++ x ++ " :", ppRaw' 0 a ++ ")", "×", ppRaw' 0 b]
    RTimes     a b      -> ppTimes p a b
    RLam   x     b      -> parens (p > 0) $ "λ" ++ x ++ ". " ++ ppRaw' 0 b
    RLet   x t v b      -> let decl = maybe (unwords [x, ":=", ppRaw' 0 v]) (\ty -> unwords [x, ":", ppRaw' 0 ty, ":=", ppRaw' 0 v]) t
                           in parens (p > 0) $ unwords ["let", decl, "in", ppRaw' 0 b]
    RApp   f   a        -> parens (p > 3) $ unwords [ppRaw' 3 f, ppRaw' 4 a]
    RPair      a b      -> "(" ++ ppRaw' 0 a ++ ", " ++ ppRaw' 0 b ++ ")"
    RFst     t          -> ppRaw' 4 t ++ ".1"
    RSnd     t          -> ppRaw' 4 t ++ ".2"
    REql     t a b      -> parens (p > 1) $ unwords [ppRaw' 2 a, "=", ppRaw' 2 b, "@", ppRaw' 3 t]
    RRefl               -> "refl"
    RHole    n t        -> "?" ++ n ++ maybe "" (\t' -> "{" ++ ppRaw' 0 t' ++ "}") t
    RContra  t          -> parens (p > 3) $ "contra " ++ ppRaw' 4 t
    RInd     k p' z s n -> parens (p > 3) $ unwords [ "ind", "{" ++ show k ++ "}", ppRaw' 4 p', ppRaw' 4 z, ppRaw' 4 s, ppRaw' 4 n ]
    RJ   a x k p' q y e -> parens (p > 3) $ unwords [ "J", ppRaw' 4 a, ppRaw' 4 x, "{" ++ show k ++ "}", ppRaw' 4 p', ppRaw' 4 q, ppRaw' 4 y, ppRaw' 4 e ]
  where ppArrow prec a b = parens (prec > 0) $ ppRaw' 1 a ++ " → " ++ ppRaw' 0 b
        ppTimes prec a b = parens (prec > 2) $ ppRaw' 3 a ++ " × " ++ ppRaw' 2 b
