{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty (pp) where

import Syntax

parens :: Bool -> String -> String
parens b s = if b then "(" ++ s ++ ")" else s

pp :: LNames -> NExp -> String
pp = pp' 0

pp' :: Int -> LNames -> NExp -> String
pp' p ctx = \case
    NU (Ul i)    -> 'U' : map sub (show i)
    NPi x a b    -> ppF "→" 0 1 x a b
    NSigma x a b -> ppF "×" 2 3 x a b
    NLam x b     -> parens (p > 0) $ withFresh x $ \x' ctx' -> "λ" ++ unLName x' ++ ". " ++ pp' 0 ctx' b
    NPair a b    -> "(" ++ pp' 0 ctx a ++ ", " ++ pp' 0 ctx b ++ ")"
    NNat         -> "ℕ"
    NZero        -> "Z"
    NSucc n      -> parens (p > 3) $ "S " ++ pp' 4 ctx n
    NEql t x y   -> parens (p > 1) $ unwords [pp' 2 ctx x, "=", pp' 2 ctx y, "@", pp' 3 ctx t]
    NRefl        -> "refl"
    NNeut n      -> ppN p ctx n
    where withFresh x k      = let x' = fresh x in k x' (x' : ctx) --           vvvvvvvvvvvvvvv It's kind of ugly, but it's a newtype, right?
          fresh n            = if n == "_" || n `notElem` ctx then n else fresh (LName (unLName n ++ "'"))
          sub c              = toEnum (fromEnum c + 0x2050) -- Offset for subscript '₀'        
          ppF op pC pL x a b = parens (p > pC) $ withFresh x $ \x' ctx' ->
              if x == "_"
              then unwords [pp' pL ctx a, op, pp' 0 ctx' b]
              else unwords ["(" ++ unLName x' ++ " : " ++ pp' 0 ctx a ++ ")", op, pp' 0 ctx' b]

ppN :: Int -> LNames -> Neutral Ix NExp -> String
ppN p ctx = ppS ppH ctx p
    where ppH = \case
            NVar i                 -> unLName (ctx !! unIx i)
            NHole h                -> "?" ++ unHName h
            NFst n                 -> ppN 4 ctx n ++ ".1"
            NSnd n                 -> ppN 4 ctx n ++ ".2"
            NContra n              -> app "contra" [ppN 4 ctx n]
            NInd (Ul k) pM z s n   -> app "ind"    [br k, atom pM, atom z, atom s, ppN 4 ctx n]
            NJ a x (Ul k) pM q y e -> app "J"      [atom a, atom x, br k, atom pM, atom q, atom y, ppN 4 ctx e]
            where atom       = pp' 4 ctx
                  br k       = "{" ++ show k ++ "}"
                  app h args = unwords (h : args)

ppS :: (i -> String) -> LNames -> Int -> Spine i (Glob NExp) -> String
ppS ppHead ctx p = \case
    Head i  -> ppHead i
    App f a -> let arg = elimGlob unGName (pp' 4 ctx) a 
               in parens (p > 3) $ unwords [ppS ppHead ctx 3 f, arg]