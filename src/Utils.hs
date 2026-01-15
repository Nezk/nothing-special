{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Utils where

import Syntax

data View s arg where
    VRigid  :: View Rigid  Check
    VStrict :: View Strict arg
    VFlex   :: View Flex   Check

viewA :: Head p mh sh argh -> Args p m s arg mh sh argh -> View s arg
viewA h = \case
    _ :> _ -> VRigid
    Nil    -> case h of
        Var    {} -> VRigid
        Hole   {} -> VRigid
        Ref    {} -> VRigid
        Fst       -> VStrict
        Snd       -> VStrict
        Contra    -> VStrict
        Ind    {} -> VFlex
        J      {} -> VFlex

viewS :: Spine p m s arg -> View s arg
viewS (Spine h args) = viewA h args

pattern Op :: Valid p m => Head p m s arg -> Spine p m s arg
pattern Op h = Spine h Nil

sapp :: Valid p m => Spine p (TApp p s m) s arg -> Choice p s arg -> Spine p m Rigid Check
sapp (Spine h args) a = Spine h (args :> a)

var :: Valid p m => V p -> Exp p m
var = Use . Op . Var

internalErr :: String -> a
internalErr = error . ("Internal Error: " ++)
