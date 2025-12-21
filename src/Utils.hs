{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Utils where

import Syntax

data View s arg where
    VRigid  :: View Rigid  Check
    VStrict :: View Strict arg
    VFlex   :: View Flex   Check

view :: Spine p m s arg -> View s arg
view = \case
    App _ _ -> VRigid
    Head h  -> case h of
        Var  {} -> VRigid
        Hole {} -> VRigid
        Ref  {} -> VRigid
        Fst     -> VStrict
        Snd     -> VStrict
        Contra  -> VStrict
        Ind  {} -> VFlex
        J    {} -> VFlex

var :: Valid p m => V p -> Exp p m
var = Use . Head . Var

internalErr :: String -> a
internalErr = error . ("Internal Error: " ++)
