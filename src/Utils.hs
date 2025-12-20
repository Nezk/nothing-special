{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Utils where

import Syntax

data SMode (m :: Mode) where
    SInfer :: SMode Infer
    SCheck :: SMode Check

data SPhase (p :: Phase) where
    SSyn :: SPhase Syn
    SSem :: SPhase Sem
    SNrm :: SPhase Nrm

class    PPPhase (p :: Phase) where phase :: SPhase p
instance PPPhase Syn          where phase = SSyn
instance PPPhase Sem          where phase = SSem
instance PPPhase Nrm          where phase = SNrm

class    HasMode (m :: Mode) where mode :: SMode m
instance HasMode Infer       where mode = SInfer
instance HasMode Check       where mode = SCheck

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
