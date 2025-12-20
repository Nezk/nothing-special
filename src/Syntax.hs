{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}

module Syntax where

import Data.String     (IsString)
import Data.Kind       (Constraint)
import Data.Map.Strict (Map)

import GHC.TypeLits (TypeError, ErrorMessage(..))

newtype RName = RName { unRName :: String } deriving (Show, Eq, Ord, IsString) via String 
newtype LName = LName { unLName :: String } deriving (Show, Eq, Ord, IsString) via String 
newtype HName = HName { unHName :: String } deriving (Show, Eq, Ord, IsString) via String 

newtype Ix = Ix { unIx :: Int } deriving (Show, Num, Eq)      via Int 
newtype Lv = Lv { unLv :: Int } deriving (Show, Num, Eq)      via Int 
newtype Ul = Ul { unUl :: Int } deriving (Show, Num, Eq, Ord) via Int 

data Mode     = Infer | Check  | None
data Phase    = Syn   | Sem    | Nrm
data Status   = Rigid | Flex   | Strict

type family T (p :: Phase) (m :: Mode) :: Mode where
    T Syn m = m
    T _   _ = None

type family V (p :: Phase) where
    V Syn = Ix
    V Sem = Lv
    V Nrm = Ix

type family Choice (p :: Phase) (s :: Status) (arg :: Mode) where
    -- Rigid (Var/Hole/Ref):
    -- In Syntax:    They accept expressions.
    -- In Semantics: They form Neutral expressions.
    Choice p   Rigid arg = Exp p (T p arg)
    -- Flex (Eliminators like Ind, J):
    -- In Syntax:    They accept expressions.
    -- In Semantics: They are stuck. They only appear in a Spine if the elimination is blocked.
    --               Thus, they accept spines.
    Choice Syn Flex   arg = Exp   Syn            arg
    Choice p   Flex   arg = Spine p   None Rigid Check
     -- Strict (Projections, Contra):
     -- In Syntax:   They accept spines with nodes of status with any locality (global or local)
     -- In Semantics They accept spines "local" nodes
    Choice Syn Strict arg = Spine Syn arg  Rigid Check
    Choice p   Strict arg = Spine p   None Rigid Check    

-- Ensures that only valid Modes are used in specific Phases.    
type family Bind (p :: Phase) (m :: Mode) where
    Bind Syn m = Exp Syn m   
    Bind Sem _ = Cl          
    Bind Nrm _ = Exp Nrm None

type Inf p = Exp p (T p Infer)
type Chk p = Exp p (T p Check)    

type family Valid (p :: Phase) (m :: Mode) :: Constraint where
    Valid Syn None  = TypeError (Text "Invalid Mode: None in phase: Syn")
    Valid Syn _     = ()
    Valid _   None  = ()
    Valid p   m     = TypeError (Text "Invalid Mode: " :<>: ShowType m :<>: Text " in phase: " :<>: ShowType p)

type family TApp (p :: Phase) (s :: Status) (m :: Mode) :: Mode where
    TApp Syn Rigid _ = Infer
    TApp Syn _     m = m
    TApp _   _     _ = None

data Head (p :: Phase) (m :: Mode) (s :: Status) (arg :: Mode) where
    Var  :: Valid p m => V p   -> Head p m           Rigid Check
    Hole :: HName              -> Head p (T p Check) Rigid Check
    Ref  :: Valid p m => RName -> Head p m           Rigid Check 
    
    Ind :: Valid p m => Ul    -> Chk p -> Chk p -> Chk p                   -> Head p m Flex Check
    J   :: Valid p m => Inf p -> Chk p -> Ul    -> Chk p -> Chk p -> Chk p -> Head p m Flex Check

    Fst    :: Valid p m => Head p m Strict Infer
    Snd    :: Valid p m => Head p m Strict Infer
    Contra ::              Head p (T p Check) Strict Infer

data Spine (p :: Phase) (m :: Mode) (s :: Status) (arg :: Mode) where
    Head :: Valid p m => Head  p m            s arg                   -> Spine p m s     arg
    App  :: Valid p m => Spine p (TApp p s m) s arg -> Choice p s arg -> Spine p m Rigid Check

data Exp (p :: Phase) (m :: Mode) where   
    U    :: Valid p m => Ul                              -> Exp p   m
    Nat  :: Valid p m =>                                    Exp p   m
    Zero :: Valid p m =>                                    Exp p   m
    Succ :: Valid p m => Chk p                           -> Exp p   m
    Pi   :: Valid p m => LName -> Inf p -> Bind p Infer  -> Exp p   m
    Lam  :: LName     -> Bind p Check                    -> Chk p
    Sig  :: Valid p m => LName -> Inf p -> Bind p Infer  -> Exp p   m
    Pair :: Chk p     -> Chk p                           -> Chk p
    Eql  :: Valid p m => Inf p -> Chk p -> Chk p         -> Exp p   m
    Refl ::                                                 Chk p
    Use  :: Valid p m => Spine p m Rigid Check           -> Exp p   m
    Let  :: LName     -> Chk Syn -> Inf Syn -> Exp Syn m -> Exp Syn m

data Cl = forall m. Cl Env (Exp Syn m)

type Sy m = Exp Syn m
type Vl   = Exp Sem None
type Nm   = Exp Nrm None

type Env = [Vl]
type Tys = [Vl]

type REnv = Map RName (Exp Sem None)
type RTys = Map RName (Exp Sem None)

type LNames = [LName]
type RNames = [RName]

data Raw
  = RVar   String
  | RU     Int
  | RNat
  | RZero
  | RSucc         Raw
  | RPi    String Raw Raw
  | RFun          Raw Raw
  | RSigma String Raw Raw
  | RTimes        Raw Raw
  | RLet   String Raw Raw Raw
  | RLam   String Raw
  | RPair         Raw Raw
  | RFst          Raw
  | RSnd          Raw
  | RApp          Raw Raw
  | REql          Raw Raw Raw
  | RRefl
  | RContra       Raw
  | RInd   Int    Raw Raw Raw Raw
  | RJ            Raw Raw Int Raw Raw Raw Raw
  | RHole  String
