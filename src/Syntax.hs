{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}

module Syntax where

import Data.Map.Strict (Map)
import Data.Bifunctor  (Bifunctor, bimap)
import Data.String     (IsString)

newtype GName = GName { unGName :: String } deriving (Show, Eq, Ord, IsString) via String -- global names
newtype LName = LName { unLName :: String } deriving (Show, Eq, Ord, IsString) via String -- local names
newtype HName = HName { unHName :: String } deriving (Show, Eq, Ord, IsString) via String -- hole names

newtype Ix = Ix { unIx :: Int } deriving (Show, Num, Eq) via Int -- De Bruijn Index
newtype Lv = Lv { unLv :: Int } deriving (Show, Num, Eq) via Int -- De Bruijn Level
--                                                       vvv for max l j of levels
newtype Ul = Ul { unUl :: Int } deriving (Show, Num, Eq, Ord) via Int -- Universe Level

-- In bidirectional type checking, lambda expressions are checkable terms. 
-- The head of application spines, however, should be inferable in order to check the arguments 
-- against the head's type. Therefore, lambdas cannot be in the head of spines 
-- (there is no point in expressions like `(λx. body) arg` anyway). 
-- However, other terms cannot appear at the head either; therefore, the head must be a variable (global or local) that refers to a lambda. 
data Spine i e 
    = Head i 
    | App (Spine i e) e 
    deriving (Show, Functor)

instance Bifunctor Spine where
    bimap f g = \case
        Head i  -> Head (f i)
        App s e -> App (bimap f g s) (g e)

data Glob e    
    = Glob GName
    | Locl e       
    deriving (Show, Functor)

elimGlob :: (GName -> r) -> (e -> r) -> Glob e -> r
elimGlob f g = \case
    Glob n -> f n
    Locl e -> g e

data CExp
    = Lam    LName CExp 
    | Inf    IExp 
    | LetC   LName CExp IExp CExp
    | Pair   CExp CExp 
    | Refl 
    | Contra CExp
    | Hole   HName       
    deriving Show

data IExp
    = U Ul
    | Pi    LName IExp IExp 
    | LetI  LName CExp IExp IExp 
    | Spine (Spine (Glob Ix) (Glob CExp))
    | Sigma LName IExp IExp 
    | Fst   IExp 
    | Snd   IExp
    | Nat 
    | Zero 
    | Succ  CExp 
    | Ind   Ul   CExp CExp CExp CExp
    | Eql   IExp CExp CExp 
    | J     IExp CExp Ul   CExp CExp CExp CExp
    deriving Show

-- Head of a neutral term
data NHead i e
    = NVar  i
    | NHole HName
    | NFst                (Neutral i e)
    | NSnd                (Neutral i e)
    | NInd  Ul e e  e     (Neutral i e)
    | NJ    e  e Ul e e e (Neutral i e)
    | NContra             (Neutral i e)
    deriving Show

-- We shouldn't evaluate globals if the head of spine is neutral
type Neutral i e = Spine (NHead i e) (Glob e)

data Cl 
    = Cl Env CExp 
    deriving Show

data Val
    = VU     Ul
    | VPi    LName Val Cl 
    | VLam   LName Cl 
    | VNeut  (Neutral Lv Val)
    | VSigma LName Val Cl 
    | VPair  Val Val
    | VNat 
    | VZero 
    | VSucc  Val 
    | VEql   Val Val Val 
    | VRefl
    deriving Show

data NExp
    = NU     Ul
    | NPi    LName NExp NExp 
    | NLam   LName NExp
    | NNeut  (Neutral Ix NExp)
    | NSigma LName NExp NExp
    | NPair  NExp NExp
    | NNat 
    | NZero 
    | NSucc  NExp 
    | NEql   NExp NExp NExp 
    | NRefl
    deriving Show

type Env  = [Val]
type GEnv = Map GName Val
type GTys = Map GName Val

type LNames = [LName]
type GNames = [GName]