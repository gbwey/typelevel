{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoStarIsType #-}
module PNum where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import Data.Kind (Type)
import PCore
import Data.Functor.Identity
import Data.Ord
import qualified Data.Semigroup as SG
import Control.Applicative

class PNum (a :: Type) where
  type family FromInteger (n :: Nat) :: a
  type FromInteger n = TypeError ('Text "PNum FromInteger n=" ':<>: 'ShowType n)

  type family ToInteger (n :: a) :: Nat
  type ToInteger n = TypeError ('Text "PNum ToInteger n=" ':<>: 'ShowType n)

  type family PAdd (n :: a) (n1 :: a) :: a
  type PAdd n n1 = FromInteger (ToInteger n + ToInteger n1)

  type family PSub (n :: a) (n1 :: a) :: a
  type PSub n n1 = FromInteger (Subtract (ToInteger n) (ToInteger n1))

  type family PMult (n :: a) (n1 :: a) :: a
  type PMult n n1 = FromInteger (ToInteger n * ToInteger n1)

instance PNum Nat where
  type FromInteger n = n
  type ToInteger n = n
  type PAdd n n1 = n + n1
  type PSub n n1 = Subtract n n1
  type PMult n n1 = n * n1

instance PNum (Down a) where
  type FromInteger n = 'Down (FromInteger n)
  type ToInteger ('Down n) = ToInteger n
  type PAdd ('Down n) ('Down n1) = 'Down (PAdd n n1)
  type PSub ('Down n) ('Down n1) = 'Down (PSub n n1)
  type PMult ('Down n) ('Down n1) = 'Down (PMult n n1)

instance PNum (SG.Sum a) where
  type FromInteger n = 'SG.Sum (FromInteger n)
  type ToInteger ('SG.Sum n) = ToInteger n
  type PAdd ('SG.Sum n) ('SG.Sum n1) = 'SG.Sum (PAdd n n1)
  type PSub ('SG.Sum n) ('SG.Sum n1) = 'SG.Sum (PSub n n1)
  type PMult ('SG.Sum n) ('SG.Sum n1) = 'SG.Sum (PMult n n1)

instance PNum (SG.Product a) where
  type FromInteger n = 'SG.Product (FromInteger n)
  type ToInteger ('SG.Product n) = ToInteger n
  type PAdd ('SG.Product n) ('SG.Product n1) = 'SG.Product (PAdd n n1)
  type PSub ('SG.Product n) ('SG.Product n1) = 'SG.Product (PSub n n1)
  type PMult ('SG.Product n) ('SG.Product n1) = 'SG.Product (PMult n n1)

instance PNum (SG.Min a) where
  type FromInteger n = 'SG.Min (FromInteger n)
  type ToInteger ('SG.Min n) = ToInteger n
  type PAdd ('SG.Min n) ('SG.Min n1) = 'SG.Min (PAdd n n1)
  type PSub ('SG.Min n) ('SG.Min n1) = 'SG.Min (PSub n n1)
  type PMult ('SG.Min n) ('SG.Min n1) = 'SG.Min (PMult n n1)

instance PNum (SG.Max a) where
  type FromInteger n = 'SG.Max (FromInteger n)
  type ToInteger ('SG.Max n) = ToInteger n
  type PAdd ('SG.Max n) ('SG.Max n1) = 'SG.Max (PAdd n n1)
  type PSub ('SG.Max n) ('SG.Max n1) = 'SG.Max (PSub n n1)
  type PMult ('SG.Max n) ('SG.Max n1) = 'SG.Max (PMult n n1)

instance PNum (Identity a) where
  type FromInteger n = 'Identity (FromInteger n)
  type ToInteger ('Identity n) = ToInteger n
  type PAdd ('Identity n) ('Identity n1) = 'Identity (PAdd n n1)
  type PSub ('Identity n) ('Identity n1) = 'Identity (PSub n n1)
  type PMult ('Identity n) ('Identity n1) = 'Identity (PMult n n1)

instance PNum (Const a b) where
  type FromInteger n = 'Const (FromInteger n)
  type ToInteger ('Const n) = ToInteger n
  type PAdd ('Const n) ('Const n1) = 'Const (PAdd n n1)
  type PSub ('Const n) ('Const n1) = 'Const (PSub n n1)
  type PMult ('Const n) ('Const n1) = 'Const (PMult n n1)


type family PSuccSym0 where PSuccSym0 = PAddSym1 (FromInteger 1)
type family PSuccSym1 x where PSuccSym1 x = PSucc x
type family PSucc x where PSucc x = PAdd x (FromInteger 1)

-- order for subtraction is important
type family PPredSym0 where PPredSym0 = FlipSym2 PSubSym0 (FromInteger 1)
type family PPredSym1 x where PPredSym1 x = PPred x
type family PPred x where PPred x = PSub x (FromInteger 1)


data PAddSym0 :: a ~> a ~> a
type instance Apply PAddSym0 x = PAddSym1 x

data PAddSym1 :: a -> a ~> a
type instance Apply (PAddSym1 x) y = PAdd x y

data PSubSym0 :: a ~> a ~> a
type instance Apply PSubSym0 x = PSubSym1 x

data PSubSym1 :: a -> a ~> a
type instance Apply (PSubSym1 x) y = PSub x y

data PMultSym0 :: a ~> a ~> a
type instance Apply PMultSym0 x = PMultSym1 x

data PMultSym1 :: a -> a ~> a
type instance Apply (PMultSym1 x) y = PMult x y

data FromIntegerSym0 :: a ~> b
type instance Apply FromIntegerSym0 x = FromInteger x

data ToIntegerSym0 :: a ~> b
type instance Apply ToIntegerSym0 x = ToInteger x

