{-# OPTIONS -Wall #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
module PN where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import Data.Proxy
import PEnum
import POrd
import PNum
import PEq
import PCore

data N = Z | S !N

type family ToNat a where
  ToNat 'Z = 0
  ToNat ('S n) = 1 + ToNat n

data ToNatSym0 :: N ~> Nat
type instance Apply ToNatSym0 a = ToNat a

type family ToN a where
  ToN 0 = 'Z
  ToN n = 'S (ToN (n-1))

data ToNSym0 :: Nat ~> N
type instance Apply ToNSym0 a = ToN a


-- safe diff
type family Diff (n :: N) (i :: N) :: N where
  Diff ('S n) ('S i) = Diff n i
  Diff ('S n) 'Z = 'S n
  Diff 'Z ('S n) = TypeError ('Text "Diff: i>n by " ':<>: 'ShowType (ToNat ('S n)))
  Diff 'Z 'Z = TypeError ('Text "Diff: diff of zero cos empty Vector")

data DiffSym0 :: N ~> N ~> N
type instance Apply DiffSym0 x = DiffSym1 x

data DiffSym1 :: N -> N ~> N
type instance Apply (DiffSym1 x) y = Diff x y

instance PEnum N where
  type ToEnum n = ToN n
  type FromEnum n = ToNat n
  type ESucc n = PAdd n (FromInteger 1)
  type EPred n = PSub n (FromInteger 1)

instance PEq N

instance POrd N where
  type LessThanOrEqual x y = ToNat x <=? ToNat y

instance PNum N where
  type FromInteger n = ToN n
  type ToInteger n = ToNat n
  type PAdd n n1 = n :+ n1
  type PSub n n1 = Diff n n1
  type PMult n n1 = n :* n1


type family m :+ n where
  'Z :+ a = a
--  a :+ 'Z = a -- breaks everything
  'S a :+ b = 'S (a :+ b)

type family m :* n where
  'Z :* a = 'Z
  'S a :* b = b :+ (a :* b) -- had to swap from (a ** b) ++ b to get vflat working

data Fin n where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

deriving instance Show (Fin n)

fin3 :: Fin (ToN 10)
fin3 = FZ

fin4 :: Fin ('S ('S ('S ('S 'Z))))
fin4 = FS FZ

class ToFin n where
  toFin :: Fin n
instance ToFin ('S 'Z) where
  toFin = FZ
instance ToFin ('S n) => ToFin ('S ('S n)) where
  toFin = FS (toFin @('S n))

nat :: forall n . KnownNat (ToNat n) => Int
nat = fromIntegral (natVal (Proxy @(ToNat n)))


