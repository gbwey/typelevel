{-# OPTIONS -Wall #-}
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
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
module PEnum where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import POrd
import PCore
import Data.Functor.Identity
import Data.Type.Equality
import PNum

class PEnum a where
  type family ToEnum (x :: Nat) :: a
  type ToEnum n = TypeError ('Text "PENum ToEnum n=" ':<>: 'ShowType n)

  type family FromEnum (x :: a) :: Nat
  type FromEnum n = TypeError ('Text "PENum FromEnum n=" ':<>: 'ShowType n)

  type family ESucc (x :: a) :: a
  type ESucc n = TypeError ('Text "PENum ESucc n=" ':<>: 'ShowType n)

  type family EPred (x :: a) :: a
  type EPred n = TypeError ('Text "PENum EPred n=" ':<>: 'ShowType n)

  type family EnumFromTo (x :: a) (y :: a) :: [a]

  --need extra error statement 1+FromEnum y <=? FromEnum x
  type EnumFromTo x y = Map ToEnumSym0 (IterateNat (FailWhen (1+FromEnum y <=? FromEnum x) ('Text "x > y") (FromEnum y - FromEnum x + 1)) SuccSym0 (FromEnum x))

  type family EnumFromThenTo (x :: a) (y :: a) (z :: a) :: [a]

  type EnumFromThenTo x y z =
         EnumFromThenToImpl
         (LT' x y)
         (FromEnum y - FromEnum x - 1)
         (EnumFromTo x z)

type family EnumFromThenToImpl (b :: Bool) (df :: Nat) (xs :: [a]) :: [a] where
  EnumFromThenToImpl 'True df '[] = '[]
  EnumFromThenToImpl 'True df (a ': as) = a ': EnumFromThenToImpl 'True df (DropUnsafe df as)
  EnumFromThenToImpl 'False df xs = TypeError ('Text "iterator has to be greater than x")

instance PEnum Nat where
  type ToEnum n = n
  type FromEnum n = n
  type ESucc n = PAdd n 1
  type EPred n = PSub n 1

instance PEnum () where
  type ToEnum n = FailWhen (n == 0) ('Text "ToEnum (): only 0 is valid found n=" ':<>: 'ShowType n) '()
  type FromEnum '() = 0

  type ESucc '() = TypeError ('Text "ToEnum (): no successor")
  type EPred '() = TypeError ('Text "ToEnum (): no predecessor")

-- have to handle the special case of only 1 element cos no next element
--  type EnumFromTo '() '() = '[ '() ]
  type EnumFromThenTo x y z = TypeError ('Text "EnumFromThenTo (): is invalid cos no successor")

instance PEnum Bool where
  type ToEnum n = Case n '[ '(0, 'False), '(1, 'True) ] (TypeError ('Text "ToEnum Bool: only 0 or 1 is valid found n=" ':<>: 'ShowType n))
  type FromEnum 'False = 0
  type FromEnum 'True = 1

  type ESucc 'False = 'True
  type ESucc 'True = TypeError ('Text "ESucc Bool: no successor to 'True")

  type EPred 'False = TypeError ('Text "EPred Bool: no successor to 'False")
  type EPred 'True = 'False

instance PEnum Ordering where
  type ToEnum n = Case n '[ '(0, 'LT), '(1, 'EQ), '(2, 'GT) ] (TypeError ('Text "ToEnum Orderng: only 0,1 or 2 is valid found n=" ':<>: 'ShowType n))
  type FromEnum 'LT = 0
  type FromEnum 'EQ = 1
  type FromEnum 'GT = 2

  type ESucc 'LT = 'EQ
  type ESucc 'EQ = 'GT
  type ESucc 'GT = TypeError ('Text "ESucc Ordering: no successor to 'GT")

  type EPred 'LT = TypeError ('Text "EPred Ordering: no successor to 'LT")
  type EPred 'EQ = 'LT
  type EPred 'GT = 'EQ

instance PEnum a => PEnum (Identity a) where
  type ToEnum n = 'Identity (ToEnum n)
  type FromEnum ('Identity n) = FromEnum n
  type ESucc ('Identity n) = 'Identity (ESucc n)
  type EPred ('Identity n) = 'Identity (EPred n)

  type EnumFromThenTo ('Identity x) ('Identity y) ('Identity z) = Map (TyCon1Sym1 'Identity) (EnumFromThenTo x y z)

data EPredSym0 :: a ~> a
type instance Apply EPredSym0 x = EPred x

data ESuccSym0 :: a ~> a
type instance Apply ESuccSym0 x = ESucc x

data ToEnumSym0 :: Nat ~> a
type instance Apply ToEnumSym0 x = ToEnum x

data FromEnumSym0 :: a ~> Nat
type instance Apply FromEnumSym0 x = FromEnum x

data EnumFromToSym0 :: a ~> a ~> [a]
type instance Apply EnumFromToSym0 x = EnumFromToSym1 x

data EnumFromToSym1 :: a -> a ~> [a]
type instance Apply (EnumFromToSym1 x) y = EnumFromTo x y


data EnumFromThenToSym0 :: a ~> a ~> a ~> [a]
type instance Apply EnumFromThenToSym0 x = EnumFromThenToSym1 x

data EnumFromThenToSym1 :: a -> a ~> a ~> [a]
type instance Apply (EnumFromThenToSym1 x) y = EnumFromThenToSym2 x y

data EnumFromThenToSym2 :: a -> a -> a ~> [a]
type instance Apply (EnumFromThenToSym2 x y) z = EnumFromThenTo x y z

