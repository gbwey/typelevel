{-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns -Wno-redundant-constraints #-}
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
{-# LANGUAGE ConstraintKinds #-}
module POrd where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import PEq
import PCore
import Data.Functor.Identity
import Data.Ord
import qualified Data.Semigroup as SG
import qualified Data.Monoid as MM
import Data.Tagged
import Data.Proxy
import Control.Applicative
import Data.These
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void

data CompareSym0 :: a ~> a ~> Ordering
type instance Apply CompareSym0 x = CompareSym1 x

data CompareSym1 :: a -> a ~> Ordering
type instance Apply (CompareSym1 x) y = Compare x y

-- Eq is just == from Data.Type.Equality
class PEq a => POrd a where
  type family LessThanOrEqual (x :: a) (y :: a) :: Bool
  type LessThanOrEqual x y = TypeError ('Text "POrd LessThanOrEqual x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)

  type family Compare (x :: a) (y :: a) :: Ordering
  type Compare a b =
       If (a === b)
          'EQ
          (If (LessThanOrEqual a b)
             'LT
             'GT
          )

  type family LE' (x :: a) (y :: a) :: Bool
  type LE' a b = Compare a b === 'LT || a === b

  type family LT' (x :: a) (y :: a) :: Bool
  type LT' a b = Compare a b === 'LT

  type family EQ' (x :: a) (y :: a) :: Bool
  type EQ' a b = Compare a b === 'EQ

  type family GT' (x :: a) (y :: a) :: Bool
  type GT' a b = Compare a b === 'GT

  type family GE' (x :: a) (y :: a) :: Bool
  type GE' a b = Compare a b === 'GT || a === b

  type family Between (x :: a) (y :: a) (z :: a) :: Bool
  type Between x y z = GE' z x && LE' z y

data BetweenSym0 :: a ~> a ~> a ~> Bool
type instance Apply BetweenSym0 x = BetweenSym1 x

data BetweenSym1 :: a -> a ~> a ~> Bool
type instance Apply (BetweenSym1 x) y = BetweenSym2 x y

data BetweenSym2 :: a -> a -> a ~> Bool
type instance Apply (BetweenSym2 x y) z = Between x y z



data LESym0 :: a ~> a ~> Bool
type instance Apply LESym0 x = LESym1 x

data LESym1 :: a -> a ~> Bool
type instance Apply (LESym1 x) y = LE' x y

data LTSym0 :: a ~> a ~> Bool
type instance Apply LTSym0 x = LTSym1 x

data LTSym1 :: a -> a ~> Bool
type instance Apply (LTSym1 x) y = LT' x y

data EQSym0 :: a ~> a ~> Bool
type instance Apply EQSym0 x = EQSym1 x

data EQSym1 :: a -> a ~> Bool
type instance Apply (EQSym1 x) y = EQ' x y

data GTSym0 :: a ~> a ~> Bool
type instance Apply GTSym0 x = GTSym1 x

data GTSym1 :: a -> a ~> Bool
type instance Apply (GTSym1 x) y = GT' x y

data GESym0 :: a ~> a ~> Bool
type instance Apply GESym0 x = GESym1 x

data GESym1 :: a -> a ~> Bool
type instance Apply (GESym1 x) y = GE' x y

-- flipped versions cos more logical 4 < vs < 4
data LESym0F :: a ~> a ~> Bool
type instance Apply LESym0F x = LESym1F x

data LESym1F :: a -> a ~> Bool
type instance Apply (LESym1F x) y = LE' y x

data LTSym0F :: a ~> a ~> Bool
type instance Apply LTSym0F x = LTSym1F x

data LTSym1F :: a -> a ~> Bool
type instance Apply (LTSym1F x) y = LT' y x

data GTSym0F :: a ~> a ~> Bool
type instance Apply GTSym0F x = GTSym1F x

data GTSym1F :: a -> a ~> Bool
type instance Apply (GTSym1F x) y = GT' y x

data GESym0F :: a ~> a ~> Bool
type instance Apply GESym0F x = GESym1F x

data GESym1F :: a -> a ~> Bool
type instance Apply (GESym1F x) y = GE' y x


instance POrd Nat where
  type LessThanOrEqual x y = x <=? y

instance POrd Ordering where
  type LessThanOrEqual 'LT y = 'True
  type LessThanOrEqual 'EQ y = Not (y === 'EQ)
  type LessThanOrEqual 'GT y = y === 'GT

instance POrd Bool where
  type LessThanOrEqual 'False y = 'True
  type LessThanOrEqual 'True y = y === 'True

instance POrd () where
  type LessThanOrEqual '() '() = 'True

instance POrd Void where
  type LessThanOrEqual x y = 'True

instance POrd a => POrd (SG.Option a) where
  type LessThanOrEqual ('SG.Option x) ('SG.Option y) = LessThanOrEqual x y

instance POrd a => POrd (Tagged s a) where
  type LessThanOrEqual ('Tagged x) ('Tagged y) = LessThanOrEqual x y

-- Arg and Down are the exceptions
-- Ordering only on First arg!
instance POrd s => POrd (SG.Arg s a) where
  type LessThanOrEqual ('SG.Arg x y) ('SG.Arg x1 y1) = LessThanOrEqual x x1
  -- fixed: uses PEq: need to override else will use equality which is different
--  type Compare ('SG.Arg x y) ('SG.Arg x1 y1) = Compare x x1

-- flip ordering but not on semigroup
instance POrd z => POrd (Down z) where
  type LessThanOrEqual ('Down a) ('Down a1) = LessThanOrEqual a1 a

instance POrd a => POrd (Maybe a) where
  type LessThanOrEqual 'Nothing x = 'True
  type LessThanOrEqual ('Just x) 'Nothing = 'False
  type LessThanOrEqual ('Just x) ('Just y) = LessThanOrEqual x y

instance (POrd a, POrd b) => POrd (Either a b) where
  type LessThanOrEqual ('Left x) ('Left y) = LessThanOrEqual x y
  type LessThanOrEqual ('Left x) ('Right y) = 'True

  type LessThanOrEqual ('Right x) ('Left y) = 'False
  type LessThanOrEqual ('Right x) ('Right y) = LessThanOrEqual x y

instance POrd Symbol where
  type LessThanOrEqual s t = CmpSymbol s t === 'EQ || CmpSymbol s t === 'LT
--  type Compare s t = CmpSymbol s t

instance POrd (Proxy a) where
  type LessThanOrEqual 'Proxy 'Proxy = 'True

instance POrd x => POrd [x] where
  type LessThanOrEqual '[] '[] = 'True
  type LessThanOrEqual '[] (a ': as) = 'True
  type LessThanOrEqual (a ': as) '[] = 'False
  type LessThanOrEqual (a ': as) (b : bs) = If (a === b) (LessThanOrEqual as bs) (LessThanOrEqual a b)

instance POrd z => POrd (ZipList z) where
  type LessThanOrEqual ('ZipList as) ('ZipList bs) = LessThanOrEqual as bs

instance POrd z => POrd (NonEmpty z) where
  type LessThanOrEqual (a ':| as) (b ':| bs) = LessThanOrEqual (a ': as) (b ': bs)

instance (POrd x, POrd y) => POrd (These x y) where
  type LessThanOrEqual ('This a) ('This a1) = LessThanOrEqual a a1
  type LessThanOrEqual ('This a) ('That b) = 'True
  type LessThanOrEqual ('This a) ('These a1 b1) = 'True

  type LessThanOrEqual ('That b) ('This a) = 'False
  type LessThanOrEqual ('That b) ('That b1) = LessThanOrEqual b b1
  type LessThanOrEqual ('That b) ('These a1 b1) = 'True

  type LessThanOrEqual ('These a b) ('These a1 b1) = If (a===a1) (LessThanOrEqual b b1) (LessThanOrEqual a a1)
  type LessThanOrEqual ('These a b) ('This a1) = 'False
  type LessThanOrEqual ('These a b) ('That b1) = 'False

-- dont flip: only on semigroup
instance POrd z => POrd (SG.Dual z) where
  type LessThanOrEqual ('SG.Dual a) ('SG.Dual a1) = LessThanOrEqual a a1

instance POrd z => POrd (SG.Sum z) where
  type LessThanOrEqual ('SG.Sum a) ('SG.Sum a1) = LessThanOrEqual a a1

instance POrd z => POrd (SG.Min z) where
  type LessThanOrEqual ('SG.Min a) ('SG.Min a1) = LessThanOrEqual a a1

instance POrd z => POrd (SG.Max z) where
  type LessThanOrEqual ('SG.Max a) ('SG.Max a1) = LessThanOrEqual a a1

instance POrd z => POrd (SG.Last z) where
  type LessThanOrEqual ('SG.Last a) ('SG.Last a1) = LessThanOrEqual a a1

instance POrd z => POrd (SG.First z) where
  type LessThanOrEqual ('SG.First a) ('SG.First a1) = LessThanOrEqual a a1


instance POrd z => POrd (MM.Last z) where
  type LessThanOrEqual ('MM.Last a) ('MM.Last a1) = LessThanOrEqual a a1

instance POrd z => POrd (MM.First z) where
  type LessThanOrEqual ('MM.First a) ('MM.First a1) = LessThanOrEqual a a1

instance POrd MM.All where
  type LessThanOrEqual ('MM.All a) ('MM.All a1) = LessThanOrEqual a a1

instance POrd MM.Any where
  type LessThanOrEqual ('MM.Any a) ('MM.Any a1) = LessThanOrEqual a a1

instance POrd z => POrd (Identity z) where
  type LessThanOrEqual ('Identity a) ('Identity a1) = LessThanOrEqual a a1

instance (POrd z1, POrd z2) => POrd (z1, z2) where
  type LessThanOrEqual '(a, b) '(a1, b1) = If (a === a1) 'True (LessThanOrEqual b b1)

instance (POrd z1, POrd z2, POrd z3) => POrd (z1, z2, z3) where
  type LessThanOrEqual '(a, b, c) '(a1, b1, c1) =
     If (a === a1) 'True (If (b === b1) 'True (LessThanOrEqual c c1))

instance (POrd z1, POrd z2, POrd z3, POrd z4) => POrd (z1, z2, z3, z4) where
  type LessThanOrEqual '(a, b, c, d) '(a1, b1, c1, d1) =
     If (a === a1) 'True (If (b === b1) 'True (If (c === c1) 'True (LessThanOrEqual d d1)))

type family Comparing (f :: a ~> (k :: k1))  (a1 :: a) (a2 :: a) :: Ordering where
  Comparing f a a1 = Compare (f @@ a) (f @@ a1)

data ComparingSym0 :: (a ~> k) ~> a ~> a ~> Ordering
type instance Apply ComparingSym0 x = ComparingSym1 x

data ComparingSym1 :: (a ~> k) -> a ~> a ~> Ordering
type instance Apply (ComparingSym1 x) y = ComparingSym2 x y

data ComparingSym2 :: (a ~> k) -> a -> a ~> Ordering
type instance Apply (ComparingSym2 x y) z = Comparing x y z

type family CompareImpl (cmp :: a ~> a ~> Ordering) (lt :: (a,a) ~> b) (eq :: (a,a) ~> b) (gt :: (a,a) ~> b) (arg :: a) (arg1 :: a) :: b where
  CompareImpl f lt eq gt a a1 = WhenCompare (UnCurrySym1 f) lt eq gt '(a,a1)

data CompareImplSym0 :: (a ~> a ~> Ordering) ~> ((a,a) ~> b) ~> ((a,a) ~> b) ~> ((a,a) ~> b) ~> a ~> a ~> b
type instance Apply CompareImplSym0 x = CompareImplSym1 x

data CompareImplSym1 :: (a ~> a ~> Ordering) -> ((a,a) ~> b) ~> ((a,a) ~> b) ~> ((a,a) ~> b) ~> a ~> a ~> b
type instance Apply (CompareImplSym1 x) y = CompareImplSym2 x y

data CompareImplSym2 :: (a ~> a ~> Ordering) -> ((a,a) ~> b) -> ((a,a) ~> b) ~> ((a,a) ~> b) ~> a ~> a ~> b
type instance Apply (CompareImplSym2 x y) z = CompareImplSym3 x y z

data CompareImplSym3 :: (a ~> a ~> Ordering) -> ((a,a) ~> b) -> ((a,a) ~> b) -> ((a,a) ~> b) ~> a ~> a ~> b
type instance Apply (CompareImplSym3 x y z) w = CompareImplSym4 x y z w

data CompareImplSym4 :: (a ~> a ~> Ordering) -> ((a,a) ~> b) -> ((a,a) ~> b) -> ((a,a) ~> b) -> a ~> a ~> b
type instance Apply (CompareImplSym4 x y z w) a = CompareImplSym5 x y z w a

data CompareImplSym5 :: (a ~> a ~> Ordering) -> ((a,a) ~> b) -> ((a,a) ~> b) -> ((a,a) ~> b) -> a -> a ~> b
type instance Apply (CompareImplSym5 x y z w a) b = CompareImpl x y z w a b

type family WhenCompare (cmp :: a ~> Ordering) (lt :: a ~> b) (eq :: a ~> b) (gt :: a ~> b) (arg :: a) :: b where
  WhenCompare f lt eq gt a = WhenCompare' (f @@ a) lt eq gt a

type family WhenCompare' (cmp :: Ordering) (lt :: a ~> b) (eq :: a ~> b) (gt :: a ~> b) (arg :: a) :: b where
  WhenCompare' 'LT lt eq gt a = lt @@ a
  WhenCompare' 'EQ lt eq gt a = eq @@ a
  WhenCompare' 'GT lt eq gt a = gt @@ a

data WhenCompareSym0 :: (a ~> Ordering) ~> (a ~> b) ~> (a ~> b) ~> (a ~> b) ~> a ~> b
type instance Apply WhenCompareSym0 x = WhenCompareSym1 x

data WhenCompareSym1 :: (a ~> Ordering) -> (a ~> b) ~> (a ~> b) ~> (a ~> b) ~> a ~> b
type instance Apply (WhenCompareSym1 x) y = WhenCompareSym2 x y

data WhenCompareSym2 :: (a ~> Ordering) -> (a ~> b) -> (a ~> b) ~> (a ~> b) ~> a ~> b
type instance Apply (WhenCompareSym2 x y) z = WhenCompareSym3 x y z

data WhenCompareSym3 :: (a ~> Ordering) -> (a ~> b) -> (a ~> b) -> (a ~> b) ~> a ~> b
type instance Apply (WhenCompareSym3 x y z) w = WhenCompareSym4 x y z w

data WhenCompareSym4 :: (a ~> Ordering) -> (a ~> b) -> (a ~> b) -> (a ~> b) -> a ~> b
type instance Apply (WhenCompareSym4 x y z w) a = WhenCompare x y z w a
