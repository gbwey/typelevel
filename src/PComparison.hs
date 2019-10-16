{-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns -Wredundant-constraints #-}
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
module PComparison where
import PCore
import PContravariant
import PMonoid
import PSemigroup
import PDivisible
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Kind (Type)
import Data.Function
import Control.Arrow

newtype ComparisonX a = ComparisonX { getComparisonX :: a ~> a ~> Ordering }

type family UnComparisonX f where
  UnComparisonX ('ComparisonX p) = p

instance PContravariant ComparisonX where
  type Contramap f ('ComparisonX g) = 'ComparisonX (OnSym2 g f)

-- this actually runs the comparison cos the code is too complex!
data ComparisonXSym0 :: (a ~> (b,c)) ~> (b ~> b ~> Ordering) ~> (c ~> c ~> Ordering) ~> a ~> a ~> Ordering
type instance Apply ComparisonXSym0 x = ComparisonXSym1 x

data ComparisonXSym1 :: (a ~> (b,c)) -> (b ~> b ~> Ordering) ~> (c ~> c ~> Ordering) ~> a ~> a ~> Ordering
type instance Apply (ComparisonXSym1 x) y = ComparisonXSym2 x y

data ComparisonXSym2 :: (a ~> (b,c)) -> (b ~> b ~> Ordering) -> (c ~> c ~> Ordering) ~> a ~> a ~> Ordering
type instance Apply (ComparisonXSym2 x y) z = ComparisonXSym3 x y z

data ComparisonXSym3 :: (a ~> (b,c)) -> (b ~> b ~> Ordering) -> (c ~> c ~> Ordering) -> a ~> a ~> Ordering
type instance Apply (ComparisonXSym3 x y z) w = ComparisonXSym4 x y z w

data ComparisonXSym4 :: (a ~> (b,c)) -> (b ~> b ~> Ordering) -> (c ~> c ~> Ordering) -> a -> a ~> Ordering
-- <> not compare ie SAppSym0 not CompareSym0 elese everything is EQ
type instance Apply (ComparisonXSym4 abc p p1 a) a1 =
      UnCurry SAppSym0
      ((&&&) (UnCurrySym1 p :.: AmpSym2 (FstSym0 :.: FstSym0) (FstSym0 :.: SndSym0))
           (UnCurrySym1 p1 :.: AmpSym2 (SndSym0 :.: FstSym0) (SndSym0 :.: SndSym0))
           '(abc @@ a, abc @@ a1))

instance PDivisible ComparisonX where
  type Divide abc ('ComparisonX p) ('ComparisonX p1) = 'ComparisonX (ComparisonXSym3 abc p p1)

  type Conquer = 'ComparisonX (KSym1 (KSym1 'EQ))

instance PSemigroup (ComparisonX (a :: Type)) where
  type p <> p1 = Divide DupSym0 p p1
  type SUnWrap ('ComparisonX p) = p

instance PMonoid (ComparisonX (a :: Type)) where
  type Mempty = Conquer

newtype CC a = CC { unCC :: a -> a -> Ordering }

instance Contravariant CC where
  contramap f (CC p) = CC (on p f)

instance Divisible CC where
  conquer = CC (const (const EQ))
  divide abc (CC p) (CC p1) =
          CC $ \a a1 -> on (curry (uncurry (<>) .
                         (uncurry p . ((fst . fst) &&& (fst . snd))   &&&   (uncurry p1 . ((snd . fst) &&& (snd . snd))))
                         )) abc a a1


instance Semigroup (CC a) where
  p <> p1 = divide (\a -> (a,a)) p p1

{-
>unCC (CC compare <> CC compare) 4 3
GT
it :: Ordering
>:kind! UnComparisonX ('ComparisonX CompareSym0 <> 'ComparisonX CompareSym0) @@ 2 @@ 9999
UnComparisonX ('ComparisonX CompareSym0 <> 'ComparisonX CompareSym0) @@ 2 @@ 9999 :: Ordering
= 'LT
-}