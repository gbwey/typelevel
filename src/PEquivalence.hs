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
module PEquivalence where
import PCore
import PContravariant
import PMonoid
import PSemigroup
import PDivisible
import Data.Functor.Contravariant ( Contravariant(contramap) )
import Data.Functor.Contravariant.Divisible ( Divisible(..) )
import Data.Kind (Type)
import Data.Function ( on )
import Control.Arrow ( Arrow((&&&)) )

newtype EquivalenceX a = EquivalenceX { getEquivalenceX :: a ~> a ~> Bool }

type family UnEquivalenceX f where
  UnEquivalenceX ('EquivalenceX p) = p

instance PContravariant EquivalenceX where
  type Contramap f ('EquivalenceX g) = 'EquivalenceX (OnSym2 g f)

-- this actually runs the Equivalence cos the code is too complex!
data EquivalenceXSym0 :: (a ~> (b,c)) ~> (b ~> b ~> Bool) ~> (c ~> c ~> Bool) ~> a ~> a ~> Bool
type instance Apply EquivalenceXSym0 x = EquivalenceXSym1 x

data EquivalenceXSym1 :: (a ~> (b,c)) -> (b ~> b ~> Bool) ~> (c ~> c ~> Bool) ~> a ~> a ~> Bool
type instance Apply (EquivalenceXSym1 x) y = EquivalenceXSym2 x y

data EquivalenceXSym2 :: (a ~> (b,c)) -> (b ~> b ~> Bool) -> (c ~> c ~> Bool) ~> a ~> a ~> Bool
type instance Apply (EquivalenceXSym2 x y) z = EquivalenceXSym3 x y z

data EquivalenceXSym3 :: (a ~> (b,c)) -> (b ~> b ~> Bool) -> (c ~> c ~> Bool) -> a ~> a ~> Bool
type instance Apply (EquivalenceXSym3 x y z) w = EquivalenceXSym4 x y z w

data EquivalenceXSym4 :: (a ~> (b,c)) -> (b ~> b ~> Bool) -> (c ~> c ~> Bool) -> a -> a ~> Bool
-- <> not compare ie SAppSym0 not CompareSym0 elese everything is EQ
type instance Apply (EquivalenceXSym4 abc p p1 a) a1 =
      UnCurry AndSym0
      ((&&&) (UnCurrySym1 p :.: AmpSym2 (FstSym0 :.: FstSym0) (FstSym0 :.: SndSym0))
           (UnCurrySym1 p1 :.: AmpSym2 (SndSym0 :.: FstSym0) (SndSym0 :.: SndSym0))
           '(abc @@ a, abc @@ a1))

instance PDivisible EquivalenceX where
  type Divide abc ('EquivalenceX p) ('EquivalenceX p1) = 'EquivalenceX (EquivalenceXSym3 abc p p1)
  type Conquer = 'EquivalenceX (KSym1 (KSym1 'True))

instance PSemigroup (EquivalenceX (a :: Type)) where
  type p <> p1 = Divide DupSym0 p p1
  type SUnWrap ('EquivalenceX p) = p

instance PMonoid (EquivalenceX (a :: Type)) where
  type Mempty = Conquer

newtype EE a = EE { unEE :: a -> a -> Bool }

instance Contravariant EE where
  contramap f (EE p) = EE (on p f)

instance Divisible EE where
  conquer = EE (const (const True))
  divide abc (EE p) (EE p1) =
          EE $ \a a1 -> on (curry (uncurry (&&) .
                               (uncurry p . ((fst . fst) &&& (fst . snd))
                           &&& (uncurry p1 . ((snd . fst) &&& (snd . snd))))
                         )) abc a a1


instance Semigroup (EE a) where
  p <> p1 = divide (\a -> (a,a)) p p1

{-
>unCC (EE (==) <> EE (==)) 4 3
GT
it :: Bool
>:kind! UnEquivalenceX ('EquivalenceX CompareSym0 <> 'EquivalenceX CompareSym0) @@ 2 @@ 9999
UnEquivalenceX ('EquivalenceX CompareSym0 <> 'EquivalenceX CompareSym0) @@ 2 @@ 9999 :: Bool
= 'LT
-}
