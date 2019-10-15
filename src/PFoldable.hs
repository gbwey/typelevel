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
module PFoldable where
import GHC.TypeNats
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty(..))
import PCore
import PMonoid
import POrd
import PSemigroup
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Compose
import qualified Data.Semigroup as SG
import Data.These
import Data.Proxy
import Data.Tagged
import Control.Applicative

class PFoldable (t :: Type -> Type) where
  type family FoldMap (arg :: a ~> m) (arg1 :: t a) :: m
--  type FoldMap x y = TypeError ('Text "PFoldable FoldMap is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)

  type family ToList (arg :: t a) :: [a]
  type ToList xs = FoldMap SingSym0 xs

  type family Fold (arg :: t m) :: m
  type Fold xs = FoldMap Id xs

  type family Null (arg :: t a) :: Bool
  type Null xs = Length xs <=? 0

  type family Length (arg :: t a) :: Nat
  type Length xs = SUnWrap (FoldMap (SSumSym0 :.: KSym1 1) xs)

data FoldMapSym0 :: (a ~> m) ~> t a ~> m
type instance Apply FoldMapSym0 x = FoldMapSym1 x

data FoldMapSym1 :: (a ~> m) -> t a ~> m
type instance Apply (FoldMapSym1 x) y = FoldMap x y

data ToListSym0 :: t a ~> [a]
type instance Apply ToListSym0 x = ToList x

data FoldSym0 :: t m ~> m
type instance Apply FoldSym0 x = Fold x

data NullSym0 :: t a ~> Bool
type instance Apply NullSym0 x = Null x

data LengthSym0 :: t a ~> Nat
type instance Apply LengthSym0 x = Length x

instance PFoldable ((,) z) where
  type FoldMap f '(e,a) = f @@ a

instance PFoldable [] where
  type FoldMap f '[] = Mempty
  type FoldMap f (x ': xs) = f @@ x <> FoldMap f xs

instance PFoldable NonEmpty where
  type FoldMap f (x ':| xs) = f @@ x <> FoldMap f xs

instance PFoldable Proxy where
  type FoldMap f 'Proxy = Mempty

instance PFoldable (Tagged z) where
  type FoldMap f ('Tagged a) = f @@ a

instance PFoldable ZipList where
  type FoldMap f ('ZipList as) = FoldMap f as

-- easier to use Maybe'
instance PFoldable Maybe where
--  type FoldMap f 'Nothing = Mempty
--  type FoldMap f ('Just x) = f @@ x
  type FoldMap f x = Maybe' Mempty f x

instance PFoldable (Either z) where
  type FoldMap f x = Either' Mempty f x

instance PFoldable (Const z) where
  type FoldMap f ('Const e) = Mempty

instance PFoldable Identity where
  type FoldMap f ('Identity a) = f @@ a

instance (PFoldable g, PFoldable h) => PFoldable (Compose g h) where
  type FoldMap f ('Compose fg) = FoldMap (FoldMapSym1 f) fg

instance PFoldable (SG.Arg e) where
  type FoldMap am ('SG.Arg x a) = am @@ a

instance PFoldable (These e) where
  type FoldMap am ('This x) = Mempty
  type FoldMap am ('That a) = am @@ a
  type FoldMap am ('These x a) = am @@ a

type family Elem (x :: a) (ta :: t a) :: Bool where
  Elem a as = SUnWrap (FoldMap (SAnySym0 :.: EQSym1 a) as)

data ElemSym0 :: a ~> t a ~> Bool
type instance Apply ElemSym0 x = ElemSym1 x

data ElemSym1 :: a -> t a ~> Bool
type instance Apply (ElemSym1 x) y = Elem x y

type family AllF (p :: k ~> Bool) (xs :: t (k::x)) :: Bool where
  AllF p xs = SUnWrap (FoldMap (SAllSym0 :.: p) xs)

data AllFSym0 :: (k ~> Bool) ~> t k ~> Bool
type instance Apply AllFSym0 x = AllFSym1 x

data AllFSym1 :: (k ~> Bool) -> t k ~> Bool
type instance Apply (AllFSym1 x) y = AllF x y

type family AnyF (p :: k ~> Bool) (xs :: t (k::x)) :: Bool where
  AnyF p xs = SUnWrap (FoldMap (SAnySym0 :.: p) xs)

data AnyFSym0 :: (k ~> Bool) ~> t k ~> Bool
type instance Apply AnyFSym0 x = AnyFSym1 x

data AnyFSym1 :: (k ~> Bool) -> t k ~> Bool
type instance Apply (AnyFSym1 x) y = AnyF x y

-- CompareImpl and WhenCompare are the same but curried versions of each other
-- CompareImpl is easier to use
type family MaximumBy (f :: a ~> a ~> Ordering) (arg :: t a) :: a where
  MaximumBy f t = Foldr1 (CompareImplSym4 f SndSym0 SndSym0 FstSym0) t
--  MaximumBy f t = Foldr1 (CurrySym1 (WhenCompareSym4 (UnCurrySym1 f) SndSym0 SndSym0 FstSym0)) t

data MaximumBySym0 :: (a ~> a ~> Ordering) ~> t a ~> a
type instance Apply MaximumBySym0 x = MaximumBySym1 x

data MaximumBySym1 :: (a ~> a ~> Ordering) -> t a ~> a
type instance Apply (MaximumBySym1 x) y = MaximumBy x y


type family MinimumBy (f :: a ~> a ~> Ordering) (arg :: t a) :: a where
  MinimumBy f t = Foldr1 (CompareImplSym4 f FstSym0 SndSym0 SndSym0) t

data MinimumBySym0 :: (a ~> a ~> Ordering) ~> t a ~> a
type instance Apply MinimumBySym0 x = MinimumBySym1 x

data MinimumBySym1 :: (a ~> a ~> Ordering) -> t a ~> a
type instance Apply (MinimumBySym1 x) y = MinimumBy x y

