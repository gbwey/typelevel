{-# OPTIONS -Wall #-}
-- {-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns #-}
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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module PAlign where
import Data.These
import PCore
import PFunctor
import PBifunctor
import PSemigroup
import Control.Applicative
import Data.Functor.Product

class PFunctor f => PAlign f where
  type family Nil :: f a

  type family AlignWith (arg0 :: These a b ~> c) (arg :: f a) (arg1 :: f b) :: f c
  type AlignWith f fa fb = f <$> Align fa fb

  type family Align (arg :: f a) (arg1 :: f b) :: f (These a b)
  type Align fa fb = AlignWith Id fa fb

  type family PadZip (arg :: f a) (arg1 :: f b) :: f (Maybe a, Maybe b)
  type PadZip fa fb = AlignWith (FromTheseSym2 'Nothing 'Nothing :.: BimapSym2 (TyCon1Sym1 'Just) (TyCon1Sym1 'Just)) fa fb

  type family PadZipWith (arg0 :: Maybe a ~> Maybe b ~> c) (arg1 :: f a) (arg2 :: f b) :: f c
  type PadZipWith f fa fb = UnCurrySym1 f <$> PadZip fa fb


data PadZipWithSym0 :: (Maybe a ~> Maybe b ~> c) ~> f a ~> f b ~> f c
type instance Apply PadZipWithSym0 x = PadZipWithSym1 x

data PadZipWithSym1 :: (Maybe a ~> Maybe b ~> c) -> f a ~> f b ~> f c
type instance Apply (PadZipWithSym1 x) y = PadZipWithSym2 x y

data PadZipWithSym2 :: (Maybe a ~> Maybe b ~> c) -> f a -> f b ~> f c
type instance Apply (PadZipWithSym2 x y) z = PadZipWith x y z


instance PAlign [] where
  type Nil = '[]
  type AlignWith f '[] '[] = '[]
  type AlignWith f (a ': as) '[] = f :.: ThisSym0 <$> (a ': as)
  type AlignWith f '[] (b ': bs) = f :.: ThatSym0 <$> (b ': bs)
  type AlignWith f (a ': as) (b ': bs) = (f @@ 'These a b) ': AlignWith f as bs

instance PAlign Maybe where
  type Nil = 'Nothing
  type AlignWith f 'Nothing 'Nothing = 'Nothing
  type AlignWith f ('Just a) ('Just b) = 'Just (f @@ 'These a b)
  type AlignWith f ('Just a) 'Nothing = 'Just (f @@ 'This a)
  type AlignWith f 'Nothing ('Just b) = 'Just (f @@ 'That b)

instance PAlign ZipList where
  type Nil = 'ZipList '[]
  type AlignWith f ('ZipList as) ('ZipList bs) = 'ZipList (AlignWith f as bs)

instance (PAlign g, PAlign h) => PAlign (Product g h) where
  type Nil = 'Pair Nil Nil
  type AlignWith f ('Pair x y) ('Pair x1 y1) = 'Pair (AlignWith f x x1) (AlignWith f y y1)

class (PAlign f, PSemigroup a) => SalignC f a where
  type family Salign (arg0 :: f a) (arg1 :: f a) :: f a
  type Salign x y = AlignWith (MergeTheseSym1 SAppSym0) x y

-- you need this else doesnt work
instance (PAlign f, PSemigroup a) => SalignC f a

type family MergeThese (f :: a ~> a ~> a) (arg :: These a a) :: a where
  MergeThese f ('This a) = a
  MergeThese f ('That a1) = a1
  MergeThese f ('These a a1) = f @@ a @@ a1

data MergeTheseSym0 :: (a ~> a ~> a) ~> These a a ~> a
type instance Apply MergeTheseSym0 x = MergeTheseSym1 x

data MergeTheseSym1 :: (a ~> a ~> a) -> These a a ~> a
type instance Apply (MergeTheseSym1 x) y = MergeThese x y

type family FromThese (arg :: a) (arg1 :: b) (th :: These a b) :: (a,b) where
  FromThese a0 b0 ('This a) = '(a, b0)
  FromThese a0 b0 ('That b) = '(a0, b)
  FromThese a0 b0 ('These a b) = '(a, b)

data FromTheseSym0 :: a ~> b ~> These a b ~> (a,b)
type instance Apply FromTheseSym0 x = FromTheseSym1 x

data FromTheseSym1 :: a -> b ~> These a b ~> (a,b)
type instance Apply (FromTheseSym1 x) y = FromTheseSym2 x y

data FromTheseSym2 :: a -> b -> These a b ~> (a,b)
type instance Apply (FromTheseSym2 x y) z = FromThese x y z


-- | Left-padded 'zipWith'.
type family LpadZipWith (arg :: Maybe a ~> b ~> c) (arg1 :: [a]) (arg2 :: [b]) :: [c] where
  LpadZipWith f xs ys = CatMaybes (PadZipWith (FmapSym0 :.: f) xs ys)

-- | Left-padded 'zip'.
type family LpadZip (arg :: [a]) (arg1 :: [b]) :: [(Maybe a, b)] where
  LpadZip as bs  = LpadZipWith PairSym0 as bs

-- | Right-padded 'zipWith'.
type family RpadZipWith (arg :: a ~> Maybe b ~> c) (arg1 :: [a]) (arg2 :: [b]) :: [c] where
  RpadZipWith f as bs = LpadZipWith (FlipSym1 f) bs as

-- | Right-padded 'zip'.
type family RpadZip (arg :: [a]) (arg1 :: [b]) :: [(a, Maybe b)] where
  RpadZip as bs = RpadZipWith PairSym0 as bs

type family PartitionThese (arg :: [These a b]) :: ([(a,b)],([a],[b])) where
  PartitionThese '[] = '( '[], '( '[], '[] ) )
  PartitionThese ('This a ': ts) = '( '[], '( '[a], '[] ) ) <> PartitionThese ts
  PartitionThese ('That b ': ts) = '( '[], '( '[], '[b] ) ) <> PartitionThese ts
  PartitionThese ('These a b ': ts) = '( '[ '(a, b) ], '( '[], '[] ) ) <> PartitionThese ts

type family PartitionEithers (arg :: [Either a b]) :: ([a],[b]) where
  PartitionEithers '[] = '( '[], '[] )
  PartitionEithers ('Left a ': ts) = '( '[a], '[] ) <> PartitionEithers ts
  PartitionEithers ('Right b ': ts) = '( '[], '[b] ) <> PartitionEithers ts

