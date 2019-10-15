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
module PFoldableWithIndex where
import Data.List.NonEmpty (NonEmpty(..))
import PCore
import PMonoid
import PSemigroup
import Data.Functor.Identity
import Data.Functor.Compose
import PFoldable
import Data.Proxy
import Data.Tagged
import Control.Applicative

class PFoldable t => PFoldableWithIndex t where
  type family IfoldMap (arg :: FWI (t a) ~> a ~> m) (arg1 :: t a) :: m

  type family IToList (arg1 :: t a) :: [(FWI (t a), a)]
  type IToList as = IfoldMap (SingletonListSym0 :..: PairSym0) as

data IfoldMapSym1 :: (FWI (t a) ~> a ~> m) -> t a ~> m
type instance Apply (IfoldMapSym1 x) y = IfoldMap x y

instance PFoldableWithIndex ((,) z) where
  type IfoldMap f '(e,a) = f @@ e @@ a

instance PFoldableWithIndex [] where
  type IfoldMap f xs = FoldMap (UnCurrySym1 f) (IToList' 0 xs)

instance PFoldableWithIndex NonEmpty where
  type IfoldMap f (a ':| as) = (f @@ 0 @@ a) <> FoldMap (UnCurrySym1 f) (IToList' 1 as)

instance PFoldableWithIndex Maybe where
--  type IfoldMap f 'Nothing = Mempty
--  type IfoldMap f ('Just x) = f @@ '() @@ x
  type IfoldMap f x = Maybe' Mempty (f @@ '()) x

instance PFoldableWithIndex Proxy where
  type IfoldMap f 'Proxy = Mempty

instance PFoldableWithIndex (Tagged s) where
  type IfoldMap f ('Tagged a) = f @@ '() @@ a

instance PFoldableWithIndex ZipList where
  type IfoldMap f ('ZipList as) = IfoldMap f as

instance PFoldableWithIndex Identity where
  type IfoldMap f ('Identity a) = f @@ '() @@ a

-- argggg wont work (i,j) we need to vary the index
-- not allowed to use IfoldMapSym0 but can use IfoldMapSym1 -- make it work
instance (PFoldableWithIndex g, PFoldableWithIndex h) => PFoldableWithIndex (Compose g h) where
--  type IfoldMap f ('Compose fg) = IfoldMap (IfoldMapSym0 :.: (f (:.:)) :.: PairSym0) fg
  type IfoldMap f ('Compose fg) = IfoldMap (IfoldMap1Sym1 f) fg

type family IfoldMap1 f i xs where
  IfoldMap1 f i xs = IfoldMap (f :.: PairSym1 i) xs

--data IfoldMap1Sym0 :: (a1, FWI (t a2) ~> b) ~> a1 ~> t a2 ~> t b

--data IfoldMap1Sym0 :: ((a1,FWI (t a2)) ~> (a2 ~> b)) ~> a1 ~> t a2 ~> t b
--type instance Apply IfoldMap1Sym0 x = IfoldMap1Sym1 x

data IfoldMap1Sym1 :: ((a1,FWI (t a2)) ~> (a2 ~> m)) -> a1 ~> t a2 ~> m
type instance Apply (IfoldMap1Sym1 x) y = IfoldMap1Sym2 x y

data IfoldMap1Sym2 :: ((a1,FWI (t a2)) ~> (a2 ~> m)) -> a1 -> t a2 ~> m
type instance Apply (IfoldMap1Sym2 x y) z = IfoldMap1 x y z



