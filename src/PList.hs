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
module PList where
import PCore
import GHC.TypeLits hiding (natVal,natVal')
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty(..))
import PFoldable

data UnConsSym0 :: t a ~> Maybe (a, [a])
type instance Apply UnConsSym0 x = UnCons x

data UnSnocSym0 :: t a ~> Maybe ([a], a)
type instance Apply UnSnocSym0 x = UnSnoc x

-- choosing to return a list no matter what
-- really should be in PFoldable but for the moment
class PList (t :: Type -> Type) where
  type family UnCons (xs :: t a) :: Maybe (a, [a])
--  type UnCons x = TypeError ('Text "PList UnCons is undefined x=" ':<>: 'ShowType x)

  type family UnCons' (xs :: t a) :: (a, [a])
  type UnCons' xs = Maybe' (TypeError ('Text "PList UnCons' empty container")) Id (UnCons xs)

  type family UnSnoc (xs :: t a) :: Maybe ([a], a)
--  type UnSnoc x = TypeError ('Text "PList UnSnoc is undefined x=" ':<>: 'ShowType x)

  type family UnSnoc' (xs :: t a) :: ([a], a)
  type UnSnoc' xs = Maybe' (TypeError ('Text "PList UnSnoc' empty container")) Id (UnSnoc xs)

-- these are partial : use UnCons and UnSnoc and peel out the piece you want
  type family Head' (xs :: t a) :: a
  type Head' xs = Fst (UnCons' xs)

  type family Tail' (xs :: t a) :: [a]
  type Tail' xs = Snd (UnCons' xs)

  type family Init' (xs :: t a) :: [a]
  type Init' xs = Fst (UnSnoc' xs)

  type family Last' (xs :: t a) :: a
  type Last' xs = Snd (UnSnoc' xs)

instance PList [] where
  type UnCons '[] = 'Nothing
  type UnCons (a ': as) = 'Just '(a, as)

  type UnSnoc '[] = 'Nothing
  type UnSnoc (a ': as) = 'Just (UnSnocList (a ': as))

instance PList NonEmpty where
  type UnCons as = UnCons (ToList as)

  type UnSnoc as = UnSnoc (ToList as)

type family UnSnocList (as :: [a]) :: ([a], a) where
  UnSnocList '[] = TypeError ('Text "PList UnSnoc' empty list")
  UnSnocList (a ': '[]) = '( '[], a )
  UnSnocList (a ': a1 ': as) = First (ConsSym1 a)  (UnSnocList (a1 ': as))

