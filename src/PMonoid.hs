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
module PMonoid where
import GHC.TypeLits hiding (natVal,natVal')
import Data.Constraint
import qualified Data.Monoid as MM
import qualified Data.Semigroup as SG
import PCore
import PSemigroup
import PNum
import Data.Functor.Const
import Data.Functor.Identity
import Data.Ord
import Data.Tagged
import Data.Proxy
import Control.Applicative
import Data.Kind (Type)
-- type family == type within class instance
class PSemigroup a => PMonoid a where
  type family Mempty :: a
--  type Mempty = TypeError ('Text "PMonoid Mempty is undefined")

  type family Mappend (arg :: a) (arg1 :: a) :: a
  type Mappend x y = x <> y  -- default version but can override

  type family Mconcat (arg :: [a]) :: a -- could use Fold
  type Mconcat xs = Foldr SAppSym0 Mempty xs

instance PMonoid Constraint where
  type Mempty = (() :: Constraint)

{-
>:kind! Mconcat '[KnownNat 4, KnownNat 5]
Mconcat '[KnownNat 4, KnownNat 5] :: Constraint
= (KnownNat 4, (KnownNat 5, () :: Constraint))
-}

instance PMonoid (SG.Sum a) where
  type Mempty = 'SG.Sum (FromInteger 0)

instance PMonoid (SG.Product a) where
  type Mempty = 'SG.Product (FromInteger 1)

instance PMonoid (SG.Option a) where
  type Mempty = 'SG.Option 'Nothing

instance PMonoid (Maybe a) where
  type Mempty = 'Nothing
--  type Mappend x y = x <> y

-- oops used 'Just a instead of 'Just x [actually anything but 'a' cos in head
instance PMonoid (MM.First a) where
  type Mempty = 'MM.First 'Nothing

instance PMonoid (MM.Last a) where
  type Mempty = 'MM.Last 'Nothing

instance PMonoid Ordering where
  type Mempty = 'EQ

instance PMonoid (SG.Max a) where
  type Mempty = 'SG.Max (FromInteger 0)

instance PMonoid (a ~> (b :: Type)) where
  type Mempty = KSym1 Mempty

instance PMonoid (EndoX a) where
  type Mempty = 'EndoX Id

instance PMonoid [a] where
  type Mempty = '[]

instance PMonoid SG.All where
  type Mempty = 'SG.All 'True


instance PMonoid SG.Any where
  type Mempty = 'SG.Any 'False

instance PMonoid (a,b) where
  type Mempty = '(Mempty, Mempty)

instance PMonoid (a, b, c) where
  type Mempty = '(Mempty, Mempty, Mempty)

instance PMonoid (a, b, c, d) where
  type Mempty = '(Mempty, Mempty, Mempty, Mempty)

instance PMonoid (SG.Dual a) where
  type Mempty = 'SG.Dual Mempty

data MFirstSym0 :: a ~> MM.First a
type instance Apply MFirstSym0 x = 'MM.First ('Just x)

data MLastSym0 :: a ~> MM.Last a
type instance Apply MLastSym0 x = 'MM.Last ('Just x)

instance PMonoid () where
  type Mempty = '()

instance PMonoid Symbol where
  type Mempty = ""

instance PMonoid (Const e a) where
  type Mempty = 'Const Mempty

instance PMonoid (Identity a) where
  type Mempty = 'Identity Mempty

instance PMonoid (Proxy z) where
  type Mempty = 'Proxy

instance PMonoid (Tagged s a) where
  type Mempty = 'Tagged Mempty

-- there is no instance for monoid or semigroup
--instance PMonoid (ZipList a) where
--  type Mempty = 'ZipList Mempty

instance PMonoid (ZipList z) where
  type Mempty = 'ZipList '[]


data MconcatSym0 :: [m] ~> m
type instance Apply MconcatSym0 x = Mconcat x

instance PMonoid (Down z) where
  type Mempty = 'Down Mempty

-- ok so it doesnt exist in Monoid but we need it! this stuff is hard enuf as it is...
instance PMonoid (Either e a) where
  type Mempty = 'Left Mempty

