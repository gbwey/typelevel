-- for safety just use DTE.== cos has the best coverage
-- PEq ie == has too many gaps but is useful for POrd
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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module PEq where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import Data.Kind (Type)
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
import qualified Data.Type.Equality as DTE

class PEq (a :: Type) where
  type family (===) (x :: a) (y :: a) :: Bool
  type family (/==) (x :: a) (y :: a) :: Bool

  type x === y = x DTE.== y
  type x /== y = Not (x === y)
--  type (x :: a) == (y :: a) = x `DefaultEq` y

  infix 4 ===
  infix 4 /==

-- doesnt go deep enough if comparing kinds!
-- Nat DTE.== Nat is true but Nat `DefaultEq` Nat is stuck cos at the kind level

-- | A sensible way to compute Boolean equality for types of any kind. Note
-- that this definition is slightly different from the '(DTE.==)' type family
-- from "Data.Type.Equality" in @base@, as '(DTE.==)' attempts to distinguish
-- applications of type constructors from other types. As a result,
-- @a == a@ does not reduce to 'True' for every @a@, but @'DefaultEq' a a@
-- /does/ reduce to 'True' for every @a@. The latter behavior is more desirable
-- for @singletons@' purposes, so we use it instead of '(DTE.==)'.
type family DefaultEq (a :: k) (b :: k) :: Bool where
  DefaultEq a a = 'True
  DefaultEq a b = 'False

-- this == not EQ!
data PEqSym0 :: k ~> k ~> Bool
type instance Apply PEqSym0 x = PEqSym1 x

data PEqSym1 :: k -> k ~> Bool
type instance Apply (PEqSym1 x) y = x === y

data PNeSym0 :: k ~> k ~> Bool
type instance Apply PNeSym0 x = PNeSym1 x

data PNeSym1 :: k -> k ~> Bool
type instance Apply (PNeSym1 x) y = x /== y


-- special case only looks at first arg for equality
instance PEq (SG.Arg x y) where
  type 'SG.Arg a b === 'SG.Arg a1 b1 = a === a1

instance PEq Nat
instance PEq Ordering
instance PEq Bool
instance PEq ()
instance PEq Void

instance PEq x => PEq (SG.Option x) where
  type 'SG.Option a === 'SG.Option b = a === b

instance PEq y => PEq (Tagged x y) where
  type 'Tagged a === 'Tagged b = a === b

instance PEq z => PEq (Down z) where
  type 'Down x === 'Down y = x === y

instance PEq a => PEq (Maybe a) where
  type 'Just x === 'Just y = x === y
  type 'Just x === 'Nothing = 'False
  type 'Nothing === 'Just y = 'False
  type 'Nothing === 'Nothing = 'True

instance (PEq a, PEq b) => PEq (Either a b) where
  type 'Right x === 'Right y = x === y
  type 'Right x === 'Left y = 'False
  type 'Left x === 'Right y = 'False
  type 'Left x === 'Left y = x === y

instance PEq Symbol where
  type s === t = s DTE.== t

instance PEq (Proxy a) where
  type 'Proxy === 'Proxy = 'True

instance PEq x => PEq [x] where
  type '[] === '[] = 'True
  type (a ': as) === (b ': bs) = a === b && as === bs
  type '[] === (b ': bs) = 'False
  type (a ': as) === '[] = 'False

instance PEq z => PEq (ZipList z) where
  type 'ZipList as === 'ZipList bs = as === bs

instance PEq z => PEq (NonEmpty z) where
  type (a ':| as) === (b ':| bs) = a === b && as === bs

instance (PEq x, PEq y) => PEq (These x y) where
  type 'This a === 'This b = a === b
  type 'This a === 'That b = 'False
  type 'This a === 'These a1 b1 = 'False

  type 'That a === 'This b = 'False
  type 'That a === 'That b = a === b
  type 'That a === 'These a1 b1 = 'False

  type 'These a b === 'This a1 = 'False
  type 'These a b === 'That b1 = 'False
  type 'These a b === 'These a1 b1 = a === a1 && b === b1


instance PEq z => PEq (SG.Dual z) where
  type 'SG.Dual a === 'SG.Dual b = a === b
instance PEq z => PEq (SG.Sum z) where
  type 'SG.Sum a === 'SG.Sum b = a === b
instance PEq z => PEq (SG.Min z) where
  type 'SG.Min a === 'SG.Min b = a === b
instance PEq z => PEq (SG.Max z) where
  type 'SG.Max a === 'SG.Max b = a === b
instance PEq z => PEq (SG.Last z) where
  type 'SG.Last a === 'SG.Last b = a === b
instance PEq z => PEq (SG.First z) where
  type 'SG.First a === 'SG.First b = a === b
instance PEq z => PEq (MM.Last z) where
  type 'MM.Last a === 'MM.Last b = a === b
instance PEq z => PEq (MM.First z) where
  type 'MM.First a === 'MM.First b = a === b
instance PEq MM.All where
  type 'MM.All b === 'MM.All b1 = b === b1
instance PEq MM.Any where
  type 'MM.Any b === 'MM.Any b1 = b === b1
instance PEq z => PEq (Identity z) where
  type 'Identity a === 'Identity a1 = a === a1
instance (PEq z1, PEq z2) => PEq (z1, z2) where
  type '(a,b) === '(a1,b1) = a === a1 && b === b1
instance (PEq z1, PEq z2, PEq z3) => PEq (z1, z2, z3) where
  type '(a,b,c) === '(a1,b1,c1) = a === a1 && b === b1 && c === c1
instance (PEq z1, PEq z2, PEq z3, PEq z4) => PEq (z1, z2, z3, z4) where
  type '(a,b,c,d) === '(a1,b1,c1,d1) = a === a1 && b === b1 && c === c1 && d === d1
instance PEq Int

instance PEq z => PEq (Const z x) where
  type 'Const a === 'Const a1 = a === a1


