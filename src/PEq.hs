-- for safety just use DTE.== cos has the best coverage
-- PEq ie == has too many gaps but is useful for POrd
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
module PEq where
import GHC.TypeNats ( Nat )
import GHC.TypeLits ( Symbol )
import Data.Kind (Type)
import PCore
import Data.Functor.Identity ( Identity(Identity) )
import Data.Ord ( Down(Down) )
import qualified Data.Semigroup as SG
import qualified Data.Monoid as MM
import Data.Tagged ( Tagged(Tagged) )
import Data.Proxy ( Proxy(..) )
import Control.Applicative ( ZipList(ZipList), Const(Const) )
import Data.These ( These(..) )
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void ( Void )
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
  DefaultEq _ _ = 'False

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
  type 'SG.Arg a _ === 'SG.Arg a1 _ = a === a1

instance PEq Nat
instance PEq Ordering
instance PEq Bool
instance PEq ()
instance PEq Void

instance PEq (SG.Option x) where
  type 'SG.Option a === 'SG.Option b = a === b

instance PEq (Tagged x y) where
  type 'Tagged a === 'Tagged b = a === b

instance PEq (Down z) where
  type 'Down x === 'Down y = x === y

instance PEq (Maybe a) where
  type 'Just x === 'Just y = x === y
  type 'Just _ === 'Nothing = 'False
  type 'Nothing === 'Just _ = 'False
  type 'Nothing === 'Nothing = 'True

instance PEq (Either a b) where
  type 'Right x === 'Right y = x === y
  type 'Right _ === 'Left _ = 'False
  type 'Left _ === 'Right _ = 'False
  type 'Left x === 'Left y = x === y

instance PEq Symbol where
  type s === t = s DTE.== t

instance PEq (Proxy a) where
  type 'Proxy === 'Proxy = 'True

instance PEq [x] where
  type '[] === '[] = 'True
  type (a ': as) === (b ': bs) = a === b && as === bs
  type '[] === (_ ': _) = 'False
  type (_ ': _) === '[] = 'False

instance PEq (ZipList z) where
  type 'ZipList as === 'ZipList bs = as === bs

instance PEq (NonEmpty z) where
  type (a ':| as) === (b ':| bs) = a === b && as === bs

instance PEq (These x y) where
  type 'This a === 'This b = a === b
  type 'This _ === 'That _ = 'False
  type 'This _ === 'These _ _ = 'False

  type 'That _ === 'This _ = 'False
  type 'That a === 'That b = a === b
  type 'That _ === 'These _ _ = 'False

  type 'These _ _ === 'This _ = 'False
  type 'These _ _ === 'That _ = 'False
  type 'These a b === 'These a1 b1 = a === a1 && b === b1


instance PEq (SG.Dual z) where
  type 'SG.Dual a === 'SG.Dual b = a === b
instance PEq (SG.Sum z) where
  type 'SG.Sum a === 'SG.Sum b = a === b
instance PEq (SG.Min z) where
  type 'SG.Min a === 'SG.Min b = a === b
instance PEq (SG.Max z) where
  type 'SG.Max a === 'SG.Max b = a === b
instance PEq (SG.Last z) where
  type 'SG.Last a === 'SG.Last b = a === b
instance PEq (SG.First z) where
  type 'SG.First a === 'SG.First b = a === b
instance PEq (MM.Last z) where
  type 'MM.Last a === 'MM.Last b = a === b
instance PEq (MM.First z) where
  type 'MM.First a === 'MM.First b = a === b
instance PEq MM.All where
  type 'MM.All b === 'MM.All b1 = b === b1
instance PEq MM.Any where
  type 'MM.Any b === 'MM.Any b1 = b === b1
instance PEq (Identity z) where
  type 'Identity a === 'Identity a1 = a === a1
instance PEq (z1, z2) where
  type '(a,b) === '(a1,b1) = a === a1 && b === b1
instance PEq (z1, z2, z3) where
  type '(a,b,c) === '(a1,b1,c1) = a === a1 && b === b1 && c === c1
instance PEq (z1, z2, z3, z4) where
  type '(a,b,c,d) === '(a1,b1,c1,d1) = a === a1 && b === b1 && c === c1 && d === d1
instance PEq Int

instance PEq (Const z x) where
  type 'Const a === 'Const a1 = a === a1


